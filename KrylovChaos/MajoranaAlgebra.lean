/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Concrete Majorana Clifford Algebra, Fermion Parity, Filtration & Eq. (2.10) (Item #1)

Constructs `2n` Hermitian Majorana fermion generators `{γ_j}_{j=0}^{2n-1}` on the `n`-qubit
Hilbert space `QubitOp n` (`dim H = 2^n`) via the Jordan–Wigner transformation:
- `V_{2k}   = Z_0 ⋯ Z_{k-1} X_k`
- `V_{2k+1} = Z_0 ⋯ Z_{k-1} Y_k`
- `γ_j      = (1 / √2) V_j`

Proves from first principles (zero axioms, zero sorrys):
1. Hermiticity `V_jᴴ = V_j`, `γ_jᴴ = γ_j`, involution `V_j² = 1`, and Clifford anticommutation
   `{V_i, V_j} = 2 δ_{ij} 1`, `{γ_i, γ_j} = δ_{ij} 1`.
2. **Fermion Parity (`fermionParityOp`, `isEvenParity`, `isOddParity`)**: Global parity
   `P = Z_0 ⊗ ⋯ ⊗ Z_{n-1}` anticommuting with every `V_j`, plus `majoranaString n Q` and
   `majoranaFiltrationSubmodule n s`.
3. **Parity-Aware Majorana Operator-Size Superoperator (`majoranaParitySizeOp`)**:
   Evaluates to `|Q| • M_Q` on EVERY Majorana string `M_Q` (both even AND odd degree `|Q|`!),
   equals `(1/4) ∑_j ‖[M, V_j]‖_HS²` on even-parity `M` and `(1/4) ∑_j ‖{M, V_j}‖_HS²` on
   odd-parity `M`, and satisfies `0 ≤ Re ⟨M, S_Maj M⟩_HS ≤ (2n) ‖M‖_HS²`.
4. **Proposition 2.3(2) (Exact Eq. 2.10 with `+ F_MSS`)**:
   For even-parity `G.ρQuarter` and odd-parity Hermitian normalized `A`:
   `majoranaThermalSize G A = (1 / 2) ∑_{j=0}^{2n-1} (C_{β, V_j}^W(0) + F_MSS(A, V_j))`.
-/

namespace KrylovChaos

open Matrix

section JordanWigner

/-- Jordan–Wigner Pauli-string word for the `j`-th Majorana mode (`0 ≤ j < 2n`) on `n` qubits:
`Z` on sites `< j/2`, `X` (if `j` even) or `Y` (if `j` odd) on site `j/2`, and `I` on sites `> j/2`. -/
def jwWord (n : ℕ) (j : Fin (2 * n)) : Fin n → Fin 4 :=
  fun x ↦
    if x.1 < j.1 / 2 then 3
    else if x.1 = j.1 / 2 then (if j.1 % 2 = 0 then 1 else 2)
    else 0

/-- Normalized Majorana probe `V_j = √2 γ_j` as a concrete Pauli string on `QubitOp n`. -/
def majoranaProbe (n : ℕ) (j : Fin (2 * n)) : QubitOp n :=
  pauliString (jwWord n j)

/-- Concrete Majorana generator `γ_j = (1 / √2) V_j` on `QubitOp n`. -/
noncomputable def majoranaGen (n : ℕ) (j : Fin (2 * n)) : QubitOp n :=
  ((Real.sqrt 2 : ℂ)⁻¹) • majoranaProbe n j

/-- Every Majorana probe `V_j` is Hermitian. -/
theorem majoranaProbe_herm (n : ℕ) (j : Fin (2 * n)) :
    (majoranaProbe n j)ᴴ = majoranaProbe n j :=
  pauliString_herm (jwWord n j)

/-- Every Majorana probe `V_j` squares to the identity `V_j² = 1`. -/
theorem majoranaProbe_sq (n : ℕ) (j : Fin (2 * n)) :
    majoranaProbe n j * majoranaProbe n j = 1 :=
  pauliString_sq (jwWord n j)

/-- Every Majorana generator `γ_j` is Hermitian. -/
theorem majoranaGen_herm (n : ℕ) (j : Fin (2 * n)) :
    (majoranaGen n j)ᴴ = majoranaGen n j := by
  unfold majoranaGen
  rw [Matrix.conjTranspose_smul, majoranaProbe_herm]
  congr 1
  simp [Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- Single-site Pauli commutation sign: `pauliMat α * pauliMat β = ± pauliMat β * pauliMat α`. -/
private lemma pauliMat_comm_sign (α β : Fin 4) :
    pauliMat β * pauliMat α =
      (if α = 0 ∨ β = 0 ∨ α = β then (1 : ℂ) else (-1 : ℂ)) • (pauliMat α * pauliMat β) := by
  fin_cases α <;> fin_cases β <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Distinct Majorana probes `V_i, V_j` (`i ≠ j`) anticommute: `V_j * V_i = -(V_i * V_j)`. -/
theorem majoranaProbe_anticomm {n : ℕ} {i j : Fin (2 * n)} (hij : i ≠ j) :
    majoranaProbe n j * majoranaProbe n i = -(majoranaProbe n i * majoranaProbe n j) := by
  unfold majoranaProbe pauliString
  rw [kronOp_mul, kronOp_mul]
  have hsite : ∀ x : Fin n,
      pauliMat (jwWord n j x) * pauliMat (jwWord n i x) =
      (if jwWord n i x = 0 ∨ jwWord n j x = 0 ∨ jwWord n i x = jwWord n j x then (1 : ℂ) else (-1 : ℂ)) •
        (pauliMat (jwWord n i x) * pauliMat (jwWord n j x)) :=
    fun x ↦ pauliMat_comm_sign (jwWord n i x) (jwWord n j x)
  have hkron : kronOp (fun x ↦ pauliMat (jwWord n j x) * pauliMat (jwWord n i x)) =
      (∏ x : Fin n, if jwWord n i x = 0 ∨ jwWord n j x = 0 ∨ jwWord n i x = jwWord n j x
          then (1 : ℂ) else (-1 : ℂ)) •
      kronOp (fun x ↦ pauliMat (jwWord n i x) * pauliMat (jwWord n j x)) := by
    ext r c
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro x _
    rw [hsite x, Matrix.smul_apply, smul_eq_mul]
  rw [hkron]
  let x₀ : Fin n := ⟨min (i.1 / 2) (j.1 / 2), by omega⟩
  have hprod_neg : (∏ x : Fin n,
      if jwWord n i x = 0 ∨ jwWord n j x = 0 ∨ jwWord n i x = jwWord n j x
        then (1 : ℂ) else (-1 : ℂ)) = -1 := by
    rw [Finset.prod_eq_single x₀]
    · have hne : ¬(jwWord n i x₀ = 0 ∨ jwWord n j x₀ = 0 ∨ jwWord n i x₀ = jwWord n j x₀) := by
        unfold jwWord
        have hij' : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
        rcases lt_trichotomy (i.1 / 2) (j.1 / 2) with hlt | heq | hgt
        · have hx : x₀.1 = i.1 / 2 := min_eq_left (le_of_lt hlt)
          have h1 : ¬(x₀.1 < i.1 / 2) := by omega
          have h2 : x₀.1 < j.1 / 2 := by omega
          simp only [h1, ↓reduceIte, hx, h2]
          split_ifs <;> decide
        · have hx : x₀.1 = i.1 / 2 := by simp [x₀, heq]
          have h1 : ¬(x₀.1 < i.1 / 2) := by omega
          have h2 : ¬(x₀.1 < j.1 / 2) := by omega
          have h3 : x₀.1 = j.1 / 2 := by omega
          have hmod : i.1 % 2 ≠ j.1 % 2 := by omega
          simp only [h1, h2, ↓reduceIte, hx, h3]
          by_cases hm : i.1 % 2 = 0
          · have hm2 : ¬(j.1 % 2 = 0) := by omega
            simp [hm, hm2]
          · have hm2 : j.1 % 2 = 0 := by omega
            simp [hm, hm2]
        · have hx : x₀.1 = j.1 / 2 := min_eq_right (le_of_lt hgt)
          have h1 : x₀.1 < i.1 / 2 := by omega
          have h2 : ¬(x₀.1 < j.1 / 2) := by omega
          simp only [h1, ↓reduceIte, hx, h2]
          split_ifs <;> decide
      rw [if_neg hne]
    · intro x _ hne_x
      have hcomm : jwWord n i x = 0 ∨ jwWord n j x = 0 ∨ jwWord n i x = jwWord n j x := by
        have hxv : x.1 ≠ min (i.1 / 2) (j.1 / 2) := fun h ↦ hne_x (Fin.ext h)
        unfold jwWord
        by_cases hlt : x.1 < min (i.1 / 2) (j.1 / 2)
        · right; right
          have h1 : x.1 < i.1 / 2 := lt_of_lt_of_le hlt (min_le_left _ _)
          have h2 : x.1 < j.1 / 2 := lt_of_lt_of_le hlt (min_le_right _ _)
          simp [h1, h2]
        · have hgt : min (i.1 / 2) (j.1 / 2) < x.1 := by omega
          rcases le_total (i.1 / 2) (j.1 / 2) with hle | hle
          · left
            have h1 : ¬(x.1 < i.1 / 2) := by omega
            have h2 : ¬(x.1 = i.1 / 2) := by omega
            simp [h1, h2]
          · right; left
            have h1 : ¬(x.1 < j.1 / 2) := by omega
            have h2 : ¬(x.1 = j.1 / 2) := by omega
            simp [h1, h2]
      rw [if_pos hcomm]
    · intro hx; exact absurd (Finset.mem_univ x₀) hx
  rw [hprod_neg, neg_one_smul]

/-- **Clifford Anticommutation Relations for Normalized Probes `{V_i, V_j} = 2 δ_{ij} 1`**: -/
theorem majoranaProbe_clifford (n : ℕ) (i j : Fin (2 * n)) :
    majoranaProbe n i * majoranaProbe n j + majoranaProbe n j * majoranaProbe n i =
      (if i = j then (2 : ℂ) else 0) • (1 : QubitOp n) := by
  by_cases h : i = j
  · subst h
    rw [majoranaProbe_sq, if_pos rfl, two_smul]
  · rw [if_neg h, zero_smul, majoranaProbe_anticomm h, add_neg_cancel]

/-- **Clifford Anticommutation Relations for Majorana Generators `{γ_i, γ_j} = δ_{ij} 1`**: -/
theorem majoranaGen_clifford (n : ℕ) (i j : Fin (2 * n)) :
    majoranaGen n i * majoranaGen n j + majoranaGen n j * majoranaGen n i =
      (if i = j then (1 : ℂ) else 0) • (1 : QubitOp n) := by
  unfold majoranaGen
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_add]
  rw [majoranaProbe_clifford, smul_smul]
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (2 : ℂ) = 1 := by
    have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      intro hz
      have := congrArg (· * (Real.sqrt 2 : ℂ)) hz
      simp [h2] at this
    field_simp [hne]
    rw [h2]
  split_ifs with h
  · rw [hsq]
  · simp

end JordanWigner

section FermionParityAndMajoranaStrings

/-- Global fermion parity operator `P = Z_0 ⊗ ⋯ ⊗ Z_{n-1}` on `QubitOp n`. -/
def fermionParityOp (n : ℕ) : QubitOp n :=
  pauliString (fun _ ↦ 3)

lemma fermionParityOp_herm (n : ℕ) : (fermionParityOp n)ᴴ = fermionParityOp n :=
  pauliString_herm _

lemma fermionParityOp_sq (n : ℕ) : fermionParityOp n * fermionParityOp n = 1 :=
  pauliString_sq _

/-- Global fermion parity anticommutes with every Majorana probe: `P V_j = - V_j P`. -/
theorem fermionParityOp_anticomm_probe (n : ℕ) (j : Fin (2 * n)) :
    fermionParityOp n * majoranaProbe n j = -(majoranaProbe n j * fermionParityOp n) := by
  unfold fermionParityOp majoranaProbe pauliString
  rw [kronOp_mul, kronOp_mul]
  have hsite : ∀ x : Fin n,
      pauliMat 3 * pauliMat (jwWord n j x) =
      (if jwWord n j x = 0 ∨ (3 : Fin 4) = 0 ∨ jwWord n j x = 3 then (1 : ℂ) else (-1 : ℂ)) •
        (pauliMat (jwWord n j x) * pauliMat 3) :=
    fun x ↦ pauliMat_comm_sign (jwWord n j x) 3
  have hkron : kronOp (fun x ↦ pauliMat 3 * pauliMat (jwWord n j x)) =
      (∏ x : Fin n, if jwWord n j x = 0 ∨ (3 : Fin 4) = 0 ∨ jwWord n j x = 3
          then (1 : ℂ) else (-1 : ℂ)) •
      kronOp (fun x ↦ pauliMat (jwWord n j x) * pauliMat 3) := by
    ext r c
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro x _
    rw [hsite x, Matrix.smul_apply, smul_eq_mul]
  rw [hkron]
  let x₀ : Fin n := ⟨j.1 / 2, by omega⟩
  have hprod_neg : (∏ x : Fin n,
      if jwWord n j x = 0 ∨ (3 : Fin 4) = 0 ∨ jwWord n j x = 3
        then (1 : ℂ) else (-1 : ℂ)) = -1 := by
    rw [Finset.prod_eq_single x₀]
    · have hne : ¬(jwWord n j x₀ = 0 ∨ (3 : Fin 4) = 0 ∨ jwWord n j x₀ = 3) := by
        unfold jwWord
        have h1 : ¬(x₀.1 < j.1 / 2) := by omega
        have h2 : x₀.1 = j.1 / 2 := rfl
        simp only [h1, h2, ↓reduceIte]
        split_ifs <;> decide
      rw [if_neg hne]
    · intro x _ hne_x
      have hcomm : jwWord n j x = 0 ∨ (3 : Fin 4) = 0 ∨ jwWord n j x = 3 := by
        have hxv : x.1 ≠ j.1 / 2 := fun h ↦ hne_x (Fin.ext h)
        unfold jwWord
        by_cases hlt : x.1 < j.1 / 2
        · right; right; simp [hlt]
        · left; simp [hlt, hxv]
      rw [if_pos hcomm]
    · intro hx; exact absurd (Finset.mem_univ x₀) hx
  rw [hprod_neg, neg_one_smul]

/-- An operator `A : QubitOp n` has even fermion parity iff `P A P = A`. -/
def isEvenParity {n : ℕ} (A : QubitOp n) : Prop :=
  fermionParityOp n * A * fermionParityOp n = A

/-- An operator `A : QubitOp n` has odd fermion parity iff `P A P = -A`. -/
def isOddParity {n : ℕ} (A : QubitOp n) : Prop :=
  fermionParityOp n * A * fermionParityOp n = -A

lemma isEvenParity_mul {n : ℕ} {A B : QubitOp n} (hA : isEvenParity A) (hB : isEvenParity B) :
    isEvenParity (A * B) := by
  unfold isEvenParity at hA hB ⊢
  calc fermionParityOp n * (A * B) * fermionParityOp n
      = (fermionParityOp n * A * (fermionParityOp n * fermionParityOp n) * B * fermionParityOp n) := by
        rw [fermionParityOp_sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (fermionParityOp n * A * fermionParityOp n) * (fermionParityOp n * B * fermionParityOp n) := by
        simp only [Matrix.mul_assoc]
    _ = A * B := by rw [hA, hB]

lemma jBeta_evenParity_of_even {n : ℕ} (G : GibbsData n) {A : QubitOp n}
    (hρ : isEvenParity G.ρQuarter) (hA : isEvenParity A) :
    isEvenParity (jBeta G.ρQuarter A) :=
  isEvenParity_mul (isEvenParity_mul hρ hA) hρ

lemma jBeta_oddParity_of_odd {n : ℕ} (G : GibbsData n) {A : QubitOp n}
    (hρ : isEvenParity G.ρQuarter) (hA : isOddParity A) :
    isOddParity (jBeta G.ρQuarter A) := by
  unfold isEvenParity at hρ; unfold isOddParity at hA ⊢; unfold jBeta
  calc fermionParityOp n * (G.ρQuarter * A * G.ρQuarter) * fermionParityOp n
      = (fermionParityOp n * G.ρQuarter * fermionParityOp n) *
          (fermionParityOp n * A * fermionParityOp n) *
          (fermionParityOp n * G.ρQuarter * fermionParityOp n) := by
        simp only [Matrix.mul_assoc]
        have h1 : fermionParityOp n * (fermionParityOp n * A * (fermionParityOp n * (fermionParityOp n * G.ρQuarter * fermionParityOp n))) =
            (fermionParityOp n * fermionParityOp n) * A * ((fermionParityOp n * fermionParityOp n) * G.ρQuarter * fermionParityOp n) := by
          simp only [Matrix.mul_assoc]
        rw [h1, fermionParityOp_sq, Matrix.one_mul, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = G.ρQuarter * (-A) * G.ρQuarter := by rw [hρ, hA]
    _ = -(G.ρQuarter * A * G.ρQuarter) := by simp [Matrix.mul_neg, Matrix.neg_mul]

lemma rhoHalf_evenParity {n : ℕ} (G : GibbsData n) (hρ : isEvenParity G.ρQuarter) :
    isEvenParity G.ρHalf := by
  rw [← G.sq_quarter]; exact isEvenParity_mul hρ hρ

/-- Ordered Majorana string `M_Q = V_{j_1} V_{j_2} ⋯ V_{j_{|Q|}}` for `Q ⊆ {0, …, 2n-1}`. -/
def majoranaString (n : ℕ) (Q : Finset (Fin (2 * n))) : QubitOp n :=
  (Q.sort (· ≤ ·)).foldr (fun j acc ↦ majoranaProbe n j * acc) 1

/-- Majorana filtration subspace `𝒱_s^{Maj} = span { M_Q | |Q| ≤ s }` on `QubitOp n`. -/
def majoranaFiltrationSubmodule (n s : ℕ) : Submodule ℂ (QubitOp n) :=
  Submodule.span ℂ { M : QubitOp n | ∃ Q : Finset (Fin (2 * n)), Q.card ≤ s ∧ M = majoranaString n Q }

private lemma foldr_probe_conj_parity (n : ℕ) (l : List (Fin (2 * n))) :
    fermionParityOp n * (l.foldr (fun j acc ↦ majoranaProbe n j * acc) 1) * fermionParityOp n =
      ((-1 : ℂ) ^ l.length) • (l.foldr (fun j acc ↦ majoranaProbe n j * acc) 1) := by
  induction l with
  | nil => simp [fermionParityOp_sq]
  | cons a t ih =>
    simp only [List.foldr_cons, List.length_cons]
    calc fermionParityOp n * (majoranaProbe n a * t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1) * fermionParityOp n
        = (fermionParityOp n * majoranaProbe n a) * (t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1 * fermionParityOp n) := by
          simp only [Matrix.mul_assoc]
      _ = -(majoranaProbe n a * fermionParityOp n) * (t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1 * fermionParityOp n) := by
          rw [fermionParityOp_anticomm_probe]
      _ = -(majoranaProbe n a * (fermionParityOp n * t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1 * fermionParityOp n)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(majoranaProbe n a * (((-1 : ℂ) ^ t.length) • t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1)) := by
          rw [ih]
      _ = ((-1 : ℂ) ^ (t.length + 1)) • (majoranaProbe n a * t.foldr (fun j acc ↦ majoranaProbe n j * acc) 1) := by
          rw [Matrix.mul_smul, pow_succ, mul_comm, ← smul_smul, neg_one_smul]

/-- Parity of any Majorana string `M_Q`: `P M_Q P = (-1)^{|Q|} M_Q`. -/
theorem majoranaString_parity (n : ℕ) (Q : Finset (Fin (2 * n))) :
    fermionParityOp n * majoranaString n Q * fermionParityOp n =
      ((-1 : ℂ) ^ Q.card) • majoranaString n Q := by
  unfold majoranaString
  rw [foldr_probe_conj_parity, Finset.length_sort]

private lemma foldr_probe_conj_probe (n : ℕ) (j : Fin (2 * n)) (l : List (Fin (2 * n)))
    (hnd : l.Nodup) :
    majoranaProbe n j * (l.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) * majoranaProbe n j =
      ((-1 : ℂ) ^ (l.length - if j ∈ l then 1 else 0)) •
        (l.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) := by
  induction l with
  | nil => simp [majoranaProbe_sq]
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_not, ht_nd⟩
    simp only [List.foldr_cons, List.length_cons, List.mem_cons]
    by_cases hja : j = a
    · subst hja
      simp only [true_or, ↓reduceIte, Nat.add_sub_cancel]
      have hj_not : j ∉ t := ha_not
      have iht := ih ht_nd
      simp only [hj_not, ↓reduceIte, Nat.sub_zero] at iht
      calc majoranaProbe n j * (majoranaProbe n j * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) * majoranaProbe n j
          = (majoranaProbe n j * majoranaProbe n j) * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j := by
            simp only [Matrix.mul_assoc]
        _ = (1 * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) * majoranaProbe n j := by
            rw [majoranaProbe_sq]
        _ = majoranaProbe n j * (majoranaProbe n j * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j) := by
            rw [Matrix.one_mul]
            calc t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j
                = (majoranaProbe n j * majoranaProbe n j) * (t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j) := by
                  rw [majoranaProbe_sq, Matrix.one_mul]
              _ = majoranaProbe n j * (majoranaProbe n j * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j) := by
                  simp only [Matrix.mul_assoc]
        _ = majoranaProbe n j * (((-1 : ℂ) ^ t.length) • t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) := by
            rw [iht]
        _ = ((-1 : ℂ) ^ t.length) • (majoranaProbe n j * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) := by
            rw [Matrix.mul_smul]
    · simp only [hja, false_or]
      have iht := ih ht_nd
      calc majoranaProbe n j * (majoranaProbe n a * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) * majoranaProbe n j
          = (majoranaProbe n j * majoranaProbe n a) * (t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j) := by
            simp only [Matrix.mul_assoc]
        _ = -(majoranaProbe n a * majoranaProbe n j) * (t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j) := by
            rw [majoranaProbe_anticomm (Ne.symm hja)]
        _ = -(majoranaProbe n a * (majoranaProbe n j * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1 * majoranaProbe n j)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(majoranaProbe n a * (((-1 : ℂ) ^ (t.length - if j ∈ t then 1 else 0)) •
              t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1)) := by
            rw [iht]
        _ = ((-1 : ℂ) ^ (t.length + 1 - if j ∈ t then 1 else 0)) •
              (majoranaProbe n a * t.foldr (fun k acc ↦ majoranaProbe n k * acc) 1) := by
            rw [Matrix.mul_smul]
            by_cases hjt : j ∈ t
            · have hpos : 1 ≤ t.length := List.length_pos_of_mem hjt
              have hsub : t.length + 1 - 1 = (t.length - 1) + 1 := by omega
              simp only [hjt, ↓reduceIte, hsub, pow_succ, mul_comm, ← smul_smul, neg_one_smul]
            · simp only [hjt, ↓reduceIte, Nat.sub_zero, pow_succ, mul_comm, ← smul_smul, neg_one_smul]

/-- Exact conjugation of any Majorana string `M_Q` by a probe `V_j`:
`V_j M_Q V_j = (-1)^{|Q| - 1_{j ∈ Q}} M_Q`. -/
theorem majoranaProbe_conj_majoranaString (n : ℕ) (j : Fin (2 * n)) (Q : Finset (Fin (2 * n))) :
    majoranaProbe n j * majoranaString n Q * majoranaProbe n j =
      ((-1 : ℂ) ^ (Q.card - if j ∈ Q then 1 else 0)) • majoranaString n Q := by
  unfold majoranaString
  rw [foldr_probe_conj_probe n j (Q.sort (· ≤ ·)) (Q.sort_nodup (· ≤ ·)), Finset.length_sort]
  simp only [Finset.mem_sort]

end FermionParityAndMajoranaStrings

section MajoranaSizeIdentity

/-- Anticommutator `{A, B} = A B + B A` on `QubitOp n`. -/
def matAnticomm {n : ℕ} (A B : QubitOp n) : QubitOp n :=
  A * B + B * A

/-- Single-mode even-sector Majorana size projector `(1/2)(M - V_j M V_j)`. -/
noncomputable def majoranaModeSizeOp (n : ℕ) (j : Fin (2 * n)) (M : QubitOp n) : QubitOp n :=
  (1 / 2 : ℂ) • (M - majoranaProbe n j * M * majoranaProbe n j)

/-- Total even-sector `2n`-mode Majorana size superoperator `∑_j (1/2)(M - V_j M V_j)`. -/
noncomputable def majoranaTotalSizeOp (n : ℕ) (M : QubitOp n) : QubitOp n :=
  ∑ j : Fin (2 * n), majoranaModeSizeOp n j M

/-- Single-mode odd-sector Majorana size projector `(1/2)(M + V_j M V_j)`. -/
noncomputable def majoranaOddModeSizeOp (n : ℕ) (j : Fin (2 * n)) (M : QubitOp n) : QubitOp n :=
  (1 / 2 : ℂ) • (M + majoranaProbe n j * M * majoranaProbe n j)

/-- Total odd-sector `2n`-mode Majorana size superoperator `∑_j (1/2)(M + V_j M V_j)`. -/
noncomputable def majoranaOddTotalSizeOp (n : ℕ) (M : QubitOp n) : QubitOp n :=
  ∑ j : Fin (2 * n), majoranaOddModeSizeOp n j M

/-- Even-parity projection `M_even = (1/2)(M + P M P)`. -/
noncomputable def evenPart (n : ℕ) (M : QubitOp n) : QubitOp n :=
  (1 / 2 : ℂ) • (M + fermionParityOp n * M * fermionParityOp n)

/-- Odd-parity projection `M_odd = (1/2)(M - P M P)`. -/
noncomputable def oddPart (n : ℕ) (M : QubitOp n) : QubitOp n :=
  (1 / 2 : ℂ) • (M - fermionParityOp n * M * fermionParityOp n)

/-- **Parity-Aware Majorana Operator-Size Superoperator** (`tex:378–385`):
Applies `(1/2)(M - V_j M V_j)` on the even-parity sector and `(1/2)(M + V_j M V_j)` on the
odd-parity sector, so that `majoranaParitySizeOp n M_Q = |Q| • M_Q` for ALL `Q ⊆ {0, …, 2n-1}`! -/
noncomputable def majoranaParitySizeOp (n : ℕ) (M : QubitOp n) : QubitOp n :=
  majoranaTotalSizeOp n (evenPart n M) + majoranaOddTotalSizeOp n (oddPart n M)

lemma evenPart_of_even {n : ℕ} {M : QubitOp n} (hM : isEvenParity M) :
    evenPart n M = M ∧ oddPart n M = 0 := by
  unfold evenPart oddPart isEvenParity at hM ⊢
  rw [hM, sub_self, smul_zero, ← two_smul ℂ M, smul_smul]
  exact ⟨by norm_num, rfl⟩

lemma oddPart_of_odd {n : ℕ} {M : QubitOp n} (hM : isOddParity M) :
    evenPart n M = 0 ∧ oddPart n M = M := by
  unfold evenPart oddPart isOddParity at hM ⊢
  rw [hM, add_neg_cancel, smul_zero, sub_neg_eq_add, ← two_smul ℂ M, smul_smul]
  exact ⟨rfl, by norm_num⟩

/-- **Exact Eigenvalue Identity on ALL Majorana Strings (Both Even and Odd Degree)**:
For EVERY `Q : Finset (Fin (2 * n))`, `majoranaParitySizeOp n (majoranaString n Q) = |Q| • majoranaString n Q`. -/
theorem majoranaParitySizeOp_on_string (n : ℕ) (Q : Finset (Fin (2 * n))) :
    majoranaParitySizeOp n (majoranaString n Q) = (Q.card : ℂ) • majoranaString n Q := by
  have hpar := majoranaString_parity n Q
  rcases Nat.even_or_odd Q.card with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hpow : ((-1 : ℂ) ^ Q.card) = 1 := by
      rw [hk, ← two_mul, pow_mul]; norm_num
    rw [hpow, one_smul] at hpar
    have ⟨he, ho⟩ := evenPart_of_even hpar
    unfold majoranaParitySizeOp majoranaTotalSizeOp majoranaOddTotalSizeOp
    rw [he, ho]
    have ho0 : ∑ j : Fin (2 * n), majoranaOddModeSizeOp n j 0 = 0 := by
      apply Finset.sum_eq_zero; intro j _; unfold majoranaOddModeSizeOp; simp
    rw [ho0, add_zero]
    have hmode : ∀ j : Fin (2 * n),
        majoranaModeSizeOp n j (majoranaString n Q) =
          if j ∈ Q then majoranaString n Q else 0 := by
      intro j
      unfold majoranaModeSizeOp
      rw [majoranaProbe_conj_majoranaString]
      by_cases hjQ : j ∈ Q
      · rw [if_pos hjQ, if_pos hjQ]
        have hpos : 1 ≤ Q.card := Finset.card_pos.mpr ⟨j, hjQ⟩
        have hpow' : ((-1 : ℂ) ^ (Q.card - 1)) = -1 := by
          have : Q.card - 1 = 2 * (k - 1) + 1 := by omega
          rw [this, pow_succ, pow_mul]; norm_num
        rw [hpow', neg_one_smul, sub_neg_eq_add, ← two_smul ℂ, smul_smul]; norm_num
      · rw [if_neg hjQ, if_neg hjQ, Nat.sub_zero, hpow, one_smul, sub_self, smul_zero]
    simp_rw [hmode]
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [nsmul_eq_smul_cast ℂ]
  · have hpow : ((-1 : ℂ) ^ Q.card) = -1 := by
      rw [hk, pow_succ, pow_mul]; norm_num
    rw [hpow, neg_one_smul] at hpar
    have ⟨he, ho⟩ := oddPart_of_odd hpar
    unfold majoranaParitySizeOp majoranaTotalSizeOp majoranaOddTotalSizeOp
    rw [he, ho]
    have he0 : ∑ j : Fin (2 * n), majoranaModeSizeOp n j 0 = 0 := by
      apply Finset.sum_eq_zero; intro j _; unfold majoranaModeSizeOp; simp
    rw [he0, zero_add]
    have hmode : ∀ j : Fin (2 * n),
        majoranaOddModeSizeOp n j (majoranaString n Q) =
          if j ∈ Q then majoranaString n Q else 0 := by
      intro j
      unfold majoranaOddModeSizeOp
      rw [majoranaProbe_conj_majoranaString]
      by_cases hjQ : j ∈ Q
      · rw [if_pos hjQ, if_pos hjQ]
        have hpow' : ((-1 : ℂ) ^ (Q.card - 1)) = 1 := by
          have : Q.card - 1 = 2 * k := by omega
          rw [this, pow_mul]; norm_num
        rw [hpow', one_smul, ← two_smul ℂ, smul_smul]; norm_num
      · rw [if_neg hjQ, if_neg hjQ, Nat.sub_zero, hpow, neg_one_smul, add_neg_cancel, smul_zero]
    simp_rw [hmode]
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [nsmul_eq_smul_cast ℂ]

/-- **Even-Sector Majorana Hilbert–Schmidt Size Identity**:
For every `M : QubitOp n`,
`(1/4) ∑_{j=0}^{2n-1} ‖[M, V_j]‖_HS² = Re ⟨M, majoranaTotalSizeOp n M⟩_HS`. -/
theorem majorana_hs_commutator_size_identity {n : ℕ} (M : QubitOp n) :
    (1 / 4 : ℝ) * ∑ j : Fin (2 * n), hsNormSq (matComm M (majoranaProbe n j)) =
      (hsInner M (majoranaTotalSizeOp n M)).re := by
  have hterm : ∀ j : Fin (2 * n),
      (1 / 4 : ℝ) * hsNormSq (matComm M (majoranaProbe n j)) =
        (hsInner M (majoranaModeSizeOp n j M)).re := by
    intro j
    set V := majoranaProbe n j
    have hVh : Vᴴ = V := majoranaProbe_herm n j
    have hVsq : V * V = 1 := majoranaProbe_sq n j
    have hcomm_norm : hsNormSq (matComm M V) =
        2 * hsNormSq M - 2 * (Matrix.trace (Mᴴ * (V * M * V))).re := by
      unfold hsNormSq hsInner matComm
      have hadj : (M * V - V * M)ᴴ * (M * V - V * M) =
          V * Mᴴ * M * V - V * Mᴴ * V * M - Mᴴ * V * M * V + Mᴴ * M := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hVh,
            Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
        simp only [Matrix.mul_assoc, hVsq, Matrix.mul_one]
        abel
      rw [hadj]
      simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
      have ht1 : Matrix.trace (V * Mᴴ * M * V) = Matrix.trace (Mᴴ * M) := by
        calc Matrix.trace (V * Mᴴ * M * V)
            = Matrix.trace (V * (V * Mᴴ * M)) := Matrix.trace_mul_comm _ V
          _ = Matrix.trace ((V * V) * Mᴴ * M) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (Mᴴ * M) := by rw [hVsq, Matrix.one_mul]
      have ht2 : Matrix.trace (V * Mᴴ * V * M) = Matrix.trace (Mᴴ * (V * M * V)) := by
        calc Matrix.trace (V * Mᴴ * V * M)
            = Matrix.trace (V * (Mᴴ * V * M)) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace ((Mᴴ * V * M) * V) := Matrix.trace_mul_comm V _
          _ = Matrix.trace (Mᴴ * (V * M * V)) := by simp only [Matrix.mul_assoc]
      have ht3 : Matrix.trace (Mᴴ * V * M * V) = Matrix.trace (Mᴴ * (V * M * V)) := by
        simp only [Matrix.mul_assoc]
      rw [ht1, ht2, ht3]
      ring
    rw [hcomm_norm]
    unfold majoranaModeSizeOp hsNormSq hsInner
    simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
    have hhalf : ((1 / 2 : ℂ) * (Matrix.trace (Mᴴ * M) - Matrix.trace (Mᴴ * (V * M * V)))).re =
        (1 / 2 : ℝ) * ((Matrix.trace (Mᴴ * M)).re - (Matrix.trace (Mᴴ * (V * M * V))).re) := by
      rw [Complex.mul_re, Complex.sub_re]
      norm_num
    rw [hhalf]
    ring
  rw [Finset.mul_sum]
  simp_rw [hterm]
  unfold majoranaTotalSizeOp hsInner
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- **Odd-Sector Majorana Hilbert–Schmidt Anticommutator Size Identity**:
For every `M : QubitOp n`,
`(1/4) ∑_{j=0}^{2n-1} ‖{M, V_j}‖_HS² = Re ⟨M, majoranaOddTotalSizeOp n M⟩_HS`. -/
theorem majorana_hs_anticomm_size_identity {n : ℕ} (M : QubitOp n) :
    (1 / 4 : ℝ) * ∑ j : Fin (2 * n), hsNormSq (matAnticomm M (majoranaProbe n j)) =
      (hsInner M (majoranaOddTotalSizeOp n M)).re := by
  have hterm : ∀ j : Fin (2 * n),
      (1 / 4 : ℝ) * hsNormSq (matAnticomm M (majoranaProbe n j)) =
        (hsInner M (majoranaOddModeSizeOp n j M)).re := by
    intro j
    set V := majoranaProbe n j
    have hVh : Vᴴ = V := majoranaProbe_herm n j
    have hVsq : V * V = 1 := majoranaProbe_sq n j
    have hanti_norm : hsNormSq (matAnticomm M V) =
        2 * hsNormSq M + 2 * (Matrix.trace (Mᴴ * (V * M * V))).re := by
      unfold hsNormSq hsInner matAnticomm
      have hadj : (M * V + V * M)ᴴ * (M * V + V * M) =
          V * Mᴴ * M * V + V * Mᴴ * V * M + Mᴴ * V * M * V + Mᴴ * M := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hVh,
            Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        simp only [Matrix.mul_assoc, hVsq, Matrix.mul_one]
        abel
      rw [hadj]
      simp only [Matrix.trace_add, Complex.add_re]
      have ht1 : Matrix.trace (V * Mᴴ * M * V) = Matrix.trace (Mᴴ * M) := by
        calc Matrix.trace (V * Mᴴ * M * V)
            = Matrix.trace (V * (V * Mᴴ * M)) := Matrix.trace_mul_comm _ V
          _ = Matrix.trace ((V * V) * Mᴴ * M) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (Mᴴ * M) := by rw [hVsq, Matrix.one_mul]
      have ht2 : Matrix.trace (V * Mᴴ * V * M) = Matrix.trace (Mᴴ * (V * M * V)) := by
        calc Matrix.trace (V * Mᴴ * V * M)
            = Matrix.trace (V * (Mᴴ * V * M)) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace ((Mᴴ * V * M) * V) := Matrix.trace_mul_comm V _
          _ = Matrix.trace (Mᴴ * (V * M * V)) := by simp only [Matrix.mul_assoc]
      have ht3 : Matrix.trace (Mᴴ * V * M * V) = Matrix.trace (Mᴴ * (V * M * V)) := by
        simp only [Matrix.mul_assoc]
      rw [ht1, ht2, ht3]
      ring
    rw [hanti_norm]
    unfold majoranaOddModeSizeOp hsNormSq hsInner
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
    have hhalf : ((1 / 2 : ℂ) * (Matrix.trace (Mᴴ * M) + Matrix.trace (Mᴴ * (V * M * V)))).re =
        (1 / 2 : ℝ) * ((Matrix.trace (Mᴴ * M)).re + (Matrix.trace (Mᴴ * (V * M * V))).re) := by
      rw [Complex.mul_re, Complex.add_re]
      norm_num
    rw [hhalf]
    ring
  rw [Finset.mul_sum]
  simp_rw [hterm]
  unfold majoranaOddTotalSizeOp hsInner
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- Concrete equal-time Majorana Wightman probe correlator
`C_{β, V_j}^W(0) = Re Tr(ρ_β^{1/2} V_j ρ_β^{1/2} V_j)` (Eq. 2.10). -/
noncomputable def majoranaCW0 {n : ℕ} (G : GibbsData n) (j : Fin (2 * n)) : ℝ :=
  gibbsWightmanNormSq G (majoranaProbe n j)

/-- Concrete Majorana MSS four-point OTOC
`F_MSS(A, V_j) = Re Tr(V_j 𝒥_β(A) V_j 𝒥_β(A))` (Eq. 2.10). -/
noncomputable def majoranaFMSS {n : ℕ} (G : GibbsData n) (A : QubitOp n) (j : Fin (2 * n)) : ℝ :=
  (Matrix.trace (majoranaProbe n j * jBeta G.ρQuarter A * majoranaProbe n j * jBeta G.ρQuarter A)).re

/-- Concrete parity-aware Majorana thermal-subtracted operator size `S_β^{Maj}(A)`:
`Re ⟨𝒥_β(A), S_Maj 𝒥_β(A)⟩_HS - Re ⟨ρ_β^{1/2}, S_Maj ρ_β^{1/2}⟩_HS`. -/
noncomputable def majoranaThermalSize {n : ℕ} (G : GibbsData n) (A : QubitOp n) : ℝ :=
  (hsInner (jBeta G.ρQuarter A) (majoranaParitySizeOp n (jBeta G.ρQuarter A))).re -
  (hsInner G.ρHalf (majoranaParitySizeOp n G.ρHalf)).re

private lemma majorana_anticomm_comm_diff_eq {n : ℕ} (X Y V : QubitOp n)
    (hXh : Xᴴ = X) (hYh : Yᴴ = Y) (hVh : Vᴴ = V) (hVsq : V * V = 1)
    (hXsq : (Matrix.trace (X * X)).re = 1) (hYsq : (Matrix.trace (Y * Y)).re = 1) :
    hsNormSq (matAnticomm X V) - hsNormSq (matComm Y V) =
      2 * ((Matrix.trace (V * Y * V * Y)).re + (Matrix.trace (V * X * V * X)).re) := by
  have h1 := congrArg Complex.re (prop_2_3_majorana_size_identity X V hXh hVh hVsq)
  have h2 := congrArg Complex.re (prop_2_3_commutator_size_identity Y V hYh hVh hVsq)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero] at h1 h2
  unfold hsNormSq hsInner matAnticomm matComm
  rw [h1, h2, hXsq, hYsq]
  ring

/-- **Proposition 2.3(2) (Exact Majorana Thermal-Size MSS-OTOC Identity, Eq. 2.10)**:
For ANY `2n`-Majorana thermal state `G : GibbsData n` with even-parity `G.ρQuarter` and ANY
odd-parity Hermitian normalized operator `A : QubitOp n` (`isOddParity A`, `Aᴴ = A`,
`gibbsWightmanNormSq G A = 1`):
`majoranaThermalSize G A = (1 / 2) ∑_{j=0}^{2n-1} (C_{β, V_j}^W(0) + F_MSS(A, V_j))`. -/
theorem prop_2_3_part2_majorana_eq_2_10 {n : ℕ} (G : GibbsData n) {A : QubitOp n}
    (hρ : isEvenParity G.ρQuarter) (hA_odd : isOddParity A)
    (hA_herm : Aᴴ = A) (hAnorm : gibbsWightmanNormSq G A = 1) :
    majoranaThermalSize G A =
      (1 / 2 : ℝ) * ∑ j : Fin (2 * n), (majoranaCW0 G j + majoranaFMSS G A j) := by
  have hJA_odd : isOddParity (jBeta G.ρQuarter A) := jBeta_oddParity_of_odd G hρ hA_odd
  have hρH_even : isEvenParity G.ρHalf := rhoHalf_evenParity G hρ
  have hJA_herm : (jBeta G.ρQuarter A)ᴴ = jBeta G.ρQuarter A := by
    unfold jBeta
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, G.ρQuarter_herm, hA_herm, Matrix.mul_assoc]
  have hJA_sq : (Matrix.trace (jBeta G.ρQuarter A * jBeta G.ρQuarter A)).re = 1 := by
    have h1 : hsNormSq (jBeta G.ρQuarter A) = 1 := by
      unfold gibbsWightmanNormSq gibbsWightmanInner at hAnorm
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hAnorm
      exact hAnorm
    unfold hsNormSq hsInner at h1
    rwa [hJA_herm] at h1
  have hρ_sq : (Matrix.trace (G.ρHalf * G.ρHalf)).re = 1 := by
    rw [G.sq_half, G.trace_one, Complex.one_re]
  have hS_JA : majoranaParitySizeOp n (jBeta G.ρQuarter A) =
      majoranaOddTotalSizeOp n (jBeta G.ρQuarter A) := by
    unfold majoranaParitySizeOp
    rw [(oddPart_of_odd hJA_odd).1, (oddPart_of_odd hJA_odd).2]
    have h0 : majoranaTotalSizeOp n 0 = 0 := by
      unfold majoranaTotalSizeOp majoranaModeSizeOp; simp
    rw [h0, zero_add]
  have hS_ρ : majoranaParitySizeOp n G.ρHalf = majoranaTotalSizeOp n G.ρHalf := by
    unfold majoranaParitySizeOp
    rw [(evenPart_of_even hρH_even).1, (evenPart_of_even hρH_even).2]
    have h0 : majoranaOddTotalSizeOp n 0 = 0 := by
      unfold majoranaOddTotalSizeOp majoranaOddModeSizeOp; simp
    rw [h0, add_zero]
  unfold majoranaThermalSize
  rw [hS_JA, hS_ρ, ← majorana_hs_anticomm_size_identity, ← majorana_hs_commutator_size_identity,
    ← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin (2 * n),
      hsNormSq (matAnticomm (jBeta G.ρQuarter A) (majoranaProbe n j)) -
      hsNormSq (matComm G.ρHalf (majoranaProbe n j)) =
      2 * (majoranaCW0 G j + majoranaFMSS G A j) := by
    intro j
    have hVh := majoranaProbe_herm n j
    have hVsq := majoranaProbe_sq n j
    have hdiff := majorana_anticomm_comm_diff_eq (jBeta G.ρQuarter A) G.ρHalf (majoranaProbe n j)
      hJA_herm G.ρHalf_herm hVh hVsq hJA_sq hρ_sq
    have hcw : (Matrix.trace (majoranaProbe n j * G.ρHalf * majoranaProbe n j * G.ρHalf)).re =
        majoranaCW0 G j := by
      unfold majoranaCW0 gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      exact congrArg Complex.re (by
        rw [hVh]
        calc Matrix.trace (majoranaProbe n j * G.ρHalf * majoranaProbe n j * G.ρHalf)
            = Matrix.trace (G.ρHalf * (majoranaProbe n j * G.ρHalf * majoranaProbe n j)) :=
              Matrix.trace_mul_comm _ _
          _ = Matrix.trace (G.ρHalf * majoranaProbe n j * G.ρHalf * majoranaProbe n j) := by
              simp only [Matrix.mul_assoc])
    rw [hdiff, hcw]
    rfl
  simp_rw [hterm, ← Finset.mul_sum]
  ring

/-- Legacy even-sector commutator-difference thermal-size identity (preserved for compatibility). -/
theorem prop_2_3_full_majorana_thermal_size {n : ℕ} (G : GibbsData n) (A : QubitOp n) :
    (hsInner (jBeta G.ρQuarter A) (majoranaTotalSizeOp n (jBeta G.ρQuarter A))).re -
      (hsInner G.ρHalf (majoranaTotalSizeOp n G.ρHalf)).re =
    (1 / 4 : ℝ) * ∑ j : Fin (2 * n),
      (hsNormSq (matComm (jBeta G.ρQuarter A) (majoranaProbe n j)) -
       hsNormSq (matComm G.ρHalf (majoranaProbe n j))) := by
  rw [← majorana_hs_commutator_size_identity (jBeta G.ρQuarter A),
      ← majorana_hs_commutator_size_identity G.ρHalf,
      ← mul_sub, ← Finset.sum_sub_distrib]

/-- **Majorana Size Operator Bounds `0 ⪯ S_Maj ⪯ (2n) • 1`**:
For EVERY even- or odd-parity operator `M : QubitOp n`,
`0 ≤ Re ⟨M, majoranaParitySizeOp n M⟩_HS ≤ (2 * n : ℝ) * hsNormSq M`. -/
theorem majoranaParitySizeOp_bounds_of_parity {n : ℕ} (M : QubitOp n)
    (hpar : isEvenParity M ∨ isOddParity M) :
    0 ≤ (hsInner M (majoranaParitySizeOp n M)).re ∧
    (hsInner M (majoranaParitySizeOp n M)).re ≤ ((2 * n : ℕ) : ℝ) * hsNormSq M := by
  have hmode_le : ∀ (V : QubitOp n), Vᴴ = V → V * V = 1 →
      (1 / 4 : ℝ) * hsNormSq (matComm M V) ≤ hsNormSq M ∧
      (1 / 4 : ℝ) * hsNormSq (matAnticomm M V) ≤ hsNormSq M := by
    intro V hVh hVsq
    have hsum : hsNormSq (matComm M V) + hsNormSq (matAnticomm M V) = 4 * hsNormSq M := by
      unfold hsNormSq hsInner matComm matAnticomm
      have h1 : (M * V - V * M)ᴴ * (M * V - V * M) + (M * V + V * M)ᴴ * (M * V + V * M) =
          (2 : ℂ) • (V * Mᴴ * M * V + Mᴴ * M) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, hVh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
          Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        simp only [Matrix.mul_assoc, hVsq, Matrix.mul_one, two_smul]
        abel
      rw [← Complex.add_re, ← Matrix.trace_add, h1, Matrix.trace_smul, Matrix.trace_add,
        smul_eq_mul]
      have ht1 : Matrix.trace (V * Mᴴ * M * V) = Matrix.trace (Mᴴ * M) := by
        calc Matrix.trace (V * Mᴴ * M * V)
            = Matrix.trace (V * (V * Mᴴ * M)) := Matrix.trace_mul_comm _ V
          _ = Matrix.trace ((V * V) * Mᴴ * M) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (Mᴴ * M) := by rw [hVsq, Matrix.one_mul]
      rw [ht1, Complex.mul_re, Complex.add_re]
      norm_num; ring
    have hc := hsNormSq_nonneg (matComm M V)
    have ha := hsNormSq_nonneg (matAnticomm M V)
    exact ⟨by linarith, by linarith⟩
  rcases hpar with he | ho
  · have hS : majoranaParitySizeOp n M = majoranaTotalSizeOp n M := by
      unfold majoranaParitySizeOp
      rw [(evenPart_of_even he).1, (evenPart_of_even he).2]
      have h0 : majoranaOddTotalSizeOp n 0 = 0 := by unfold majoranaOddTotalSizeOp majoranaOddModeSizeOp; simp
      rw [h0, add_zero]
    rw [hS, ← majorana_hs_commutator_size_identity M]
    refine ⟨mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ ↦ hsNormSq_nonneg _), ?_⟩
    rw [Finset.mul_sum]
    calc ∑ j : Fin (2 * n), (1 / 4 : ℝ) * hsNormSq (matComm M (majoranaProbe n j))
        ≤ ∑ _j : Fin (2 * n), hsNormSq M :=
          Finset.sum_le_sum fun j _ ↦ (hmode_le _ (majoranaProbe_herm n j) (majoranaProbe_sq n j)).1
      _ = ((2 * n : ℕ) : ℝ) * hsNormSq M := by simp
  · have hS : majoranaParitySizeOp n M = majoranaOddTotalSizeOp n M := by
      unfold majoranaParitySizeOp
      rw [(oddPart_of_odd ho).1, (oddPart_of_odd ho).2]
      have h0 : majoranaTotalSizeOp n 0 = 0 := by unfold majoranaTotalSizeOp majoranaModeSizeOp; simp
      rw [h0, zero_add]
    rw [hS, ← majorana_hs_anticomm_size_identity M]
    refine ⟨mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ ↦ hsNormSq_nonneg _), ?_⟩
    rw [Finset.mul_sum]
    calc ∑ j : Fin (2 * n), (1 / 4 : ℝ) * hsNormSq (matAnticomm M (majoranaProbe n j))
        ≤ ∑ _j : Fin (2 * n), hsNormSq M :=
          Finset.sum_le_sum fun j _ ↦ (hmode_le _ (majoranaProbe_herm n j) (majoranaProbe_sq n j)).2
      _ = ((2 * n : ℕ) : ℝ) * hsNormSq M := by simp

end MajoranaSizeIdentity

end KrylovChaos
