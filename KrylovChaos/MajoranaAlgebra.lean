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
# Concrete Majorana Clifford Algebra & Eq. (2.10) (Section 2.1–2.2)

Constructs `2n` Hermitian Majorana fermion generators `{γ_j}_{j=0}^{2n-1}` on the `n`-qubit
Hilbert space `QubitOp n` (`dim H = 2^n`) via the Jordan–Wigner transformation:
- `V_{2k}   = Z_0 ⋯ Z_{k-1} X_k`
- `V_{2k+1} = Z_0 ⋯ Z_{k-1} Y_k`
- `γ_j      = (1 / √2) V_j`

Proves from first principles (zero axioms, zero sorrys):
1. Hermiticity `V_jᴴ = V_j`, `γ_jᴴ = γ_j`, and involution `V_j * V_j = 1`.
2. **Exact Clifford anticommutation relations**:
   `V_i * V_j + V_j * V_i = (if i = j then 2 else 0) • 1`,
   `γ_i * γ_j + γ_j * γ_i = (if i = j then 1 else 0) • 1`.
3. **Majorana operator-size identity & Proposition 2.3 (Eq. 2.10)**:
   `Re ⟨M, S_Maj M⟩_HS = (1/4) ∑_{j=0}^{2n-1} ‖[M, V_j]‖_HS²` and the full `2n`-Majorana
   thermal-subtracted size identity.
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
    simp [pauliMat] <;> ring

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
          rw [if_neg h1, if_pos hx, if_pos h2]
          split_ifs <;> decide
        · have hx : x₀.1 = i.1 / 2 := by simp [x₀, heq]
          have h1 : ¬(x₀.1 < i.1 / 2) := by omega
          have h2 : ¬(x₀.1 < j.1 / 2) := by omega
          have h3 : x₀.1 = j.1 / 2 := by omega
          have hmod : i.1 % 2 ≠ j.1 % 2 := by omega
          rw [if_neg h1, if_pos hx, if_neg h2, if_pos h3]
          by_cases hm : i.1 % 2 = 0
          · have hm2 : ¬(j.1 % 2 = 0) := by omega
            rw [if_pos hm, if_neg hm2]; decide
          · have hm2 : j.1 % 2 = 0 := by omega
            rw [if_neg hm, if_pos hm2]; decide
        · have hx : x₀.1 = j.1 / 2 := min_eq_right (le_of_lt hgt)
          have h1 : x₀.1 < i.1 / 2 := by omega
          have h2 : ¬(x₀.1 < j.1 / 2) := by omega
          rw [if_pos h1, if_neg h2, if_pos hx]
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
          rw [if_pos h1, if_pos h2]
        · have hgt : min (i.1 / 2) (j.1 / 2) < x.1 := by omega
          rcases le_total (i.1 / 2) (j.1 / 2) with hle | hle
          · left
            have h1 : ¬(x.1 < i.1 / 2) := by omega
            have h2 : ¬(x.1 = i.1 / 2) := by omega
            rw [if_neg h1, if_neg h2]
          · right; left
            have h1 : ¬(x.1 < j.1 / 2) := by omega
            have h2 : ¬(x.1 = j.1 / 2) := by omega
            rw [if_neg h1, if_neg h2]
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

section MajoranaSizeIdentity

/-- Single-mode Majorana parity-flip size projector `S_j(M) := (1/2) (M - V_j M V_j)`. -/
noncomputable def majoranaModeSizeOp (n : ℕ) (j : Fin (2 * n)) (M : QubitOp n) : QubitOp n :=
  (1 / 2 : ℂ) • (M - majoranaProbe n j * M * majoranaProbe n j)

/-- Total `2n`-mode Majorana operator-size superoperator `S_Maj(M) := ∑_{j=0}^{2n-1} S_j(M)`. -/
noncomputable def majoranaTotalSizeOp (n : ℕ) (M : QubitOp n) : QubitOp n :=
  ∑ j : Fin (2 * n), majoranaModeSizeOp n j M

/-- **Majorana Hilbert–Schmidt Size Identity**:
For every `M : QubitOp n`,
`(1/4) ∑_{j=0}^{2n-1} ‖[M, V_j]‖_HS² = Re ⟨M, S_Maj(M)⟩_HS`. -/
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
      have hterm4 : Mᴴ * V * (V * M) = Mᴴ * M := by
        calc Mᴴ * V * (V * M)
            = Mᴴ * ((V * V) * M) := by simp only [Matrix.mul_assoc]
          _ = Mᴴ * M := by rw [hVsq, Matrix.one_mul]
      have hadj : (M * V - V * M)ᴴ * (M * V - V * M) =
          V * Mᴴ * (M * V) - V * Mᴴ * (V * M) - Mᴴ * V * (M * V) + Mᴴ * M := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hVh,
            Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hterm4]
        abel
      rw [hadj]
      simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
      have ht1 : Matrix.trace (V * Mᴴ * (M * V)) = Matrix.trace (Mᴴ * M) := by
        calc Matrix.trace (V * Mᴴ * (M * V))
            = Matrix.trace ((V * Mᴴ * M) * V) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (V * (V * Mᴴ * M)) := Matrix.trace_mul_comm _ V
          _ = Matrix.trace ((V * V) * (Mᴴ * M)) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (Mᴴ * M) := by rw [hVsq, Matrix.one_mul]
      have ht2 : Matrix.trace (V * Mᴴ * (V * M)) = Matrix.trace (Mᴴ * (V * M * V)) := by
        calc Matrix.trace (V * Mᴴ * (V * M))
            = Matrix.trace (V * (Mᴴ * (V * M))) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace ((Mᴴ * (V * M)) * V) := Matrix.trace_mul_comm V _
          _ = Matrix.trace (Mᴴ * (V * M * V)) := by simp only [Matrix.mul_assoc]
      have ht3 : Matrix.trace (Mᴴ * V * (M * V)) = Matrix.trace (Mᴴ * (V * M * V)) := by
        simp only [Matrix.mul_assoc]
      rw [ht1, ht2, ht3]
      ring
    rw [hcomm_norm]
    unfold majoranaModeSizeOp hsInner hsNormSq
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

/-- **Proposition 2.3 (Full 2n-Majorana Thermal-Subtracted Size Identity, Eq. 2.10)**:
For any `n`-qubit (`2n`-Majorana) thermal state `G : GibbsData n` and operator `A : QubitOp n`,
`Re ⟨𝒥_β(A), S_Maj 𝒥_β(A)⟩_HS - Re ⟨ρ_β^{1/2}, S_Maj ρ_β^{1/2}⟩_HS =
 (1/4) ∑_{j=0}^{2n-1} (‖[𝒥_β(A), V_j]‖_HS² - ‖[ρ_β^{1/2}, V_j]‖_HS²)`. -/
theorem prop_2_3_full_majorana_thermal_size {n : ℕ} (G : GibbsData n) (A : QubitOp n) :
    (hsInner (jBeta G.ρQuarter A) (majoranaTotalSizeOp n (jBeta G.ρQuarter A))).re -
      (hsInner G.ρHalf (majoranaTotalSizeOp n G.ρHalf)).re =
    (1 / 4 : ℝ) * ∑ j : Fin (2 * n),
      (hsNormSq (matComm (jBeta G.ρQuarter A) (majoranaProbe n j)) -
       hsNormSq (matComm G.ρHalf (majoranaProbe n j))) := by
  rw [← majorana_hs_commutator_size_identity (jBeta G.ρQuarter A),
      ← majorana_hs_commutator_size_identity G.ρHalf,
      ← mul_sub, ← Finset.sum_sub_distrib]

end MajoranaSizeIdentity

end KrylovChaos
