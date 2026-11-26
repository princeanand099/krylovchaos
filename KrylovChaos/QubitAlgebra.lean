/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ProductState
import KrylovChaos.WightmanIsometry
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Concrete N-Qubit Operator Algebra, Pauli Strings, Superoperators, and Locality Filtration

Constructs the concrete finite-dimensional many-body quantum operator algebra on
`ℋ = (ℂ²)^{⊗ N}` (`QubitOp N := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ`):
1. `kronOp`, `pauliMat`, `pauliString`, `pauliSite`: Concrete tensor-product operators,
   Hermiticity, unitarity (`P² = 1`), and exact trace orthogonality (`Tr(P_a P_b) = 2^N δ_{ab}`).
2. `partialTraceSite` (`ℰ_x`) and `siteSizeOp` (`𝒮_x = 1 - ℰ_x`): Concrete single-site
   partial-trace and size superoperators, with a ground-up proof of **Eq. (2.8)**:
   `(1/8) ∑_{x, α ∈ {X,Y,Z}} ‖[A, σ_x^α]‖_HS² = ∑_x Re ⟨A, 𝒮_x(A)⟩_HS`.
3. `filtrationSubmodule` (`𝒱_s`): Concrete ascending locality filtration spanned by Pauli strings
   of Hamming weight `≤ s`, with a ground-up proof of the **r-local commutator step**:
   if `H ∈ 𝒱_r` and `A ∈ 𝒱_s`, then `[H, A] ∈ 𝒱_{min N (s + (r - 1))}`.
-/

namespace KrylovChaos

open Matrix

/-- The concrete `2^N × 2^N` operator algebra on `N` qubits `(ℂ²)^{⊗ N}`. -/
abbrev QubitOp (N : ℕ) := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ

/-- Single-qubit Pauli matrices indexed by `Fin 4`: `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`. -/
def pauliMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- Pauli product index table on `Fin 4` (XOR group `(ℤ/2)²`). -/
def pauliMulIdx : Fin 4 → Fin 4 → Fin 4
  | 0, b => b
  | a, 0 => a
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 1 => 2
  | 3, 2 => 1
  | 3, 3 => 0
  | _, _ => 0

/-- Pauli product phase table `±1, ±i` on `Fin 4`. -/
def pauliMulPhase : Fin 4 → Fin 4 → ℂ
  | 1, 2 => Complex.I
  | 2, 3 => Complex.I
  | 3, 1 => Complex.I
  | 2, 1 => -Complex.I
  | 3, 2 => -Complex.I
  | 1, 3 => -Complex.I
  | _, _ => 1

lemma pauliMulIdx_comm (u v : Fin 4) : pauliMulIdx u v = pauliMulIdx v u := by
  fin_cases u <;> fin_cases v <;> rfl

lemma pauliMulPhase_zero_comm (u v : Fin 4) (h : u = 0 ∨ v = 0) :
    pauliMulPhase u v = pauliMulPhase v u := by
  rcases h with rfl | rfl <;> (try fin_cases v) <;> (try fin_cases u) <;> rfl

lemma pauliMat_herm (α : Fin 4) : (pauliMat α)ᴴ = pauliMat α := by
  fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMat]

lemma pauliMat_mul (α β : Fin 4) :
    pauliMat α * pauliMat β = pauliMulPhase α β • pauliMat (pauliMulIdx α β) := by
  fin_cases α <;> fin_cases β <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, pauliMulPhase, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliMat_sq (α : Fin 4) : pauliMat α * pauliMat α = 1 := by
  rw [pauliMat_mul]
  fin_cases α <;> simp [pauliMulPhase, pauliMulIdx, pauliMat]

lemma pauliMat_trace (α : Fin 4) :
    (pauliMat α).trace = if α = 0 then 2 else 0 := by
  fin_cases α <;> simp [pauliMat, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring

/-- Kronecker tensor product `⊗_{x : Fin N} M_x` acting on `(ℂ²)^{⊗ N}`. -/
def kronOp {N : ℕ} (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) : QubitOp N :=
  Matrix.of fun i j ↦ ∏ x : Fin N, M x (i x) (j x)

theorem kronOp_mul {N : ℕ} (M K : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    kronOp M * kronOp K = kronOp (fun x ↦ M x * K x) := by
  ext i j
  simp only [kronOp, Matrix.mul_apply, Matrix.of_apply]
  have h1 : ∀ k : Fin N → Fin 2,
      (∏ x : Fin N, M x (i x) (k x)) * (∏ x : Fin N, K x (k x) (j x)) =
      ∏ x : Fin N, (M x (i x) (k x) * K x (k x) (j x)) := fun k ↦
    (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun x c ↦ M x (i x) c * K x c (j x))).symm

theorem kronOp_conjTranspose {N : ℕ} (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    (kronOp M)ᴴ = kronOp (fun x ↦ (M x)ᴴ) := by
  ext i j
  simp only [kronOp, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

theorem kronOp_trace {N : ℕ} (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    (kronOp M).trace = ∏ x : Fin N, (M x).trace := by
  simp only [Matrix.trace, Matrix.diag, kronOp, Matrix.of_apply]
  exact (Fintype.prod_sum (fun x c ↦ M x c c)).symm

theorem kronOp_one {N : ℕ} :
    kronOp (fun _ : Fin N ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    have hex : ∃ x : Fin N, i x ≠ j x := by
      by_contra hall
      exact h (funext fun x ↦ by by_contra hne; exact hall ⟨x, hne⟩)
    obtain ⟨x₀, hx₀⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ x₀) (if_neg hx₀)

theorem kronOp_smul {N : ℕ} (c : Fin N → ℂ) (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    kronOp (fun x ↦ c x • M x) = (∏ x : Fin N, c x) • kronOp M := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- Concrete `N`-qubit Pauli string `P_a = ⊗_{x=1}^N σ_{a_x}`. -/
def pauliString {N : ℕ} (a : Fin N → Fin 4) : QubitOp N :=
  kronOp (fun x ↦ pauliMat (a x))

/-- Single-site Pauli operator `σ_x^α` acting on site `x` and as identity elsewhere. -/
def pauliSite {N : ℕ} (x : Fin N) (α : Fin 4) : QubitOp N :=
  pauliString (Function.update (fun _ ↦ (0 : Fin 4)) x α)

theorem pauliString_herm {N : ℕ} (a : Fin N → Fin 4) :
    (pauliString a)ᴴ = pauliString a := by
  unfold pauliString
  rw [kronOp_conjTranspose]
  congr 1; funext x; exact pauliMat_herm (a x)

theorem pauliString_mul {N : ℕ} (a b : Fin N → Fin 4) :
    pauliString a * pauliString b =
      (∏ x : Fin N, pauliMulPhase (a x) (b x)) •
        pauliString (fun x ↦ pauliMulIdx (a x) (b x)) := by
  unfold pauliString
  rw [kronOp_mul]
  have h : (fun x ↦ pauliMat (a x) * pauliMat (b x)) =
      fun x ↦ pauliMulPhase (a x) (b x) • pauliMat (pauliMulIdx (a x) (b x)) := by
    funext x; exact pauliMat_mul (a x) (b x)
  rw [h, kronOp_smul]

theorem pauliString_sq {N : ℕ} (a : Fin N → Fin 4) :
    pauliString a * pauliString a = 1 := by
  unfold pauliString
  rw [kronOp_mul]
  have h : (fun x ↦ pauliMat (a x) * pauliMat (a x)) = fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext x; exact pauliMat_sq (a x)
  rw [h, kronOp_one]

theorem pauliSite_herm {N : ℕ} (x : Fin N) (α : Fin 4) :
    (pauliSite x α)ᴴ = pauliSite x α :=
  pauliString_herm _

theorem pauliSite_sq {N : ℕ} (x : Fin N) (α : Fin 4) :
    pauliSite x α * pauliSite x α = 1 :=
  pauliString_sq _

theorem pauliSite_zero {N : ℕ} (x : Fin N) : pauliSite x 0 = 1 := by
  unfold pauliSite pauliString
  have h : (fun y ↦ pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x 0 y)) =
      fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    by_cases hy : y = x
    · subst hy; simp [pauliMat]
    · simp [hy, pauliMat]
  rw [h, kronOp_one]

/-- Exact trace orthogonality of the `4^N` Pauli strings: `Tr(P_a P_b) = 2^N δ_{a,b}`. -/
theorem pauliString_trace_ortho {N : ℕ} (a b : Fin N → Fin 4) :
    (pauliString a * pauliString b).trace = if a = b then (2 : ℂ) ^ N else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, pauliString_sq, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    push_cast; rfl
  · rw [if_neg hab, pauliString_mul, Matrix.trace_smul, smul_eq_mul]
    have hex : ∃ x : Fin N, a x ≠ b x := by
      by_contra hall
      exact hab (funext fun x ↦ by by_contra hne; exact hall ⟨x, hne⟩)
    obtain ⟨x₀, hx₀⟩ := hex
    have hidx_ne : pauliMulIdx (a x₀) (b x₀) ≠ 0 := by
      revert hx₀
      generalize a x₀ = u; generalize b x₀ = v
      fin_cases u <;> fin_cases v <;> decide
    unfold pauliString
    rw [kronOp_trace]
    have hzero : ∏ x : Fin N, (pauliMat (pauliMulIdx (a x) (b x))).trace = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x₀) (by rw [pauliMat_trace, if_neg hidx_ne])
    rw [hzero, mul_zero]

section Superoperators

/-- Normalized single-site partial trace `ℰ_x(A) = (1/4) ∑_{α=0}^3 σ_x^α A σ_x^α = (1/2) Tr_x(A) ⊗ I_x`. -/
noncomputable def partialTraceSite {N : ℕ} (x : Fin N) (A : QubitOp N) : QubitOp N :=
  (1 / 4 : ℂ) • ∑ α : Fin 4, pauliSite x α * A * pauliSite x α

/-- Single-site operator-size superoperator `𝒮_x(A) = A - ℰ_x(A)`. -/
noncomputable def siteSizeOp {N : ℕ} (x : Fin N) (A : QubitOp N) : QubitOp N :=
  A - partialTraceSite x A

/-- Total Hilbert–Schmidt operator-size superoperator `𝒮(A) = ∑_{x=1}^N 𝒮_x(A)`. -/
noncomputable def totalSizeOp {N : ℕ} (A : QubitOp N) : QubitOp N :=
  ∑ x : Fin N, siteSizeOp x A

/-- **Eq. (2.8)** (Concrete `N`-Qubit Hilbert–Schmidt Commutator Size Identity):
For every `N`-qubit operator `A : QubitOp N`,
`(1/8) ∑_{x=1}^N ∑_{α ∈ {X,Y,Z}} ‖[A, σ_x^α]‖_HS² = Re ⟨A, 𝒮(A)⟩_HS`. -/
theorem eq_2_8_hs_commutator_size_identity {N : ℕ} (A : QubitOp N) :
    (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (matComm A (pauliSite x α.succ)) =
    (hsInner A (totalSizeOp A)).re := by
  have hsite : ∀ x : Fin N,
      (1 / 8 : ℝ) * ∑ α : Fin 3, hsNormSq (matComm A (pauliSite x α.succ)) =
      (hsInner A (siteSizeOp x A)).re := by
    intro x
    have hterm : ∀ α : Fin 4,
        hsNormSq (matComm A (pauliSite x α)) =
          2 * hsNormSq A - 2 * (Matrix.trace (Aᴴ * (pauliSite x α * A * pauliSite x α))).re := by
      intro α
      set P := pauliSite x α
      have hP : Pᴴ = P := pauliSite_herm x α
      have hP2 : P * P = 1 := pauliSite_sq x α
      unfold hsNormSq hsInner matComm
      have hAdj : (A * P - P * A)ᴴ = P * Aᴴ - Aᴴ * P := by
        simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hP]
      rw [hAdj]
      have hexp : (P * Aᴴ - Aᴴ * P) * (A * P - P * A) =
          P * Aᴴ * A * P - P * Aᴴ * P * A - Aᴴ * P * A * P + Aᴴ * P * P * A := by
        noncomm_ring
      rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
      have ht1 : (P * Aᴴ * A * P).trace = (Aᴴ * A).trace := by
        rw [Matrix.trace_mul_comm (P * Aᴴ * A) P]
        calc (P * (P * Aᴴ * A)).trace
            = ((P * P) * Aᴴ * A).trace := by simp [Matrix.mul_assoc]
          _ = (Aᴴ * A).trace := by rw [hP2, Matrix.one_mul]
      have ht4 : (Aᴴ * P * P * A).trace = (Aᴴ * A).trace := by
        calc (Aᴴ * P * P * A).trace
            = (Aᴴ * (P * P) * A).trace := by simp [Matrix.mul_assoc]
          _ = (Aᴴ * A).trace := by rw [hP2, Matrix.mul_one]
      have ht2 : (P * Aᴴ * P * A).trace = (Aᴴ * (P * A * P)).trace := by
        rw [Matrix.trace_mul_comm (P * Aᴴ * P) A]
        calc (A * (P * Aᴴ * P)).trace
            = (A * P * Aᴴ * P).trace := by simp [Matrix.mul_assoc]
          _ = (P * (A * P * Aᴴ)).trace := by rw [Matrix.trace_mul_comm]
          _ = (P * A * P * Aᴴ).trace := by simp [Matrix.mul_assoc]
          _ = (Aᴴ * (P * A * P)).trace := by rw [Matrix.trace_mul_comm]
      have ht3 : (Aᴴ * P * A * P).trace = (Aᴴ * (P * A * P)).trace := by
        simp [Matrix.mul_assoc]
      rw [ht1, ht2, ht3, ht4]
      simp only [Complex.add_re, Complex.sub_re]
      ring
    have hsum4 : ∑ α : Fin 3, hsNormSq (matComm A (pauliSite x α.succ)) =
        ∑ α : Fin 4, hsNormSq (matComm A (pauliSite x α)) := by
      symm
      rw [Fin.sum_univ_succ]
      have h0 : matComm A (pauliSite x 0) = 0 := by
        unfold matComm; rw [pauliSite_zero, Matrix.mul_one, Matrix.one_mul, sub_self]
      rw [h0]
      have hz : hsNormSq (0 : QubitOp N) = 0 := by unfold hsNormSq hsInner; simp
      rw [hz, zero_add]
    rw [hsum4]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    unfold hsNormSq hsInner siteSizeOp partialTraceSite
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul, Complex.mul_re, Complex.re_sum]
    have h14re : (1 / 4 : ℂ).re = 1 / 4 := by norm_num
    have h14im : (1 / 4 : ℂ).im = 0 := by norm_num
    rw [h14re, h14im]
    ring
  rw [Finset.mul_sum]
  unfold totalSizeOp hsInner
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun x _ ↦ hsite x

end Superoperators

section LocalityFiltration

/-- Concrete ascending locality filtration `𝒱_s ⊆ QubitOp N` spanned by all Pauli strings
of Hamming weight `≤ s`. -/
def filtrationSubmodule (N s : ℕ) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ {P : QubitOp N | ∃ a : Fin N → Fin 4, stringWeight a ≤ s ∧ P = pauliString a}

theorem filtrationSubmodule_mono (N : ℕ) : Monotone (filtrationSubmodule N) := by
  intro s₁ s₂ hle
  apply Submodule.span_mono
  rintro P ⟨a, ha, rfl⟩
  exact ⟨a, le_trans ha hle, rfl⟩

/-- **Concrete `r`-Local Commutator Locality Step**:
For any `H ∈ 𝒱_r` and any `A ∈ 𝒱_s`, the commutator `[H, A]` lies in `𝒱_{min N (s + (r - 1))}`.
This directly discharges the abstract locality hypothesis `hL` of Proposition 4.1 on `(ℂ²)^{⊗ N}`. -/
theorem filtration_comm_step {N r s : ℕ} (hr : 1 ≤ r)
    {H A : QubitOp N}
    (hH : H ∈ filtrationSubmodule N r)
    (hA : A ∈ filtrationSubmodule N s) :
    matComm H A ∈ filtrationSubmodule N (min N (s + (r - 1))) := by
  have hbase : ∀ (a b : Fin N → Fin 4),
      stringWeight a ≤ r → stringWeight b ≤ s →
      matComm (pauliString a) (pauliString b) ∈ filtrationSubmodule N (min N (s + (r - 1))) := by
    intro a b ha hb
    by_cases hdisj : ∀ x : Fin N, a x = 0 ∨ b x = 0
    · have hcomm : matComm (pauliString a) (pauliString b) = 0 := by
        unfold matComm
        rw [pauliString_mul a b, pauliString_mul b a]
        have hph : ∀ x : Fin N, pauliMulPhase (a x) (b x) = pauliMulPhase (b x) (a x) :=
          fun x ↦ pauliMulPhase_zero_comm (a x) (b x) (hdisj x)
        have hidx : (fun x ↦ pauliMulIdx (a x) (b x)) = fun x ↦ pauliMulIdx (b x) (a x) := by
          funext x; exact pauliMulIdx_comm (a x) (b x)
        simp_rw [hph]
        rw [hidx, sub_self]
      rw [hcomm]
      exact Submodule.zero_mem _
    · have hex : ∃ x₀ : Fin N, a x₀ ≠ 0 ∧ b x₀ ≠ 0 := by
        by_contra hno
        apply hdisj; intro x
        by_cases hax : a x = 0
        · exact Or.inl hax
        · right; by_contra hbx; exact hno ⟨x, hax, hbx⟩
      obtain ⟨x₀, hax₀, hbx₀⟩ := hex
      set d : Fin N → Fin 4 := fun x ↦ pauliMulIdx (a x) (b x)
      have hd_le_N : stringWeight d ≤ N := by
        unfold stringWeight
        exact le_trans (Finset.card_filter_le _ _) (by simp)
      have hd_le_sum : stringWeight d ≤ s + (r - 1) := by
        set Sa := Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0)
        set Sb := Finset.univ.filter (fun x : Fin N ↦ b x ≠ 0)
        set Sd := Finset.univ.filter (fun x : Fin N ↦ d x ≠ 0)
        have hsub : Sd ⊆ Sa ∪ Sb := by
          intro x hx
          have hdx : pauliMulIdx (a x) (b x) ≠ 0 := (Finset.mem_filter.mp hx).2
          by_cases hax : a x = 0
          · apply Finset.mem_union_right
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
            intro hbx; rw [hax, hbx] at hdx; exact hdx rfl
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hax⟩)
        have hx0_inter : x₀ ∈ Sa ∩ Sb :=
          Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax₀⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx₀⟩⟩
        have hinter_pos : 1 ≤ (Sa ∩ Sb).card := Finset.card_pos.mpr ⟨x₀, hx0_inter⟩
        have hunion : (Sa ∪ Sb).card + (Sa ∩ Sb).card = Sa.card + Sb.card :=
          Finset.card_union_add_card_inter Sa Sb
        have hSd_le : Sd.card ≤ (Sa ∪ Sb).card := Finset.card_le_card hsub
        change Sd.card ≤ s + (r - 1)
        change Sa.card ≤ r at ha
        change Sb.card ≤ s at hb
        omega
      have hd_mem : pauliString d ∈ filtrationSubmodule N (min N (s + (r - 1))) :=
        Submodule.subset_span ⟨d, le_min hd_le_N hd_le_sum, rfl⟩
      have hidx_comm : (fun x ↦ pauliMulIdx (b x) (a x)) = d := by
        funext x; exact pauliMulIdx_comm (b x) (a x)
      unfold matComm
      rw [pauliString_mul a b, pauliString_mul b a, hidx_comm, ← sub_smul]
      exact Submodule.smul_mem _ _ hd_mem
  have hgenH : ∀ (a : Fin N → Fin 4), stringWeight a ≤ r →
      matComm (pauliString a) A ∈ filtrationSubmodule N (min N (s + (r - 1))) := by
    intro a ha
    refine Submodule.span_induction (p := fun X _ ↦
      matComm (pauliString a) X ∈ filtrationSubmodule N (min N (s + (r - 1)))) ?_ ?_ ?_ ?_ hA
    · rintro P ⟨b, hb, rfl⟩; exact hbase a b ha hb
    · unfold matComm; simp
    · intro X Y _ _ hX hY
      have hlin : matComm (pauliString a) (X + Y) =
          matComm (pauliString a) X + matComm (pauliString a) Y := by
        unfold matComm; noncomm_ring
      rw [hlin]; exact Submodule.add_mem _ hX hY
    · intro c X _ hX
      have hlin : matComm (pauliString a) (c • X) = c • matComm (pauliString a) X := by
        unfold matComm; simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rw [hlin]; exact Submodule.smul_mem _ c hX
  refine Submodule.span_induction (p := fun Y _ ↦
    matComm Y A ∈ filtrationSubmodule N (min N (s + (r - 1)))) ?_ ?_ ?_ ?_ hH
  · rintro P ⟨a, ha, rfl⟩; exact hgenH a ha
  · unfold matComm; simp
  · intro X Y _ _ hX hY
    have hlin : matComm (X + Y) A = matComm X A + matComm Y A := by
      unfold matComm; noncomm_ring
    rw [hlin]; exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    have hlin : matComm (c • X) A = c • matComm X A := by
      unfold matComm; simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [hlin]; exact Submodule.smul_mem _ c hX

end LocalityFiltration

end KrylovChaos
