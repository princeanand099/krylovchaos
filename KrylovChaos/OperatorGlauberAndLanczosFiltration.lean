/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.HighTempConditioning
import KrylovChaos.KrylovTail
import KrylovChaos.Filtration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Operator-Level Quantum Relative Entropy, Gibbs–Donsker–Varadhan Variational Inequality,
# Lemma 6.1 HS Identity & Concrete Lanczos Filtration Containment (Flaws #4 & #5)

1. **Concrete Quantum Relative Entropy on `QubitOp N` (Prop. 6.4(2), Flaw #4)**:
   - `quantumRelEntropy hρ hσ := Re Tr(ρ (log ρ - log σ))` and `quantumRelEntropy_nonneg` (Klein).
   - `gibbsRelEntropy hρ hH β := Re Tr(ρ (log ρ + β H)) + log Z(β)` and `gibbsRelEntropy_nonneg`.
   - `gibbs_variational_bound` (Eq. 6.9 on `QubitOp N`):
     `Re Tr(ρ X) ≤ gibbsRelEntropy hρ hH β + log(Z(-β H + X) / Z(-β H))`.
2. **Concrete Operator-Level Lemma 6.1 Identity on `QubitOp N` (Flaw #4)**:
   - `hsNormSq_siteSizeOp_eq_comm_avg`: `hsNormSq (siteSizeOp x M) = (1/8) ∑_{α=1}^3 hsNormSq (matComm M (pauliSite x α.succ))`.
   - `lemma_6_1_concrete_operator`: exact Hilbert–Schmidt commutator representation of `𝒮_x(𝒥_β A)`.
3. **Concrete Lanczos Filtration Containment & Truncation (Flaw #5)**:
   - `matComm_mem_filtration`: if `H ∈ filtrationSubmodule N r` (`r ≥ 1`) and `A ∈ filtrationSubmodule N k`,
     then `matComm H A ∈ filtrationSubmodule N (k + (r - 1))`.
   - `lanczosOp_mem_filtration`: `lanczosOp G H O n ∈ filtrationSubmodule N (s₀ + n * (r - 1))`.
   - `lanczosTrunc_mem_filtration`: the concrete `M`-term Lanczos truncation lies in
     `filtrationSubmodule N (s₀ + (M - 1) * (r - 1))`.
-/

namespace KrylovChaos

open Matrix

section QuantumRelativeEntropy

/-- Concrete quantum relative entropy `D(ρ ‖ σ) = Re Tr(ρ (log ρ - log σ))` on `QubitOp N`. -/
noncomputable def quantumRelEntropy {N : ℕ} {ρ σ : QubitOp N}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : ℝ :=
  (ρ * (hermFunc hρ (fun x ↦ (Real.log x : ℂ)) - hermFunc hσ (fun y ↦ (Real.log y : ℂ)))).trace.re

/-- Concrete Gibbs quantum relative entropy `D(ρ ‖ ρ_β) = Re Tr(ρ (log ρ + β H)) + log Z(β)`. -/
noncomputable def gibbsRelEntropy {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  (ρ * (hermFunc hρ (fun x ↦ (Real.log x : ℂ)) + ((β : ℝ) : ℂ) • H)).trace.re +
    Real.log (gibbsPartitionFn hH β)

private lemma eigU_mul_star' {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

private lemma eigU_star_mul' {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

private lemma log_ineq_kl {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x * (Real.log x - Real.log y) - x + y := by
  have h1 : 1 - y / x ≤ -Real.log (y / x) := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
    linarith
  have h2 : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'
  rw [h2] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hx.le
  have hmul : x * (1 - y / x) = x - y := by field_simp [hx.ne']
  linarith

private lemma trace_herm_mul_hermFunc_re {N : ℕ} {ρ A : QubitOp N}
    (hρ : ρ.IsHermitian) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (ρ * hermFunc hA (fun y ↦ (f y : ℂ))).trace.re =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖((hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hA.eigenvectorUnitary : QubitOp N)) i j‖ ^ 2 *
          (hρ.eigenvalues i * f (hA.eigenvalues j)) := by
  set U : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
  set V : QubitOp N := (hA.eigenvectorUnitary : QubitOp N)
  set W : QubitOp N := Uᴴ * V
  set Dρ : QubitOp N := Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))
  set F : QubitOp N := Matrix.diagonal (fun j ↦ (f (hA.eigenvalues j) : ℂ))
  have hρ_eq : ρ = U * Dρ * Uᴴ := (hermFunc_id hρ).symm
  have hA_eq : hermFunc hA (fun y ↦ (f y : ℂ)) = V * F * Vᴴ := rfl
  have hcyc : (ρ * hermFunc hA (fun y ↦ (f y : ℂ))).trace = (Dρ * W * F * Wᴴ).trace := by
    rw [hρ_eq, hA_eq]
    have h1 : U * Dρ * Uᴴ * (V * F * Vᴴ) = U * (Dρ * W * F * Vᴴ) := by
      simp only [W, Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    have h2 : Dρ * W * F * Vᴴ * U = Dρ * W * F * Wᴴ := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [h2]
  rw [hcyc]
  simp only [Dρ, F, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hnorm : W i j * star (W i j) = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  have hrew : (hρ.eigenvalues i : ℂ) * W i j * (f (hA.eigenvalues j) : ℂ) * star (W i j) =
      (((‖W i j‖ ^ 2 * (hρ.eigenvalues i * f (hA.eigenvalues j)) : ℝ) : ℂ)) := by
    push_cast; linear_combination (hρ.eigenvalues i : ℂ) * (f (hA.eigenvalues j) : ℂ) * hnorm
  rw [hrew, Complex.ofReal_re]

private lemma unitary_overlap_doubly_stochastic {N : ℕ} {ρ A : QubitOp N}
    (hρ : ρ.IsHermitian) (hA : A.IsHermitian) :
    let W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hA.eigenvectorUnitary : QubitOp N)
    (∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 = 1) ∧
    (∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖W i j‖ ^ 2 = 1) := by
  intro W
  set U : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
  set V : QubitOp N := (hA.eigenvectorUnitary : QubitOp N)
  have hW1 : W * Wᴴ = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * U := by rw [eigU_mul_star' hA, Matrix.mul_one]
      _ = 1 := eigU_star_mul' hρ
  have hW2 : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * V := by rw [eigU_mul_star' hρ, Matrix.mul_one]
      _ = 1 := eigU_star_mul' hA
  constructor
  · intro i
    have h1 := congrFun (congrFun hW1 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  · intro j
    have h1 := congrFun (congrFun hW2 j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Klein's Inequality (`D(ρ ‖ σ) ≥ 0`) on `QubitOp N`**. -/
theorem quantumRelEntropy_nonneg {N : ℕ} {ρ σ : QubitOp N}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ_pos : ∀ i : QubitIdx N, 0 < hρ.eigenvalues i)
    (hσ_pos : ∀ j : QubitIdx N, 0 < hσ.eigenvalues j)
    (hρ_tr : ρ.trace = 1) (hσ_tr : σ.trace = 1) :
    0 ≤ quantumRelEntropy hρ hσ := by
  set W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hσ.eigenvectorUnitary : QubitOp N)
  obtain ⟨hrow, hcol⟩ := unitary_overlap_doubly_stochastic hρ hσ
  have hsum_ρ : ∑ i : QubitIdx N, hρ.eigenvalues i = 1 := by
    have h1 := hermFunc_trace hρ (fun x ↦ (x : ℂ))
    rw [hermFunc_id hρ, hρ_tr] at h1
    simpa [Complex.re_sum] using (congrArg Complex.re h1.symm)
  have hsum_σ : ∑ j : QubitIdx N, hσ.eigenvalues j = 1 := by
    have h1 := hermFunc_trace hσ (fun x ↦ (x : ℂ))
    rw [hermFunc_id hσ, hσ_tr] at h1
    simpa [Complex.re_sum] using (congrArg Complex.re h1.symm)
  have htr1 : (ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))).trace.re =
      ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
    have h1 : ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) =
        hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := by
      calc ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))
          = hermFunc hρ (fun x ↦ (x : ℂ)) * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) :=
            congrArg (· * _) (hermFunc_id hρ).symm
        _ = hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := hermFunc_mul hρ _ _
    rw [h1, hermFunc_trace, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have htr2 := trace_herm_mul_hermFunc_re hρ hσ Real.log
  have hD : quantumRelEntropy hρ hσ =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (hσ.eigenvalues j)) -
          hρ.eigenvalues i + hσ.eigenvalues j) := by
    unfold quantumRelEntropy
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, htr1, htr2]
    have h1 : ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) := by
      apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, hrow i, one_mul]
    have h2 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = 1 := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = hρ.eigenvalues i := fun i ↦ by
        rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this]; exact hsum_ρ
    have h3 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hσ.eigenvalues j = 1 := by
      rw [Finset.sum_comm]
      have : ∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖W i j‖ ^ 2 * hσ.eigenvalues j = hσ.eigenvalues j := fun j ↦ by
        rw [← Finset.sum_mul, hcol j, one_mul]
      simp_rw [this]; exact hsum_σ
    have hsplit : ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (hσ.eigenvalues j)) -
          hρ.eigenvalues i + hσ.eigenvalues j) =
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i))) -
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hσ.eigenvalues j))) -
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i) +
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hσ.eigenvalues j) := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hsplit, ← h1, h2, h3]; ring
  rw [hD]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (sq_nonneg _) (log_ineq_kl (hρ_pos i) (hσ_pos j))

/-- **Gibbs Klein Inequality (`D(ρ ‖ ρ_β) ≥ 0`) on `QubitOp N`**. -/
theorem gibbsRelEntropy_nonneg {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hρ_pos : ∀ i : QubitIdx N, 0 < hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β : ℝ) :
    0 ≤ gibbsRelEntropy hρ hH β := by
  set W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N)
  obtain ⟨hrow, hcol⟩ := unitary_overlap_doubly_stochastic hρ hH
  have hZ := gibbsPartitionFn_pos hH β
  set μ : QubitIdx N → ℝ := fun j ↦ (gibbsPartitionFn hH β)⁻¹ * Real.exp (-β * hH.eigenvalues j)
  have hμ_pos : ∀ j, 0 < μ j := fun j ↦ mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)
  have hμ_sum : ∑ j : QubitIdx N, μ j = 1 := by
    simp only [μ, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hZ.ne'
  have hlogμ : ∀ j, Real.log (μ j) = -β * hH.eigenvalues j - Real.log (gibbsPartitionFn hH β) := by
    intro j
    simp only [μ, Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    ring
  have hsum_ρ : ∑ i : QubitIdx N, hρ.eigenvalues i = 1 := by
    have h1 := hermFunc_trace hρ (fun x ↦ (x : ℂ))
    rw [hermFunc_id hρ, hρ_tr] at h1
    simpa [Complex.re_sum] using (congrArg Complex.re h1.symm)
  have htr1 : (ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))).trace.re =
      ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
    have h1 : ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) =
        hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := by
      calc ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))
          = hermFunc hρ (fun x ↦ (x : ℂ)) * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) :=
            congrArg (· * _) (hermFunc_id hρ).symm
        _ = hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := hermFunc_mul hρ _ _
    rw [h1, hermFunc_trace, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have htrH : (ρ * (((β : ℝ) : ℂ) • H)).trace.re =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j)) := by
    have hH_eq : ((β : ℝ) : ℂ) • H = hermFunc hH (fun y ↦ ((β * y : ℝ) : ℂ)) := by
      calc ((β : ℝ) : ℂ) • H
          = ((β : ℝ) : ℂ) • hermFunc hH (fun x ↦ (x : ℂ)) :=
            congrArg (((β : ℝ) : ℂ) • ·) (hermFunc_id hH).symm
        _ = hermFunc hH (fun y ↦ ((β * y : ℝ) : ℂ)) := by
            unfold hermFunc
            rw [← smul_mul_assoc, ← mul_smul_comm]
            congr 1; congr 1; ext a b
            by_cases hab : a = b
            · subst hab; simp [Matrix.diagonal_apply]
            · simp [Matrix.diagonal_apply, hab]
    rw [hH_eq]
    exact trace_herm_mul_hermFunc_re hρ hH (fun y ↦ β * y)
  have hD : gibbsRelEntropy hρ hH β =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (μ j)) -
          hρ.eigenvalues i + μ j) := by
    unfold gibbsRelEntropy
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, htr1, htrH]
    have h1 : ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) := by
      apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, hrow i, one_mul]
    have h2 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = 1 := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = hρ.eigenvalues i := fun i ↦ by
        rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this]; exact hsum_ρ
    have h3 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * μ j = 1 := by
      rw [Finset.sum_comm]
      have : ∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖W i j‖ ^ 2 * μ j = μ j := fun j ↦ by
        rw [← Finset.sum_mul, hcol j, one_mul]
      simp_rw [this]; exact hμ_sum
    have h4 : Real.log (gibbsPartitionFn hH β) =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β)) := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β)) =
          hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β) := fun i ↦ by
        rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this, ← Finset.sum_mul, hsum_ρ, one_mul]
    simp_rw [hlogμ]
    have hsplit : ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - (-β * hH.eigenvalues j - Real.log (gibbsPartitionFn hH β))) -
          hρ.eigenvalues i + μ j) =
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i))) +
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j))) +
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β))) -
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i) +
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * μ j) := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hsplit, ← h1, ← h4, h2, h3]; ring
  rw [hD]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (sq_nonneg _) (log_ineq_kl (hρ_pos i) (hμ_pos j))

/-- **Exact Gibbs–Donsker–Varadhan Variational Inequality (Eq. 6.9 of Prop. 6.4(2)) on `QubitOp N`**:
For ANY positive-definite unit-trace density matrix `ρ`, ANY Hermitian `H` and `X`, and ANY `β : ℝ`:
`Re Tr(ρ X) ≤ D(ρ ‖ ρ_β) + log(Tr(exp(-β H + X)) / Tr(exp(-β H)))`. -/
theorem gibbs_variational_bound {N : ℕ} {ρ H X : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian) (hX : X.IsHermitian)
    (hρ_pos : ∀ i : QubitIdx N, 0 < hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β : ℝ) :
    let K : QubitOp N := ((-β : ℝ) : ℂ) • H + X
    have hK : K.IsHermitian := by
      simp only [K, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Complex.star_def, Complex.conj_ofReal, hH.eq, hX.eq]
    (ρ * X).trace.re ≤
      gibbsRelEntropy hρ hH β +
        Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) := by
  intro K hK
  have hnn := gibbsRelEntropy_nonneg hρ hK hρ_pos hρ_tr (-1)
  have hZβ := gibbsPartitionFn_pos hH β
  have hZK := gibbsPartitionFn_pos hK (-1)
  have hlog_div : Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) =
      Real.log (gibbsPartitionFn hK (-1)) - Real.log (gibbsPartitionFn hH β) :=
    Real.log_div hZK.ne' hZβ.ne'
  have hK_eq : (((-1 : ℝ) : ℂ) • K) = ((β : ℝ) : ℂ) • H - X := by
    simp only [K, smul_add, smul_smul]; ext i j; simp; ring
  unfold gibbsRelEntropy at hnn ⊢
  rw [hK_eq, ← add_sub_assoc, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
    Complex.sub_re, Complex.add_re] at hnn
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hlog_div]
  linarith

end QuantumRelativeEntropy

section ConcreteLemma61

/-- Exact single-site Hilbert–Schmidt identity:
`‖𝒮_x(M)‖_HS² = (1 / 8) ∑_{α=1}^3 ‖[M, σ_x^α]‖_HS²` for EVERY `M : QubitOp N` and `x : Fin N`. -/
theorem hsNormSq_siteSizeOp_eq_comm_avg {N : ℕ} (x : Fin N) (M : QubitOp N) :
    hsNormSq (siteSizeOp x M) =
      (1 / 8 : ℝ) * ∑ α : Fin 3, hsNormSq (matComm M (pauliSite x α.succ)) := by
  have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
  set c : (Fin N → Fin 4) → ℂ := fun a ↦ (1 / (2 : ℂ) ^ N) * (pauliString a * M).trace
  have hM : M = ∑ a : Fin N → Fin 4, c a • pauliString a := pauli_expansion_concrete M
  have hsite_pauli : ∀ a : Fin N → Fin 4,
      siteSizeOp x (pauliString a) = if a x ≠ 0 then pauliString a else 0 := by
    intro a
    unfold siteSizeOp partialTraceSite pauliString
    have hconj : ∀ k : Fin 4,
        pauliSite x k * kronOp (fun y ↦ pauliMat (a y)) * pauliSite x k =
        kronOp (fun y ↦ if y = x then pauliMat k * pauliMat (a x) * pauliMat k else pauliMat (a y)) := by
      intro k; unfold pauliSite pauliString; rw [kronOp_mul, kronOp_mul]; congr 1; funext y
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy, hp0]
    simp_rw [hconj]
    ext p q
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, kronOp, Matrix.of_apply, smul_eq_mul]
    have hsplit : ∀ k : Fin 4,
        (∏ y : Fin N, (if y = x then pauliMat k * pauliMat (a x) * pauliMat k else pauliMat (a y)) (p y) (q y)) =
        (pauliMat k * pauliMat (a x) * pauliMat k) (p x) (q x) *
          ∏ y ∈ Finset.univ.erase x, pauliMat (a y) (p y) (q y) := by
      intro k; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      congr 1; · simp
      · apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
    simp_rw [hsplit, ← Finset.sum_mul, ← mul_assoc]
    have htw : (1 / 4 : ℂ) * (∑ k : Fin 4, (pauliMat k * pauliMat (a x) * pauliMat k) (p x) (q x)) =
        if a x = 0 then pauliMat (a x) (p x) (q x) else 0 := by
      generalize a x = u; generalize p x = i1; generalize q x = j1
      fin_cases u <;> fin_cases i1 <;> fin_cases j1 <;>
        (simp [Fin.sum_univ_four, pauliMat, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
    rw [htw]
    by_cases hax : a x = 0
    · rw [if_pos hax, if_neg (not_not.mpr hax), Matrix.zero_apply]
      rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ pauliMat (a y) (p y) (q y)) (Finset.mem_univ x), sub_self]
    · rw [if_neg hax, if_pos hax, zero_mul, sub_zero]; rfl
  have hcomm_hs : ∀ α : Fin 3,
      hsNormSq (matComm M (pauliSite x α.succ)) =
      2 * hsNormSq M - 2 * (Matrix.trace (Mᴴ * pauliSite x α.succ * M * pauliSite x α.succ)).re := by
    intro α
    set P := pauliSite x α.succ
    have hPh : Pᴴ = P := by
      unfold P pauliSite pauliString; rw [kronOp_conjTranspose]; congr 1; funext y
      by_cases hy : y = x
      · subst hy; simp; exact pauliMat_herm α.succ
      · simp [hy]; exact pauliMat_herm 0
    have hPsq : P * P = 1 := by
      unfold P pauliSite pauliString; rw [kronOp_mul]
      have h1 : (fun y : Fin N ↦ pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y) *
          pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y)) = fun _ ↦ 1 := by
        funext y; exact pauliMat_sq _
      rw [h1, kronOp_one]
    unfold hsNormSq hsInner matComm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh]
    simp only [sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
    have ht1 : (P * Mᴴ * (M * P)).trace = (Mᴴ * M).trace := by
      calc (P * Mᴴ * (M * P)).trace = ((P * Mᴴ * M) * P).trace := by simp only [Matrix.mul_assoc]
        _ = (P * (P * Mᴴ * M)).trace := Matrix.trace_mul_comm _ _
        _ = ((P * P) * Mᴴ * M).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * M).trace := by rw [hPsq, Matrix.one_mul]
    have ht2 : (Mᴴ * P * (P * M)).trace = (Mᴴ * M).trace := by
      calc (Mᴴ * P * (P * M)).trace = (Mᴴ * (P * P) * M).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * M).trace := by rw [hPsq, Matrix.mul_one]
    have ht3 : (P * Mᴴ * (P * M)).trace = (Mᴴ * P * M * P).trace := by
      calc (P * Mᴴ * (P * M)).trace = (P * (Mᴴ * P * M)).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * P * M * P).trace := Matrix.trace_mul_comm _ _
    have ht4 : (Mᴴ * P * (M * P)).trace = (Mᴴ * P * M * P).trace := by simp only [Matrix.mul_assoc]
    rw [ht1, ht2, ht3, ht4]; ring
  have hsum_twirl : (∑ α : Fin 3, pauliSite x α.succ * M * pauliSite x α.succ) =
      (4 : ℂ) • partialTraceSite x M - M := by
    unfold partialTraceSite
    have h4 : (4 : ℂ) • ((1 / 4 : ℂ) • ∑ k : Fin 4, pauliSite x k * M * pauliSite x k) =
        ∑ k : Fin 4, pauliSite x k * M * pauliSite x k := by
      rw [smul_smul]; norm_num
    have h0 : pauliSite x 0 = 1 := by
      unfold pauliSite pauliString
      have : (fun y : Fin N ↦ pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x (0 : Fin 4) y)) = fun _ ↦ 1 := by
        funext y; by_cases hy : y = x <;> simp [hy, hp0]
      rw [this, kronOp_one]
    rw [h4]
    symm
    rw [Fin.sum_univ_succ, h0, Matrix.one_mul, Matrix.mul_one, add_sub_cancel_left]
  have hsite_hs : hsNormSq (siteSizeOp x M) =
      hsNormSq M - (Matrix.trace (Mᴴ * partialTraceSite x M)).re := by
    have hidem := siteSizeOp_idem x M
    have hsa := siteSizeOp_self_adj x M (siteSizeOp x M)
    unfold hsNormSq hsInner at hsa ⊢
    have heq : ((siteSizeOp x M)ᴴ * siteSizeOp x M).trace = (Mᴴ * siteSizeOp x M).trace := by
      rw [hsa, hidem]
    rw [heq]
    unfold siteSizeOp
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp_rw [hcomm_hs]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have htr_sum : (∑ α : Fin 3, (Matrix.trace (Mᴴ * pauliSite x α.succ * M * pauliSite x α.succ)).re) =
      4 * (Matrix.trace (Mᴴ * partialTraceSite x M)).re - hsNormSq M := by
    have h1 : (∑ α : Fin 3, (Matrix.trace (Mᴴ * pauliSite x α.succ * M * pauliSite x α.succ)).re) =
        (Matrix.trace (Mᴴ * ∑ α : Fin 3, pauliSite x α.succ * M * pauliSite x α.succ)).re := by
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro α _
      congr 1; simp only [Matrix.mul_assoc]
    rw [h1, hsum_twirl, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, Complex.sub_re]
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rfl
  rw [← Finset.mul_sum, htr_sum, hsite_hs]
  ring

/-- **Concrete Operator-Level Lemma 6.1 HS Identity on `QubitOp N`**:
For ANY `G : GibbsData N`, site `x : Fin N`, and operator `A : QubitOp N`:
`hsNormSq (siteSizeOp x (jBeta G.ρQuarter A)) = (1 / 8) ∑_{α=1}^3 hsNormSq (matComm (jBeta G.ρQuarter A) (pauliSite x α.succ))`. -/
theorem lemma_6_1_concrete_operator {N : ℕ} (G : GibbsData N) (x : Fin N) (A : QubitOp N) :
    hsNormSq (siteSizeOp x (jBeta G.ρQuarter A)) =
      (1 / 8 : ℝ) * ∑ α : Fin 3,
        hsNormSq (matComm (jBeta G.ρQuarter A) (pauliSite x α.succ)) :=
  hsNormSq_siteSizeOp_eq_comm_avg x (jBeta G.ρQuarter A)

end ConcreteLemma61

section ConcreteLanczosFiltration

private lemma pauliMat_mul_pauliMat_exists (a b : Fin 4) :
    ∃ (c : ℂ) (d : Fin 4), pauliMat a * pauliMat b = c • pauliMat d ∧
      (a = 0 → b = 0 → d = 0) := by
  fin_cases a <;> fin_cases b
  all_goals first
    | (refine ⟨1, 0, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨1, 1, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨1, 2, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨1, 3, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨Complex.I, 1, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨Complex.I, 2, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨Complex.I, 3, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨-Complex.I, 1, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨-Complex.I, 2, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)
    | (refine ⟨-Complex.I, 3, ?_, by simp⟩; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; done)

private lemma pauliString_mul_mem_filtration {N : ℕ} (a b : Fin N → Fin 4) :
    ∃ (c : ℂ) (d : Fin N → Fin 4), pauliString a * pauliString b = c • pauliString d ∧
      ∀ x : Fin N, a x = 0 → b x = 0 → d x = 0 := by
  choose c d hmul hz using fun x ↦ pauliMat_mul_pauliMat_exists (a x) (b x)
  refine ⟨∏ x : Fin N, c x, d, ?_, hz⟩
  unfold pauliString
  rw [kronOp_mul]
  ext p q
  simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro x _
  have h1 := congrFun (congrFun (hmul x) (p x)) (q x)
  simpa [Matrix.smul_apply, smul_eq_mul] using h1

/-- **Concrete Commutator Support Growth Bound on `QubitOp N`**:
If `H ∈ filtrationSubmodule N r` (`1 ≤ r`) and `A ∈ filtrationSubmodule N k`, then
`matComm H A ∈ filtrationSubmodule N (k + (r - 1))`. -/
theorem matComm_mem_filtration {N r k : ℕ} (hr : 1 ≤ r)
    {H A : QubitOp N} (hH : H ∈ filtrationSubmodule N r) (hA : A ∈ filtrationSubmodule N k) :
    matComm H A ∈ filtrationSubmodule N (k + (r - 1)) := by
  have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
  have hbasis : ∀ (a b : Fin N → Fin 4), stringWeight a ≤ r → stringWeight b ≤ k →
      matComm (pauliString a) (pauliString b) ∈ filtrationSubmodule N (k + (r - 1)) := by
    intro a b ha hb
    by_cases hover : ∃ x : Fin N, a x ≠ 0 ∧ b x ≠ 0
    · rcases hover with ⟨x₀, hax₀, hbx₀⟩
      have hcard_union : (Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0 ∨ b x ≠ 0)).card ≤ k + (r - 1) := by
        set Sa := Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0)
        set Sb := Finset.univ.filter (fun x : Fin N ↦ b x ≠ 0)
        have hu : Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0 ∨ b x ≠ 0) = Sa ∪ Sb := by
          ext x; simp [Sa, Sb]
        rw [hu]
        have h1 := Finset.card_union_add_card_inter Sa Sb
        have h2 : 1 ≤ (Sa ∩ Sb).card :=
          Finset.Nonempty.card_pos ⟨x₀, Finset.mem_inter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax₀⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx₀⟩⟩⟩
        have hSa : Sa.card ≤ r := ha
        have hSb : Sb.card ≤ k := hb
        omega
      obtain ⟨c₁, d₁, hmul₁, hz₁⟩ := pauliString_mul_mem_filtration a b
      obtain ⟨c₂, d₂, hmul₂, hz₂⟩ := pauliString_mul_mem_filtration b a
      have hd₁ : stringWeight d₁ ≤ k + (r - 1) := by
        refine le_trans ?_ hcard_union
        unfold stringWeight
        apply Finset.card_le_card; intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        by_contra hnor; push Not at hnor
        exact hx (hz₁ x hnor.1 hnor.2)
      have hd₂ : stringWeight d₂ ≤ k + (r - 1) := by
        refine le_trans ?_ hcard_union
        unfold stringWeight
        apply Finset.card_le_card; intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        by_contra hnor; push Not at hnor
        exact hx (hz₂ x hnor.2 hnor.1)
      unfold matComm
      rw [hmul₁, hmul₂]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨d₁, hd₁, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨d₂, hd₂, rfl⟩))
    · push Not at hover
      have hcomm : matComm (pauliString a) (pauliString b) = 0 := by
        unfold matComm pauliString
        rw [kronOp_mul, kronOp_mul]
        have heq : (fun x : Fin N ↦ pauliMat (a x) * pauliMat (b x)) =
            fun x ↦ pauliMat (b x) * pauliMat (a x) := by
          funext x
          by_cases hax : a x = 0
          · simp [hax, hp0]
          · have hbx : b x = 0 := hover x hax
            simp [hbx, hp0]
        rw [heq, sub_self]
      rw [hcomm]; exact Submodule.zero_mem _
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hH
  · rintro _ ⟨a, ha, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
    · rintro _ ⟨b, hb, rfl⟩; exact hbasis a b ha hb
    · unfold matComm; simp
    · intro X Y _ _ hX hY
      have hlin : matComm (pauliString a) (X + Y) = matComm (pauliString a) X + matComm (pauliString a) Y := by
        unfold matComm; rw [Matrix.mul_add, Matrix.add_mul]; abel
      rw [hlin]; exact Submodule.add_mem _ hX hY
    · intro c X _ hX
      have hlin : matComm (pauliString a) (c • X) = c • matComm (pauliString a) X := by
        unfold matComm; rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rw [hlin]; exact Submodule.smul_mem _ _ hX
  · unfold matComm; simp
  · intro X Y _ _ hX hY
    have hlin : matComm (X + Y) A = matComm X A + matComm Y A := by
      unfold matComm; rw [Matrix.add_mul, Matrix.mul_add]; abel
    rw [hlin]; exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    have hlin : matComm (c • X) A = c • matComm X A := by
      unfold matComm; rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [hlin]; exact Submodule.smul_mem _ _ hX

private lemma filtrationSubmodule_le {N k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    filtrationSubmodule N k₁ ≤ filtrationSubmodule N k₂ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact Submodule.subset_span ⟨a, le_trans ha h, rfl⟩

/-- **Concrete Lanczos Basis Filtration Containment (Flaw #5)**:
If `H ∈ filtrationSubmodule N r` (`1 ≤ r`) and `O ∈ filtrationSubmodule N s₀`, then for EVERY
`n : ℕ`, the concrete `n`-th Wightman Lanczos operator satisfies:
`lanczosOp G H O n ∈ filtrationSubmodule N (s₀ + n * (r - 1))`. -/
theorem lanczosOp_mem_filtration {N r s₀ : ℕ} (hr : 1 ≤ r)
    (G : GibbsData N) {H O : QubitOp N}
    (hH : H ∈ filtrationSubmodule N r) (hO : O ∈ filtrationSubmodule N s₀) :
    ∀ n : ℕ, lanczosOp G H O n ∈ filtrationSubmodule N (s₀ + n * (r - 1)) ∧
      (lanczosState G H O n).2.1 ∈ filtrationSubmodule N (s₀ + n * (r - 1)) := by
  intro n
  induction n with
  | zero =>
    simp only [zero_mul, add_zero, lanczosOp, lanczosState]
    constructor
    · split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ hO
    · exact Submodule.zero_mem _
  | succ n ih =>
    rcases ih with ⟨hOn, hOprev⟩
    have hcomm : matComm H (lanczosOp G H O n) ∈ filtrationSubmodule N (s₀ + (n + 1) * (r - 1)) := by
      have h1 := matComm_mem_filtration hr hH hOn
      have heq : s₀ + n * (r - 1) + (r - 1) = s₀ + (n + 1) * (r - 1) := by ring
      rwa [heq] at h1
    have hprev_mono : (lanczosState G H O n).2.1 ∈ filtrationSubmodule N (s₀ + (n + 1) * (r - 1)) :=
      filtrationSubmodule_le (by nlinarith) hOprev
    have hOn_mono : lanczosOp G H O n ∈ filtrationSubmodule N (s₀ + (n + 1) * (r - 1)) :=
      filtrationSubmodule_le (by nlinarith) hOn
    have hAnext : matComm H (lanczosOp G H O n) -
        ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1 ∈
        filtrationSubmodule N (s₀ + (n + 1) * (r - 1)) :=
      Submodule.sub_mem _ hcomm (Submodule.smul_mem _ _ hprev_mono)
    constructor
    · unfold lanczosOp
      simp only [lanczosState]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ hAnext
    · exact hOn_mono

/-- Concrete `M`-term Lanczos truncation `A_M(t) = ∑_{n < M} (i^n φ_n(t)) • 𝒪_n` (Eq. 2.7 / Eq. 4.3). -/
noncomputable def lanczosTrunc {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (M : ℕ) (t : ℝ) : QubitOp N :=
  ∑ n ∈ Finset.range M,
    (Complex.I ^ n * concreteKrylovWavefn hH β O n t) •
      lanczosOp (concreteGibbsData hH β) H O n

/-- **Concrete `M`-Term Lanczos Truncation Filtration Containment**:
For `M ≥ 1`, `H ∈ filtrationSubmodule N r` (`r ≥ 1`), `O ∈ filtrationSubmodule N s₀`,
`lanczosTrunc hH β O M t ∈ filtrationSubmodule N (s₀ + (M - 1) * (r - 1))`. -/
theorem lanczosTrunc_mem_filtration {N r s₀ M : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp N} (hH : H.IsHermitian) (β : ℝ) (t : ℝ)
    (hHf : H ∈ filtrationSubmodule N r) (hOf : O ∈ filtrationSubmodule N s₀) :
    lanczosTrunc hH β O M t ∈ filtrationSubmodule N (s₀ + (M - 1) * (r - 1)) := by
  unfold lanczosTrunc
  apply Submodule.sum_mem; intro n hn
  have hnM : n ≤ M - 1 := by have := Finset.mem_range.mp hn; omega
  apply Submodule.smul_mem
  have hmem := (lanczosOp_mem_filtration hr (concreteGibbsData hH β) hHf hOf n).1
  exact filtrationSubmodule_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ hnM) s₀) hmem

end ConcreteLanczosFiltration

end KrylovChaos
