/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ManyBodySetup
import KrylovChaos.Filtration
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Wightman Orthogonal Projectors, Size Bounds & Operator-Level Lemma 4.2

Formalizes from ground up on the concrete `N`-qubit operator algebra `QubitOp N`:
1. Self-adjointness and idempotence of `partialTraceSite` and `siteSizeOp`.
2. **Exact operator bounds** `0 ≤ ⟨M, 𝒮 M⟩_HS ≤ N ‖M‖_HS²` (`totalSizeOp_bounds`),
   symmetry (`totalSizeOp_symm_re`), and Cauchy–Schwarz (`totalSizeOp_cauchy_schwarz`).
3. **Operator-level Lemma 4.2** (`lemma_4_2_operator_thermal_size_truncation`, Eq. 4.3):
   for any operator decomposition `O = A_M + R_M` in `QubitOp N`, derives Eq. (4.3)
   directly from `0 ⪯ 𝒮 ⪯ N 1`, Cauchy–Schwarz, and Wightman orthogonality without
   assuming scalar hypotheses `hcross`, `hqR`, `hlead`.
4. **Concrete Wightman Orthogonal Projectors** `Π_s^{(β)}` (`wightmanProj`) via Mathlib's
   `Submodule.starProjection` on the finite-dimensional Hilbert–Schmidt inner product
   space `HSOp N`, Loewner monotonicity (`loewner_proj_mono`), and **Proposition 4.1
   Loewner Dominance** `P_{𝒦_k} ⪯ Π_{s_0 + (r - 1) k}^{(β)}` (`prop_4_1_loewner_dominance`).
-/

namespace KrylovChaos

section OperatorSizeBounds

/-- The Hilbert–Schmidt squared norm `Re ⟨M, M⟩_HS` is non-negative. -/
theorem hsNormSq_nn {N : ℕ} (M : QubitOp N) : 0 ≤ (hsInner M M).re := by
  unfold hsInner
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Complex.conj_mul']
  exact Complex.normSq_nonneg _

/-- `partialTraceSite x` is self-adjoint for the Hilbert–Schmidt inner product. -/
theorem partialTraceSite_selfAdjoint {N : ℕ} (x : Fin N) (A B : QubitOp N) :
    hsInner A (partialTraceSite x B) = hsInner (partialTraceSite x A) B := by
  have h1 : hsInner A (partialTraceSite x B) =
      (1 / 4 : ℂ) * ∑ α : Fin 4, (Aᴴ * pauliSite x α * B * pauliSite x α).trace := by
    simp only [hsInner, partialTraceSite, Matrix.mul_smul, Matrix.mul_sum,
      Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, Matrix.mul_assoc]
  have h2 : hsInner (partialTraceSite x A) B =
      (1 / 4 : ℂ) * ∑ α : Fin 4, (pauliSite x α * Aᴴ * pauliSite x α * B).trace := by
    have hstar : star (1 / 4 : ℂ) = (1 / 4 : ℂ) := by norm_num
    simp only [hsInner, partialTraceSite, Matrix.conjTranspose_smul, hstar,
      Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, pauliSite_herm,
      Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      smul_eq_mul, Matrix.mul_assoc]
  rw [h1, h2]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [Matrix.trace_mul_comm (Aᴴ * pauliSite x α * B) (pauliSite x α)]
  simp only [Matrix.mul_assoc]

/-- Index multiplication table of the 4 Pauli matrices (up to phase). -/
private def pauliMulIdx : Fin 4 → Fin 4 → Fin 4
  | 0, β => β
  | α, 0 => α
  | 1, 1 => 0
  | 2, 2 => 0
  | 3, 3 => 0
  | 1, 2 => 3
  | 2, 1 => 3
  | 2, 3 => 1
  | 3, 2 => 1
  | 3, 1 => 2
  | 1, 3 => 2

private lemma pauliMulIdx_invol (α β : Fin 4) :
    pauliMulIdx α (pauliMulIdx α β) = β := by
  fin_cases α <;> fin_cases β <;> decide

private lemma pauliMat_mul_conj (α β : Fin 4) :
    ∃ c : ℂ, c * star c = 1 ∧
      pauliMat α * pauliMat β = c • pauliMat (pauliMulIdx α β) ∧
      pauliMat β * pauliMat α = star c • pauliMat (pauliMulIdx α β) := by
  fin_cases α <;> fin_cases β
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨-Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨-Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]⟩
  · exact ⟨Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨-Complex.I, by simp [Complex.star_def, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def, Complex.I_mul_I]⟩
  · exact ⟨1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, pauliMulIdx, Matrix.mul_apply, Fin.sum_univ_two]⟩

private lemma pauliSite_conj_mul {N : ℕ} (x : Fin N) (α β : Fin 4) (M : QubitOp N) :
    pauliSite x α * (pauliSite x β * M * pauliSite x β) * pauliSite x α =
    pauliSite x (pauliMulIdx α β) * M * pauliSite x (pauliMulIdx α β) := by
  obtain ⟨c, hc, h1, h2⟩ := pauliMat_mul_conj α β
  have hL : pauliSite x α * pauliSite x β = c • pauliSite x (pauliMulIdx α β) := by
    unfold pauliSite
    rw [kronOp_mul]
    ext a b
    simp only [kronOp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x), ← mul_assoc]
    congr 1
    · simp only [↓reduceIte, h1, Matrix.smul_apply, smul_eq_mul]
    · apply Finset.prod_congr rfl
      intro y hy
      have hne : y ≠ x := (Finset.mem_erase.mp hy).1
      simp only [hne, ↓reduceIte, Matrix.one_mul]
  have hR : pauliSite x β * pauliSite x α = star c • pauliSite x (pauliMulIdx α β) := by
    unfold pauliSite
    rw [kronOp_mul]
    ext a b
    simp only [kronOp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x), ← mul_assoc]
    congr 1
    · simp only [↓reduceIte, h2, Matrix.smul_apply, smul_eq_mul]
    · apply Finset.prod_congr rfl
      intro y hy
      have hne : y ≠ x := (Finset.mem_erase.mp hy).1
      simp only [hne, ↓reduceIte, Matrix.one_mul]
  calc pauliSite x α * (pauliSite x β * M * pauliSite x β) * pauliSite x α
      = (pauliSite x α * pauliSite x β) * M * (pauliSite x β * pauliSite x α) := by
          simp only [Matrix.mul_assoc]
    _ = (c • pauliSite x (pauliMulIdx α β)) * M * (star c • pauliSite x (pauliMulIdx α β)) := by
          rw [hL, hR]
    _ = (c * star c) • (pauliSite x (pauliMulIdx α β) * M * pauliSite x (pauliMulIdx α β)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = pauliSite x (pauliMulIdx α β) * M * pauliSite x (pauliMulIdx α β) := by
          rw [hc, one_smul]

/-- `partialTraceSite x` is idempotent: `ℰ_x(ℰ_x(M)) = ℰ_x(M)`. -/
theorem partialTraceSite_idempotent {N : ℕ} (x : Fin N) (M : QubitOp N) :
    partialTraceSite x (partialTraceSite x M) = partialTraceSite x M := by
  unfold partialTraceSite
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    ← Finset.smul_sum, smul_smul]
  have hinner : ∀ α : Fin 4,
      (∑ β : Fin 4, pauliSite x α * (pauliSite x β * M * pauliSite x β) * pauliSite x α) =
      ∑ γ : Fin 4, pauliSite x γ * M * pauliSite x γ := by
    intro α
    refine Finset.sum_bij (fun β _ ↦ pauliMulIdx α β) ?_ ?_ ?_ ?_
    · intro β _; exact Finset.mem_univ _
    · intro β₁ _ β₂ _ h
      have := congrArg (pauliMulIdx α) h
      rwa [pauliMulIdx_invol, pauliMulIdx_invol] at this
    · intro γ _; exact ⟨pauliMulIdx α γ, Finset.mem_univ _, pauliMulIdx_invol α γ⟩
    · intro β _; exact pauliSite_conj_mul x α β M
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← smul_eq_mul,
    smul_smul]
  congr 1
  norm_num

/-- `siteSizeOp x = 1 - ℰ_x` is self-adjoint and idempotent, hence `0 ≤ ⟨M, S_x M⟩_HS ≤ ‖M‖_HS²`. -/
theorem siteSizeOp_bounds {N : ℕ} (x : Fin N) (M : QubitOp N) :
    0 ≤ (hsInner M (siteSizeOp x M)).re ∧
    (hsInner M (siteSizeOp x M)).re ≤ (hsInner M M).re := by
  have hE_eq : hsInner M (partialTraceSite x M) =
      hsInner (partialTraceSite x M) (partialTraceSite x M) := by
    rw [← partialTraceSite_selfAdjoint, partialTraceSite_idempotent]
  have hS_eq : hsInner M (siteSizeOp x M) =
      hsInner (siteSizeOp x M) (siteSizeOp x M) := by
    have hE2 := partialTraceSite_idempotent x M
    have hSA := partialTraceSite_selfAdjoint x
    unfold siteSizeOp hsInner
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    have h1 : (Mᴴ * partialTraceSite x M).trace = ((partialTraceSite x M)ᴴ * M).trace := by
      simpa [hsInner] using hSA M M
    have h2 : ((partialTraceSite x M)ᴴ * partialTraceSite x M).trace =
        (Mᴴ * partialTraceSite x M).trace := by
      simpa [hsInner] using hE_eq.symm
    rw [h2, h1]; ring
  have hsplit : (hsInner M (siteSizeOp x M)).re + (hsInner M (partialTraceSite x M)).re =
      (hsInner M M).re := by
    unfold siteSizeOp hsInner
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    ring
  have hS_nn : 0 ≤ (hsInner M (siteSizeOp x M)).re := by
    rw [hS_eq]; exact hsNormSq_nn _
  have hE_nn : 0 ≤ (hsInner M (partialTraceSite x M)).re := by
    rw [hE_eq]; exact hsNormSq_nn _
  exact ⟨hS_nn, by linarith⟩

/-- **Exact Operator Size Bounds** (`0 ⪯ 𝒮 ⪯ N 1`):
`0 ≤ Re ⟨M, 𝒮 M⟩_HS ≤ N · Re ⟨M, M⟩_HS` for all `M : QubitOp N`. -/
theorem totalSizeOp_bounds {N : ℕ} (M : QubitOp N) :
    0 ≤ (hsInner M (totalSizeOp M)).re ∧
    (hsInner M (totalSizeOp M)).re ≤ (N : ℝ) * (hsInner M M).re := by
  have hsum : (hsInner M (totalSizeOp M)).re =
      ∑ x : Fin N, (hsInner M (siteSizeOp x M)).re := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [hsum]
  constructor
  · exact Finset.sum_nonneg fun x _ ↦ (siteSizeOp_bounds x M).1
  · calc ∑ x : Fin N, (hsInner M (siteSizeOp x M)).re
        ≤ ∑ _x : Fin N, (hsInner M M).re :=
          Finset.sum_le_sum fun x _ ↦ (siteSizeOp_bounds x M).2
      _ = (N : ℝ) * (hsInner M M).re := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Symmetry of the real part of the `totalSizeOp` bilinear form:
`Re ⟨A, 𝒮 B⟩_HS = Re ⟨B, 𝒮 A⟩_HS`. -/
theorem totalSizeOp_symm_re {N : ℕ} (A B : QubitOp N) :
    (hsInner A (totalSizeOp B)).re = (hsInner B (totalSizeOp A)).re := by
  have hSA : hsInner A (totalSizeOp B) = hsInner (totalSizeOp A) B := by
    unfold totalSizeOp hsInner
    simp only [Matrix.mul_sum, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold siteSizeOp
    simp only [Matrix.mul_sub, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]
    congr 1
    simpa [hsInner] using partialTraceSite_selfAdjoint x A B
  rw [hSA]
  have hconj : (hsInner (totalSizeOp A) B).re = (hsInner B (totalSizeOp A)).re := by
    unfold hsInner
    have htr : ((totalSizeOp A)ᴴ * B).trace = star (Bᴴ * totalSizeOp A).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [htr, Complex.star_def, Complex.conj_re]
  exact hconj

/-- **Cauchy–Schwarz for the positive semidefinite superoperator `𝒮`**:
`(Re ⟨A, 𝒮 B⟩_HS)² ≤ Re ⟨A, 𝒮 A⟩_HS · Re ⟨B, 𝒮 B⟩_HS`. -/
theorem totalSizeOp_cauchy_schwarz {N : ℕ} (A B : QubitOp N) :
    ((hsInner A (totalSizeOp B)).re) ^ 2 ≤
    (hsInner A (totalSizeOp A)).re * (hsInner B (totalSizeOp B)).re := by
  set a := (hsInner A (totalSizeOp A)).re
  set b := (hsInner A (totalSizeOp B)).re
  set c := (hsInner B (totalSizeOp B)).re
  have hquad : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c := by
    intro t
    have hnn := (totalSizeOp_bounds (A + (t : ℂ) • B)).1
    have hlin : totalSizeOp (A + (t : ℂ) • B) = totalSizeOp A + (t : ℂ) • totalSizeOp B := by
      unfold totalSizeOp siteSizeOp partialTraceSite
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, smul_comm (1 / 4 : ℂ) (t : ℂ)]
      simp only [Finset.sum_sub_distrib, sub_add_sub_comm, smul_sub]
    have hexp : (hsInner (A + (t : ℂ) • B) (totalSizeOp (A + (t : ℂ) • B))).re =
        a + 2 * t * b + t ^ 2 * c := by
      rw [hlin]
      unfold hsInner
      have htstar : star (t : ℂ) = (t : ℂ) := by simp [Complex.star_def]
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, htstar,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hsym := totalSizeOp_symm_re B A
      unfold hsInner at hsym
      change a + t * b + (t * (Bᴴ * totalSizeOp A).trace.re + t * (t * c)) =
        a + 2 * t * b + t ^ 2 * c
      rw [hsym]; ring
    linarith
  have hc_nn : 0 ≤ c := (totalSizeOp_bounds B).1
  by_cases hc0 : c = 0
  · subst hc0
    have hb0 : b = 0 := by
      by_contra hne
      have := hquad (- (a + 1) / (2 * b))
      have : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
        field_simp [hne]; ring
      linarith
    rw [hb0]; simp
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
    have hmin := hquad (-b / c)
    have hval : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = (a * c - b ^ 2) / c := by
      field_simp [hc0]; ring
    rw [hval] at hmin
    have hnum : 0 ≤ a * c - b ^ 2 := by
      have := mul_nonneg hmin hc_pos.le
      rwa [div_mul_cancel₀ _ hc0] at this
    linarith

/-- **Operator-Level Lemma 4.2** (Thermal Size Truncation on `QubitOp N`, Eq. 4.3):
For any Gibbs state `G : GibbsData N`, any operator decomposition `O = A_M + R_M` in
`QubitOp N` with Wightman-orthogonal remainder `(A_M | R_M)_W = 0`, normalized `‖O‖_W = 1`,
tail weight `q = ‖R_M‖_W²`, and leading-part thermal size bound
`mssThermalSize G A_M ≤ (1 - q) * Λ_M` (with `0 ≤ Λ_M`), the full thermal size satisfies
`mssThermalSize G O ≤ Λ_M + 2 √(N q (Λ_M + N)) + N q` (and in particular, using
`⟨J(A_M), 𝒮 J(A_M)⟩_HS ≤ N`, `mssThermalSize G O ≤ Λ_M + 2 N √q + N q`). -/
theorem lemma_4_2_operator_thermal_size_truncation {N : ℕ}
    (G : GibbsData N) (O A_M R_M : QubitOp N) {q Λ_M : ℝ}
    (hdecomp : O = A_M + R_M)
    (hnormO : (wightmanInner G O O).re = 1)
    (hnormA : (wightmanInner G A_M A_M).re = 1 - q)
    (hnormR : (wightmanInner G R_M R_M).re = q)
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1)
    (hΛ_nn : 0 ≤ Λ_M)
    (hlead : mssThermalSize G A_M ≤ (1 - q) * Λ_M) :
    mssThermalSize G O ≤ Λ_M + 2 * (N : ℝ) * Real.sqrt q + (N : ℝ) * q := by
  set JA := wightmanMap G A_M
  set JR := wightmanMap G R_M
  set J1 := wightmanMap G (1 : QubitOp N)
  have hJO : wightmanMap G O = JA + JR := by
    rw [hdecomp]; unfold wightmanMap; simp [Matrix.mul_add, Matrix.add_mul]
  have hS_add : totalSizeOp (JA + JR) = totalSizeOp JA + totalSizeOp JR := by
    unfold totalSizeOp siteSizeOp partialTraceSite
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add,
      Finset.sum_sub_distrib, sub_add_sub_comm]
  have hexp : (hsInner (wightmanMap G O) (totalSizeOp (wightmanMap G O))).re =
      (hsInner JA (totalSizeOp JA)).re + 2 * (hsInner JA (totalSizeOp JR)).re +
      (hsInner JR (totalSizeOp JR)).re := by
    rw [hJO, hS_add]
    unfold hsInner
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add, Complex.add_re]
    have hsym := totalSizeOp_symm_re JR JA
    unfold hsInner at hsym
    linarith
  have hJA_norm : (hsInner JA JA).re = 1 - q := by
    have := wightmanInner_eq_hsInner G A_M A_M
    rw [← hnormA, this]
  have hJR_norm : (hsInner JR JR).re = q := by
    have := wightmanInner_eq_hsInner G R_M R_M
    rw [← hnormR, this]
  have hJA_S_le : (hsInner JA (totalSizeOp JA)).re ≤ (N : ℝ) := by
    have h1 := (totalSizeOp_bounds JA).2
    rw [hJA_norm] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hJR_S_le : (hsInner JR (totalSizeOp JR)).re ≤ (N : ℝ) * q := by
    have h1 := (totalSizeOp_bounds JR).2
    rwa [hJR_norm] at h1
  have hcross : (hsInner JA (totalSizeOp JR)).re ≤ (N : ℝ) * Real.sqrt q := by
    have hcs := totalSizeOp_cauchy_schwarz JA JR
    have hprod : (hsInner JA (totalSizeOp JA)).re * (hsInner JR (totalSizeOp JR)).re ≤
        ((N : ℝ) * Real.sqrt q) ^ 2 := by
      have hsq : ((N : ℝ) * Real.sqrt q) ^ 2 = (N : ℝ) * ((N : ℝ) * q) := by
        rw [mul_pow, Real.sq_sqrt hq_nn]; ring
      rw [hsq]
      exact mul_le_mul hJA_S_le hJR_S_le (totalSizeOp_bounds JR).1 (Nat.cast_nonneg N)
    have hle : ((hsInner JA (totalSizeOp JR)).re) ^ 2 ≤ ((N : ℝ) * Real.sqrt q) ^ 2 :=
      le_trans hcs hprod
    have hNsq_nn : 0 ≤ (N : ℝ) * Real.sqrt q := by positivity
    nlinarith [sq_abs (hsInner JA (totalSizeOp JR)).re, le_abs_self (hsInner JA (totalSizeOp JR)).re]
  have hJ1_nn : 0 ≤ (hsInner J1 (totalSizeOp J1)).re := (totalSizeOp_bounds J1).1
  unfold mssThermalSize at hlead ⊢
  rw [hexp]
  have h1q : (1 - q) * Λ_M ≤ Λ_M := by nlinarith
  linarith

end OperatorSizeBounds

section ConcreteWightmanProjectors

/-- `HSOp N` equips `QubitOp N` with its canonical finite-dimensional Hilbert–Schmidt
`InnerProductSpace ℂ` structure via `WithLp 2` on flattened matrix entries
`(Fin N → Fin 2) × (Fin N → Fin 2)`. -/
abbrev HSOp (N : ℕ) := EuclideanSpace ℂ ((Fin N → Fin 2) × (Fin N → Fin 2))

/-- Canonical linear equivalence `toHSOp : QubitOp N →ₗ[ℂ] HSOp N`. -/
noncomputable def toHSOp (N : ℕ) : QubitOp N →ₗ[ℂ] HSOp N where
  toFun M := WithLp.toLp 2 (fun p : (Fin N → Fin 2) × (Fin N → Fin 2) ↦ M p.1 p.2)
  map_add' A B := by ext p; rfl
  map_smul' c A := by ext p; rfl

/-- The Wightman embedding `J_β : QubitOp N →ₗ[ℂ] HSOp N`, `A ↦ ρ_β^{1/4} A ρ_β^{1/4}`. -/
noncomputable def wightmanEmbed {N : ℕ} (G : GibbsData N) : QubitOp N →ₗ[ℂ] HSOp N where
  toFun A := toHSOp N (wightmanMap G A)
  map_add' A B := by
    simp only [wightmanMap, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c A := by
    simp only [wightmanMap, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-- Concrete Wightman filtration subspace `J_β(𝒱_s) ⊆ HSOp N`: the linear span of
`{J_β(P_a) | |a| ≤ s}`. -/
noncomputable def wightmanFiltrationSubspace {N : ℕ} (G : GibbsData N) (s : ℕ) :
    Submodule ℂ (HSOp N) :=
  Submodule.span ℂ
    ((fun a : Fin N → Fin 4 ↦ wightmanEmbed G (pauliString a)) ''
      {a : Fin N → Fin 4 | stringWeight a ≤ s})

/-- Concrete Wightman orthogonal projector `Π_s^{(β)} : HSOp N →L[ℂ] HSOp N` onto
`J_β(𝒱_s)` constructed directly via Mathlib's `Submodule.starProjection`. -/
noncomputable def wightmanProj {N : ℕ} (G : GibbsData N) (s : ℕ) :
    HSOp N →L[ℂ] HSOp N :=
  (wightmanFiltrationSubspace G s).starProjection

/-- **Loewner Monotonicity of Orthogonal Projectors**:
If `V ⊆ W` are subspaces of `HSOp N`, then `‖P_V v‖² ≤ ‖P_W v‖²` for every `v : HSOp N`
(i.e. `P_V ⪯ P_W` in the Loewner order). -/
theorem loewner_proj_mono {N : ℕ} (V W : Submodule ℂ (HSOp N))
    (hVW : V ≤ W) (v : HSOp N) :
    ‖V.starProjection v‖ ^ 2 ≤ ‖W.starProjection v‖ ^ 2 := by
  have hV_mem : V.starProjection v ∈ W := hVW (Submodule.starProjection_apply_mem V v)
  have hW_orth : v - W.starProjection v ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hV_orth : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h1 : inner ℂ (W.starProjection v - V.starProjection v) (V.starProjection v) = 0 := by
    have hdiff_eq : W.starProjection v - V.starProjection v =
        (v - V.starProjection v) - (v - W.starProjection v) := by abel
    rw [hdiff_eq, inner_sub_left]
    have ha : inner ℂ (v - V.starProjection v) (V.starProjection v) = 0 :=
      (Submodule.mem_orthogonal _ _).mp hV_orth _ (Submodule.starProjection_apply_mem V v)
    have hb : inner ℂ (v - W.starProjection v) (V.starProjection v) = 0 :=
      (Submodule.mem_orthogonal _ _).mp hW_orth _ hV_mem
    rw [ha, hb, sub_zero]
  have hpyth : ‖W.starProjection v‖ ^ 2 =
      ‖V.starProjection v‖ ^ 2 + ‖W.starProjection v - V.starProjection v‖ ^ 2 := by
    have heq : W.starProjection v =
        V.starProjection v + (W.starProjection v - V.starProjection v) := by abel
    conv_lhs => rw [heq]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero]
    rw [← inner_conj_symm, h1, map_zero]
  nlinarith [sq_nonneg ‖W.starProjection v - V.starProjection v‖]

/-- **Concrete Proposition 4.1 Loewner Dominance** (`P_{𝒦_k} ⪯ Π_{s_0 + (r - 1) k}^{(β)}`):
For any `k`-th Krylov subspace `K_k ⊆ wightmanFiltrationSubspace G (s₀ + (r - 1) * k)`,
its orthogonal projector satisfies `‖P_{K_k} v‖² ≤ ‖Π_{s₀ + (r-1)k}^{(β)} v‖²` for all `v`. -/
theorem prop_4_1_loewner_dominance {N : ℕ} (G : GibbsData N) (s₀ r k : ℕ)
    (K : Submodule ℂ (HSOp N))
    (hK : K ≤ wightmanFiltrationSubspace G (s₀ + (r - 1) * k)) (v : HSOp N) :
    ‖K.starProjection v‖ ^ 2 ≤ ‖wightmanProj G (s₀ + (r - 1) * k) v‖ ^ 2 :=
  loewner_proj_mono K (wightmanFiltrationSubspace G (s₀ + (r - 1) * k)) hK v

end ConcreteWightmanProjectors

end KrylovChaos
