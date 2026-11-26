/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.ProductState
import KrylovChaos.ProductStateDerivation
import KrylovChaos.InfiniteChainLimit
import Mathlib.Tactic

/-!
# Multi-Site Product-State Wiring (Flaw #11) & Unconditional Eq. (1.13) Constant (Flaw #12)

1. **Multi-Site Product State (`prodGibbsData`, `prodGSBasis`)**: Connects the concrete
   `N`-qubit product state `ρ = ⨂_{x=1}^N (I + m_x Z_x) / 2` and tensor-product Gram–Schmidt
   basis `E_a = ⨂_x E_x^{(a_x)}` from `ProductStateDerivation` directly to `mssThermalSize`
   and `prop_4_3_product_state_static_bound` in `ProductState`.
2. **Unconditional Theorem 1.1(a) Exact Eq. (1.13) Constant (`theorem_1_1a_infinite_exact_constant`)**:
   Feeds the proved MGF bound from `theorem_1_1a_infinite_unconditional` directly into
   `theorem_1_1a_infinite_tail_and_complexity` to obtain the exact manuscript constant
   `exp((1/2 + γ/α) θ₀) / (4 e tanh(θ₀/4)) * exp(2 α t)` unconditionally.
-/

namespace KrylovChaos

open Matrix

section MultiSiteProductState

/-- Single-site `ρ_x^{-1/4}` for `ρ_x = (I + m Z)/2` with `|m| < 1`. -/
noncomputable def singleSiteRhoQuarterInv (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((Real.sqrt (Real.sqrt ((1 + m) / 2)))⁻¹ : ℝ) : ℂ), 0;
     0, (((Real.sqrt (Real.sqrt ((1 - m) / 2)))⁻¹ : ℝ) : ℂ)]

private lemma singleSiteRho_herm (m : ℝ) :
    (singleSiteRho m)ᴴ = singleSiteRho m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [singleSiteRho, Complex.star_def]

private lemma singleSiteRhoHalf_herm (m : ℝ) :
    (singleSiteRhoHalf m)ᴴ = singleSiteRhoHalf m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [singleSiteRhoHalf, Complex.star_def]

private lemma singleSiteRhoQuarter_herm (m : ℝ) :
    (singleSiteRhoQuarter m)ᴴ = singleSiteRhoQuarter m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [singleSiteRhoQuarter, Complex.star_def]

private lemma singleSiteRhoQuarterInv_herm (m : ℝ) :
    (singleSiteRhoQuarterInv m)ᴴ = singleSiteRhoQuarterInv m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [singleSiteRhoQuarterInv, Complex.star_def]

private lemma singleSiteRho_inv_left {m : ℝ} (hm : |m| < 1) :
    singleSiteRhoQuarterInv m * singleSiteRhoQuarter m = 1 := by
  have hlt := abs_lt.mp hm
  have hp : 0 < Real.sqrt (Real.sqrt ((1 + m) / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hr : 0 < Real.sqrt (Real.sqrt ((1 - m) / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleSiteRhoQuarterInv, singleSiteRhoQuarter, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one]
  · rw [← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]

private lemma singleSiteRho_inv_right {m : ℝ} (hm : |m| < 1) :
    singleSiteRhoQuarter m * singleSiteRhoQuarterInv m = 1 := by
  have hlt := abs_lt.mp hm
  have hp : 0 < Real.sqrt (Real.sqrt ((1 + m) / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hr : 0 < Real.sqrt (Real.sqrt ((1 - m) / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleSiteRhoQuarterInv, singleSiteRhoQuarter, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne', Complex.ofReal_one]
  · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one]

private lemma singleSiteRho_trace (m : ℝ) : (singleSiteRho m).trace = 1 := by
  simp only [singleSiteRho, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast; ring

/-- Concrete `N`-qubit product state `GibbsData N` for `ρ = ⨂_x (I + m_x Z_x)/2`. -/
noncomputable def prodGibbsData {N : ℕ} (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) :
    GibbsData N where
  ρβ := kronOp (fun x ↦ singleSiteRho (m x))
  ρHalf := kronOp (fun x ↦ singleSiteRhoHalf (m x))
  ρQuarter := kronOp (fun x ↦ singleSiteRhoQuarter (m x))
  ρQuarterInv := kronOp (fun x ↦ singleSiteRhoQuarterInv (m x))
  ρβ_herm := by
    rw [kronOp_conjTranspose]; congr 1; funext x; exact singleSiteRho_herm (m x)
  ρHalf_herm := by
    rw [kronOp_conjTranspose]; congr 1; funext x; exact singleSiteRhoHalf_herm (m x)
  ρQuarter_herm := by
    rw [kronOp_conjTranspose]; congr 1; funext x; exact singleSiteRhoQuarter_herm (m x)
  ρQuarterInv_herm := by
    rw [kronOp_conjTranspose]; congr 1; funext x; exact singleSiteRhoQuarterInv_herm (m x)
  sq_quarter := by
    rw [kronOp_mul]; congr 1; funext x; exact (singleSiteRho_roots (hm x)).2
  sq_half := by
    rw [kronOp_mul]; congr 1; funext x; exact (singleSiteRho_roots (hm x)).1
  inv_left := by
    rw [kronOp_mul]
    have : (fun x ↦ singleSiteRhoQuarterInv (m x) * singleSiteRhoQuarter (m x)) = fun _ ↦ 1 := by
      funext x; exact singleSiteRho_inv_left (hm x)
    rw [this, kronOp_one]
  inv_right := by
    rw [kronOp_mul]
    have : (fun x ↦ singleSiteRhoQuarter (m x) * singleSiteRhoQuarterInv (m x)) = fun _ ↦ 1 := by
      funext x; exact singleSiteRho_inv_right (hm x)
    rw [this, kronOp_one]
  trace_one := by
    rw [kronOp_trace]
    exact Finset.prod_eq_one fun x _ ↦ singleSiteRho_trace (m x)

/-- Tensor-product Gram–Schmidt basis `E_a = ⨂_{x=1}^N E_x^{(a_x)}` on `QubitOp N`. -/
noncomputable def prodGSBasis {N : ℕ} (m : Fin N → ℝ) (a : Fin N → Fin 4) : QubitOp N :=
  kronOp (fun x ↦ gsBasis (m x) (a x))

/-- **Multi-Site Wightman Orthonormality**:
`(E_a | E_b)_β^W = δ_{ab}` for the tensor-product Gram–Schmidt basis `prodGSBasis m`. -/
theorem prodGSBasis_wightman_orthonormal {N : ℕ} (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1)
    (a b : Fin N → Fin 4) :
    gibbsWightmanInner (prodGibbsData m hm) (prodGSBasis m a) (prodGSBasis m b) =
      if a = b then 1 else 0 := by
  unfold gibbsWightmanInner prodGibbsData prodGSBasis
  dsimp only
  rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul, kronOp_mul, kronOp_trace]
  have hfac : ∀ x : Fin N,
      (singleSiteRhoHalf (m x) * (gsBasis (m x) (a x))ᴴ *
        singleSiteRhoHalf (m x) * gsBasis (m x) (b x)).trace =
      if a x = b x then 1 else 0 :=
    fun x ↦ gsBasis_wightman_orthonormal (hm x) (a x) (b x)
  simp_rw [hfac]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab]
    have hex : ∃ x : Fin N, a x ≠ b x := by
      by_contra hall; push_neg at hall; exact hab (funext hall)
    rcases hex with ⟨x₀, hx₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ x₀) (if_neg hx₀)

/-- Wightman norm squared of `A = ∑_a c_a E_a` equals `∑_a ‖c_a‖²`. -/
theorem prodGSBasis_wightman_normSq {N : ℕ} (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1)
    (c : (Fin N → Fin 4) → ℂ) :
    gibbsWightmanNormSq (prodGibbsData m hm) (∑ a : Fin N → Fin 4, c a • prodGSBasis m a) =
      ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := by
  unfold gibbsWightmanNormSq gibbsWightmanInner
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have hinner : ∀ a b : Fin N → Fin 4,
      ((prodGibbsData m hm).ρHalf * (prodGSBasis m a)ᴴ *
        (prodGibbsData m hm).ρHalf * prodGSBasis m b).trace =
      if a = b then 1 else 0 :=
    fun a b ↦ prodGSBasis_wightman_orthonormal m hm a b
  have hsum : (∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
      star (c a) * (c b * ((prodGibbsData m hm).ρHalf * (prodGSBasis m a)ᴴ *
        (prodGibbsData m hm).ρHalf * prodGSBasis m b).trace)) =
      ∑ a : Fin N → Fin 4, star (c a) * c a := by
    apply Finset.sum_congr rfl; intro a _
    simp_rw [hinner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hsum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

private lemma singleSite_kron_siteSizeOp {N : ℕ} (F : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin N) :
    siteSizeOp x (kronOp F) =
      kronOp (fun y ↦ if y = x then singleSiteSizeOp (F x) else F y) := by
  unfold siteSizeOp singleSiteSizeOp partialTraceSite
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply,
    kronOp, Matrix.of_apply, smul_eq_mul]
  -- Simplify the partial trace sum at site x
  have hpt : (1 / 2 : ℂ) * ∑ u : Fin 2, ∑ v : Fin 2,
      pauliSite x 0 i u * 0 = 0 := by simp
  -- Directly verify via Kronecker product multiplication
  have hpartial : partialTraceSite x (kronOp F) =
      kronOp (fun y ↦ if y = x then ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) := by
    unfold partialTraceSite
    ext p q
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul, kronOp]
    have hsplit : ∀ b : Fin 2,
        (∏ y : Fin N, F y (Function.update p x b y) (Function.update q x b y)) =
        F x b b * ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
      intro b
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro y hy
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        simp [Function.update_of_ne hyx]
    simp_rw [hsplit, ← Finset.sum_mul]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    have hrest : (∏ y ∈ Finset.univ.erase x,
        (if y = x then ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
      apply Finset.prod_congr rfl; intro y hy
      simp [(Finset.mem_erase.mp hy).1]
    rw [hrest]
    by_cases hpq : p x = q x
    · simp only [hpq, ↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Matrix.trace, Matrix.diag]
      ring
    · simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_ne hpq, smul_eq_mul, mul_zero,
        zero_mul]
      simp [hpq]
  have hsub : kronOp F - partialTraceSite x (kronOp F) =
      kronOp (fun y ↦ if y = x then F x - ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) := by
    rw [hpartial]
    ext p q
    simp only [Matrix.sub_apply, kronOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ F y (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦
      (if y = x then ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦
      (if y = x then F x - ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) (p y) (q y)) (Finset.mem_univ x)]
    have h1 : (∏ y ∈ Finset.univ.erase x,
        (if y = x then ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
      apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
    have h2 : (∏ y ∈ Finset.univ.erase x,
        (if y = x then F x - ((1 / 2 : ℂ) * (F x).trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) else F y) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
      apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
    rw [h1, h2]
    simp only [↓reduceIte, Matrix.sub_apply]
    ring
  have hfull := congrFun (congrFun hsub i) j
  simpa [siteSizeOp, singleSiteSizeOp, kronOp] using hfull

/-- Exact matrix element of `S_x` in the tensor-product Gram–Schmidt basis `prodGSBasis m`. -/
theorem prodGSBasis_siteSize_matrix_elem {N : ℕ} (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1)
    (x : Fin N) (a b : Fin N → Fin 4) :
    hsInner (jBeta (prodGibbsData m hm).ρQuarter (prodGSBasis m a))
      (siteSizeOp x (jBeta (prodGibbsData m hm).ρQuarter (prodGSBasis m b))) -
    (if a = b then
      hsInner (prodGibbsData m hm).ρHalf (siteSizeOp x (prodGibbsData m hm).ρHalf)
     else 0) =
    if ∀ y : Fin N, y ≠ x → a y = b y then
      (singleSiteM (m x) (a x) (b x) : ℂ)
    else 0 := by
  have hJ : ∀ c : Fin N → Fin 4,
      jBeta (prodGibbsData m hm).ρQuarter (prodGSBasis m c) =
      kronOp (fun y ↦ singleSiteJ (m y) (gsBasis (m y) (c y))) := by
    intro c
    unfold jBeta prodGibbsData prodGSBasis singleSiteJ
    dsimp only
    rw [kronOp_mul, kronOp_mul]
  have hsite_term : hsInner (jBeta (prodGibbsData m hm).ρQuarter (prodGSBasis m a))
      (siteSizeOp x (jBeta (prodGibbsData m hm).ρQuarter (prodGSBasis m b))) =
      singleSiteSizeForm (m x) (gsBasis (m x) (a x)) (gsBasis (m x) (b x)) *
        ∏ y ∈ Finset.univ.erase x, (if a y = b y then (1 : ℂ) else 0) := by
    rw [hJ a, hJ b, singleSite_kron_siteSizeOp]
    unfold hsInner
    rw [kronOp_conjTranspose, kronOp_mul, kronOp_trace]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    congr 1
    · simp [singleSiteSizeForm]
    · apply Finset.prod_congr rfl; intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      simp only [hyx, ↓reduceIte]
      have h1 : ((singleSiteJ (m y) (gsBasis (m y) (a y)))ᴴ *
          singleSiteJ (m y) (gsBasis (m y) (b y))).trace =
          singleSiteWightmanInner (m y) (gsBasis (m y) (a y)) (gsBasis (m y) (b y)) := by
        unfold singleSiteJ singleSiteWightmanInner
        have hsq := (singleSiteRho_roots (hm y)).2
        have hh := singleSiteRhoQuarter_herm (m y)
        exact (prop_2_2_wightman_isometry_inner (singleSiteRhoQuarter (m y))
          (singleSiteRhoHalf (m y)) (gsBasis (m y) (a y)) (gsBasis (m y) (b y)) hh hsq).symm
      rw [h1, gsBasis_wightman_orthonormal (hm y)]
  have hbg_term : hsInner (prodGibbsData m hm).ρHalf (siteSizeOp x (prodGibbsData m hm).ρHalf) =
      singleSiteSizeForm (m x) (gsBasis (m x) 0) (gsBasis (m x) 0) := by
    unfold prodGibbsData hsInner
    dsimp only
    rw [singleSite_kron_siteSizeOp, kronOp_conjTranspose, kronOp_mul, kronOp_trace]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    have hrest : (∏ y ∈ Finset.univ.erase x,
        ((singleSiteRhoHalf (m y))ᴴ *
          (if y = x then singleSiteSizeOp (singleSiteRhoHalf (m x)) else singleSiteRhoHalf (m y))).trace) = 1 := by
      apply Finset.prod_eq_one; intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      simp only [hyx, ↓reduceIte, singleSiteRhoHalf_herm, (singleSiteRho_roots (hm y)).1,
        singleSiteRho_trace]
    rw [hrest, mul_one]
    simp only [↓reduceIte]
    have hgs0 : singleSiteJ (m x) (gsBasis (m x) 0) = singleSiteRhoHalf (m x) := by
      unfold singleSiteJ gsBasis
      simp only [Matrix.mul_one]
      exact (singleSiteRho_roots (hm x)).2
    unfold singleSiteSizeForm
    rw [hgs0]
  rw [hsite_term, hbg_term]
  by_cases hrest_eq : ∀ y : Fin N, y ≠ x → a y = b y
  · rw [if_pos hrest_eq]
    have hprod1 : (∏ y ∈ Finset.univ.erase x, (if a y = b y then (1 : ℂ) else 0)) = 1 := by
      apply Finset.prod_eq_one; intro y hy
      rw [if_pos (hrest_eq y (Finset.mem_erase.mp hy).1)]
    rw [hprod1, mul_one]
    have heq_iff : (a = b) ↔ (a x = b x) := by
      constructor
      · intro h; rw [h]
      · intro hx; funext y
        by_cases hyx : y = x
        · subst hyx; exact hx
        · exact hrest_eq y hyx
    have hite : (if a = b then singleSiteSizeForm (m x) (gsBasis (m x) 0) (gsBasis (m x) 0) else 0) =
        if a x = b x then singleSiteSizeForm (m x) (gsBasis (m x) 0) (gsBasis (m x) 0) else 0 := by
      by_cases hx : a x = b x
      · rw [if_pos (heq_iff.mpr hx), if_pos hx]
      · rw [if_neg (fun h ↦ hx (heq_iff.mp h)), if_neg hx]
    rw [hite]
    exact gsBasis_derives_singleSiteM (hm x) (a x) (b x)
  · rw [if_neg hrest_eq]
    have hne : a ≠ b := fun h ↦ hrest_eq fun y _ ↦ congrFun h y
    rw [if_neg hne, sub_zero]
    push_neg at hrest_eq
    rcases hrest_eq with ⟨y₀, hy₀x, hy₀ne⟩
    have hprod0 : (∏ y ∈ Finset.univ.erase x, (if a y = b y then (1 : ℂ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hy₀x, Finset.mem_univ y₀⟩) (if_neg hy₀ne)
    rw [hprod0, mul_zero]

/-- **Proposition 4.3 (Full Concrete Multi-Site Operator Form, Flaw #11)**:
For the concrete `N`-qubit product state `ρ = ⨂_{x=1}^N (I + m_x Z_x)/2` with `|m_x| ≤ mmax < 1`,
every operator `A = ∑_a c_a (⨂_x E_x^{(a_x)})` supported on `stringWeight a ≤ s` and normalized
with `‖A‖_{β,W}² = 1` satisfies:
`mssThermalSize (prodGibbsData m hm) A ≤ s + mmax * √(N * s)`. -/
theorem prop_4_3_concrete_product_state_bound {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1)
    (c : (Fin N → Fin 4) → ℂ)
    (hsupp : ∀ a, s < stringWeight a → c a = 0)
    (hnorm : gibbsWightmanNormSq (prodGibbsData m (fun x ↦ lt_of_le_of_lt (hm_le x) hmmax))
      (∑ a : Fin N → Fin 4, c a • prodGSBasis m a) = 1) :
    mssThermalSize (prodGibbsData m (fun x ↦ lt_of_le_of_lt (hm_le x) hmmax))
      (∑ a : Fin N → Fin 4, c a • prodGSBasis m a) ≤
    (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  have hm : ∀ x, |m x| < 1 := fun x ↦ lt_of_le_of_lt (hm_le x) hmmax
  set G := prodGibbsData m hm
  set A := ∑ a : Fin N → Fin 4, c a • prodGSBasis m a
  have hc_norm : ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 = 1 := by
    rw [← prodGSBasis_wightman_normSq m hm c]; exact hnorm
  have hS_eq : mssThermalSize G A =
      ∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
        if ∀ y : Fin N, y ≠ x → a y = b y then
          (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
        else 0 := by
    unfold mssThermalSize totalSizeOp
    have hJA : jBeta G.ρQuarter A = ∑ a : Fin N → Fin 4, c a • jBeta G.ρQuarter (prodGSBasis m a) := by
      unfold jBeta A
      simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hlin_site : ∀ x : Fin N,
        siteSizeOp x (jBeta G.ρQuarter A) =
        ∑ b : Fin N → Fin 4, c b • siteSizeOp x (jBeta G.ρQuarter (prodGSBasis m b)) := by
      intro x; rw [hJA]
      unfold siteSizeOp partialTraceSite
      ext i j
      simp [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_sub_distrib,
        Finset.mul_sum]
      rw [Finset.sum_comm]; simp [Finset.mul_sum]
    have hsum1 : (hsInner (jBeta G.ρQuarter A) (∑ x : Fin N, siteSizeOp x (jBeta G.ρQuarter A))).re =
        ∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
          (star (c a) * c b * hsInner (jBeta G.ρQuarter (prodGSBasis m a))
            (siteSizeOp x (jBeta G.ρQuarter (prodGSBasis m b)))).re := by
      unfold hsInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [hlin_site x, hJA]
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
        Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
        smul_eq_mul, Complex.re_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      congr 1; ring
    have hsum2 : (hsInner G.ρHalf (∑ x : Fin N, siteSizeOp x G.ρHalf)).re =
        ∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
          (star (c a) * c b * (if a = b then hsInner G.ρHalf (siteSizeOp x G.ρHalf) else 0)).re := by
      unfold hsInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro x _
      have hinner_x : (∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
          (star (c a) * c b * (if a = b then (G.ρHalfᴴ * siteSizeOp x G.ρHalf).trace else 0)).re) =
          (∑ a : Fin N → Fin 4, ‖c a‖ ^ 2) * (G.ρHalfᴴ * siteSizeOp x G.ρHalf).trace.re := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a _
        simp only [mul_ite, mul_zero, apply_ite Complex.re, Complex.zero_re, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte]
        have hcc : star (c a) * c a = ((‖c a‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
        rw [hcc, Complex.re_ofReal_mul]
      rw [hinner_x, hc_norm, one_mul]
    rw [hsum1, hsum2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _
    rw [← Complex.sub_re, ← mul_sub, prodGSBasis_siteSize_matrix_elem m hm x a b]
    by_cases hrest : ∀ y : Fin N, y ≠ x → a y = b y
    · rw [if_pos hrest, if_pos hrest, Complex.mul_ofReal_re]
    · rw [if_neg hrest, if_neg hrest, mul_zero, Complex.zero_re]
  rw [hS_eq]
  exact prop_4_3_product_state_static_bound m hm_le hmmax c hsupp hc_norm

end MultiSiteProductState

section ExactInfiniteConstant

/-- **Theorem 1.1(a) Unconditional Exact Eq. (1.13) Constant (Flaw #12)**:
Combines the unconditionally proved infinite-chain MGF bound from
`theorem_1_1a_infinite_unconditional` with `theorem_1_1a_infinite_tail_and_complexity`
to obtain the exact manuscript tail bound and complexity constant
`exp((1/2 + γ/α) θ₀) / (4 e tanh(θ₀/4)) * exp(2 α t)` with zero extra hypotheses. -/
theorem theorem_1_1a_infinite_exact_constant
    {α γ θ₀ : ℝ} (b : ℕ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb0 : b 0 = 0) (hb_nn : ∀ n, 1 ≤ n → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → b n ≤ α * (n : ℝ) + γ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ n : ℕ, ∑' m : ℕ, (infiniteKrylovWavefn b (n + m) t) ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) *
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
    (∑' n : ℕ, (n : ℝ) * (infiniteKrylovWavefn b n t) ^ 2 ≤
      (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
        Real.exp (2 * α * t)) := by
  have huncond := theorem_1_1a_infinite_unconditional b hα hγ hθ₀ hb0 hb_nn hb_lin t ht
  exact theorem_1_1a_infinite_tail_and_complexity
    (fun m s ↦ infiniteKrylovWavefn b m s) hα hγ hθ₀ t ht huncond.1

end ExactInfiniteConstant

end KrylovChaos
