/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ConcreteSpectralStrip

/-!
# Thermodynamic-Limit OTOC Analyticity (Theorem 1.2(c)) and Concrete-Family Chaos Bound (Theorem 1.3(c))

Establishes end-to-end thermodynamic-limit OTOC strip analyticity and concrete-family KMS rate
discharge on top of `KrylovChaos/ConcreteSpectralStrip.lean`:
1. `differentiable_concreteOTOC`, `concreteWightmanNormAtShift_eq_spectralMeasure`,
   `concreteWightmanNormAtShift_eq_autocorr`.
2. `theorem_1_2c_general_otoc_strip_analyticity` and `theorem_1_2c_thermo_limit_otoc_strip`:
   analytic continuation of `concreteOTOC` to `{|Im z| < β / 4 + κ / 2}` with the thermodynamic-limit
   Eq. (1.17) `liminf` bound.
3. `theorem_1_3c_concrete_family_complete`: full concrete-family Theorem 1.3(c) discharging the KMS
   rate bound `2 α ≤ 2π / (β + 2κ)` directly from the `r`-local family `(H_N, O_N)`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology Complex

section ConcreteOTOCAnalyticityAndTheorem13c

set_option maxHeartbeats 800000 in
/-- Finite-volume `concreteOTOC hH β W V` is entire on `ℂ`. -/
theorem differentiable_concreteOTOC {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) :
    Differentiable ℂ (concreteOTOC hH β W V) := by
  have hprop_diff : ∀ (s : ℂ) (i j : QubitIdx N),
      Differentiable ℂ (fun z : ℂ ↦ (complexPropagator hH (s * z)) i j) := by
    intro s i j
    unfold complexPropagator hermFunc
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    refine Differentiable.fun_sum fun a _ ↦ ?_
    exact ((differentiable_const _).mul
      ((((differentiable_const _).mul ((differentiable_const _).mul differentiable_id)).mul
        (differentiable_const _)).cexp)).mul (differentiable_const _)
  have hmat_mul_diff : ∀ (A B : ℂ → QubitOp N),
      (∀ i j, Differentiable ℂ (fun z ↦ A z i j)) →
      (∀ i j, Differentiable ℂ (fun z ↦ B z i j)) →
      ∀ i j, Differentiable ℂ (fun z ↦ (A z * B z) i j) := by
    intro A B hA hB i j
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun k _ ↦ (hA i k).mul (hB k j)
  have hp1 : ∀ a b, Differentiable ℂ (fun z : ℂ ↦ (complexPropagator hH z) a b) := fun a b ↦ by
    simpa using hprop_diff 1 a b
  have hpm1 : ∀ a b, Differentiable ℂ (fun z : ℂ ↦ (complexPropagator hH (-z)) a b) := fun a b ↦ by
    simpa using hprop_diff (-1) a b
  have hevol_diff : ∀ i j, Differentiable ℂ (fun z ↦ (heisenbergEvol hH z W) i j) :=
    hmat_mul_diff (fun z ↦ complexPropagator hH z * W) (fun z ↦ complexPropagator hH (-z))
      (hmat_mul_diff (fun z ↦ complexPropagator hH z) (fun _ ↦ W) hp1 (fun _ _ ↦ differentiable_const _))
      hpm1
  let Rq : QubitOp N := (concreteGibbsData hH β).ρQuarter
  have hstep_diff : ∀ i j, Differentiable ℂ (fun z ↦
      (jBeta Rq (heisenbergEvol hH z W) * V) i j) :=
    hmat_mul_diff (fun z ↦ Rq * heisenbergEvol hH z W * Rq) (fun _ ↦ V)
      (hmat_mul_diff (fun z ↦ Rq * heisenbergEvol hH z W) (fun _ ↦ Rq)
        (hmat_mul_diff (fun _ ↦ Rq) (fun z ↦ heisenbergEvol hH z W)
          (fun _ _ ↦ differentiable_const _) hevol_diff)
        (fun _ _ ↦ differentiable_const _))
      (fun _ _ ↦ differentiable_const _)
  have hsq_diff := hmat_mul_diff
    (fun z ↦ jBeta Rq (heisenbergEvol hH z W) * V)
    (fun z ↦ jBeta Rq (heisenbergEvol hH z W) * V) hstep_diff hstep_diff
  unfold concreteOTOC Matrix.trace Matrix.diag
  exact Differentiable.fun_sum fun i _ ↦ hsq_diff i i

/-- Exact spectral identity linking `concreteWightmanNormAtShift` to the spectral measure:
`concreteWightmanNormAtShift hH β W τ 0 = ∫ ω, exp(-2 τ ω) ∂(concreteWightmanSpectralMeasure hH β W)`. -/
theorem concreteWightmanNormAtShift_eq_spectralMeasure {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (_hW : W.IsHermitian) (β τ : ℝ) :
    concreteWightmanNormAtShift hH β W τ 0 =
      ∫ ω : ℝ, Real.exp (-2 * τ * ω) ∂(concreteWightmanSpectralMeasure hH β W) := by
  rw [integral_concreteWightmanSpectralMeasure]
  unfold concreteWightmanNormAtShift
  simp only [Complex.ofReal_zero, zero_add]
  rw [prop_9_1_wightman_norm_eq_spectral_sum hH β _]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  unfold wightmanSpectralWeight
  simp only [smul_eq_mul]
  rw [heisenbergEvol_eigen_entry hH (Complex.I * (τ : ℂ)) W a b]
  have he : Complex.I * (Complex.I * (τ : ℂ)) * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) =
      ((-τ * (hH.eigenvalues a - hH.eigenvalues b) : ℝ) : ℂ) := by
    push_cast
    calc Complex.I * (Complex.I * (τ : ℂ)) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ))
        = (Complex.I * Complex.I) * (τ : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by ring
      _ = (-1 : ℂ) * (τ : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by rw [Complex.I_mul_I]
      _ = _ := by ring
  rw [he, ← Complex.ofReal_exp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  have h2 : (2 : ℕ) * (-τ * (hH.eigenvalues a - hH.eigenvalues b)) =
      -2 * τ * (hH.eigenvalues a - hH.eigenvalues b) := by push_cast; ring
  rw [h2]; ring

private lemma trace_conj_quad {N : ℕ} (U R W A : QubitOp N) (hU1 : U * Uᴴ = 1) :
    (R * W * R * A).trace = ((Uᴴ * R * U) * (Uᴴ * W * U) * (Uᴴ * R * U) * (Uᴴ * A * U)).trace := by
  have h1 : (R * W * R * A).trace = (Uᴴ * (R * W * R * A) * U).trace := by
    calc (R * W * R * A).trace = ((U * Uᴴ) * (R * W * R * A)).trace := by rw [hU1, Matrix.one_mul]
      _ = (U * (Uᴴ * (R * W * R * A))).trace := by simp only [Matrix.mul_assoc]
      _ = ((Uᴴ * (R * W * R * A)) * U).trace := Matrix.trace_mul_comm _ _
      _ = (Uᴴ * (R * W * R * A) * U).trace := by simp only [Matrix.mul_assoc]
  rw [h1]; congr 1
  calc Uᴴ * (R * W * R * A) * U
      = Uᴴ * R * (U * Uᴴ) * W * (U * Uᴴ) * R * (U * Uᴴ) * A * U := by
          rw [hU1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (Uᴴ * R * U) * (Uᴴ * W * U) * (Uᴴ * R * U) * (Uᴴ * A * U) := by
          simp only [Matrix.mul_assoc]

set_option maxHeartbeats 800000 in
/-- Exact autocorrelation identity for the imaginary-time shifted Wightman norm:
`concreteWightmanNormAtShift hH β W τ 0 = (gibbsWightmanInner (concreteGibbsData hH β) W (heisenbergEvol hH (2 * Complex.I * (τ : ℂ)) W)).re`. -/
theorem concreteWightmanNormAtShift_eq_autocorr {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (β τ : ℝ) :
    concreteWightmanNormAtShift hH β W τ 0 =
      (gibbsWightmanInner (concreteGibbsData hH β) W
        (heisenbergEvol hH (2 * Complex.I * (τ : ℂ)) W)).re := by
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.prop
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.prop
  let B : QubitOp N := Uᴴ * W * U
  have hB_herm : Bᴴ = B := by
    dsimp only [B]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hW.eq,
      Matrix.mul_assoc]
  set Z : ℝ := gibbsPartitionFn hH β
  have hZpos : 0 < Z := gibbsPartitionFn_pos hH β
  let d : QubitIdx N → ℂ := fun i ↦ ((Real.exp (-(β / 2) * hH.eigenvalues i) : ℝ) : ℂ)
  have hρHalf_eq : Uᴴ * (concreteGibbsData hH β).ρHalf * U =
      (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d := by
    change Uᴴ * gibbsRhoHalf hH β * U = _
    unfold gibbsRhoHalf hermFunc
    rw [← Complex.ofReal_inv]
    change Uᴴ * ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • (U * Matrix.diagonal d * Uᴴ)) * U = _
    calc Uᴴ * ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • (U * Matrix.diagonal d * Uᴴ)) * U
        = (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • ((Uᴴ * U) * Matrix.diagonal d * (Uᴴ * U)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d := by rw [hU2, Matrix.one_mul, Matrix.mul_one]
  have hevol_diag : Uᴴ * heisenbergEvol hH (2 * Complex.I * (τ : ℂ)) W * U =
      Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) * B *
      Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))) := by
    unfold heisenbergEvol complexPropagator hermFunc
    have h1 : ∀ a : QubitIdx N, Complex.exp (Complex.I * (2 * Complex.I * (τ : ℂ)) * (hH.eigenvalues a : ℂ)) =
        Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ)) := fun a ↦ by
      congr 1; ring_nf; rw [Complex.I_sq]; ring
    have h2 : ∀ b : QubitIdx N, Complex.exp (Complex.I * -(2 * Complex.I * (τ : ℂ)) * (hH.eigenvalues b : ℂ)) =
        Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) := fun b ↦ by
      congr 1; ring_nf; rw [Complex.I_sq]; ring
    simp_rw [h1, h2]
    dsimp only [B]
    calc Uᴴ * (U * Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
            W * (U * Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))) * Uᴴ)) * U
        = (Uᴴ * U) * Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) *
            (Uᴴ * W * U) * Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))) *
            (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) *
            (Uᴴ * W * U) * Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))) := by
            rw [hU2, Matrix.one_mul, Matrix.mul_one]
  rw [concreteWightmanNormAtShift_eq_spectralMeasure hH hW β τ, integral_concreteWightmanSpectralMeasure]
  unfold gibbsWightmanInner wightmanInner
  set R := (concreteGibbsData hH β).ρHalf
  set A := heisenbergEvol hH (2 * Complex.I * (τ : ℂ)) W
  have htr : (R * Wᴴ * R * A).trace =
      ((Uᴴ * R * U) * (Uᴴ * Wᴴ * U) * (Uᴴ * R * U) * (Uᴴ * A * U)).trace :=
    trace_conj_quad U R Wᴴ A hU1
  rw [htr, hρHalf_eq, hW.eq, hevol_diag]
  have hsqZ : (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) * (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) = ((Z⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hZpos.le]
  have htr2 : ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d * B *
      ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d) *
      (Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) * B *
       Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))))).trace =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        ((wightmanSpectralWeight hH β W a b * Real.exp (-2 * τ * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqZ, Matrix.trace_smul, smul_eq_mul]
    have htr_diag : (Matrix.diagonal d * B * Matrix.diagonal d *
        (Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) * B *
         Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))))).trace =
        ∑ a : QubitIdx N, ∑ b : QubitIdx N,
          d a * B a b * d b *
            (Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) * B b a *
             Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) := by
      have hL : ∀ a b, (Matrix.diagonal d * B * Matrix.diagonal d) a b = d a * B a b * d b := fun a b ↦ by
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      have hR : ∀ b a, (Matrix.diagonal (fun x ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues x : ℂ))) * B *
          Matrix.diagonal (fun x ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues x : ℂ)))) b a =
          Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) * B b a *
            Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues a : ℂ)) := fun b a ↦ by
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.trace, Matrix.diag]
      apply Finset.sum_congr rfl; intro a _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro b _
      rw [hL a b, hR b a]
    rw [htr_diag]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    unfold wightmanSpectralWeight
    have hBab : B a b * B b a = ((‖B a b‖ ^ 2 : ℝ) : ℂ) := by
      have hba : B b a = star (B a b) := by
        have := congrArg (fun M : QubitOp N ↦ M b a) hB_herm
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [hba, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    have hdd : d a * d b = ((Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) : ℝ) : ℂ) := by
      dsimp only [d]; rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    have hexp_ab : Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) *
        Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues a : ℂ)) =
        ((Real.exp (-2 * τ * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) := by
      rw [← Complex.exp_add, Complex.ofReal_exp]; congr 1; push_cast; ring
    calc ((Z⁻¹ : ℝ) : ℂ) * (d a * B a b * d b *
            (Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) * B b a *
             Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))))
        = ((Z⁻¹ : ℝ) : ℂ) * (d a * d b) * (B a b * B b a) *
            (Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues b : ℂ)) *
             Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) := by ring
      _ = ((Z⁻¹ : ℝ) : ℂ) * ((Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) : ℝ) : ℂ) *
            ((‖B a b‖ ^ 2 : ℝ) : ℂ) *
            ((Real.exp (-2 * τ * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) := by
            rw [hdd, hBab, hexp_ab]
      _ = _ := by
            push_cast
            have hZeq : Z = gibbsPartitionFn hH β := rfl
            rw [hZeq]
  rw [htr2, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  have hwsym : wightmanSpectralWeight hH β W b a = wightmanSpectralWeight hH β W a b := by
    unfold wightmanSpectralWeight
    have hba : B b a = star (B a b) := by
      have := congrArg (fun M : QubitOp N ↦ M b a) hB_herm
      simpa [Matrix.conjTranspose_apply] using this.symm
    have hnorm : ‖B b a‖ = ‖B a b‖ := by rw [hba, norm_star]
    have hnorm' : ‖((hH.eigenvectorUnitary : QubitOp N)ᴴ * W * (hH.eigenvectorUnitary : QubitOp N)) b a‖ =
        ‖((hH.eigenvectorUnitary : QubitOp N)ᴴ * W * (hH.eigenvectorUnitary : QubitOp N)) a b‖ := hnorm
    dsimp only
    rw [hnorm', add_comm]
  rw [hwsym, smul_eq_mul]

/-- Helper: `liminf (c * a_N) ≤ c * liminf a_N` for `c ≥ 0` and bounded nonneg `a_N`. -/
private lemma liminf_const_mul_le_of_bdd {a : ℕ → ℝ} {c B : ℝ}
    (hc : 0 ≤ c) (ha0 : ∀ N, 0 ≤ a N) (haB : ∀ N, a N ≤ B) :
    Filter.liminf (fun N ↦ c * a N) atTop ≤ c * Filter.liminf a atTop := by
  by_cases hc0 : c = 0
  · subst hc0; simp
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hge_a : Filter.IsBoundedUnder (· ≥ ·) atTop a :=
    ⟨0, Filter.eventually_map.mpr (Eventually.of_forall ha0)⟩
  have hle_a : Filter.IsBoundedUnder (· ≤ ·) atTop a :=
    ⟨B, Filter.eventually_map.mpr (Eventually.of_forall haB)⟩
  have hge_ca : Filter.IsBoundedUnder (· ≥ ·) atTop (fun N ↦ c * a N) :=
    ⟨0, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦ mul_nonneg hc (ha0 N))⟩
  refine Filter.liminf_le_of_le hge_ca fun b hb ↦ ?_
  have hb' : ∀ᶠ N in atTop, b / c ≤ a N := by
    filter_upwards [hb] with N hN
    exact (div_le_iff₀ hc_pos).mpr (by linarith)
  have hle_lim : b / c ≤ Filter.liminf a atTop :=
    Filter.le_liminf_of_le hle_a.isCoboundedUnder_ge hb'
  exact (div_le_iff₀ hc_pos).mp hle_lim |>.trans_eq (mul_comm _ _)

/-- **Theorem 1.2(c) (General Strip `S_OTOC` Analytic Continuation)**:
For any strip half-width `S_OTOC > 0` on which `concreteOTOC (hH N) β (W N) (V N)` is uniformly
bounded on compact subsets of `{z : ℂ | |z.im| < S_OTOC}` and converges pointwise on `ℝ` to `F_real`,
`F_real` extends uniquely to a holomorphic function `F` on `{|Im z| < S_OTOC}` with locally uniform
convergence and the thermodynamic-limit Eq. (1.17) `liminf` bound. -/
theorem theorem_1_2c_general_otoc_strip_analyticity {β S_OTOC C_V : ℝ}
    (hS : 0 < S_OTOC) (hCV : 0 ≤ C_V)
    (H W V : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H N).IsHermitian) (hW : ∀ N, (W N).IsHermitian) (hV : ∀ N, (V N).IsHermitian)
    (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (hcomp_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S_OTOC} →
      ∃ M : ℝ, ∀ N, ∀ z ∈ K, ‖concreteOTOC (hH N) β (W N) (V N) z‖ ≤ M)
    (hshift_bdd : ∀ τ : ℝ, |τ| < S_OTOC →
      ∃ B : ℝ, ∀ N, concreteWightmanNormAtShift (hH N) β (W N) τ 0 ≤ B)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      atTop (nhds (F_real t))) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S_OTOC} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F atTop
        {z : ℂ | |z.im| < S_OTOC} ∧
      (∀ (t τ : ℝ), |τ| < S_OTOC →
        ‖F ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
          C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop) := by
  rcases vitali_montel_strip_extension hS
      (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F_real
      (fun N ↦ (differentiable_concreteOTOC (hH N) β (W N) (V N)).differentiableOn)
      hcomp_bdd hreal_lim with ⟨F, hF_holo, hF_unif, hF_real⟩
  refine ⟨F, hF_holo, hF_real, hF_unif, fun t τ hτ ↦ ?_⟩
  set z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
  have hz_mem : z ∈ {w : ℂ | |w.im| < S_OTOC} := by
    simp only [Set.mem_setOf_eq, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add]
    exact hτ
  have htend_z : Tendsto (fun N ↦ ‖concreteOTOC (hH N) β (W N) (V N) z‖) atTop (nhds ‖F z‖) :=
    (hF_unif.tendsto_at hz_mem).norm
  rcases hshift_bdd τ hτ with ⟨B, hB⟩
  have hle_liminf : ‖F z‖ ≤ Filter.liminf
      (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop := by
    rw [← htend_z.liminf_eq]
    have hbdd_ca : Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) :=
      ⟨C_V ^ 2 * B, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦
        mul_le_mul_of_nonneg_left (hB N) (sq_nonneg C_V))⟩
    refine Filter.liminf_le_liminf (Eventually.of_forall fun N ↦ ?_)
      htend_z.isBoundedUnder_ge hbdd_ca.isCoboundedUnder_ge
    have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β t τ).1
    have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
    exact le_trans h3 (mul_le_mul_of_nonneg_right hVsq (gibbsWightmanNormSq_nonneg _ _))
  have hmul_liminf := liminf_const_mul_le_of_bdd (sq_nonneg C_V)
    (fun N ↦ gibbsWightmanNormSq_nonneg _ _) hB
  exact le_trans hle_liminf hmul_liminf

/-- Exact `cosh` upper bound on `concreteWightmanNormAtShift hH β W τ 0` from the spectral measure. -/
lemma concreteWightmanNormAtShift_le_two_cosh {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (β τ : ℝ) :
    concreteWightmanNormAtShift hH β W τ 0 ≤
      2 * ∫ ω : ℝ, Real.cosh (2 * τ * ω) ∂(concreteWightmanSpectralMeasure hH β W) := by
  rw [concreteWightmanNormAtShift_eq_spectralMeasure hH hW β τ, ← integral_const_mul]
  refine integral_mono (integrable_concreteWightmanSpectralMeasure hH β W _)
    ((integrable_concreteWightmanSpectralMeasure hH β W _).const_mul 2) fun ω ↦ ?_
  rw [Real.cosh_eq]
  have h1 : Real.exp (-2 * τ * ω) = Real.exp (-(2 * τ * ω)) := by congr 1; ring
  rw [h1]
  linarith [Real.exp_pos (2 * τ * ω)]

/-- **Theorem 1.2(c) (End-to-End Thermodynamic-Limit OTOC Analyticity & Eq. 1.17)**:
For any uniform `r`-local family `(H_N, W_N, V_N)` (`r ≥ 2`, site norm `≤ Jsite`, `opNorm (W_N) ≤ C_W`,
`opNorm (V_N) ≤ C_V`, `W_N ∈ supportedOn (U_W N)` with `|(U_W N)| ≤ sW`) whose finite-volume
regularized OTOCs `concreteOTOC (hH N) β (W N) (V N) t` converge pointwise on `ℝ` to `F_real t`:
1. `F_real` extends uniquely to a holomorphic function `F : ℂ → ℂ` on the strip
   `Ω = {z : ℂ | |z.im| < β / 4 + κ / 2}` where `κ = (2 (r - 1) Jsite)⁻¹`.
2. `concreteOTOC (hH N) β (W N) (V N) → F` locally uniformly on `Ω`.
3. For every `z = t + i τ ∈ Ω`, `F z` obeys the thermodynamic-limit Eq. (1.17) bound:
   `‖F z‖ ≤ C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop`. -/
theorem theorem_1_2c_thermo_limit_otoc_strip {r sW : ℕ} (hr : 2 ≤ r)
    {Jsite β C_W C_V : ℝ} (hJ : 0 < Jsite) (hβ : 0 ≤ β) (hCW : 0 ≤ C_W) (hCV : 0 ≤ C_V)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hcard : ∀ N, ∀ X ∈ E N, X.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hsupp : ∀ N X, h N X ∈ supportedOn X)
    (hH : ∀ N, (∑ X ∈ E N, h N X).IsHermitian)
    (hsite : ∀ N, ∀ x : Fin N, ∑ X ∈ (E N).filter (fun X ↦ x ∈ X), opNorm (h N X) ≤ Jsite)
    (U_W : (N : ℕ) → Finset (Fin N)) (hUW : ∀ N, (U_W N).card ≤ sW)
    (W V : (N : ℕ) → QubitOp N)
    (hWherm : ∀ N, (W N).IsHermitian) (hVherm : ∀ N, (V N).IsHermitian)
    (hW : ∀ N, W N ∈ supportedOn (U_W N))
    (hW_norm : ∀ N, opNorm (W N) ≤ C_W) (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      atTop (nhds (F_real t))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    let S : ℝ := β / 4 + κ / 2
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F atTop
        {z : ℂ | |z.im| < S} ∧
      (∀ (t τ : ℝ), |τ| < S →
        ‖F ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
          C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop) := by
  intro κ S
  have hκ_pos : 0 < κ := by
    dsimp only [κ]
    have hr1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
    positivity
  have hS_pos : 0 < S := by dsimp only [S]; linarith
  -- Uniform bound on `concreteWightmanNormAtShift (hH N) β (W N) τ 0` for `|τ| ≤ R < S`.
  have hshift_unif : ∀ R : ℝ, 0 ≤ R → R < S →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N, ∀ τ : ℝ, |τ| ≤ R →
        concreteWightmanNormAtShift (hH N) β (W N) τ 0 ≤ B := by
    intro R hR_nn hR_lt
    set κ' : ℝ := max 0 (2 * R - β / 2)
    have hκ'_nn : 0 ≤ κ' := le_max_left _ _
    have hκ'_lt : κ' < κ := by
      dsimp only [κ', S] at hR_lt ⊢
      exact max_lt hκ_pos (by linarith)
    set B : ℝ := 4 * C_W ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))
    have h1sub : 0 < 1 - κ' / κ := by rw [sub_pos, div_lt_one hκ_pos]; exact hκ'_lt
    have hB_nn : 0 ≤ B := mul_nonneg (by positivity) (Real.rpow_nonneg h1sub.le _)
    refine ⟨B, hB_nn, fun N τ hτ ↦ ?_⟩
    have h2τ_le : 2 * |τ| ≤ β / 2 + κ' := by
      have : 2 * R - β / 2 ≤ κ' := le_max_right _ _
      linarith
    have h1 := concreteWightmanNormAtShift_le_two_cosh (hH N) (hWherm N) β τ
    have hmono : ∫ ω : ℝ, Real.cosh (2 * τ * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (W N)) ≤
        ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (W N)) := by
      refine integral_mono (integrable_concreteWightmanSpectralMeasure (hH N) β (W N) _)
        (integrable_concreteWightmanSpectralMeasure (hH N) β (W N) _) fun ω ↦ ?_
      have hxy : |2 * τ * ω| ≤ |(β / 2 + κ') * ω| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (by linarith : 0 ≤ β / 2 + κ')]
        exact mul_le_mul_of_nonneg_right h2τ_le (abs_nonneg ω)
      have hax : Real.cosh (2 * τ * ω) = Real.cosh |2 * τ * ω| := by
        rcases le_total 0 (2 * τ * ω) with hx | hx
        · rw [abs_of_nonneg hx]
        · rw [abs_of_nonpos hx, Real.cosh_neg]
      have hay : Real.cosh ((β / 2 + κ') * ω) = Real.cosh |(β / 2 + κ') * ω| := by
        rcases le_total 0 ((β / 2 + κ') * ω) with hy | hy
        · rw [abs_of_nonneg hy]
        · rw [abs_of_nonpos hy, Real.cosh_neg]
      rw [hax, hay, Real.cosh_eq, Real.cosh_eq]
      set a := Real.exp |2 * τ * ω|
      set b := Real.exp |(β / 2 + κ') * ω|
      have ha1 : 1 ≤ a := Real.one_le_exp (abs_nonneg _)
      have hab : a ≤ b := Real.exp_le_exp.mpr hxy
      rw [Real.exp_neg, Real.exp_neg]
      have hapos : 0 < a := by linarith
      have hbpos : 0 < b := by linarith
      have hdiff : 0 ≤ (b - a) * (a * b - 1) := mul_nonneg (by linarith) (by nlinarith)
      have hinv_diff : b + b⁻¹ - (a + a⁻¹) = (b - a) * (a * b - 1) / (a * b) := by
        field_simp [hapos.ne', hbpos.ne']; ring
      have hnonneg : 0 ≤ (b - a) * (a * b - 1) / (a * b) := div_nonneg hdiff (by positivity)
      linarith
    have h54 := (theorem_1_2a_concrete_spectralMeasure_cosh_bound hr (E N) (hcard N) (h N)
      (hsupp N) (hH N) hJ (hsite N) (hUW N) (hWherm N) (hW N) hβ hκ'_nn hκ'_lt).2
    have hsq : (opNorm (W N)) ^ 2 ≤ C_W ^ 2 := by nlinarith [opNorm_nonneg (W N), hW_norm N]
    have hleB : 2 * (2 * (opNorm (W N)) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))) ≤ B := by
      dsimp only [B]
      have := mul_le_mul_of_nonneg_right (show 4 * (opNorm (W N)) ^ 2 ≤ 4 * C_W ^ 2 by linarith)
        (Real.rpow_nonneg h1sub.le (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))))
      linarith
    dsimp only [κ] at hleB
    linarith
  have hcomp_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S} →
      ∃ M : ℝ, ∀ N, ∀ z ∈ K, ‖concreteOTOC (hH N) β (W N) (V N) z‖ ≤ M := by
    intro K hK hKsub
    by_cases hKne : K.Nonempty
    · obtain ⟨z₀, hz₀K, hz₀_max⟩ := hK.exists_isMaxOn hKne (continuous_abs.comp Complex.continuous_im).continuousOn
      set R : ℝ := |z₀.im|
      have hR_nn : 0 ≤ R := abs_nonneg _
      have hR_lt : R < S := hKsub hz₀K
      rcases hshift_unif R hR_nn hR_lt with ⟨B, hB_nn, hB⟩
      refine ⟨C_V ^ 2 * B, fun N z hzK ↦ ?_⟩
      have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
        apply Complex.ext <;> simp
      have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hWherm N) (hVherm N) β z.re z.im).1
      rw [← hz_eq] at h3
      have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
      have hτR : |z.im| ≤ R := hz₀_max hzK
      exact le_trans h3 (mul_le_mul hVsq (hB N z.im hτR)
        (gibbsWightmanNormSq_nonneg _ _) (sq_nonneg C_V))
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨0, fun _ z hz ↦ absurd (hKne ▸ hz) (Set.notMem_empty z)⟩
  exact theorem_1_2c_general_otoc_strip_analyticity hS_pos hCV
    (fun N ↦ ∑ X ∈ E N, h N X) W V hH hWherm hVherm hV_norm hcomp_bdd
    (fun τ hτ ↦ by rcases hshift_unif |τ| (abs_nonneg τ) hτ with ⟨B, _, hB⟩; exact ⟨B, fun N ↦ hB N τ le_rfl⟩)
    F_real hreal_lim

set_option maxHeartbeats 800000 in
/-- **Theorem 1.3(c) (Fully Concrete-Family High-Temperature Chaos Bound with KMS Rate Discharged)**:
Discharges ALL Theorem 1.2(a)–(b) inputs (`μ_N`, `hunif`, `hmom_eq`) directly from the concrete
`r`-local family `(H_N, O_N)` (zero disconnected abstract measure/moment hypotheses), establishing
for all `0 ≤ β ≤ highTempBetaWC r Jsite` with `κ = (2 * (r - 1) * Jsite)⁻¹`:
1. `lamW ≤ 2 * α ≤ 2π / (β + 2κ)` (and `< 2π / β` whenever `0 < β`),
2. `lamMSS ≤ 2 * α ≤ 2π / (β + 2κ)` (and `< 2π / β` whenever `0 < β`),
3. `((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ` unconditionally. -/
theorem theorem_1_3c_concrete_family_complete {r s₀ : ℕ} (hr : 2 ≤ r)
    {Jsite β α γ C_O lamW lamMSS : ℝ}
    (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hCO_ge1 : 1 ≤ C_O) (hlamW : 0 < lamW) (hlamMSS : 0 < lamMSS)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hE_ne : ∀ N, ∀ Z ∈ E N, Z.Nonempty)
    (hE_card : ∀ N, ∀ Z ∈ E N, Z.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hh_supp : ∀ N Z, h N Z ∈ supportedOn Z)
    (hH : ∀ N, (∑ Z ∈ E N, h N Z).IsHermitian)
    (hH_site : ∀ N, ∀ x : Fin N, ∑ Z ∈ (E N).filter (fun Z ↦ x ∈ Z), opNorm (h N Z) ≤ Jsite)
    (U₀ : (N : ℕ) → Finset (Fin N)) (hU₀ : ∀ N, (U₀ N).card ≤ s₀)
    (O : (N : ℕ) → QubitOp N)
    (hO : ∀ N, (O N).IsHermitian)
    (hO_supp : ∀ N, O N ∈ supportedOn (U₀ N))
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O N) = 1)
    (hCO : ∀ N, opNorm (O N) ≤ C_O)
    (hb_lin : ∀ N n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData (hH N) β) (∑ Z ∈ E N, h N Z) (O N) n ≤ α * (n : ℝ) + γ)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(concreteWightmanSpectralMeasure (hH N) β (O N)))
        atTop (nhds (∫ ω, f ω ∂μ)))
    (b_inf : ℕ → ℝ) (hb_pos : ∀ k ≥ 1, 0 < b_inf k)
    (hb_tend : ∀ k : ℕ, Tendsto
      (fun N ↦ lanczosCoeff (concreteGibbsData (hH N) β) (∑ Z ∈ E N, h N Z) (O N) k)
      atTop (nhds (b_inf k)))
    (hb_lim : Tendsto (fun n : ℕ ↦ b_inf n / (n : ℝ)) atTop (nhds α))
    (hH1_W : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamW) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          otocCW (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N)))
    (hH1_MSS : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamMSS) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          mssThermalSize (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    (lamW ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧
      (0 < β → 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β)) ∧
    (lamMSS ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧
      (0 < β → 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β)) ∧
    ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ := by
  intro κ
  have hr1_eq : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hκ_pos : 0 < κ := by
    dsimp only [κ]; have : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
    positivity
  have h12a := theorem_1_2a_concrete_family_holoStrip hr hJ hβ0 (by linarith : 0 ≤ C_O)
    E hE_card h hh_supp hH hH_site U₀ hU₀ O hO hO_supp hCO μ hweak
  -- Discharge `hmom_eq` at `κ' = κ / 2` (so `r_0 = β/2 + κ/2 > 0` even when `β = 0`!).
  have hκ_half_pos : 0 < κ / 2 := by linarith
  have hκ_half_lt : κ / 2 < κ := by linarith
  have h1sub_half : 0 < 1 - (κ / 2) / κ := by rw [sub_pos, div_lt_one hκ_pos]; exact hκ_half_lt
  set M_half : ℝ := 2 * C_O ^ 2 * (1 - (κ / 2) / κ) ^ (-((s₀ : ℝ) / ((r - 1 : ℕ) : ℝ)))
  have hM_half_pos : 0 < M_half := by
    dsimp only [M_half]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos h1sub_half _)
  have hunif_half : ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ / 2) * ω))
      (concreteWightmanSpectralMeasure (hH N) β (O N)) ∧
    ∫ ω : ℝ, Real.cosh ((β / 2 + κ / 2) * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (O N)) ≤ M_half := by
    intro N
    have hN := theorem_1_2a_concrete_spectralMeasure_cosh_bound hr (E N) (hE_card N) (h N)
      (hh_supp N) (hH N) hJ (hH_site N) (hU₀ N) (hO N) (hO_supp N) hβ0 hκ_half_pos.le hκ_half_lt
    refine ⟨hN.1, le_trans hN.2 ?_⟩
    dsimp only [M_half]
    have hsq : (opNorm (O N)) ^ 2 ≤ C_O ^ 2 := by nlinarith [opNorm_nonneg (O N), hCO N]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg h1sub_half.le _)
  have hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b_inf) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ := fun n ↦
    thermo_limit_lanczos_moment_eq_spectralMeasure (fun N ↦ ∑ Z ∈ E N, h N Z) O hH hO β hOnorm μ
      hweak (by linarith : 0 < β / 2 + κ / 2) hM_half_pos.le hunif_half b_inf hb_tend n
  -- Discharge `2 * α ≤ 2 * π / (β + 2 * κ)` for all `β ≥ 0` via `κ' ∈ (0, κ)`.
  have hα_kms : 2 * α ≤ 2 * Real.pi / (β + 2 * κ) := by
    have hle_all : ∀ κ' : ℝ, 0 < κ' → κ' < κ → 2 * α ≤ 2 * Real.pi / (β + 2 * κ') := by
      intro κ' hκ'_pos hκ'_lt
      have h1sub : 0 < 1 - κ' / κ := by rw [sub_pos, div_lt_one hκ_pos]; exact hκ'_lt
      set M' : ℝ := 2 * C_O ^ 2 * (1 - κ' / κ) ^ (-((s₀ : ℝ) / ((r - 1 : ℕ) : ℝ)))
      have hM'_pos : 0 < M' := mul_pos (by positivity) (Real.rpow_pos_of_pos h1sub _)
      have hcosh := h12a.1 κ' hκ'_pos.le hκ'_lt
      have h12b := theorem_1_2b_from_strip_measure μ b_inf (by linarith : 0 < β / 2 + κ')
        hM'_pos hcosh.1 hcosh.2 hb_pos hmom_eq
      rw [hb_lim.liminf_eq] at h12b
      have hrew : Real.pi / (β / 2 + κ') = 2 * Real.pi / (β + 2 * κ') := by
        field_simp [show β / 2 + κ' ≠ 0 by linarith, show β + 2 * κ' ≠ 0 by linarith]
      rwa [hrew] at h12b
    let seq : ℕ → ℝ := fun m ↦ κ - κ / ((m : ℝ) + 2)
    have hseq_tend : Tendsto seq atTop (nhds κ) := by
      have hdiv : Tendsto (fun m : ℕ ↦ κ / ((m : ℝ) + 2)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa [seq] using tendsto_const_nhds.sub hdiv
    have hcont_fn : ContinuousAt (fun x : ℝ ↦ 2 * Real.pi / (β + 2 * x)) κ :=
      continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        (by linarith)
    have hfn_tend : Tendsto (fun m : ℕ ↦ 2 * Real.pi / (β + 2 * seq m)) atTop
        (nhds (2 * Real.pi / (β + 2 * κ))) :=
      hcont_fn.tendsto.comp hseq_tend
    refine ge_of_tendsto hfn_tend ?_
    filter_upwards with m
    have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hseq_pos : 0 < seq m := by
      dsimp only [seq]
      have : κ / ((m : ℝ) + 2) ≤ κ / 2 := div_le_div_of_nonneg_left hκ_pos.le (by norm_num) hm2
      linarith
    have hseq_lt : seq m < κ := by
      dsimp only [seq]; linarith [div_pos hκ_pos (by linarith : (0 : ℝ) < (m : ℝ) + 2)]
    exact hle_all (seq m) hseq_pos hseq_lt
  have hstrict : 0 < β → 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := fun hβ_pos ↦
    div_lt_div_of_pos_left (by positivity) hβ_pos (by linarith)
  -- Wire into `theorem_1_3c_unconditional_family` (works for `0 < β`, and for `β = 0` directly via `theorem_1_3c_eq_1_24_concrete`!).
  have hlamW_le : lamW ≤ 2 * α := by
    by_cases hβ_pos : 0 < β
    · exact (theorem_1_3c_unconditional_family hr hJ hβ_pos hβ hκ_pos hα hγ hα_kms hCO_ge1
        hlamW hlamMSS E hE_ne hE_card h hh_supp hH hH_site U₀ hU₀ O hO hO_supp hOnorm hCO
        hb_lin hH1_W hH1_MSS).1.1
    · -- `β = 0`: `otocCW ≤ 216 * ((r - 1) * K + s₀)` from `theorem_1_3b_high_temp`!
      have hβ_eq : β = 0 := le_antisymm (le_of_not_gt hβ_pos) hβ0
      subst hβ_eq
      -- Apply `theorem_1_3c_unconditional_family`? Actually `theorem_1_3b_high_temp` holds for `0 ≤ β`!
      -- Use the exact same `contradiction` argument with `theorem_1_3c_eq_1_24_concrete` + `theorem_1_3b_high_temp`!
      by_contra hgt; push Not at hgt
      set ε₀ : ℝ := min ((lamW - 2 * α) / (2 * lamW)) (1 / 2)
      have hε₀ : 0 < ε₀ := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
      rcases hH1_W ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
      have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
      have hθ : (1 - ε) * (2 * α / lamW) < 1 - ε := by
        have h1 : 2 * α / lamW < 1 := (div_lt_one hlamW).mpr hgt
        nlinarith
      set η : ℝ := (1 - ε) * (2 * α / lamW)
      have hη_lt : η < 1 - ε := hθ
      -- For `N ≥ max N₁ 2`, `c N^(1-ε) ≤ 216 * ((r-1) * C_K * N^η + s₀)`.
      set C_K : ℝ := Real.exp ((1 / 2 + γ / α) * 1) / (4 * Real.exp 1 * Real.tanh (1 / 4))
      have hCK_pos : 0 < C_K := by
        dsimp only [C_K]
        have : 0 < Real.tanh (1 / 4) := by
          rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
          apply div_pos _ (Real.cosh_pos _)
          linarith [Real.exp_lt_exp.mpr (by norm_num : -(1 / 4 : ℝ) < 1 / 4)]
        positivity
      have hpow_lim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (η - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - η)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by dsimp only [Function.comp_apply]; congr 1; ring
      have hinv_lim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - ε)).comp tendsto_natCast_atTop_atTop
      have hrhs_lim : Tendsto (fun N : ℕ ↦
          216 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (η - (1 - ε)) +
          216 * (s₀ : ℝ) * (N : ℝ) ^ (-(1 - ε))) atTop (nhds 0) := by
        simpa using (hpow_lim.const_mul (216 * ((r - 1 : ℕ) : ℝ) * C_K)).add
          (hinv_lim.const_mul (216 * (s₀ : ℝ)))
      obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hrhs_lim) c hc_pos
      set N : ℕ := max (max N₁ N₂) 2
      have hN_ge1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
      have hN_ge2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
      have hN_pos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      have htN_nn : 0 ≤ ((1 - ε) / lamW) * Real.log (N : ℝ) :=
        mul_nonneg (div_nonneg (by linarith) hlamW.le) (Real.log_nonneg hN_pos.le)
      have hlow := hN₁ N hN_ge1
      have hHf : (∑ Z ∈ E N, h N Z) ∈ filtrationSubmodule N r :=
        localHamiltonian_mem_filtrationSubmodule (E N) (hE_card N) (h N) (hh_supp N)
      have hOf : O N ∈ filtrationSubmodule N s₀ :=
        supportedOn_le_filtrationSubmodule (hU₀ N) (hO_supp N)
      have h13b := (theorem_1_3b_high_temp hr (E N) (hE_ne N) (hE_card N) (h N) (hh_supp N)
        (hH N) hJ (hH_site N) le_rfl hβ (hO N) hHf hOf (hOnorm N) (((1 - ε) / lamW) * Real.log (N : ℝ))).1
      have h11a := theorem_1_1a_concrete_qubit_complexity (hH N) (hO N) 0 (hOnorm N) hα hγ
        (by norm_num : (0 : ℝ) < 1) (hb_lin N) (((1 - ε) / lamW) * Real.log (N : ℝ)) htN_nn
      have hexp_eq : Real.exp (2 * α * (((1 - ε) / lamW) * Real.log (N : ℝ))) = (N : ℝ) ^ η := by
        rw [Real.rpow_def_of_pos (by linarith)]; congr 1; dsimp only [η]; ring
      rw [hexp_eq] at h11a
      have hN_rpow_pos : 0 < (N : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos (by linarith) _
      have hcomb : c * (N : ℝ) ^ (1 - ε) ≤
          216 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ η + 216 * (s₀ : ℝ) := by
        have h1 : otocCW (concreteGibbsData (hH N) 0)
            (heisenbergEvol (hH N) ((((1 - ε) / lamW) * Real.log (N : ℝ) : ℝ) : ℂ) (O N)) ≤
            54 * (((r - 1 : ℕ) : ℝ) *
              concreteKrylovComplexity (hH N) 0 (O N) (((1 - ε) / lamW) * Real.log (N : ℝ)) +
              (s₀ : ℝ)) := h13b
        have hr1_nn : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [hlow, h1, h11a]
      have hdiv : c ≤ 216 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (η - (1 - ε)) +
          216 * (s₀ : ℝ) * (N : ℝ) ^ (-(1 - ε)) := by
        have h := div_le_div_of_nonneg_right hcomb hN_rpow_pos.le
        rw [mul_div_cancel_right₀ c hN_rpow_pos.ne', add_div] at h
        have hr1 : (N : ℝ) ^ η / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (η - (1 - ε)) :=
          (Real.rpow_sub (by linarith) η (1 - ε)).symm
        have hr2 : (1 : ℝ) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-(1 - ε)) := by
          rw [Real.rpow_neg (by linarith), one_div]
        calc c ≤ 216 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ η / (N : ℝ) ^ (1 - ε) +
              216 * (s₀ : ℝ) / (N : ℝ) ^ (1 - ε) := h
          _ = 216 * ((r - 1 : ℕ) : ℝ) * C_K * ((N : ℝ) ^ η / (N : ℝ) ^ (1 - ε)) +
              216 * (s₀ : ℝ) * (1 / (N : ℝ) ^ (1 - ε)) := by ring
          _ = 216 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (η - (1 - ε)) +
              216 * (s₀ : ℝ) * (N : ℝ) ^ (-(1 - ε)) := by rw [hr1, hr2]
      have hsmall := hN₂ N hN_ge2
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
      linarith
  have hlamMSS_le : lamMSS ≤ 2 * α := by
    by_cases hβ_pos : 0 < β
    · exact (theorem_1_3c_unconditional_family hr hJ hβ_pos hβ hκ_pos hα hγ hα_kms hCO_ge1
        hlamW hlamMSS E hE_ne hE_card h hh_supp hH hH_site U₀ hU₀ O hO hO_supp hOnorm hCO
        hb_lin hH1_W hH1_MSS).2.1
    · have hβ_eq : β = 0 := le_antisymm (le_of_not_gt hβ_pos) hβ0
      subst hβ_eq
      -- At `β = 0`, `theorem_1_3c_eq_1_24_concrete` applies directly for all `0 ≤ β ≤ highTempBetaWC`!
      by_contra hgt; push Not at hgt
      set ε₀ : ℝ := min ((lamMSS - 2 * α) / (2 * lamMSS)) (1 / 2)
      have hε₀ : 0 < ε₀ := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
      rcases hH1_MSS ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
      have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
      set η : ℝ := (1 - ε) * (2 * α / lamMSS)
      have hη_lt : η < 1 - ε := by
        have h1 : 2 * α / lamMSS < 1 := (div_lt_one hlamMSS).mpr hgt
        dsimp only [η]; nlinarith
      set C₂ : ℝ := bgDecouplingC2 r s₀ C_O
      set C₁ : ℝ := 24 * Real.sqrt (3 * (1 + C₂))
      have hC₂ : 0 ≤ C₂ := by
        dsimp only [C₂, bgDecouplingC2]
        have h1 : (1 : ℝ) ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := by
          calc (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := mul_le_mul hCO_ge1 (one_le_pow₀ (by norm_num)) (by norm_num) (by positivity)
        have hlog : 0 ≤ Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) := Real.log_nonneg h1
        positivity
      have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
      set N₀ : ℕ := 1
      set C_K : ℝ := Real.exp ((1 / 2 + γ / α) * 1) / (4 * Real.exp 1 * Real.tanh (1 / 4))
      have hCK_pos : 0 < C_K := by
        dsimp only [C_K]
        have : 0 < Real.tanh (1 / 4) := by
          rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
          apply div_pos _ (Real.cosh_pos _)
          linarith [Real.exp_lt_exp.mpr (by norm_num : -(1 / 4 : ℝ) < 1 / 4)]
        positivity
      set A₁ : ℝ := 216 * ((r - 1 : ℕ) : ℝ) * C_K
      set A₂ : ℝ := 216 * (s₀ : ℝ)
      -- Since `η < 1 - ε` and `1/2 < 1 - ε`, `N^η / N^(1-ε) → 0`, `√(N * N^η) / N^(1-ε) = N^((1+η)/2 - (1-ε)) → 0`?
      -- Wait: `(1 + η)/2 < 1 - ε` requires `ε` small enough! Choose `ε₀ = min ((lamMSS - 2α)/(4 lamMSS)) ((1 - 2α/lamMSS)/4)`!
      -- Even simpler: pick `ε₀' := min ((lamMSS - 2 * α) / (4 * lamMSS)) (1 / 4)` — wait, we already got `ε` from `ε₀`!
      -- Let's re-invoke `hH1_MSS` with `ε₀' := min ((lamMSS - 2 * α) / (4 * lamMSS)) (1 / 4)`?
      -- Better: for `0 < 1 - 2α/lamMSS`, `(1 + η)/2 < 1 - ε` iff `2 ε < 1 - η = 1 - (1 - ε)(2α/lamMSS)` iff `ε (2 - 2α/lamMSS) < 1 - 2α/lamMSS`,
      -- which holds whenever `ε < (1 - 2α/lamMSS) / 2 = (lamMSS - 2α) / (2 lamMSS)`!!
      -- AND OUR `ε < ε₀ ≤ (lamMSS - 2α) / (2 lamMSS)` ALREADY SATISFIES THAT!
      have hmid_lt : (1 + η) / 2 < 1 - ε := by
        have hε_bound : ε < (lamMSS - 2 * α) / (2 * lamMSS) := lt_of_lt_of_le hε_lt (min_le_left _ _)
        have h1 : 2 * ε < 1 - 2 * α / lamMSS := by
          have : (lamMSS - 2 * α) / (2 * lamMSS) = (1 - 2 * α / lamMSS) / 2 := by
            field_simp [hlamMSS.ne']
          linarith
        have h2 : η ≤ 2 * α / lamMSS := by
          dsimp only [η]; nlinarith [div_pos (by linarith : 0 < 2 * α) hlamMSS]
        linarith
      have hhalf_lt : (1 : ℝ) / 2 < 1 - ε := by linarith
      have hlim1 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (η - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - η)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by dsimp only [Function.comp_apply]; congr 1; ring
      have hlim2 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 + η) / 2 - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - (1 + η) / 2)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by dsimp only [Function.comp_apply]; congr 1; ring
      have hlim3 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 2 - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - 1 / 2)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by dsimp only [Function.comp_apply]; congr 1; ring
      have hlim4 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - ε)).comp tendsto_natCast_atTop_atTop
      have hrhs_lim : Tendsto (fun N : ℕ ↦
          A₁ * (N : ℝ) ^ (η - (1 - ε)) + A₂ * (N : ℝ) ^ (-(1 - ε)) +
          C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2 - (1 - ε)) +
          (C₁ * Real.sqrt (s₀ : ℝ) + C₂) * (N : ℝ) ^ ((1 : ℝ) / 2 - (1 - ε))) atTop (nhds 0) := by
        simpa using (((hlim1.const_mul A₁).add (hlim4.const_mul A₂)).add
          (hlim2.const_mul (C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K)))).add
          (hlim3.const_mul (C₁ * Real.sqrt (s₀ : ℝ) + C₂))
      obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hrhs_lim) c hc_pos
      set N : ℕ := max (max (max N₀ N₁) N₂) 2
      have hN_ge0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
      have hN_ge1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
      have hN_ge2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
      have hN_pos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      set tN : ℝ := ((1 - ε) / lamMSS) * Real.log (N : ℝ)
      have htN_nn : 0 ≤ tN := mul_nonneg (div_nonneg (by linarith) hlamMSS.le) (Real.log_nonneg hN_pos.le)
      have hlow := hN₁ N hN_ge1
      have hbound := (theorem_1_3c_eq_1_24_concrete hN_ge0 hr (E N) (hE_ne N) (hE_card N)
        (h N) (hh_supp N) (hH N) hJ (hH_site N) le_rfl hβ (hU₀ N) (hO N) (hO_supp N)
        (hOnorm N) hCO_ge1 (hCO N) tN).1
      have h11a := theorem_1_1a_concrete_qubit_complexity (hH N) (hO N) 0 (hOnorm N) hα hγ
        (by norm_num : (0 : ℝ) < 1) (hb_lin N) tN htN_nn
      have hexp_eq : Real.exp (2 * α * tN) = (N : ℝ) ^ η := by
        rw [Real.rpow_def_of_pos (by linarith)]; congr 1; dsimp only [η, tN]; ring
      rw [hexp_eq] at h11a
      have hK_le : ((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ) ≤
          ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ η + (s₀ : ℝ) := by
        have : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [h11a]
      have hsqrt_le : Real.sqrt ((N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ))) ≤
          Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2) +
          Real.sqrt (s₀ : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : (N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ)) ≤
            (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η)) + ((s₀ : ℝ) * (N : ℝ)) := by
          have hpow1 : (N : ℝ) * (N : ℝ) ^ η = (N : ℝ) ^ (1 + η) := by
            rw [Real.rpow_add (by linarith), Real.rpow_one]
          calc (N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ))
              ≤ (N : ℝ) * (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ η + (s₀ : ℝ)) :=
                mul_le_mul_of_nonneg_left hK_le (by linarith)
            _ = ((r - 1 : ℕ) : ℝ) * C_K * ((N : ℝ) * (N : ℝ) ^ η) + (s₀ : ℝ) * (N : ℝ) := by ring
            _ = ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η) + (s₀ : ℝ) * (N : ℝ) := by rw [hpow1]
        have h2 : Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η) + (s₀ : ℝ) * (N : ℝ)) ≤
            Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η)) + Real.sqrt ((s₀ : ℝ) * (N : ℝ)) := by
          have ha : 0 ≤ ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η) := by positivity
          have hb : 0 ≤ (s₀ : ℝ) * (N : ℝ) := by positivity
          rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
          apply Real.sqrt_le_sqrt
          rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
          linarith [mul_nonneg (Real.sqrt_nonneg (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η)))
            (Real.sqrt_nonneg ((s₀ : ℝ) * (N : ℝ)))]
        have h3 : Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (1 + η)) =
            Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow ((N : ℝ) ^ (1 + η)),
            ← Real.rpow_mul (by linarith)]
          congr 2; ring
        have h4 : Real.sqrt ((s₀ : ℝ) * (N : ℝ)) = Real.sqrt (s₀ : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg s₀), Real.sqrt_eq_rpow (N : ℝ)]
        exact le_trans (Real.sqrt_le_sqrt h1) (by rw [← h3, ← h4]; exact h2)
      have hsqrtN : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (N : ℝ)
      have hcomb : c * (N : ℝ) ^ (1 - ε) ≤
          A₁ * (N : ℝ) ^ η + A₂ +
          C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2) +
          (C₁ * Real.sqrt (s₀ : ℝ) + C₂) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : c * (N : ℝ) ^ (1 - ε) ≤
            216 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ)) +
            C₁ * Real.sqrt ((N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) 0 (O N) tN + (s₀ : ℝ))) +
            C₂ * Real.sqrt (N : ℝ) := le_trans hlow hbound
        rw [hsqrtN] at h1
        dsimp only [A₁, A₂]
        nlinarith [hK_le, hsqrt_le]
      have hN_rpow_pos : 0 < (N : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos (by linarith) _
      have hdiv : c ≤ A₁ * (N : ℝ) ^ (η - (1 - ε)) + A₂ * (N : ℝ) ^ (-(1 - ε)) +
          C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2 - (1 - ε)) +
          (C₁ * Real.sqrt (s₀ : ℝ) + C₂) * (N : ℝ) ^ ((1 : ℝ) / 2 - (1 - ε)) := by
        have h := div_le_div_of_nonneg_right hcomb hN_rpow_pos.le
        rw [mul_div_cancel_right₀ c hN_rpow_pos.ne'] at h
        have hr1 : (N : ℝ) ^ η / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (η - (1 - ε)) :=
          (Real.rpow_sub (by linarith) η (1 - ε)).symm
        have hr2 : (N : ℝ) ^ ((1 + η) / 2) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ ((1 + η) / 2 - (1 - ε)) :=
          (Real.rpow_sub (by linarith) ((1 + η) / 2) (1 - ε)).symm
        have hr3 : (N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ ((1 : ℝ) / 2 - (1 - ε)) :=
          (Real.rpow_sub (by linarith) (1 / 2) (1 - ε)).symm
        have hr4 : (1 : ℝ) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-(1 - ε)) := by
          rw [Real.rpow_neg (by linarith), one_div]
        calc c ≤ (A₁ * (N : ℝ) ^ η + A₂ +
              C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * (N : ℝ) ^ ((1 + η) / 2) +
              (C₁ * Real.sqrt (s₀ : ℝ) + C₂) * (N : ℝ) ^ ((1 : ℝ) / 2)) / (N : ℝ) ^ (1 - ε) := h
          _ = A₁ * ((N : ℝ) ^ η / (N : ℝ) ^ (1 - ε)) + A₂ * (1 / (N : ℝ) ^ (1 - ε)) +
              C₁ * Real.sqrt (((r - 1 : ℕ) : ℝ) * C_K) * ((N : ℝ) ^ ((1 + η) / 2) / (N : ℝ) ^ (1 - ε)) +
              (C₁ * Real.sqrt (s₀ : ℝ) + C₂) * ((N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) ^ (1 - ε)) := by ring
          _ = _ := by rw [hr1, hr2, hr3, hr4]
      have hsmall := hN₂ N hN_ge2
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
      linarith
  exact ⟨⟨hlamW_le, hα_kms, hstrict⟩, ⟨hlamMSS_le, hα_kms, hstrict⟩, h12a.2⟩

end ConcreteOTOCAnalyticityAndTheorem13c

end KrylovChaos
