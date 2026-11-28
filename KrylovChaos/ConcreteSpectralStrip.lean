/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Theorem12Concrete
import KrylovChaos.Milestone2SpectralAndVitali
import KrylovChaos.HighTempChaosFull
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Concrete Wightman Spectral Measure, Holomorphic Strip Half-Width, and Thermodynamic-Limit Moments

Bridges the concrete `QubitOp N` framework directly to `Measure ℝ`, holomorphic strip half-widths,
and thermodynamic-limit Lanczos moments:
1. `concreteWightmanSpectralMeasure`: constructs the finite Borel spectral measure on `ℝ` directly
   from `wightmanSpectralWeight hH β W` and proves `theorem_1_2a_concrete_eq54_r_local_bound`
   discharges uniform `cosh` integrability for any uniform `r`-local family `(H_N, W_N)`.
2. `holoStripHalfWidth : Measure ℝ → EReal`: genuine holomorphic strip half-width
   `sup { R > 0 : z ↦ ∫ exp(i z ω) dμ extends holomorphically to |Im z| < R }` in `EReal`
   (taking value `⊤` in finite volume without any `BddAbove` guard), with
   `((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ` for any weak thermodynamic limit `μ`.
3. `concrete_adPowOp_eq_spectralMeasure_moment` and `thermo_limit_lanczos_moment_eq_spectralMeasure`:
   prove `Re (O | (ad_H)^{2n} O)_β^W = ∫ ω^(2n) dμ_N` and wire finite-volume Lanczos convergence
   into the thermodynamic-limit moment identity `((T_{2n+1})^{2n})_{0,0} = ∫ ω^(2n) dμ`.
4. `holoStrip_even_moment_bound` and `theorem_1_2b_from_holoStripHalfWidth`:
   prove the complex-analytic Cauchy–Hadamard upper bound directly from holomorphy on `{|Im z| < R}`,
   yielding Eq. (1.16) `2 * liminf (b n / n) ≤ π / r_W ≤ 2π / (β + 2κ) < 2π / β` with holomorphic `r_W`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology Complex

section ConcreteSpectralMeasureAndHoloStrip

/-- Concrete Wightman spectral measure on `ℝ` built directly from `wightmanSpectralWeight hH β W`. -/
noncomputable def concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N) : Measure ℝ :=
  ∑ a : QubitIdx N, ∑ b : QubitIdx N,
    ENNReal.ofReal (wightmanSpectralWeight hH β W a b) •
      Measure.dirac (hH.eigenvalues a - hH.eigenvalues b)

instance instIsFiniteMeasure_concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N) :
    IsFiniteMeasure (concreteWightmanSpectralMeasure hH β W) := by
  refine ⟨?_⟩
  unfold concreteWightmanSpectralMeasure
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  exact ENNReal.sum_lt_top.mpr fun a _ ↦ ENNReal.sum_lt_top.mpr fun b _ ↦ ENNReal.ofReal_lt_top

/-- Every function `f : ℝ → E` is integrable with respect to the finite atomic measure
`concreteWightmanSpectralMeasure hH β W`. -/
lemma integrable_concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (concreteWightmanSpectralMeasure hH β W) := by
  unfold concreteWightmanSpectralMeasure
  refine integrable_finset_sum_measure.mpr fun a _ ↦
    integrable_finset_sum_measure.mpr fun b _ ↦ ?_
  exact (integrable_dirac (enorm_lt_top)).smul_measure ENNReal.ofReal_ne_top

/-- Exact Bochner integral formula against `concreteWightmanSpectralMeasure hH β W`. -/
lemma integral_concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) :
    ∫ ω : ℝ, f ω ∂(concreteWightmanSpectralMeasure hH β W) =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b • f (hH.eigenvalues a - hH.eigenvalues b) := by
  unfold concreteWightmanSpectralMeasure
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl; intro a _
    rw [integral_finset_sum_measure]
    · apply Finset.sum_congr rfl; intro b _
      rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal (wightmanSpectralWeight_nonneg hH β W a b)]
    · intro b _
      exact (integrable_dirac (enorm_lt_top)).smul_measure ENNReal.ofReal_ne_top
  · intro a _
    refine integrable_finset_sum_measure.mpr fun b _ ↦ ?_
    exact (integrable_dirac (enorm_lt_top)).smul_measure ENNReal.ofReal_ne_top

/-- Concrete finite-volume `cosh` bound on `concreteWightmanSpectralMeasure` directly from
`theorem_1_2a_concrete_eq54_r_local_bound`. -/
theorem theorem_1_2a_concrete_spectralMeasure_cosh_bound {N r sW : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ sW) {W : QubitOp N}
    (hWherm : W.IsHermitian) (hW : W ∈ supportedOn U₀)
    {β : ℝ} (hβ : 0 ≤ β) {κ' : ℝ} (hκ'0 : 0 ≤ κ')
    (hκ'_lt : κ' < 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω))
      (concreteWightmanSpectralMeasure hH β W) ∧
    ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(concreteWightmanSpectralMeasure hH β W) ≤
      2 * (opNorm W) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) := by
  intro κ
  refine ⟨integrable_concreteWightmanSpectralMeasure hH β W _, ?_⟩
  rw [integral_concreteWightmanSpectralMeasure]
  have h54 := theorem_1_2a_concrete_eq54_r_local_bound hr E hcard h hsupp hH hJ hsite hU₀
    hWherm hW β hκ'0 hκ'_lt
  refine le_trans ?_ h54
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (wightmanSpectralWeight_nonneg hH β W a b)
  rw [Real.cosh_eq]
  have h1 : (β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b) ≤
      (β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  have h2 : -((β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b)) ≤
      (β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b| := by
    have : -(hH.eigenvalues a - hH.eigenvalues b) ≤ |hH.eigenvalues a - hH.eigenvalues b| :=
      neg_le_abs _
    have hmul := mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ β / 2 + κ')
    linarith
  linarith [Real.exp_le_exp.mpr h1, Real.exp_le_exp.mpr h2]

/-- **Holomorphic Strip Half-Width `r_W(μ) ∈ EReal`**:
`r_W(μ) := sup { R > 0 : t ↦ ∫ ω, exp(i t ω) dμ extends holomorphically to |Im z| < R }`.
In finite volume `r_W = ⊤` with no `BddAbove` guard required. -/
noncomputable def holoStripHalfWidth (μ : Measure ℝ) : EReal :=
  sSup { r : EReal | ∃ R : ℝ, r = (R : EReal) ∧ 0 < R ∧
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | |z.im| < R} ∧
      ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ }

/-- In finite volume, the Wightman autocorrelation function is entire, so
`holoStripHalfWidth (concreteWightmanSpectralMeasure hH β W) = ⊤`. -/
theorem holoStripHalfWidth_finite_eq_top {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N) :
    holoStripHalfWidth (concreteWightmanSpectralMeasure hH β W) = ⊤ := by
  rw [eq_top_iff]
  unfold holoStripHalfWidth
  refine le_of_forall_lt_imp_le_of_dense fun x hx ↦ ?_
  cases x using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hx (lt_irrefl _)
  | coe r =>
    set R : ℝ := max r 0 + 1
    have hR_pos : 0 < R := by dsimp only [R]; linarith [le_max_right r 0]
    have hr_le : (r : EReal) ≤ (R : EReal) :=
      EReal.coe_le_coe_iff.mpr (by dsimp only [R]; linarith [le_max_left r 0])
    refine le_trans hr_le (le_sSup ?_)
    refine ⟨R, rfl, hR_pos,
      fun z : ℂ ↦ ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        ((wightmanSpectralWeight hH β W a b : ℝ) : ℂ) *
          Complex.exp (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)),
      ?_, ?_⟩
    · refine (Differentiable.fun_sum fun a _ ↦ Differentiable.fun_sum fun b _ ↦ ?_).differentiableOn
      exact (differentiable_const _).mul
        ((((differentiable_const _).mul differentiable_id).mul (differentiable_const _)).cexp)
    · intro t
      rw [integral_concreteWightmanSpectralMeasure]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [Complex.real_smul]

/-- **Theorem 1.2(a) (Concrete `r`-Local Family Thermodynamic Limit & Holomorphic `r_W ≥ β/2 + κ`)**:
For any uniform `r`-local qubit family `(H_N, W_N)` (`r ≥ 2`, site norm `≤ Jsite`, `opNorm (W_N) ≤ C_W`,
`W_N ∈ supportedOn (U₀ N)` with `|(U₀ N)| ≤ sW`) whose concrete Wightman spectral measures converge
weakly to `μ`, proves unconditionally (with no `BddAbove` guard):
1. For every `κ' ∈ [0, κ)` where `κ = (2 (r - 1) Jsite)⁻¹`, `cosh((β/2 + κ') ω)` is `μ`-integrable
   with exact Eq. (1.15) bound `∫ cosh((β/2 + κ') ω) dμ ≤ 2 C_W² (1 - κ'/κ)^{-sW/(r-1)}`.
2. `((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ`. -/
theorem theorem_1_2a_concrete_family_holoStrip {r sW : ℕ} (hr : 2 ≤ r)
    {Jsite β C_W : ℝ} (hJ : 0 < Jsite) (hβ : 0 ≤ β) (hCW : 0 ≤ C_W)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hcard : ∀ N, ∀ X ∈ E N, X.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hsupp : ∀ N X, h N X ∈ supportedOn X)
    (hH : ∀ N, (∑ X ∈ E N, h N X).IsHermitian)
    (hsite : ∀ N, ∀ x : Fin N, ∑ X ∈ (E N).filter (fun X ↦ x ∈ X), opNorm (h N X) ≤ Jsite)
    (U₀ : (N : ℕ) → Finset (Fin N)) (hU₀ : ∀ N, (U₀ N).card ≤ sW)
    (W : (N : ℕ) → QubitOp N) (hWherm : ∀ N, (W N).IsHermitian)
    (hW : ∀ N, W N ∈ supportedOn (U₀ N)) (hW_norm : ∀ N, opNorm (W N) ≤ C_W)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(concreteWightmanSpectralMeasure (hH N) β (W N)))
        atTop (nhds (∫ ω, f ω ∂μ))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    (∀ κ' : ℝ, 0 ≤ κ' → κ' < κ →
      Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) μ ∧
      ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂μ ≤
        2 * C_W ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))) ∧
    ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ := by
  intro κ
  have hκ_pos : 0 < κ := by
    dsimp only [κ]
    have hr1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
    positivity
  have hcosh_all : ∀ κ' : ℝ, 0 ≤ κ' → κ' < κ →
      Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) μ ∧
      ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂μ ≤
        2 * C_W ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) := by
    intro κ' hκ'0 hκ'_lt
    set M : ℝ := 2 * C_W ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))
    have h1sub : 0 < 1 - κ' / κ := by
      rw [sub_pos, div_lt_one hκ_pos]; exact hκ'_lt
    have hM_nn : 0 ≤ M := by
      dsimp only [M]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg h1sub.le _)
    have hunif : ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω))
          (concreteWightmanSpectralMeasure (hH N) β (W N)) ∧
        ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (W N)) ≤ M := by
      intro N
      have hN := theorem_1_2a_concrete_spectralMeasure_cosh_bound hr (E N) (hcard N) (h N)
        (hsupp N) (hH N) hJ (hsite N) (hU₀ N) (hWherm N) (hW N) hβ hκ'0 hκ'_lt
      refine ⟨hN.1, le_trans hN.2 ?_⟩
      dsimp only [M]
      have hsq : (opNorm (W N)) ^ 2 ≤ C_W ^ 2 := by
        nlinarith [opNorm_nonneg (W N), hW_norm N]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg h1sub.le _)
    by_cases hpos : 0 < β / 2 + κ'
    · have h12 := theorem_1_2a_thermo_limit_eq_1_15_and_rW
        (fun N ↦ concreteWightmanSpectralMeasure (hH N) β (W N)) μ hweak hpos hM_nn hunif
      exact ⟨h12.1, h12.2.1⟩
    · have hzero : β / 2 + κ' = 0 := le_antisymm (le_of_not_gt hpos) (by linarith)
      have hlint : ∫⁻ ω, ENNReal.ofReal (Real.cosh ((β / 2 + κ') * ω)) ∂μ ≤ ENNReal.ofReal M := by
        have h0 : ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * (0 : ℝ) * ω)) ∂μ ≤ ENNReal.ofReal M := by
          refine lintegral_cosh_le_of_weak_limit (fun N ↦ concreteWightmanSpectralMeasure (hH N) β (W N))
            μ hweak hM_nn fun N ↦ ?_
          have h1 : ∫ ω : ℝ, (1 : ℝ) ∂(concreteWightmanSpectralMeasure (hH N) β (W N)) ≤ M := by
            simpa [hzero] using (hunif N).2
          have heq : (fun ω : ℝ ↦ Real.cosh (2 * (0 : ℝ) * ω)) = fun _ ↦ (1 : ℝ) := by
            funext ω; simp
          simp_rw [heq]
          have hnn : 0 ≤ᵐ[concreteWightmanSpectralMeasure (hH N) β (W N)] (fun _ : ℝ ↦ (1 : ℝ)) :=
            Eventually.of_forall fun _ ↦ zero_le_one
          rw [← ofReal_integral_eq_lintegral_ofReal (integrable_const 1) hnn]
          exact ENNReal.ofReal_le_ofReal h1
        refine le_trans (le_of_eq ?_) h0
        congr 1; funext ω; rw [hzero]; simp
      exact integrable_cosh_of_lintegral_le μ hM_nn hlint
  refine ⟨hcosh_all, ?_⟩
  have hle_all : ∀ κ' : ℝ, 0 < κ' → κ' < κ → ((β / 2 + κ' : ℝ) : EReal) ≤ holoStripHalfWidth μ := by
    intro κ' hκ'_pos hκ'_lt
    have hhint := (hcosh_all κ' hκ'_pos.le hκ'_lt).1
    have hR_pos : 0 < β / 2 + κ' := by linarith
    refine le_sSup ⟨β / 2 + κ', rfl, hR_pos,
      fun z : ℂ ↦ ∫ ω : ℝ, Complex.exp (Complex.I * z * (ω : ℂ)) ∂μ,
      wightmanAutocorr_measure_differentiableOn_strip μ hR_pos hhint, fun _ ↦ rfl⟩
  by_contra hlt
  push Not at hlt
  cases hval : holoStripHalfWidth μ using EReal.rec with
  | bot =>
    have h1 := hle_all (κ / 2) (by linarith) (by linarith)
    rw [hval] at h1
    exact absurd h1 (by simp)
  | top =>
    rw [hval] at hlt
    exact absurd hlt (not_lt_of_ge le_top)
  | coe w =>
    rw [hval, EReal.coe_lt_coe_iff] at hlt
    set κ' : ℝ := max (κ / 2) ((w - β / 2 + κ) / 2)
    have hκ'_pos : 0 < κ' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hκ'_lt : κ' < κ := max_lt (by linarith) (by linarith)
    have hle := hle_all κ' hκ'_pos hκ'_lt
    rw [hval, EReal.coe_le_coe_iff] at hle
    have hge : (w - β / 2 + κ) / 2 ≤ κ' := le_max_right _ _
    linarith

end ConcreteSpectralMeasureAndHoloStrip

section ConcreteMomentsAndHolomorphicCauchyHadamard

/-- Eigenbasis formula for `adPowOp H m O`:
`(Uᴴ * adPowOp H m O * U) a b = (E_a - E_b)^m * (Uᴴ * O * U) a b`. -/
lemma adPowOp_eigen_entry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (O : QubitOp N) :
    ∀ (m : ℕ) (a b : QubitIdx N),
      ((hH.eigenvectorUnitary : QubitOp N)ᴴ * adPowOp H m O *
        (hH.eigenvectorUnitary : QubitOp N)) a b =
      (((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) ^ m) *
        ((hH.eigenvectorUnitary : QubitOp N)ᴴ * O * (hH.eigenvectorUnitary : QubitOp N)) a b := by
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.prop
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.prop
  have hH_diag : Uᴴ * H * U = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
    have hspec := (hermFunc_id hH).symm
    unfold hermFunc at hspec
    change Uᴴ * H * U = _
    conv_lhs => rw [hspec]
    calc Uᴴ * (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by rw [hU2, Matrix.one_mul, Matrix.mul_one]
  intro m
  induction m with
  | zero => intro a b; simp [adPowOp]
  | succ m ih =>
    intro a b
    have hcomm : Uᴴ * matComm H (adPowOp H m O) * U =
        Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * adPowOp H m O * U) -
        (Uᴴ * adPowOp H m O * U) * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
      unfold matComm
      rw [Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      · calc Uᴴ * (H * adPowOp H m O) * U
            = Uᴴ * H * (U * Uᴴ) * adPowOp H m O * U := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = (Uᴴ * H * U) * (Uᴴ * adPowOp H m O * U) := by simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * adPowOp H m O * U) := by rw [hH_diag]
      · calc Uᴴ * (adPowOp H m O * H) * U
            = Uᴴ * adPowOp H m O * (U * Uᴴ) * H * U := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = (Uᴴ * adPowOp H m O * U) * (Uᴴ * H * U) := by simp only [Matrix.mul_assoc]
          _ = (Uᴴ * adPowOp H m O * U) * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by rw [hH_diag]
    change (Uᴴ * matComm H (adPowOp H m O) * U) a b = _
    rw [hcomm, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, ih a b]
    push_cast; rw [pow_succ']; ring

/-- **Concrete Moment–Spectral-Measure Identity**:
`Re (O | (ad_H)^{2n} O)_β^W = ∫ ω, ω^(2n) ∂(concreteWightmanSpectralMeasure hH β O)`. -/
theorem concrete_adPowOp_eq_spectralMeasure_moment {N : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) (n : ℕ) :
    (gibbsWightmanInner (concreteGibbsData hH β) O (adPowOp H (2 * n) O)).re =
      ∫ ω : ℝ, ω ^ (2 * n) ∂(concreteWightmanSpectralMeasure hH β O) := by
  rw [integral_concreteWightmanSpectralMeasure]
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.prop
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.prop
  let B : QubitOp N := Uᴴ * O * U
  have hB_herm : Bᴴ = B := by
    dsimp only [B]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hO.eq,
      Matrix.mul_assoc]
  set Z : ℝ := gibbsPartitionFn hH β
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
  unfold gibbsWightmanInner wightmanInner
  set R := (concreteGibbsData hH β).ρHalf
  set A := adPowOp H (2 * n) O
  have htr : (R * Oᴴ * R * A).trace =
      ((Uᴴ * R * U) * (Uᴴ * Oᴴ * U) * (Uᴴ * R * U) * (Uᴴ * A * U)).trace := by
    have h1 : (R * Oᴴ * R * A).trace = (Uᴴ * (R * Oᴴ * R * A) * U).trace := by
      calc (R * Oᴴ * R * A).trace = (1 * (R * Oᴴ * R * A)).trace := by rw [Matrix.one_mul]
        _ = ((U * Uᴴ) * (R * Oᴴ * R * A)).trace := by rw [hU1]
        _ = (U * (Uᴴ * (R * Oᴴ * R * A))).trace := by simp only [Matrix.mul_assoc]
        _ = ((Uᴴ * (R * Oᴴ * R * A)) * U).trace := Matrix.trace_mul_comm _ _
        _ = (Uᴴ * (R * Oᴴ * R * A) * U).trace := by simp only [Matrix.mul_assoc]
    rw [h1]
    congr 1
    calc Uᴴ * (R * Oᴴ * R * A) * U
        = Uᴴ * R * (U * Uᴴ) * Oᴴ * (U * Uᴴ) * R * (U * Uᴴ) * A * U := by
            rw [hU1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Uᴴ * R * U) * (Uᴴ * Oᴴ * U) * (Uᴴ * R * U) * (Uᴴ * A * U) := by
            simp only [Matrix.mul_assoc]
  rw [htr, hρHalf_eq, hO.eq]
  have hZpos : 0 < Z := gibbsPartitionFn_pos hH β
  have hsqZ : (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) * (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) = ((Z⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hZpos.le]
  have htr2 : ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d * B *
      ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d) * (Uᴴ * A * U)).trace =
      ((Z⁻¹ : ℝ) : ℂ) * ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        d a * B a b * d b * (Uᴴ * A * U) b a := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqZ, Matrix.trace_smul, smul_eq_mul]
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [htr2]
  have hA_ent : ∀ b a : QubitIdx N, (Uᴴ * A * U) b a =
      (((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ) ^ (2 * n)) * B b a := fun b a ↦
    adPowOp_eigen_entry hH O (2 * n) b a
  simp_rw [hA_ent]
  have hsum_eq : ((Z⁻¹ : ℝ) : ℂ) * ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      d a * B a b * d b * ((((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ) ^ (2 * n)) * B b a) =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        ((wightmanSpectralWeight hH β O a b * (hH.eigenvalues a - hH.eigenvalues b) ^ (2 * n) : ℝ) : ℂ) := by
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
    have heven_diff : ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ) ^ (2 * n) =
        (((hH.eigenvalues a - hH.eigenvalues b) ^ (2 * n) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow]
      congr 1
      have : hH.eigenvalues b - hH.eigenvalues a = -(hH.eigenvalues a - hH.eigenvalues b) := by ring
      rw [this, Even.neg_pow (even_two_mul n)]
    have hd_prod : d a * d b = ((Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) : ℝ) : ℂ) := by
      dsimp only [d]
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2; ring
    have hnorm_eq : ‖B a b‖ = ‖((hH.eigenvectorUnitary : QubitOp N)ᴴ * O *
        (hH.eigenvectorUnitary : QubitOp N)) a b‖ := rfl
    rw [heven_diff, show d a * B a b * d b *
        ((((hH.eigenvalues a - hH.eigenvalues b) ^ (2 * n) : ℝ) : ℂ) * B b a) =
        (d a * d b) * (B a b * B b a) *
          (((hH.eigenvalues a - hH.eigenvalues b) ^ (2 * n) : ℝ) : ℂ) by ring,
      hd_prod, hBab, hnorm_eq]
    push_cast; ring
  rw [hsum_eq, Complex.re_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  simp [smul_eq_mul]

/-- Truncation invariance of `(jacobiMat D b ^ k) 0 0` for `k < D`: paths of length `k` from `0`
cannot reach index `≥ k + 1`, so `(jacobiMat D b ^ k) 0 0 = (jacobiMat (k + 1) b ^ k) 0 0`. -/
lemma jacobiMat_pow_zero_trunc_eq {D₁ D₂ : ℕ} (b : ℕ → ℝ) {k : ℕ}
    (h1 : k < D₁) (h2 : k < D₂) :
    (jacobiMat D₁ b ^ k) ⟨0, by omega⟩ ⟨0, by omega⟩ =
      (jacobiMat D₂ b ^ k) ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  have hgen : ∀ m : ℕ, m ≤ k → ∀ (j : ℕ) (hj1 : j < D₁) (hj2 : j < D₂),
      (jacobiMat D₁ b ^ m) ⟨0, by omega⟩ ⟨j, hj1⟩ =
        (jacobiMat D₂ b ^ m) ⟨0, by omega⟩ ⟨j, hj2⟩ := by
    intro m
    induction m with
    | zero =>
      intro _ j hj1 hj2
      simp only [pow_zero, Matrix.one_apply, Fin.ext_iff]
    | succ m ih =>
      intro hm j hj1 hj2
      have hzero_far : ∀ (D : ℕ) (hD : 0 < D) (r : ℕ) (c : Fin D), r < c.1 →
          (jacobiMat D b ^ r) ⟨0, hD⟩ c = 0 := by
        intro D hD r
        induction r with
        | zero =>
          intro c hc
          simp only [pow_zero, Matrix.one_apply, Fin.ext_iff]
          rw [if_neg (by omega)]
        | succ r ihr =>
          intro c hc
          rw [pow_succ, Matrix.mul_apply]
          apply Finset.sum_eq_zero; intro l _
          by_cases hl : r < l.1
          · rw [ihr l hl, zero_mul]
          · have hT0 : jacobiMat D b l c = 0 := by
              unfold jacobiMat; simp only [Matrix.of_apply]
              split_ifs with h1' h2'
              · omega
              · omega
              · rfl
            rw [hT0, mul_zero]
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      have hsum_eq : ∀ (D : ℕ) (hD : k < D) (hjD : j < D),
          ∑ l : Fin D, (jacobiMat D b ^ m) ⟨0, by omega⟩ l * jacobiMat D b l ⟨j, hjD⟩ =
          (if h0 : 0 < j then
            (jacobiMat D b ^ m) ⟨0, by omega⟩ ⟨j - 1, by omega⟩ * b j else 0) +
          (if h1' : j + 1 ≤ m then
            (jacobiMat D b ^ m) ⟨0, by omega⟩ ⟨j + 1, by omega⟩ * b (j + 1) else 0) := by
        intro D hD hjD
        have hstep1 : ∀ l : Fin D,
            (jacobiMat D b ^ m) ⟨0, by omega⟩ l * jacobiMat D b l ⟨j, hjD⟩ =
            (if l.1 + 1 = j then (jacobiMat D b ^ m) ⟨0, by omega⟩ l * b j else 0) +
            (if j + 1 = l.1 then (jacobiMat D b ^ m) ⟨0, by omega⟩ l * b (j + 1) else 0) := by
          intro l
          unfold jacobiMat; simp only [Matrix.of_apply]
          by_cases ha : l.1 + 1 = j
          · have hb : ¬(j + 1 = l.1) := by omega
            have ha' : j = l.1 + 1 := ha.symm
            rw [if_pos ha', if_pos ha, if_neg hb, add_zero, ha]
          · by_cases hb : j + 1 = l.1
            · have ha' : ¬(j = l.1 + 1) := by omega
              have hb' : l.1 = j + 1 := hb.symm
              rw [if_neg ha', if_pos hb', if_neg ha, if_pos hb, zero_add]
            · have ha' : ¬(j = l.1 + 1) := by omega
              have hb' : ¬(l.1 = j + 1) := by omega
              rw [if_neg ha', if_neg hb', if_neg ha, if_neg hb, mul_zero, add_zero]
        simp_rw [hstep1, Finset.sum_add_distrib]
        congr 1
        · by_cases h0 : 0 < j
          · rw [dif_pos h0, Finset.sum_eq_single ⟨j - 1, by omega⟩]
            · rw [if_pos (by dsimp; omega)]
            · intro l _ hl; rw [if_neg (fun h ↦ hl (Fin.ext (by dsimp; omega)))]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [dif_neg h0]; apply Finset.sum_eq_zero; intro l _; rw [if_neg (by omega)]
        · by_cases h1' : j + 1 ≤ m
          · rw [dif_pos h1', Finset.sum_eq_single ⟨j + 1, by omega⟩]
            · rw [if_pos rfl]
            · intro l _ hl; rw [if_neg (fun h ↦ hl (Fin.ext (by dsimp; omega)))]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [dif_neg h1']; apply Finset.sum_eq_zero; intro l _
            by_cases hlj : j + 1 = l.1
            · rw [if_pos hlj, hzero_far D (by omega) m l (by omega), zero_mul]
            · rw [if_neg hlj]
      rw [hsum_eq D₁ h1 hj1, hsum_eq D₂ h2 hj2]
      congr 1
      · split_ifs with h0
        · rw [ih (by omega) (j - 1) (by omega) (by omega)]
        · rfl
      · split_ifs with h1'
        · rw [ih (by omega) (j + 1) (by omega) (by omega)]
        · rfl
  exact hgen k le_rfl 0 (by omega) (by omega)

/-- Continuity of `b ↦ ((jacobiMat D b) ^ m) i j` with respect to pointwise convergence of `b`. -/
lemma tendsto_jacobiMat_pow_entry {D : ℕ} (b_N : ℕ → ℕ → ℝ) (b_inf : ℕ → ℝ)
    (hb_tend : ∀ k : ℕ, Tendsto (fun N ↦ b_N N k) atTop (nhds (b_inf k)))
    (m : ℕ) (i j : Fin D) :
    Tendsto (fun N ↦ ((jacobiMat D (b_N N)) ^ m) i j) atTop
      (nhds (((jacobiMat D b_inf) ^ m) i j)) := by
  induction m generalizing i j with
  | zero => simp only [pow_zero]; exact tendsto_const_nhds
  | succ m ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    refine tendsto_finset_sum _ fun l _ ↦ (ih i l).mul ?_
    unfold jacobiMat; simp only [Matrix.of_apply]
    split_ifs
    · exact hb_tend _
    · exact hb_tend _
    · exact tendsto_const_nhds

/-- **Thermodynamic-Limit Moment Convergence under Uniform Exponential Weight**:
If `μ_N ⇒ μ` weakly on `ℝ` with uniform `∫ cosh(r * ω) dμ_N ≤ M` (`r > 0`), then every even
moment converges: `∫ ω^(2n) dμ_N → ∫ ω^(2n) dμ`. -/
lemma tendsto_even_moment_of_weak_limit_cosh (μ_N : ℕ → Measure ℝ) (μ : Measure ℝ)
    [∀ N, IsFiniteMeasure (μ_N N)] [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(μ_N N)) atTop (nhds (∫ ω, f ω ∂μ)))
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hunif : ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) (μ_N N) ∧
      ∫ ω : ℝ, Real.cosh (r * ω) ∂(μ_N N) ≤ M)
    (n : ℕ) :
    Tendsto (fun N ↦ ∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N)) atTop
      (nhds (∫ ω : ℝ, ω ^ (2 * n) ∂μ)) := by
  have h12 := theorem_1_2a_thermo_limit_eq_1_15_and_rW μ_N μ hweak hr hM hunif
  set C_n : ℝ := 2 * ((2 * n).factorial : ℝ) * (r / 2)⁻¹ ^ (2 * n)
  have hCn_pos : 0 < C_n := by dsimp only [C_n]; positivity
  have hdom_half : ∀ ω : ℝ, ω ^ (2 * n) ≤ C_n * Real.cosh ((r / 2) * ω) := by
    intro ω
    have h1 := pow_even_div_factorial_le_two_cosh ((r / 2) * ω) n
    have hfac_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
    have h2 : ((r / 2) * ω) ^ (2 * n) ≤ 2 * ((2 * n).factorial : ℝ) * Real.cosh ((r / 2) * ω) := by
      have := (div_le_iff₀ hfac_pos).mp h1; linarith
    rw [mul_pow] at h2
    calc ω ^ (2 * n)
        = (r / 2)⁻¹ ^ (2 * n) * ((r / 2) ^ (2 * n) * ω ^ (2 * n)) := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity : r / 2 ≠ 0), one_pow, one_mul]
      _ ≤ (r / 2)⁻¹ ^ (2 * n) * (2 * ((2 * n).factorial : ℝ) * Real.cosh ((r / 2) * ω)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C_n * Real.cosh ((r / 2) * ω) := by dsimp only [C_n]; ring
  have hone_le_cosh : ∀ x : ℝ, 1 ≤ Real.cosh x := fun x ↦ by
    rw [Real.cosh_eq]
    have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [sq_nonneg (Real.exp x - 1), Real.exp_pos x, Real.exp_pos (-x), h1]
  have hcosh_mono : ∀ {x y : ℝ}, |x| ≤ |y| → Real.cosh x ≤ Real.cosh y := by
    intro x y hxy
    have hax : Real.cosh x = Real.cosh |x| := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.cosh_neg]
    have hay : Real.cosh y = Real.cosh |y| := by
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_nonpos hy, Real.cosh_neg]
    rw [hax, hay, Real.cosh_eq, Real.cosh_eq]
    set a := Real.exp |x|
    set b := Real.exp |y|
    have ha1 : 1 ≤ a := Real.one_le_exp (abs_nonneg x)
    have hab : a ≤ b := Real.exp_le_exp.mpr hxy
    have hia : Real.exp (-|x|) = a⁻¹ := Real.exp_neg |x|
    have hib : Real.exp (-|y|) = b⁻¹ := Real.exp_neg |y|
    rw [hia, hib]
    have hapos : 0 < a := by linarith
    have hbpos : 0 < b := by linarith
    have hdiff : 0 ≤ (b - a) * (a * b - 1) := mul_nonneg (by linarith) (by nlinarith)
    have hinv_diff : b + b⁻¹ - (a + a⁻¹) = (b - a) * (a * b - 1) / (a * b) := by
      field_simp [hapos.ne', hbpos.ne']; ring
    have hnonneg : 0 ≤ (b - a) * (a * b - 1) / (a * b) := div_nonneg hdiff (by positivity)
    linarith
  have hcosh_prod : ∀ ω : ℝ, Real.cosh ((r / 2) * ω) * Real.cosh ((r / 2) * ω) ≤ Real.cosh (r * ω) := by
    intro ω
    have h1 : Real.cosh ((r / 2) * ω) * Real.cosh ((r / 2) * ω) =
        (Real.cosh (r * ω) + 1) / 2 := by
      rw [Real.cosh_eq, Real.cosh_eq]
      have ha : Real.exp ((r / 2) * ω) * Real.exp ((r / 2) * ω) = Real.exp (r * ω) := by
        rw [← Real.exp_add]; congr 1; ring
      have hb : Real.exp (-((r / 2) * ω)) * Real.exp (-((r / 2) * ω)) = Real.exp (-(r * ω)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hc : Real.exp ((r / 2) * ω) * Real.exp (-((r / 2) * ω)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [ha, hb, hc]
    linarith [hone_le_cosh (r * ω)]
  have hdom_full : ∀ ω : ℝ, ω ^ (2 * n) ≤ C_n * Real.cosh (r * ω) := fun ω ↦
    le_trans (hdom_half ω) (mul_le_mul_of_nonneg_left
      (by have := hone_le_cosh ((r / 2) * ω); nlinarith [hcosh_prod ω]) hCn_pos.le)
  have hint_pow : ∀ (ν : Measure ℝ), Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) ν →
      Integrable (fun ω : ℝ ↦ ω ^ (2 * n)) ν := fun ν hν ↦
    Integrable.mono' (hν.const_mul C_n) (continuous_pow (2 * n)).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (even_two_mul n) ω)]; exact hdom_full ω)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail_lim : Tendsto (fun R : ℝ ↦ C_n * M / Real.cosh ((r / 2) * R)) atTop (nhds 0) := by
    have hcosh_top : Tendsto (fun R : ℝ ↦ Real.cosh ((r / 2) * R)) atTop atTop := by
      have hexp : Tendsto (fun R : ℝ ↦ Real.exp ((r / 2) * R) / 2) atTop atTop :=
        (Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (by positivity : 0 < r / 2) tendsto_id)).atTop_div_const (by norm_num)
      refine tendsto_atTop_mono (fun R ↦ ?_) hexp
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-((r / 2) * R))]
    exact tendsto_const_nhds.div_atTop hcosh_top
  obtain ⟨R, hR_pos, hR_small⟩ : ∃ R : ℝ, 0 < R ∧ C_n * M / Real.cosh ((r / 2) * R) < ε / 3 := by
    have h1 := (Metric.tendsto_atTop.mp htail_lim) (ε / 3) (by linarith)
    rcases h1 with ⟨R₀, hR₀⟩
    refine ⟨max R₀ 1, by linarith [le_max_right R₀ 1], ?_⟩
    have h := hR₀ (max R₀ 1) (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    exact h
  let χ : ℝ → ℝ := fun ω ↦ max 0 (min 1 (R + 1 - |ω|))
  have hχ_cont : Continuous χ := by dsimp only [χ]; fun_prop
  have hχ_01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1 := fun ω ↦
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hχ_one : ∀ ω, |ω| ≤ R → χ ω = 1 := fun ω hω ↦ by
    dsimp only [χ]
    have : min 1 (R + 1 - |ω|) = 1 := min_eq_left (by linarith)
    rw [this]; norm_num
  have hχ_supp : HasCompactSupport (fun ω : ℝ ↦ χ ω * ω ^ (2 * n)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(R + 1)) (b := R + 1)) ?_
    intro ω hω
    simp only [Function.mem_support, ne_eq, Set.mem_Icc] at hω ⊢
    by_contra hnot
    have hgt : R + 1 < |ω| := by
      rw [lt_abs]; push Not at hnot
      rcases lt_or_ge ω (-(R + 1)) with h1 | h1
      · right; linarith
      · left; exact hnot h1
    have hχ0 : χ ω = 0 := by
      dsimp only [χ]
      have : min 1 (R + 1 - |ω|) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
      exact max_eq_left this
    exact hω (by simp [hχ0])
  have htail_bound : ∀ (ν : Measure ℝ), Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) ν →
      ∫ ω : ℝ, Real.cosh (r * ω) ∂ν ≤ M →
      |∫ ω : ℝ, ω ^ (2 * n) ∂ν - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂ν| ≤
        C_n * M / Real.cosh ((r / 2) * R) := by
    intro ν hν_int hν_le
    have hχ_int : Integrable (fun ω : ℝ ↦ χ ω * ω ^ (2 * n)) ν := by
      refine Integrable.mono' (hint_pow ν hν_int)
        (hχ_cont.mul (continuous_pow (2 * n))).aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ_01 ω).1,
        abs_of_nonneg (Even.pow_nonneg (even_two_mul n) ω)]
      exact mul_le_of_le_one_left (Even.pow_nonneg (even_two_mul n) ω) (hχ_01 ω).2
    rw [← integral_sub (hint_pow ν hν_int) hχ_int]
    have hdiff_nn : ∀ ω, 0 ≤ ω ^ (2 * n) - χ ω * ω ^ (2 * n) := fun ω ↦ by
      have := Even.pow_nonneg (even_two_mul n) ω
      have := (hχ_01 ω).2
      nlinarith
    have hdiff_le : ∀ ω, ω ^ (2 * n) - χ ω * ω ^ (2 * n) ≤
        (C_n / Real.cosh ((r / 2) * R)) * Real.cosh (r * ω) := by
      intro ω
      by_cases hω : |ω| ≤ R
      · rw [hχ_one ω hω, one_mul, sub_self]; positivity
      · push Not at hω
        have hcosh_le : Real.cosh ((r / 2) * R) ≤ Real.cosh ((r / 2) * ω) :=
          hcosh_mono (by
            rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < r / 2), abs_of_pos hR_pos]
            exact mul_le_mul_of_nonneg_left hω.le (by positivity))
        have h1 : ω ^ (2 * n) - χ ω * ω ^ (2 * n) ≤ ω ^ (2 * n) := by
          have := mul_nonneg (hχ_01 ω).1 (Even.pow_nonneg (even_two_mul n) ω); linarith
        have h2 : Real.cosh ((r / 2) * ω) ≤ Real.cosh (r * ω) / Real.cosh ((r / 2) * R) := by
          rw [le_div_iff₀ (Real.cosh_pos _)]
          exact le_trans (mul_le_mul_of_nonneg_left hcosh_le (Real.cosh_pos _).le) (hcosh_prod ω)
        calc ω ^ (2 * n) - χ ω * ω ^ (2 * n)
            ≤ ω ^ (2 * n) := h1
          _ ≤ C_n * Real.cosh ((r / 2) * ω) := hdom_half ω
          _ ≤ C_n * (Real.cosh (r * ω) / Real.cosh ((r / 2) * R)) :=
                mul_le_mul_of_nonneg_left h2 hCn_pos.le
          _ = (C_n / Real.cosh ((r / 2) * R)) * Real.cosh (r * ω) := by ring
    have hint_nn : 0 ≤ ∫ ω : ℝ, (ω ^ (2 * n) - χ ω * ω ^ (2 * n)) ∂ν :=
      integral_nonneg hdiff_nn
    rw [abs_of_nonneg hint_nn]
    calc ∫ ω : ℝ, (ω ^ (2 * n) - χ ω * ω ^ (2 * n)) ∂ν
        ≤ ∫ ω : ℝ, (C_n / Real.cosh ((r / 2) * R)) * Real.cosh (r * ω) ∂ν :=
          integral_mono ((hint_pow ν hν_int).sub hχ_int) (hν_int.const_mul _) hdiff_le
      _ = (C_n / Real.cosh ((r / 2) * R)) * ∫ ω : ℝ, Real.cosh (r * ω) ∂ν := integral_const_mul _ _
      _ ≤ (C_n / Real.cosh ((r / 2) * R)) * M := mul_le_mul_of_nonneg_left hν_le (by positivity)
      _ = C_n * M / Real.cosh ((r / 2) * R) := by ring
  have hweak_χ := hweak (fun ω ↦ χ ω * ω ^ (2 * n))
    (hχ_cont.mul (continuous_pow (2 * n))) hχ_supp
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hweak_χ) (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have hmid := hN₀ N hN
  rw [Real.dist_eq] at hmid ⊢
  have htN := htail_bound (μ_N N) (hunif N).1 (hunif N).2
  have htμ := htail_bound μ h12.1 h12.2.1
  calc |∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, ω ^ (2 * n) ∂μ|
      = |(∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N)) +
         (∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ) -
         (∫ ω : ℝ, ω ^ (2 * n) ∂μ - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ)| := by ring_nf
    _ ≤ |∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N)| +
        |∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ| +
        |∫ ω : ℝ, ω ^ (2 * n) ∂μ - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ| := by
          have h1 := abs_sub
            ((∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N)) +
             (∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ))
            (∫ ω : ℝ, ω ^ (2 * n) ∂μ - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ)
          have h2 := abs_add_le
            (∫ ω : ℝ, ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N))
            (∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂(μ_N N) - ∫ ω : ℝ, χ ω * ω ^ (2 * n) ∂μ)
          linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- **Concrete-to-Thermodynamic Lanczos Moment Bridge**:
Wires finite-volume Lanczos convergence `lanczosCoeff (H_N, O_N) k → b_inf k` and weak convergence
`concreteWightmanSpectralMeasure (H_N, O_N) ⇒ μ` (with uniform `cosh(r * ω)` bound) directly to
`((jacobiMat (2 * n + 1) b_inf) ^ (2 * n)) 0 0 = ∫ ω, ω^(2n) ∂μ`. -/
theorem thermo_limit_lanczos_moment_eq_spectralMeasure
    (H O : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H N).IsHermitian) (hO : ∀ N, (O N).IsHermitian)
    (β : ℝ)
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O N) = 1)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(concreteWightmanSpectralMeasure (hH N) β (O N)))
        atTop (nhds (∫ ω, f ω ∂μ)))
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hunif : ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh (r * ω))
        (concreteWightmanSpectralMeasure (hH N) β (O N)) ∧
      ∫ ω : ℝ, Real.cosh (r * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (O N)) ≤ M)
    (b_inf : ℕ → ℝ)
    (hb_tend : ∀ k : ℕ, Tendsto
      (fun N ↦ lanczosCoeff (concreteGibbsData (hH N) β) (H N) (O N) k) atTop (nhds (b_inf k)))
    (n : ℕ) :
    ((jacobiMat (2 * n + 1) b_inf) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
      ∫ ω : ℝ, ω ^ (2 * n) ∂μ := by
  have htend_lhs := tendsto_jacobiMat_pow_entry (D := 2 * n + 1)
    (fun N k ↦ lanczosCoeff (concreteGibbsData (hH N) β) (H N) (O N) k) b_inf hb_tend
    (2 * n) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
  have htend_rhs := tendsto_even_moment_of_weak_limit_cosh
    (fun N ↦ concreteWightmanSpectralMeasure (hH N) β (O N)) μ hweak hr hM hunif n
  have heq_ev : (fun N ↦ ((jacobiMat (2 * n + 1)
      (lanczosCoeff (concreteGibbsData (hH N) β) (H N) (O N))) ^ (2 * n))
      ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩) =ᶠ[atTop]
      fun N ↦ ∫ ω : ℝ, ω ^ (2 * n) ∂(concreteWightmanSpectralMeasure (hH N) β (O N)) := by
    filter_upwards [eventually_ge_atTop (2 * n + 1)] with N hN
    have h4N : 2 * n + 1 ≤ 4 ^ N := by
      have h1 : N < 4 ^ N := Nat.lt_pow_self (by norm_num : 1 < 4)
      omega
    have hmom_N := concrete_lanczos_moment_eq_jacobi (hH N) (hO N) β (hOnorm N) (D := 4 ^ N) le_rfl (2 * n)
    have hspec_N := concrete_adPowOp_eq_spectralMeasure_moment (hH N) (hO N) β n
    have htrunc := jacobiMat_pow_zero_trunc_eq
      (lanczosCoeff (concreteGibbsData (hH N) β) (H N) (O N))
      (D₁ := 2 * n + 1) (D₂ := 4 ^ N) (k := 2 * n) (by omega) (by omega)
    rw [htrunc, ← hmom_N, hspec_N]
  exact tendsto_nhds_unique (htend_lhs.congr' heq_ev) htend_rhs

/-- **Holomorphic Cauchy–Hadamard Even Moment Upper Bound**:
If `F : ℂ → ℂ` is holomorphic on `{|Im z| < R}` (`R > 0`) and agrees on `ℝ` with
`t ↦ ∫ ω, exp(i t ω) dμ` (with `iteratedDeriv (2n) F 0 = (-1)^n ∫ ω^(2n) dμ`),
then for every `0 < ρ < R` there exists `M_ρ > 0` such that for all `n : ℕ`:
`∫ ω, ω^(2n) dμ ≤ (2n)! * M_ρ * ρ⁻¹ ^ (2n)`. -/
theorem holoStrip_even_moment_bound (μ : Measure ℝ) {R ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < R)
    (F : ℂ → ℂ) (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_deriv : ∀ n : ℕ, iteratedDeriv (2 * n) F 0 =
      ((-1 : ℂ) ^ n) * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ)) :
    ∃ M_ρ > 0, ∀ n : ℕ,
      ∫ ω : ℝ, ω ^ (2 * n) ∂μ ≤ ((2 * n).factorial : ℝ) * M_ρ * ρ⁻¹ ^ (2 * n) := by
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ {z : ℂ | |z.im| < R} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact lt_of_le_of_lt (le_trans (Complex.abs_im_le_norm z) hz) hρ_lt
  have hcont_sphere : ContinuousOn (fun z : ℂ ↦ ‖F z‖) (Metric.sphere 0 ρ) :=
    (hF_holo.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub)).norm
  obtain ⟨z_max, _, hz_max⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hρ_pos.le) hcont_sphere
  set M_ρ : ℝ := ‖F z_max‖ + 1
  have hM_pos : 0 < M_ρ := by dsimp only [M_ρ]; positivity
  have hbound_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M_ρ := fun z hz ↦ by
    have hle : ‖F z‖ ≤ ‖F z_max‖ := hz_max hz
    dsimp only [M_ρ]; linarith
  have hcm_cont : Continuous (fun θ : ℝ ↦ circleMap (0 : ℂ) ρ θ) := continuous_circleMap 0 ρ
  have hdcm_cont : Continuous (fun θ : ℝ ↦ deriv (circleMap (0 : ℂ) ρ) θ) := by
    have : (fun θ : ℝ ↦ deriv (circleMap (0 : ℂ) ρ) θ) =
        fun θ ↦ circleMap 0 ρ θ * Complex.I := funext fun θ ↦ deriv_circleMap 0 ρ θ
    rw [this]; exact hcm_cont.mul continuous_const
  have hFcm_cont : Continuous (fun θ : ℝ ↦ F (circleMap (0 : ℂ) ρ θ)) :=
    (hF_holo.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub)).comp_continuous
      hcm_cont (fun θ ↦ circleMap_mem_sphere 0 hρ_pos.le θ)
  have hcauchy_formula : ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
      iteratedDeriv k F w =
        ((k.factorial : ℝ) : ℂ) * (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap (0 : ℂ) ρ) θ *
              ((circleMap (0 : ℂ) ρ θ - w) ^ (k + 1))⁻¹ * F (circleMap (0 : ℂ) ρ θ) := by
    intro k
    induction k with
    | zero =>
      intro w hw
      rw [iteratedDeriv_zero]
      have hc := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (f := F) (c := (0 : ℂ)) (R := ρ) (w := w) (s := ∅) Set.countable_empty hw
        (hF_holo.continuousOn.mono hsub) (fun z hz ↦ (hF_holo.mono (Metric.ball_subset_closedBall.trans hsub)) z hz.1)
      rw [← hc]
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_one, smul_eq_mul, circleIntegral]
      congr 1; apply intervalIntegral.integral_congr; intro θ _; ring
    | succ k ih =>
      intro w hw
      have hev : iteratedDeriv k F =ᶠ[nhds w]
          fun u ↦ ((k.factorial : ℝ) : ℂ) * (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              deriv (circleMap (0 : ℂ) ρ) θ *
                ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 1))⁻¹ * F (circleMap (0 : ℂ) ρ θ) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball 0 ρ, Metric.isOpen_ball.mem_nhds hw, fun u hu ↦ ih u hu⟩
      rw [iteratedDeriv_succ, hev.deriv_eq]
      set δ : ℝ := (ρ - ‖w‖) / 2
      have hw_norm : ‖w‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hw
      have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
      have hdist_lb : ∀ u ∈ Metric.ball w δ, ∀ θ : ℝ, δ ≤ ‖circleMap (0 : ℂ) ρ θ - u‖ := by
        intro u hu θ
        have huw : ‖u - w‖ < δ := by simpa [Metric.mem_ball, Complex.dist_eq] using hu
        have hu_norm : ‖u‖ ≤ ‖w‖ + δ := by
          have := norm_add_le (u - w) w; simp only [sub_add_cancel] at this; linarith
        have hcm : ‖circleMap (0 : ℂ) ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ_pos]
        have htri := norm_sub_norm_le (circleMap (0 : ℂ) ρ θ) u
        dsimp only [δ] at hu_norm ⊢; linarith
      let G : ℂ → ℝ → ℂ := fun u θ ↦
        deriv (circleMap (0 : ℂ) ρ) θ * ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 1))⁻¹ *
          F (circleMap (0 : ℂ) ρ θ)
      let G' : ℂ → ℝ → ℂ := fun u θ ↦
        ((k + 1 : ℕ) : ℂ) * deriv (circleMap (0 : ℂ) ρ) θ *
          ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 2))⁻¹ * F (circleMap (0 : ℂ) ρ θ)
      have hG_cont : ∀ u ∈ Metric.ball w δ, Continuous (G u) := fun u hu ↦ by
        dsimp only [G]
        refine (hdcm_cont.mul (((hcm_cont.sub continuous_const).pow (k + 1)).inv₀ fun θ ↦ ?_)).mul hFcm_cont
        exact pow_ne_zero _ (norm_ne_zero_iff.mp (by linarith [hdist_lb u hu θ]))
      have hG'_cont : Continuous (G' w) := by
        dsimp only [G']
        refine ((continuous_const.mul hdcm_cont).mul
          (((hcm_cont.sub continuous_const).pow (k + 2)).inv₀ fun θ ↦ ?_)).mul hFcm_cont
        exact pow_ne_zero _ (norm_ne_zero_iff.mp (by linarith [hdist_lb w (Metric.mem_ball_self hδ_pos) θ]))
      have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := G) (F' := G') (s := Metric.ball w δ) (x₀ := w)
        (a := (0 : ℝ)) (b := 2 * Real.pi)
        (bound := fun _ : ℝ ↦ ((k + 1 : ℕ) : ℝ) * ρ * (δ ^ (k + 2))⁻¹ * M_ρ)
        (Metric.ball_mem_nhds w hδ_pos)
        (by filter_upwards [Metric.ball_mem_nhds w hδ_pos] with u hu; exact (hG_cont u hu).aestronglyMeasurable)
        ((hG_cont w (Metric.mem_ball_self hδ_pos)).intervalIntegrable 0 (2 * Real.pi))
        hG'_cont.aestronglyMeasurable
        (Eventually.of_forall fun θ _ u hu ↦ by
          dsimp only [G']
          have hd_norm : ‖deriv (circleMap (0 : ℂ) ρ) θ‖ = ρ := by
            rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ_pos]
          have hF_le : ‖F (circleMap (0 : ℂ) ρ θ)‖ ≤ M_ρ :=
            hbound_sphere _ (circleMap_mem_sphere 0 hρ_pos.le θ)
          have hinv_le : ‖((circleMap (0 : ℂ) ρ θ - u) ^ (k + 2))⁻¹‖ ≤ (δ ^ (k + 2))⁻¹ := by
            rw [norm_inv, norm_pow]
            exact inv_anti₀ (pow_pos hδ_pos _) (pow_le_pow_left₀ hδ_pos.le (hdist_lb u hu θ) _)
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hd_norm]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv_le (by positivity)) hF_le (norm_nonneg _) (by positivity))
        intervalIntegrable_const
        (Eventually.of_forall fun θ _ u hu ↦ by
          dsimp only [G, G']
          have hne : circleMap (0 : ℂ) ρ θ - u ≠ 0 :=
            norm_ne_zero_iff.mp (by linarith [hdist_lb u hu θ])
          have h1 : HasDerivAt (fun x : ℂ ↦ circleMap (0 : ℂ) ρ θ - x) (-1) u := by
            simpa using (hasDerivAt_const u (circleMap (0 : ℂ) ρ θ)).sub (hasDerivAt_id u)
          have h2 : HasDerivAt (fun x : ℂ ↦ (circleMap (0 : ℂ) ρ θ - x) ^ (k + 1))
              (((k + 1 : ℕ) : ℂ) * (circleMap (0 : ℂ) ρ θ - u) ^ k * (-1)) u :=
            h1.fun_pow (k + 1)
          have h3 := h2.inv (pow_ne_zero (k + 1) hne)
          have h4 := (h3.const_mul (deriv (circleMap (0 : ℂ) ρ) θ)).mul_const (F (circleMap (0 : ℂ) ρ θ))
          convert h4 using 1
          have hpow_alg : -(((k + 1 : ℕ) : ℂ) * (circleMap (0 : ℂ) ρ θ - u) ^ k * (-1)) /
              ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 1)) ^ 2 =
              ((k + 1 : ℕ) : ℂ) * ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 2))⁻¹ := by
            have hne1 : (circleMap (0 : ℂ) ρ θ - u) ^ (k + 1) ≠ 0 := pow_ne_zero _ hne
            have hne2 : (circleMap (0 : ℂ) ρ θ - u) ^ (k + 2) ≠ 0 := pow_ne_zero _ hne
            field_simp [hne, hne1, hne2]
            ring
          calc ((k + 1 : ℕ) : ℂ) * deriv (circleMap (0 : ℂ) ρ) θ *
                ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 2))⁻¹ * F (circleMap (0 : ℂ) ρ θ)
              = deriv (circleMap (0 : ℂ) ρ) θ *
                (((k + 1 : ℕ) : ℂ) * ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 2))⁻¹) *
                F (circleMap (0 : ℂ) ρ θ) := by ring
            _ = deriv (circleMap (0 : ℂ) ρ) θ *
                (-(((k + 1 : ℕ) : ℂ) * (circleMap (0 : ℂ) ρ θ - u) ^ k * (-1)) /
                  ((circleMap (0 : ℂ) ρ θ - u) ^ (k + 1)) ^ 2) *
                F (circleMap (0 : ℂ) ρ θ) := by rw [← hpow_alg])
      have htot := hparam.2.const_mul (((k.factorial : ℝ) : ℂ) * (2 * Real.pi * Complex.I : ℂ)⁻¹)
      rw [htot.deriv]
      dsimp only [G']
      have hpull : ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((k + 1 : ℕ) : ℂ) * deriv (circleMap (0 : ℂ) ρ) θ *
            ((circleMap (0 : ℂ) ρ θ - w) ^ (k + 2))⁻¹ * F (circleMap (0 : ℂ) ρ θ) =
          ((k + 1 : ℕ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap (0 : ℂ) ρ) θ *
              ((circleMap (0 : ℂ) ρ θ - w) ^ (k + 2))⁻¹ * F (circleMap (0 : ℂ) ρ θ) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr; intro θ _; ring
      rw [hpull, Nat.factorial_succ, Nat.cast_mul, Complex.ofReal_mul]
      push_cast; ring
  refine ⟨M_ρ, hM_pos, fun n ↦ ?_⟩
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ_pos
  have hc := hcauchy_formula (2 * n) 0 h0_mem
  have hnorm_lhs : ‖iteratedDeriv (2 * n) F 0‖ = ∫ ω : ℝ, ω ^ (2 * n) ∂μ := by
    rw [hF_deriv n, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun ω ↦ Even.pow_nonneg (even_two_mul n) ω)]
  rw [← hnorm_lhs, hc, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _),
    norm_inv]
  have h2pi_norm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi_norm]
  have hint_le : ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap (0 : ℂ) ρ) θ *
        ((circleMap (0 : ℂ) ρ θ - 0) ^ (2 * n + 1))⁻¹ * F (circleMap (0 : ℂ) ρ θ)‖ ≤
      (ρ * (ρ ^ (2 * n + 1))⁻¹ * M_ρ) * (2 * Real.pi) := by
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (C := ρ * (ρ ^ (2 * n + 1))⁻¹ * M_ρ)
      (fun θ _ ↦ by
        have hd_norm : ‖deriv (circleMap (0 : ℂ) ρ) θ‖ = ρ := by
          rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ_pos]
        have hcm_norm : ‖circleMap (0 : ℂ) ρ θ - 0‖ = ρ := by
          rw [sub_zero, norm_circleMap_zero, abs_of_pos hρ_pos]
        have hF_le : ‖F (circleMap (0 : ℂ) ρ θ)‖ ≤ M_ρ :=
          hbound_sphere _ (circleMap_mem_sphere 0 hρ_pos.le θ)
        rw [norm_mul, norm_mul, hd_norm, norm_inv, norm_pow, hcm_norm]
        exact mul_le_mul_of_nonneg_left hF_le (by positivity))
    rwa [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbd
  calc ((2 * n).factorial : ℝ) * (2 * Real.pi)⁻¹ *
        ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap (0 : ℂ) ρ) θ *
            ((circleMap (0 : ℂ) ρ θ - 0) ^ (2 * n + 1))⁻¹ * F (circleMap (0 : ℂ) ρ θ)‖
      ≤ ((2 * n).factorial : ℝ) * (2 * Real.pi)⁻¹ *
          ((ρ * (ρ ^ (2 * n + 1))⁻¹ * M_ρ) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = ((2 * n).factorial : ℝ) * M_ρ * ρ⁻¹ ^ (2 * n) := by
        rw [pow_succ, mul_inv, inv_pow]
        field_simp [Real.pi_pos.ne', hρ_pos.ne']

/-- **Theorem 1.2(b) from Holomorphic Strip Half-Width `holoStripHalfWidth μ` (Eq. 1.16)**:
For ANY `R > 0` where the holomorphic extension `F` on `{|Im z| < R}` has even derivatives
`iteratedDeriv (2n) F 0 = (-1)^n μ_{2n}` and `b` matches the moments of `μ`:
`2 * Filter.liminf (fun n ↦ b n / (n : ℝ)) atTop ≤ Real.pi / R`. -/
theorem theorem_1_2b_from_holoStripHalfWidth (μ : Measure ℝ) {R : ℝ} (b : ℕ → ℝ)
    (hR_pos : 0 < R)
    (F : ℂ → ℂ) (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_deriv : ∀ n : ℕ, iteratedDeriv (2 * n) F 0 =
      ((-1 : ℂ) ^ n) * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ))
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / R := by
  have hle_ρ : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / ρ := by
    intro ρ hρ_pos hρ_lt
    rcases holoStrip_even_moment_bound μ hρ_pos hρ_lt F hF_holo hF_deriv with ⟨M_ρ, hM_pos, hM_ub⟩
    have hmom_ub : ∀ n : ℕ,
        ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
          2 * ((2 * n).factorial : ℝ) * ρ⁻¹ ^ (2 * n) * M_ρ := by
      intro n; rw [hmom_eq n]
      have h1 := hM_ub n
      have hnn : 0 ≤ ((2 * n).factorial : ℝ) * M_ρ * ρ⁻¹ ^ (2 * n) := by positivity
      linarith
    have hlim := theorem_1_2b_liminf_unconditional b hρ_pos hM_pos hb_pos hmom_ub
    have h2 : 2 * (Real.pi / (2 * ρ)) = Real.pi / ρ := by field_simp [hρ_pos.ne']
    linarith
  let seq : ℕ → ℝ := fun m ↦ R - R / ((m : ℝ) + 2)
  have hseq_tend : Tendsto seq atTop (nhds R) := by
    have hdiv : Tendsto (fun m : ℕ ↦ R / ((m : ℝ) + 2)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [seq] using tendsto_const_nhds.sub hdiv
  have hfn_tend : Tendsto (fun m : ℕ ↦ Real.pi / seq m) atTop (nhds (Real.pi / R)) :=
    (continuousAt_const.div continuousAt_id hR_pos.ne').tendsto.comp hseq_tend
  refine ge_of_tendsto hfn_tend ?_
  filter_upwards with m
  have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hseq_pos : 0 < seq m := by
    dsimp only [seq]
    have h1 : R / ((m : ℝ) + 2) ≤ R / 2 := div_le_div_of_nonneg_left hR_pos.le (by norm_num) hm2
    linarith
  have hseq_lt : seq m < R := by
    dsimp only [seq]; linarith [div_pos hR_pos (by linarith : (0 : ℝ) < (m : ℝ) + 2)]
  exact hle_ρ (seq m) hseq_pos hseq_lt

end ConcreteMomentsAndHolomorphicCauchyHadamard

end KrylovChaos
