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
# Concrete Wightman Spectral Measure, Holomorphic Strip Half-Width, and Thermodynamic-Limit OTOC Analyticity

Bridges the concrete `QubitOp N` framework directly to `Measure ℝ`, holomorphic strip half-widths,
Lanczos moments, thermodynamic-limit OTOC analyticity, and high-temperature chaos bounds:
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
5. `differentiable_concreteOTOC`, `concreteWightmanNormAtShift_eq_autocorr`, and
   `theorem_1_2c_thermo_limit_otoc_strip`: assemble end-to-end thermodynamic-limit OTOC holomorphy
   on `{|Im z| < β/4 + κ/2}` (and general compactly bounded strips) with `liminf` Eq. (1.17) RHS.
6. `theorem_1_3c_concrete_family_complete`: discharges the KMS rate bound in Theorem 1.3(c)
   directly from the concrete `r`-local family `(H_N, O_N)`.
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
  exact ENNReal.sum_lt_top.mpr fun a _ ↦ ENNReal.sum_lt_top.mpr fun b _ ↦ ENNReal.ofReal_ne_top

/-- Every function `f : ℝ → E` is integrable with respect to the finite atomic measure
`concreteWightmanSpectralMeasure hH β W`. -/
lemma integrable_concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (concreteWightmanSpectralMeasure hH β W) := by
  unfold concreteWightmanSpectralMeasure
  refine integrable_finset_sum_measure.mpr fun a _ ↦
    integrable_finset_sum_measure.mpr fun b _ ↦ ?_
  exact (integrable_dirac (by simp : ‖f (hH.eigenvalues a - hH.eigenvalues b)‖ₑ ≠ ⊤)).smul_measure
    ENNReal.ofReal_ne_top

/-- Exact Bochner integral formula against `concreteWightmanSpectralMeasure hH β W`. -/
lemma integral_concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
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
      exact (integrable_dirac (by simp : ‖f (hH.eigenvalues a - hH.eigenvalues b)‖ₑ ≠ ⊤)).smul_measure
        ENNReal.ofReal_ne_top
  · intro a _
    refine integrable_finset_sum_measure.mpr fun b _ ↦ ?_
    exact (integrable_dirac (by simp : ‖f (hH.eigenvalues a - hH.eigenvalues b)‖ₑ ≠ ⊤)).smul_measure
      ENNReal.ofReal_ne_top

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
      have hκ'0_eq : κ' = 0 := by linarith
      have hM_eq : M = 2 * C_W ^ 2 := by
        dsimp only [M]; rw [hκ'0_eq, zero_div, sub_zero, Real.one_rpow, mul_one]
      have hlint : ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * (0 : ℝ) * ω)) ∂μ ≤ ENNReal.ofReal M := by
        refine lintegral_cosh_le_of_weak_limit (fun N ↦ concreteWightmanSpectralMeasure (hH N) β (W N))
          μ hweak hM_nn fun N ↦ ?_
        have h1 := (hunif N).2
        rw [hzero] at h1
        have heq : (fun ω : ℝ ↦ Real.cosh (2 * (0 : ℝ) * ω)) = fun _ ↦ (1 : ℝ) := by
          funext ω; simp
        simp_rw [heq]
        have hnn : 0 ≤ᵐ[concreteWightmanSpectralMeasure (hH N) β (W N)] (fun _ : ℝ ↦ (1 : ℝ)) :=
          Eventually.of_forall fun _ ↦ zero_le_one
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_const 1) hnn]
        simpa [hzero] using ENNReal.ofReal_le_ofReal h1
      have hrew : (fun ω : ℝ ↦ Real.cosh (2 * (0 : ℝ) * ω)) = fun ω ↦ Real.cosh ((β / 2 + κ') * ω) := by
        funext ω; rw [hzero]; simp
      rw [hrew] at hlint
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
  let d : QubitIdx N → ℂ := fun i ↦ ((Real.exp (-(β * hH.eigenvalues i / 2)) : ℝ) : ℂ)
  have hρHalf_eq : Uᴴ * (concreteGibbsData hH β).ρHalf * U =
      (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d := by
    change Uᴴ * gibbsRhoHalf hH β * U = _
    unfold gibbsRhoHalf hermFunc
    calc Uᴴ * (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • (U * Matrix.diagonal d * Uᴴ) * U
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
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsqZ, Matrix.trace_smul,
      smul_eq_mul]
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [htr2]
  simp only [A, adPowOp_eigen_entry hH O (2 * n)]
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
      rw [hba, Complex.mul_conj', Complex.ofReal_pow]
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
  have hgen : ∀ m : ℕ, m ≤ k → ∀ j : ℕ, j < D₁ → j < D₂ →
      (jacobiMat D₁ b ^ m) ⟨0, by omega⟩ ⟨j, ‹j < D₁›⟩ =
        (jacobiMat D₂ b ^ m) ⟨0, by omega⟩ ⟨j, ‹j < D₂›⟩ := by
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
          · have hnotadj : ¬(l.1 + 1 = c.1 ∨ c.1 + 1 = l.1) := by omega
            have hT0 : jacobiMat D b l c = 0 := by
              unfold jacobiMat; simp only [Matrix.of_apply]
              split_ifs <;> omega
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
            simp [ha, hb]
          · by_cases hb : j + 1 = l.1
            · simp [ha, hb]
            · simp [ha, hb]
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
            · rw [if_pos (by dsimp; omega)]
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
      ∫ ω : ℝ, Real.cosh (r * ω) ∂(μ_N N) ≤ M) (n : ℕ) :
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
  have hcosh_prod : ∀ ω : ℝ, Real.cosh ((r / 2) * ω) * Real.cosh ((r / 2) * ω) ≤ Real.cosh (r * ω) := by
    intro ω
    have h1 : Real.cosh ((r / 2) * ω) * Real.cosh ((r / 2) * ω) =
        (Real.cosh (r * ω) + 1) / 2 := by
      rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
      have ha : Real.exp ((r / 2) * ω) * Real.exp ((r / 2) * ω) = Real.exp (r * ω) := by
        rw [← Real.exp_add]; congr 1; ring
      have hb : Real.exp (-((r / 2) * ω)) * Real.exp (-((r / 2) * ω)) = Real.exp (-(r * ω)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hc : Real.exp ((r / 2) * ω) * Real.exp (-((r / 2) * ω)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [ha, hb, hc]
    linarith [Real.one_le_cosh (r * ω)]
  have hdom_full : ∀ ω : ℝ, ω ^ (2 * n) ≤ C_n * Real.cosh (r * ω) := fun ω ↦
    le_trans (hdom_half ω) (mul_le_mul_of_nonneg_left
      (by have := Real.one_le_cosh ((r / 2) * ω); nlinarith [hcosh_prod ω]) hCn_pos.le)
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
  have hχ_cont : Continuous χ := by
    dsimp only [χ]; fun_prop
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
        have hcosh_le : Real.cosh ((r / 2) * R) ≤ Real.cosh ((r / 2) * ω) := by
          rw [← Real.cosh_abs ((r / 2) * ω), abs_mul, abs_of_pos (by positivity : 0 < r / 2)]
          exact Real.cosh_le_cosh.mpr (by
            rw [abs_of_pos (by positivity : 0 < r / 2 * R), abs_of_pos (by positivity : 0 < r / 2 * |ω|)]
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
  exact tendsto_nhds_unique (htend_lhs.congr' heq_ev) htend_rhs |>.symm

/-- **Holomorphic Cauchy–Hadamard Even Moment Upper Bound**:
If `F : ℂ → ℂ` is holomorphic on `{|Im z| < R}` (`R > 0`) and agrees on `ℝ` with
`t ↦ ∫ ω, exp(i t ω) dμ` (with `∫ ω^(2n) dμ` finite and `iteratedDeriv (2n) F 0 = (-1)^n ∫ ω^(2n) dμ`),
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
  refine ⟨M_ρ, hM_pos, fun n ↦ ?_⟩
  have hdiff_ball : DiffContOnCl ℂ F (Metric.ball 0 ρ) := by
    rw [Metric.closure_ball (0 : ℂ) hρ_pos.ne']
    exact (hF_holo.mono hsub).diffContOnCl_ball (by rw [Metric.closure_ball (0 : ℂ) hρ_pos.ne'])
  have hbound_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M_ρ := fun z hz ↦ by
    have := hz_max hz; dsimp only [M_ρ]; linarith
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    hρ_pos hdiff_ball hbound_sphere (2 * n)
  rw [hF_deriv n, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun ω ↦ Even.pow_nonneg (even_two_mul n) ω)] at hcauchy
  calc ∫ ω : ℝ, ω ^ (2 * n) ∂μ
      ≤ ((2 * n).factorial : ℝ) * M_ρ / ρ ^ (2 * n) := by
          simpa [mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv] using hcauchy
    _ = ((2 * n).factorial : ℝ) * M_ρ * ρ⁻¹ ^ (2 * n) := by rw [div_eq_mul_inv, inv_pow]

/-- **Theorem 1.2(b) from Holomorphic Strip Half-Width `holoStripHalfWidth μ` (Eq. 1.16)**:
For ANY `R > 0` with `(R : EReal) ≤ holoStripHalfWidth μ` (in particular `R = β/2 + κ`) where the
holomorphic extension `F` on `{|Im z| < R}` has even derivatives `iteratedDeriv (2n) F 0 = (-1)^n μ_{2n}`
and `b` matches the moments of `μ`:
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

section ConcreteOTOCAnalyticityAndTheorem13c

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
  have hevol_diff : ∀ i j, Differentiable ℂ (fun z ↦ (heisenbergEvol hH z W) i j) := by
    intro i j
    unfold heisenbergEvol
    refine hmat_mul_diff _ _ (hmat_mul_diff _ _ (fun a b ↦ ?_) (fun a b ↦ differentiable_const _))
      (fun a b ↦ ?_) i j
    · simpa using hprop_diff 1 a b
    · simpa using hprop_diff (-1) a b
  have hstep_diff : ∀ i j, Differentiable ℂ (fun z ↦
      (jBeta (concreteGibbsData hH β).ρQuarter (heisenbergEvol hH z W) * V) i j) := by
    intro i j
    unfold jBeta
    exact hmat_mul_diff _ _ (hmat_mul_diff _ _ (hmat_mul_diff _ _ (fun _ _ ↦ differentiable_const _)
      hevol_diff) (fun _ _ ↦ differentiable_const _)) (fun _ _ ↦ differentiable_const _) i j
  have hsq_diff := hmat_mul_diff _ _ hstep_diff hstep_diff
  unfold concreteOTOC Matrix.trace Matrix.diag
  exact Differentiable.fun_sum fun i _ ↦ hsq_diff i i

/-- Exact spectral identity linking `concreteWightmanNormAtShift` to the spectral measure:
`concreteWightmanNormAtShift hH β W τ 0 = ∫ ω, exp(-2 τ ω) ∂(concreteWightmanSpectralMeasure hH β W)`. -/
theorem concreteWightmanNormAtShift_eq_spectralMeasure {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (β τ : ℝ) :
    concreteWightmanNormAtShift hH β W τ 0 =
      ∫ ω : ℝ, Real.exp (-2 * τ * ω) ∂(concreteWightmanSpectralMeasure hH β W) := by
  rw [integral_concreteWightmanSpectralMeasure]
  unfold concreteWightmanNormAtShift
  simp only [Complex.ofReal_zero, zero_add]
  have h1 := theorem_1_2a_concrete_exp_moment hH hW β τ
  convert h1 using 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  simp only [smul_eq_mul]
  congr 2; ring

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
  let d : QubitIdx N → ℂ := fun i ↦ ((Real.exp (-(β * hH.eigenvalues i / 2)) : ℝ) : ℂ)
  have hρHalf_eq : Uᴴ * (concreteGibbsData hH β).ρHalf * U =
      (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d := by
    change Uᴴ * gibbsRhoHalf hH β * U = _
    unfold gibbsRhoHalf hermFunc
    calc Uᴴ * (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • (U * Matrix.diagonal d * Uᴴ) * U
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
      ((Uᴴ * R * U) * (Uᴴ * Wᴴ * U) * (Uᴴ * R * U) * (Uᴴ * A * U)).trace := by
    have h1 : (R * Wᴴ * R * A).trace = (Uᴴ * (R * Wᴴ * R * A) * U).trace := by
      calc (R * Wᴴ * R * A).trace = ((U * Uᴴ) * (R * Wᴴ * R * A)).trace := by rw [hU1, Matrix.one_mul]
        _ = (U * (Uᴴ * (R * Wᴴ * R * A))).trace := by simp only [Matrix.mul_assoc]
        _ = ((Uᴴ * (R * Wᴴ * R * A)) * U).trace := Matrix.trace_mul_comm _ _
        _ = (Uᴴ * (R * Wᴴ * R * A) * U).trace := by simp only [Matrix.mul_assoc]
    rw [h1]; congr 1
    calc Uᴴ * (R * Wᴴ * R * A) * U
        = Uᴴ * R * (U * Uᴴ) * Wᴴ * (U * Uᴴ) * R * (U * Uᴴ) * A * U := by
            rw [hU1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Uᴴ * R * U) * (Uᴴ * Wᴴ * U) * (Uᴴ * R * U) * (Uᴴ * A * U) := by
            simp only [Matrix.mul_assoc]
  rw [htr, hρHalf_eq, hW.eq, hevol_diag]
  have hsqZ : (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) * (((Real.sqrt Z)⁻¹ : ℝ) : ℂ) = ((Z⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hZpos.le]
  have htr2 : ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d * B *
      ((((Real.sqrt Z)⁻¹ : ℝ) : ℂ) • Matrix.diagonal d) *
      (Matrix.diagonal (fun a ↦ Complex.exp (-2 * (τ : ℂ) * (hH.eigenvalues a : ℂ))) * B *
       Matrix.diagonal (fun b ↦ Complex.exp (2 * (τ : ℂ) * (hH.eigenvalues b : ℂ))))).trace =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        ((wightmanSpectralWeight hH β W a b * Real.exp (-2 * τ * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsqZ, Matrix.trace_smul,
      smul_eq_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    unfold wightmanSpectralWeight
    have hBab : B a b * B b a = ((‖B a b‖ ^ 2 : ℝ) : ℂ) := by
      have hba : B b a = star (B a b) := by
        have := congrArg (fun M : QubitOp N ↦ M b a) hB_herm
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [hba, Complex.mul_conj', Complex.ofReal_pow]
    have hdd : d a * d b = ((Real.exp (-(β * (hH.eigenvalues a + hH.eigenvalues b) / 2)) : ℝ) : ℂ) := by
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
      _ = ((Z⁻¹ : ℝ) : ℂ) * ((Real.exp (-(β * (hH.eigenvalues a + hH.eigenvalues b) / 2)) : ℝ) : ℂ) *
            ((‖B a b‖ ^ 2 : ℝ) : ℂ) *
            ((Real.exp (-2 * τ * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) := by
            rw [hdd, hBab, hexp_ab]
      _ = _ := by
            push_cast
            have hZeq : Z = gibbsPartitionFn hH β := rfl
            rw [hZeq]; ring
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
    change (gibbsPartitionFn hH β)⁻¹ * Real.exp (-(β * (hH.eigenvalues b + hH.eigenvalues a) / 2)) *
        ‖B b a‖ ^ 2 =
      (gibbsPartitionFn hH β)⁻¹ * Real.exp (-(β * (hH.eigenvalues a + hH.eigenvalues b) / 2)) *
        ‖B a b‖ ^ 2
    rw [hnorm, add_comm]
  rw [hwsym]

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
      (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z)
      (fun N ↦ (differentiable_concreteOTOC (hH N) β (W N) (V N)).differentiableOn)
      hcomp_bdd F_real hreal_lim with ⟨F, hF_holo, hF_real, hF_unif⟩
  refine ⟨F, hF_holo, hF_real, hF_unif, fun t τ hτ ↦ ?_⟩
  set z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
  have hz_mem : z ∈ {w : ℂ | |w.im| < S_OTOC} := by
    simp only [Set.mem_setOf_eq, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add]
    exact hτ
  have htend_z : Tendsto (fun N ↦ ‖concreteOTOC (hH N) β (W N) (V N) z‖) atTop (nhds ‖F z‖) :=
    (hF_unif.tendsto_at hz_mem).norm
  rcases hshift_bdd τ hτ with ⟨B, hB⟩
  have hbdd_upper : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) :=
    ⟨B, Eventually.of_forall hB⟩
  have hle_liminf : ‖F z‖ ≤ Filter.liminf
      (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop := by
    rw [← htend_z.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall fun N ↦ ?_)
      htend_z.isBoundedUnder_ge ⟨C_V ^ 2 * B, Eventually.of_forall fun N ↦
        mul_le_mul_of_nonneg_left (hB N) (sq_nonneg C_V)⟩
    have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β t τ).1
    have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
    exact le_trans h3 (mul_le_mul_of_nonneg_right hVsq (gibbsWightmanNormSq_nonneg _ _))
  have hmul_liminf : Filter.liminf
      (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop ≤
      C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop := by
    by_cases hCV0 : C_V = 0
    · simp [hCV0]
    · have hCV2_pos : 0 < C_V ^ 2 := sq_pos_of_ne_zero hCV0
      have hge : Filter.IsBoundedUnder (· ≥ ·) atTop
          (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) :=
        ⟨0, Eventually.of_forall fun N ↦ gibbsWightmanNormSq_nonneg _ _⟩
      exact (Filter.liminf_const_mul (f := fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0)
        (l := atTop) hCV2_pos hge hbdd_upper).le
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
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (by linarith : 0 ≤ β / 2 + κ')]
      exact mul_le_mul_of_nonneg_right h2τ_le (abs_nonneg ω)
    have h54 := (theorem_1_2a_concrete_spectralMeasure_cosh_bound hr (E N) (hcard N) (h N)
      (hsupp N) (hH N) hJ (hsite N) (hUW N) (hWherm N) (hW N) hβ hκ'_nn hκ'_lt).2
    have hsq : (opNorm (W N)) ^ 2 ≤ C_W ^ 2 := by nlinarith [opNorm_nonneg (W N), hW_norm N]
    have hleB : 2 * (2 * (opNorm (W N)) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))) ≤ B := by
      dsimp only [B]
      have := mul_le_mul_of_nonneg_right (show 4 * (opNorm (W N)) ^ 2 ≤ 4 * C_W ^ 2 by linarith)
        (Real.rpow_nonneg h1sub.le _)
      linarith
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

/-- **Theorem 1.3(c) (Fully Concrete-Family High-Temperature Chaos Bound with KMS Rate Discharged)**:
Discharges ALL Theorem 1.2(a)–(b) inputs (`μ_N`, `hunif`, `hmom_eq`) directly from the concrete
`r`-local family `(H_N, O_N)`, establishing for all `0 ≤ β ≤ highTempBetaWC r Jsite` with
`κ = (2 * (r - 1) * Jsite)⁻¹`:
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
    have hfn_tend : Tendsto (fun m : ℕ ↦ 2 * Real.pi / (β + 2 * seq m)) atTop
        (nhds (2 * Real.pi / (β + 2 * κ))) :=
      (continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        (by linarith)).tendsto.comp hseq_tend
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
  have hlamW_le : lamW ≤ 2 * α := by
    by_cases hβ_pos : 0 < β
    · exact (theorem_1_3c_unconditional_family hr hJ hβ_pos hβ hκ_pos hα hγ hα_kms hCO_ge1
        hlamW hlamMSS E hE_ne hE_card h hh_supp hH hH_site U₀ hU₀ O hO hO_supp hOnorm hCO
        hb_lin hH1_W hH1_MSS).1.1
    · have hβ_eq : β = 0 := le_antisymm (le_of_not_gt hβ_pos) hβ0
      subst hβ_eq
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
          fun N ↦ by congr 1; ring
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
      have h13b := theorem_1_3b_high_temp hr hJ le_rfl hβ (E N) (hE_ne N) (hE_card N) (h N)
        (hh_supp N) (hH N) (hH_site N) (heisenbergEvol (hH N) ((((1 - ε) / lamW) * Real.log (N : ℝ) : ℝ) : ℂ) (O N))
        (heisenbergEvol_real_isHermitian (hH N) (hO N) _)
      have h41 := prop_4_1_part2_concrete_operator (hH N) (hO N) 0 (hOnorm N) hr (E N) (hE_card N)
        (h N) (hh_supp N) (U₀ N) (hU₀ N) (hO_supp N) (((1 - ε) / lamW) * Real.log (N : ℝ))
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
            216 * (((r - 1 : ℕ) : ℝ) *
              concreteKrylovComplexity (hH N) 0 (O N) (((1 - ε) / lamW) * Real.log (N : ℝ)) +
              (s₀ : ℝ)) := by
          linarith [h13b.2, h41]
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
      by_contra hgt; push Not at hgt
      set ε₀ : ℝ := min ((lamMSS - 2 * α) / (2 * lamMSS)) (1 / 2)
      have hε₀ : 0 < ε₀ := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
      rcases hH1_MSS ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
      have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
      set η : ℝ := (1 - ε) * (2 * α / lamMSS)
      have hη_lt : η < 1 - ε := by
        have h1 : 2 * α / lamMSS < 1 := (div_lt_one hlamMSS).mpr hgt
        dsimp only [η]; nlinarith
      rcases theorem_1_3c_eq_1_24_concrete hr hJ le_rfl hβ hCO_ge1 with ⟨C₁, C₂, hC₁, hC₂, N₀, h124⟩
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
          fun N ↦ by congr 1; ring
      have hlim2 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 + η) / 2 - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - (1 + η) / 2)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by congr 1; ring
      have hlim3 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 2 - (1 - ε))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) - 1 / 2)).comp tendsto_natCast_atTop_atTop |>.congr
          fun N ↦ by congr 1; ring
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
      have hbound := h124 N hN_ge0 (E N) (hE_ne N) (hE_card N) (h N) (hh_supp N) (hH N) (hH_site N)
        (U₀ N) (hU₀ N) (O N) (hO N) (hO_supp N) (hOnorm N) (hCO N) tN
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
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
          congr 2; ring
        have h4 : Real.sqrt ((s₀ : ℝ) * (N : ℝ)) = Real.sqrt (s₀ : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg s₀), Real.sqrt_eq_rpow]
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
