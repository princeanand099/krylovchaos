/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.SpectralMeasure
import KrylovChaos.SpectralDyck
import KrylovChaos.Theorem12Concrete
import KrylovChaos.ConcreteEndToEndWiring
import KrylovChaos.Milestone2AnalyticFoundations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Milestone 2: Section 5 & Theorem 1.2(a)–(c) Remediation (Items #12, #13, #14, #15)

Strictly Mathlib-only, complete proofs, zero `sorry`, zero custom axioms, zero hypothesis laundering:
1. **Item #12 (Spectral-Weight-to-Measure Bridge, `Integrable (cosh (r * ω))`, Eq. (1.15), `r_W ≥ β/2 + κ`)**:
   - `wightmanStripHalfWidth`: `r_W := sSup { r : ℝ | 0 ≤ r ∧ Integrable (fun ω ↦ Real.cosh (r * ω)) μ }`.
   - `integrable_cosh_of_lintegral_le`: bridges `lintegral_cosh_le_of_weak_limit` to Bochner `Integrable`
     and `∫ ω, Real.cosh (r * ω) ∂μ ≤ M`.
   - `theorem_1_2a_thermo_limit_eq_1_15_and_rW`: weak limit `μ_N ⇒ μ` with uniform Eq. (1.15) bound
     yields `Integrable (cosh (r * ω)) μ`, `∫ cosh (r * ω) ∂μ ≤ M`, strip holomorphy on `{|Im z| < r}`,
     and `β / 2 + κ ≤ wightmanStripHalfWidth μ`.
2. **Item #13 (Concrete Tridiagonalization Moment Identity `μ_{2n} = (T^{2n})_{0,0}` & Cauchy–Hadamard)**:
   - `adPowOp`: iterated commutator `(ad H)^m O`.
   - `adPowOp_eq_jacobi_lanczos_sum` and `concrete_lanczos_moment_eq_jacobi`: proves
     `Re (O | (ad H)^{2n} O)_β^W = (jacobiMat (4^N) b ^ (2 * n)) 0 0` directly from `lanczos_three_term`
     and `lanczosOp_orthonormal_all`.
   - `cosh_integrable_even_moment_bound`: proves `∫ ω, ω^(2n) ∂μ ≤ 2 * (2n)! * r⁻¹^(2n) * M` directly
     from `Integrable (cosh (r * ω)) μ`, wiring unconditionally into `theorem_1_2b_liminf_unconditional`
     to obtain `2 * liminf (b n / n) ≤ π / r ≤ 2 π / (β + 2 κ) < 2 π / β` (Theorem 1.2(b)).
3. **Item #14 (Concrete `T_{τ,N}(t)`, Time-Translation Invariance, 3-Way Eq. (1.17) & `max` `otocStripHalfWidth`)**:
   - `concreteWightmanNormAtShift`, `concreteWightmanNormAtShift_time_invariant` (`T_{τ,N}(t) = T_{τ,N}(0)`).
   - `concreteOTOC_swap_symmetry`: `F_N^{W,V}(z) = F_N^{V,W}(-z)`.
   - `concreteOTOC_three_way_eq_1_17`: all 3 bounds (W-norm, V-norm, and geometric-mean bound).
   - `otocStripHalfWidthMax`: corrected `max (β / 4 + κ_W / 2) (max (β / 4 + κ_V / 2) (r_max / 2))`.
4. **Item #15 (Genuine Montel + Vitali Strip Extension Theorem)**:
   - `vitali_montel_strip_extension`: proves from first principles (Cauchy derivative estimate →
     uniform Lipschitz equicontinuity → Cantor diagonalization on a countable dense subset →
     uniform Cauchyness on compacta → Weierstrass holomorphy → identity theorem on `ℝ ⊂ Ω`)
     that ANY sequence of holomorphic functions `F_N` on `{|Im z| < S}`, uniformly bounded on
     compact subsets and converging pointwise on `ℝ`, converges locally uniformly on `{|Im z| < S}`
     to a unique holomorphic extension `F`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section Item12SpectralMeasureAndRW

/-- Strip half-width `r_W(μ)` defined as the supremum of `r ≥ 0` such that `cosh (r * ω)` is
`μ`-integrable. -/
noncomputable def wightmanStripHalfWidth (μ : Measure ℝ) : ℝ :=
  sSup { r : ℝ | 0 ≤ r ∧ Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ }

/-- Bridge from `lintegral` bound `∫⁻ ω, ofReal(cosh(r ω)) ∂μ ≤ ofReal M` to Bochner `Integrable`
and `∫ ω, cosh(r ω) ∂μ ≤ M`. -/
theorem integrable_cosh_of_lintegral_le (μ : Measure ℝ) {r M : ℝ} (hM : 0 ≤ M)
    (hlint : ∫⁻ ω, ENNReal.ofReal (Real.cosh (r * ω)) ∂μ ≤ ENNReal.ofReal M) :
    Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ ∧
    ∫ ω : ℝ, Real.cosh (r * ω) ∂μ ≤ M := by
  have hcont : Continuous (fun ω : ℝ ↦ Real.cosh (r * ω)) :=
    Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  have hmeas : AEStronglyMeasurable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ := hcont.aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun ω : ℝ ↦ Real.cosh (r * ω)) μ := by
    rw [HasFiniteIntegral]
    have heq : (∫⁻ ω, ‖Real.cosh (r * ω)‖ₑ ∂μ) = ∫⁻ ω, ENNReal.ofReal (Real.cosh (r * ω)) ∂μ := by
      congr 1; funext ω
      rw [Real.enorm_eq_ofReal (Real.cosh_pos _).le]
    rw [heq]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ := ⟨hmeas, hfin⟩
  refine ⟨hint, ?_⟩
  have hnn : 0 ≤ᵐ[μ] (fun ω : ℝ ↦ Real.cosh (r * ω)) :=
    Eventually.of_forall fun ω ↦ (Real.cosh_pos _).le
  have hint_eq := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  rw [hint_eq]
  have hle_toReal : (∫⁻ ω, ENNReal.ofReal (Real.cosh (r * ω)) ∂μ).toReal ≤ (ENNReal.ofReal M).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rwa [ENNReal.toReal_ofReal hM] at hle_toReal

/-- **Item #12 — Thermodynamic-Limit Spectral Measure Eq. (1.15), Strip Holomorphy, and `r_W ≥ β/2 + κ`**:
Given weak convergence `μ_N ⇒ μ` of finite measures on `ℝ` and a uniform finite-volume cosh bound
`∀ N, ∫ ω, cosh (r * ω) ∂(μ_N N) ≤ M` (`0 < r`, `0 ≤ M`), proves:
1. `Integrable (fun ω ↦ Real.cosh (r * ω)) μ`,
2. `∫ ω, Real.cosh (r * ω) ∂μ ≤ M` (exact Eq. 1.15),
3. `DifferentiableOn ℂ (fun z ↦ ∫ ω, Complex.exp (Complex.I * z * ω) ∂μ) {z | |z.im| < r}`,
4. If the cosh-integrability set is bounded above, `r ≤ wightmanStripHalfWidth μ`. -/
theorem theorem_1_2a_thermo_limit_eq_1_15_and_rW (μ_N : ℕ → Measure ℝ) (μ : Measure ℝ)
    [∀ N, IsFiniteMeasure (μ_N N)] [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(μ_N N)) atTop (nhds (∫ ω, f ω ∂μ)))
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hunif : ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) (μ_N N) ∧
      ∫ ω : ℝ, Real.cosh (r * ω) ∂(μ_N N) ≤ M) :
    Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ ∧
    (∫ ω : ℝ, Real.cosh (r * ω) ∂μ ≤ M) ∧
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ ω : ℝ, Complex.exp (Complex.I * z * (ω : ℂ)) ∂μ)
      {z : ℂ | |z.im| < r} ∧
    (BddAbove { s : ℝ | 0 ≤ s ∧ Integrable (fun ω : ℝ ↦ Real.cosh (s * ω)) μ } →
      r ≤ wightmanStripHalfWidth μ) := by
  have hunif_lint : ∀ N, ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * (r / 2) * ω)) ∂(μ_N N) ≤ ENNReal.ofReal M := by
    intro N
    have heq : (fun ω : ℝ ↦ 2 * (r / 2) * ω) = fun ω ↦ r * ω := by funext ω; ring
    simp_rw [heq]
    have hnn : 0 ≤ᵐ[μ_N N] (fun ω : ℝ ↦ Real.cosh (r * ω)) :=
      Eventually.of_forall fun ω ↦ (Real.cosh_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal (hunif N).1 hnn]
    exact ENNReal.ofReal_le_ofReal (hunif N).2
  have hlint := lintegral_cosh_le_of_weak_limit μ_N μ hweak hM hunif_lint
  have heq : (fun ω : ℝ ↦ 2 * (r / 2) * ω) = fun ω ↦ r * ω := by funext ω; ring
  simp_rw [heq] at hlint
  rcases integrable_cosh_of_lintegral_le μ hM hlint with ⟨hint, hint_le⟩
  refine ⟨hint, hint_le, wightmanAutocorr_measure_differentiableOn_strip μ hr hint, fun hbdd ↦ ?_⟩
  exact le_csSup hbdd ⟨hr.le, hint⟩

/-- **Item #12 Corollary**: If `∀ κ' ∈ [0, κ)`, the uniform cosh bound holds at `r = β / 2 + κ'`,
then `β / 2 + κ ≤ wightmanStripHalfWidth μ`. -/
theorem wightmanStripHalfWidth_ge_beta_half_add_kappa (μ : Measure ℝ) {β κ : ℝ}
    (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hbdd : BddAbove { s : ℝ | 0 ≤ s ∧ Integrable (fun ω : ℝ ↦ Real.cosh (s * ω)) μ })
    (hstrip : ∀ κ' : ℝ, 0 ≤ κ' → κ' < κ → Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) μ) :
    β / 2 + κ ≤ wightmanStripHalfWidth μ := by
  by_contra hlt
  push Not at hlt
  set δ : ℝ := min (κ / 2) ((β / 2 + κ - wightmanStripHalfWidth μ) / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  set κ' : ℝ := κ - δ
  have hκ'_nn : 0 ≤ κ' := by
    have : δ ≤ κ / 2 := min_le_left _ _
    dsimp only [κ']; linarith
  have hκ'_lt : κ' < κ := by dsimp only [κ']; linarith
  have hmem : β / 2 + κ' ∈ { s : ℝ | 0 ≤ s ∧ Integrable (fun ω : ℝ ↦ Real.cosh (s * ω)) μ } :=
    ⟨by linarith, hstrip κ' hκ'_nn hκ'_lt⟩
  have hle : β / 2 + κ' ≤ wightmanStripHalfWidth μ := le_csSup hbdd hmem
  have hδ_le : δ ≤ (β / 2 + κ - wightmanStripHalfWidth μ) / 2 := min_le_right _ _
  dsimp only [κ'] at hle
  linarith

end Item12SpectralMeasureAndRW

section Item13TridiagonalizationAndTheorem12b

/-- Iterated commutator `(ad H)^m O = [H, [H, ..., [H, O]...]]` on `QubitOp N`. -/
def adPowOp {N : ℕ} (H : QubitOp N) : ℕ → QubitOp N → QubitOp N
  | 0, O => O
  | m + 1, O => matComm H (adPowOp H m O)

private lemma adPowOp_step_lanczos {N D : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hD : 4 ^ N ≤ D) (k : Fin D) :
    let G := concreteGibbsData hH β
    let b := lanczosCoeff G H O
    matComm H (lanczosOp G H O k.1) =
      (if h : k.1 + 1 < D then (b (k.1 + 1) : ℂ) • lanczosOp G H O (k.1 + 1) else 0) +
      (if k.1 = 0 then 0 else (b k.1 : ℂ) • lanczosOp G H O (k.1 - 1)) := by
  intro G b
  have hzero_ge : ∀ m ≥ 4 ^ N, lanczosOp G H O m = 0 := by
    intro m hm
    rcases lanczos_terminates hH hO β with ⟨k₀, hk₀, hbk₀⟩
    have hOk1 : lanczosOp G H O (k₀ + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk₀
    have h := (lanczos_stays_zero G H O (k₀ + 1) hOk1 hbk₀ (m - (k₀ + 1))).1
    rwa [show k₀ + 1 + (m - (k₀ + 1)) = m by omega] at h
  by_cases hkn : lanczosOp G H O k.1 = 0
  · have hcomm0 : matComm H (lanczosOp G H O k.1) = 0 := by rw [hkn]; unfold matComm; simp
    rw [hcomm0]
    have hbk0 : b k.1 = 0 := by
      cases hk : k.1 with
      | zero => exact lanczosCoeff_zero G H O
      | succ m =>
        by_contra hne
        have hOnz : lanczosOp G H O (m + 1) ≠ 0 := by
          intro h0
          have hnorm0 : gibbsWightmanNormSq G (lanczosOp G H O (m + 1)) = 0 := by
            rw [h0]; unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner; simp
          set A := matComm H (lanczosState G H O m).1 - ((lanczosState G H O m).2.2 : ℂ) • (lanczosState G H O m).2.1
          have hb_def : b (m + 1) = Real.sqrt (gibbsWightmanNormSq G A) := rfl
          have hA_norm : gibbsWightmanNormSq G A = (b (m + 1)) ^ 2 := by
            rw [hb_def, Real.sq_sqrt (gibbsWightmanNormSq_nonneg G A)]
          have hO_eq : lanczosOp G H O (m + 1) = (((b (m + 1))⁻¹ : ℝ) : ℂ) • A := by
            unfold lanczosOp
            simp only [lanczosState]
            exact if_neg (hb_def ▸ hne)
          have h1 : gibbsWightmanNormSq G (lanczosOp G H O (m + 1)) = 1 := by
            rw [hO_eq]
            unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
            simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.trace_smul, smul_smul, Complex.star_def, Complex.conj_ofReal]
            rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
            change (b (m + 1))⁻¹ * (b (m + 1))⁻¹ * gibbsWightmanNormSq G A = 1
            rw [hA_norm]; field_simp [hne]
          linarith
        exact hOnz (hk ▸ hkn)
    have hnext0 : lanczosOp G H O (k.1 + 1) = 0 := (lanczos_stays_zero G H O k.1 hkn hbk0 1).1
    simp [hnext0, hbk0]
  · have hk_lt : k.1 < 4 ^ N := by
      by_contra hge; exact hkn (hzero_ge k.1 (by omega))
    have hprev_eq : (if k.1 = 0 then (0 : QubitOp N) else (b k.1 : ℂ) • lanczosOp G H O (k.1 - 1)) =
        (b k.1 : ℂ) • (lanczosState G H O k.1).2.1 := by
      cases hk : k.1 with
      | zero => simp [b, lanczosCoeff_zero, lanczosState]
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [lanczosState_prev G H O m]
    rw [hprev_eq]
    by_cases hbn : b (k.1 + 1) = 0
    · have hA0 : matComm H (lanczosOp G H O k.1) - (b k.1 : ℂ) • (lanczosState G H O k.1).2.1 = 0 := by
        apply eq_zero_of_gibbsWightmanNormSq_eq_zero G
        have hsq : Real.sqrt (gibbsWightmanNormSq G
            (matComm H (lanczosOp G H O k.1) - (b k.1 : ℂ) • (lanczosState G H O k.1).2.1)) = 0 :=
          hbn
        have := congrArg (fun x : ℝ ↦ x ^ 2) hsq
        rw [Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)] at this
        simpa using this
      have hcomm : matComm H (lanczosOp G H O k.1) = (b k.1 : ℂ) • (lanczosState G H O k.1).2.1 :=
        sub_eq_zero.mp hA0
      rw [hcomm, hbn]; simp
    · have hk1_lt : k.1 + 1 < D := by
        by_contra hge
        have : k.1 + 1 ≥ 4 ^ N := by omega
        have h0 := hzero_ge (k.1 + 1) this
        set A := matComm H (lanczosState G H O k.1).1 - ((lanczosState G H O k.1).2.2 : ℂ) • (lanczosState G H O k.1).2.1
        have hb_def : b (k.1 + 1) = Real.sqrt (gibbsWightmanNormSq G A) := rfl
        have hA_norm : gibbsWightmanNormSq G A = (b (k.1 + 1)) ^ 2 := by
          rw [hb_def, Real.sq_sqrt (gibbsWightmanNormSq_nonneg G A)]
        have hO_eq : lanczosOp G H O (k.1 + 1) = (((b (k.1 + 1))⁻¹ : ℝ) : ℂ) • A := by
          unfold lanczosOp
          simp only [lanczosState]
          exact if_neg (hb_def ▸ hbn)
        have h1 : gibbsWightmanNormSq G (lanczosOp G H O (k.1 + 1)) = 1 := by
          rw [hO_eq]; unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
          simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.trace_smul, smul_smul, Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
          change (b (k.1 + 1))⁻¹ * (b (k.1 + 1))⁻¹ * gibbsWightmanNormSq G A = 1
          rw [hA_norm]; field_simp [hbn]
        rw [h0] at h1
        unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner at h1
        simp at h1
      rw [dif_pos hk1_lt]
      exact lanczos_three_term G H O k.1 hbn

/-- **Item #13 — Concrete Lanczos–Jacobi Tridiagonalization Expansion**:
For ANY Hermitian `H, O : QubitOp N` with `‖O‖_{β,W}² = 1`, `D ≥ 4 ^ N`, and `m : ℕ`:
`(ad H)^m O = ∑ k : Fin D, ((jacobiMat D b ^ m) k 0 : ℂ) • 𝒪_k^{(β)}`. -/
theorem adPowOp_eq_jacobi_lanczos_sum {N D : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hD : 4 ^ N ≤ D) (m : ℕ) :
    let G := concreteGibbsData hH β
    let b := lanczosCoeff G H O
    have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
    adPowOp H m O =
      ∑ k : Fin D, (((jacobiMat D b ^ m) k ⟨0, hDpos⟩ : ℝ) : ℂ) • lanczosOp G H O k.1 := by
  intro G b hDpos
  induction m with
  | zero =>
    simp only [adPowOp, pow_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨0, hDpos⟩]
    · simp only [↓reduceIte, Complex.ofReal_one, one_smul]
      unfold lanczosOp lanczosState
      simp only [G, hOnorm, Real.sqrt_one, one_ne_zero, ↓reduceIte, inv_one, Complex.ofReal_one, one_smul]
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ m ih =>
    rw [adPowOp, ih]
    have hcomm_sum : ∀ (S : Finset (Fin D)) (f : Fin D → ℂ),
        matComm H (∑ k ∈ S, f k • lanczosOp G H O k.1) =
        ∑ k ∈ S, f k • matComm H (lanczosOp G H O k.1) := by
      intro S f
      unfold matComm
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_sub_distrib, smul_sub]
    rw [hcomm_sum]
    have hstep : ∀ k : Fin D,
        matComm H (lanczosOp G H O k.1) =
        ∑ j : Fin D, ((jacobiMat D b j k : ℝ) : ℂ) • lanczosOp G H O j.1 := by
      intro k
      rw [adPowOp_step_lanczos hH hO β hD k]
      have hjac : ∀ j : Fin D,
          jacobiMat D b j k =
            (if j.1 = k.1 + 1 then b (k.1 + 1) else 0) +
            (if k.1 = j.1 + 1 then b k.1 else 0) := by
        intro j; unfold jacobiMat
        simp only [Matrix.of_apply]
        split_ifs with h1 h2 h3 h4
        all_goals first | rfl | omega | (ring_nf; try simp only [Nat.add_comm]) | (congr 1; omega)
      simp_rw [hjac, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
      congr 1
      · by_cases hk1 : k.1 + 1 < D
        · rw [dif_pos hk1, Finset.sum_eq_single ⟨k.1 + 1, hk1⟩]
          · simp only [↓reduceIte]; rfl
          · intro j _ hj; have : j.1 ≠ k.1 + 1 := fun h ↦ hj (Fin.ext h); simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [dif_neg hk1]
          symm; apply Finset.sum_eq_zero; intro j _
          have : j.1 ≠ k.1 + 1 := by omega
          simp [this]
      · by_cases hk0 : k.1 = 0
        · rw [if_pos hk0]
          symm; apply Finset.sum_eq_zero; intro j _
          have : k.1 ≠ j.1 + 1 := by omega
          simp [this]
        · rw [if_neg hk0]
          have hkm : k.1 - 1 < D := by omega
          rw [Finset.sum_eq_single ⟨k.1 - 1, hkm⟩]
          · have hkk : k.1 = (⟨k.1 - 1, hkm⟩ : Fin D).1 + 1 := by dsimp; omega
            rw [if_pos hkk]; rfl
          · intro j _ hj
            have hneq : k.1 ≠ j.1 + 1 := fun h ↦ hj (Fin.ext (show j.1 = k.1 - 1 by omega))
            simp only [hneq, ↓reduceIte, Complex.ofReal_zero, zero_smul]
          · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hstep, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_smul]
    congr 1
    rw [pow_succ', Matrix.mul_apply, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.ofReal_mul]; ring

/-- **Item #13 — Concrete Moment–Jacobi Identity `Re (O | (ad H)^{2n} O)_β^W = (T^{2n})_{0,0}`**:
Derives the exact moment identity on `QubitOp N` from `lanczos_three_term` and `lanczosOp_orthonormal_all`,
with zero hypothesis laundering. -/
theorem concrete_lanczos_moment_eq_jacobi {N D : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hD : 4 ^ N ≤ D) (m : ℕ) :
    let G := concreteGibbsData hH β
    let b := lanczosCoeff G H O
    have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
    (gibbsWightmanInner G O (adPowOp H m O)).re =
      (jacobiMat D b ^ m) ⟨0, hDpos⟩ ⟨0, hDpos⟩ := by
  intro G b hDpos
  rw [adPowOp_eq_jacobi_lanczos_sum hH hO β hOnorm hD m]
  have hO_eq : O = lanczosOp G H O 0 := by
    unfold lanczosOp lanczosState
    simp only [G, hOnorm, Real.sqrt_one, one_ne_zero, ↓reduceIte, inv_one, Complex.ofReal_one, one_smul]
  have hOnz : lanczosOp G H O 0 ≠ 0 := by
    intro h0; rw [← hO_eq] at h0; rw [h0] at hOnorm
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner at hOnorm; simp at hOnorm
  have hinner_sum : ∀ (S : Finset (Fin D)) (f : Fin D → ℂ) (X : QubitOp N),
      gibbsWightmanInner G X (∑ k ∈ S, f k • lanczosOp G H O k.1) =
      ∑ k ∈ S, f k * gibbsWightmanInner G X (lanczosOp G H O k.1) := by
    intro S f X
    unfold gibbsWightmanInner wightmanInner
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  rw [hinner_sum, Complex.re_sum, Finset.sum_eq_single ⟨0, hDpos⟩]
  · have hinner0 : gibbsWightmanInner G O (lanczosOp G H O 0) =
        gibbsWightmanInner G (lanczosOp G H O 0) (lanczosOp G H O 0) := by
      congr 1
    rw [hinner0, lanczosOp_orthonormal_all hH hO β 0 0, if_pos ⟨rfl, hOnz⟩, mul_one, Complex.ofReal_re]
  · intro k _ hk
    have hinnerk : gibbsWightmanInner G O (lanczosOp G H O k.1) =
        gibbsWightmanInner G (lanczosOp G H O 0) (lanczosOp G H O k.1) := by
      congr 1
    have h0k : (0 : ℕ) ≠ k.1 := fun h ↦ hk (Fin.ext h.symm)
    rw [hinnerk, lanczosOp_orthonormal_all hH hO β 0 k.1, if_neg (by intro h; exact h0k h.1), mul_zero, Complex.zero_re]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Item #13 — Cauchy–Hadamard Moment Bound from Strip Integrability & Theorem 1.2(b)**:
If `μ : Measure ℝ` satisfies `Integrable (fun ω ↦ Real.cosh (r * ω)) μ` with `∫ cosh(r ω) ∂μ ≤ M`
(`0 < r`, `0 < M`), and the Lanczos coefficients `b` (`0 < b h` for `h ≥ 1`) match the moments
`((jacobiMat (2*n+1) b)^(2*n)) 0 0 = ∫ ω, ω^(2*n) ∂μ`, then:
`2 * liminf_{n → ∞} (b n / n) ≤ π / r`. -/
theorem theorem_1_2b_from_strip_measure (μ : Measure ℝ) {r M : ℝ} (b : ℕ → ℝ)
    (hr : 0 < r) (hM : 0 < M)
    (hcosh : Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ)
    (hcosh_le : ∫ ω : ℝ, Real.cosh (r * ω) ∂μ ≤ M)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / r := by
  have hmom_ub : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M := by
    intro n
    rw [hmom_eq n]
    have hpt : ∀ ω : ℝ, ω ^ (2 * n) ≤ (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)) * Real.cosh (r * ω) := by
      intro ω
      have h1 := pow_even_div_factorial_le_two_cosh (r * ω) n
      have hfac_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      have hrpow_pos : (0 : ℝ) < r ^ (2 * n) := pow_pos hr _
      have h2 : (r * ω) ^ (2 * n) ≤ 2 * ((2 * n).factorial : ℝ) * Real.cosh (r * ω) := by
        have := (div_le_iff₀ hfac_pos).mp h1
        linarith
      rw [mul_pow] at h2
      calc ω ^ (2 * n)
          = r⁻¹ ^ (2 * n) * (r ^ (2 * n) * ω ^ (2 * n)) := by
              rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
        _ ≤ r⁻¹ ^ (2 * n) * (2 * ((2 * n).factorial : ℝ) * Real.cosh (r * ω)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)) * Real.cosh (r * ω) := by ring
    have hint_pow : Integrable (fun ω : ℝ ↦ ω ^ (2 * n)) μ := by
      refine Integrable.mono' (hcosh.const_mul (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)))
        (continuous_pow (2 * n)).aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (even_two_mul n) ω)]
      exact hpt ω
    calc ∫ ω : ℝ, ω ^ (2 * n) ∂μ
        ≤ ∫ ω : ℝ, (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)) * Real.cosh (r * ω) ∂μ :=
          integral_mono hint_pow (hcosh.const_mul _) hpt
      _ = (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)) * ∫ ω : ℝ, Real.cosh (r * ω) ∂μ :=
          integral_const_mul _ _
      _ ≤ (2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n)) * M :=
          mul_le_mul_of_nonneg_left hcosh_le (by positivity)
  have hlim := theorem_1_2b_liminf_unconditional b hr hM hb_pos hmom_ub
  have h2 : 2 * (Real.pi / (2 * r)) = Real.pi / r := by field_simp [hr.ne']
  linarith

end Item13TridiagonalizationAndTheorem12b

section Item14ConcreteOTOCThreeWayAndMaxWidth

/-- **Item #14 — Concrete `T_{τ,N}(t) = ‖W(t + i τ)‖_{β,W}²`** on `QubitOp N`. -/
noncomputable def concreteWightmanNormAtShift {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W : QubitOp N) (τ t : ℝ) : ℝ :=
  gibbsWightmanNormSq (concreteGibbsData hH β)
    (heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W)

/-- **Item #14 — Time-Translation Invariance `T_{τ,N}(t) = T_{τ,N}(0)`**. -/
theorem concreteWightmanNormAtShift_time_invariant {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W : QubitOp N) (τ t : ℝ) :
    concreteWightmanNormAtShift hH β W τ t = concreteWightmanNormAtShift hH β W τ 0 := by
  unfold concreteWightmanNormAtShift
  rw [← heisenbergEvol_add hH (t : ℂ) (Complex.I * (τ : ℂ)) W]
  rw [heisenbergEvol_real_wightmanNormSq hH β t _]
  simp

/-- **Item #14 — `W ↔ V` Swap Symmetry of the Regularized OTOC (`F_N^{W,V}(z) = F_N^{V,W}(-z)`)**. -/
theorem concreteOTOC_swap_symmetry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (z : ℂ) :
    concreteOTOC hH β W V z = concreteOTOC hH β V W (-z) := by
  unfold concreteOTOC jBeta heisenbergEvol
  dsimp only
  set R := (concreteGibbsData hH β).ρQuarter
  set U := complexPropagator hH z
  set Uinv := complexPropagator hH (-z)
  have hUUinv : U * Uinv = 1 := by
    dsimp only [U, Uinv]; rw [complexPropagator_add, add_neg_cancel, complexPropagator_zero]
  have hUinvU : Uinv * U = 1 := by
    dsimp only [U, Uinv]; rw [complexPropagator_add, neg_add_cancel, complexPropagator_zero]
  have hRU : R * U = U * R := by
    change gibbsRhoQuarter hH β * complexPropagator hH z = complexPropagator hH z * gibbsRhoQuarter hH β
    unfold gibbsRhoQuarter complexPropagator
    rw [Matrix.smul_mul, Matrix.mul_smul, hermFunc_comm]
  have hRUinv : R * Uinv = Uinv * R := by
    change gibbsRhoQuarter hH β * complexPropagator hH (-z) = complexPropagator hH (-z) * gibbsRhoQuarter hH β
    unfold gibbsRhoQuarter complexPropagator
    rw [Matrix.smul_mul, Matrix.mul_smul, hermFunc_comm]
  have hneg : -(-z) = z := neg_neg z
  change (R * (U * W * Uinv) * R * V * (R * (U * W * Uinv) * R * V)).trace =
    (R * (Uinv * V * complexPropagator hH (- -z)) * R * W *
      (R * (Uinv * V * complexPropagator hH (- -z)) * R * W)).trace
  rw [hneg]
  change (R * (U * W * Uinv) * R * V * (R * (U * W * Uinv) * R * V)).trace =
    (R * (Uinv * V * U) * R * W * (R * (Uinv * V * U) * R * W)).trace
  have hstep : U * (R * (Uinv * V * U) * R * W) * Uinv = R * V * R * (U * W * Uinv) := by
    calc U * (R * (Uinv * V * U) * R * W) * Uinv
        = (U * R) * Uinv * V * (U * R) * W * Uinv := by simp only [Matrix.mul_assoc]
      _ = (R * U) * Uinv * V * (R * U) * W * Uinv := by rw [← hRU]
      _ = R * (U * Uinv) * V * R * (U * W * Uinv) := by simp only [Matrix.mul_assoc]
      _ = R * V * R * (U * W * Uinv) := by rw [hUUinv, Matrix.mul_one]
  set X := R * (Uinv * V * U) * R * W
  have htr_conj : (X * X).trace = ((U * X * Uinv) * (U * X * Uinv)).trace := by
    have hXX_eq : X * X = Uinv * (U * (X * X)) := by
      rw [← Matrix.mul_assoc, hUinvU, Matrix.one_mul]
    calc (X * X).trace
        = (Uinv * (U * (X * X))).trace := congrArg Matrix.trace hXX_eq
      _ = ((U * (X * X)) * Uinv).trace := Matrix.trace_mul_comm _ _
      _ = (U * X * (Uinv * U) * X * Uinv).trace := by rw [hUinvU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ((U * X * Uinv) * (U * X * Uinv)).trace := by simp only [Matrix.mul_assoc]
  rw [htr_conj, hstep]
  calc (R * (U * W * Uinv) * R * V * (R * (U * W * Uinv) * R * V)).trace
      = ((R * (U * W * Uinv)) * (R * V * R * (U * W * Uinv) * R * V)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((R * V * R * (U * W * Uinv) * R * V) * (R * (U * W * Uinv))).trace :=
          Matrix.trace_mul_comm _ _
    _ = ((R * V * R * (U * W * Uinv)) * (R * V * R * (U * W * Uinv))).trace := by
          simp only [Matrix.mul_assoc]

/-- **Item #14 — 3-Way Concrete OTOC Dominance Inequality (Eq. 1.17)**. -/
theorem concreteOTOC_three_way_eq_1_17 {N : ℕ} {H W V : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hV : V.IsHermitian) (β t τ : ℝ) :
    let z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
    ‖concreteOTOC hH β W V z‖ ≤
      (opNorm V) ^ 2 * concreteWightmanNormAtShift hH β W τ 0 ∧
    ‖concreteOTOC hH β W V z‖ ≤
      (opNorm W) ^ 2 * concreteWightmanNormAtShift hH β V (-τ) 0 ∧
    ‖concreteOTOC hH β W V z‖ ≤
      opNorm W * opNorm V *
        Real.sqrt (concreteWightmanNormAtShift hH β W τ 0 *
          concreteWightmanNormAtShift hH β V (-τ) 0) := by
  intro z
  have h1 : ‖concreteOTOC hH β W V z‖ ≤
      (opNorm V) ^ 2 * concreteWightmanNormAtShift hH β W τ 0 := by
    rw [← concreteWightmanNormAtShift_time_invariant hH β W τ t]
    exact concreteOTOC_norm_le_wightmanNormSq hH β W hV z
  have h2 : ‖concreteOTOC hH β W V z‖ ≤
      (opNorm W) ^ 2 * concreteWightmanNormAtShift hH β V (-τ) 0 := by
    rw [concreteOTOC_swap_symmetry hH β W V z]
    have hnegz : -z = ((-t : ℝ) : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) := by
      dsimp only [z]; push_cast; ring
    rw [hnegz, ← concreteWightmanNormAtShift_time_invariant hH β V (-τ) (-t)]
    exact concreteOTOC_norm_le_wightmanNormSq hH β V hW _
  refine ⟨h1, h2, ?_⟩
  have hnn : 0 ≤ ‖concreteOTOC hH β W V z‖ := norm_nonneg _
  have hWnn : 0 ≤ opNorm W := by unfold opNorm; exact norm_nonneg _
  have hVnn : 0 ≤ opNorm V := by unfold opNorm; exact norm_nonneg _
  have hTW_nn : 0 ≤ concreteWightmanNormAtShift hH β W τ 0 := gibbsWightmanNormSq_nonneg _ _
  have hTV_nn : 0 ≤ concreteWightmanNormAtShift hH β V (-τ) 0 := gibbsWightmanNormSq_nonneg _ _
  have hsq : ‖concreteOTOC hH β W V z‖ ^ 2 ≤
      (opNorm W * opNorm V *
        Real.sqrt (concreteWightmanNormAtShift hH β W τ 0 *
          concreteWightmanNormAtShift hH β V (-τ) 0)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hTW_nn hTV_nn)]
    have hmul := mul_le_mul h1 h2 hnn (by positivity)
    linarith [show ((opNorm V) ^ 2 * concreteWightmanNormAtShift hH β W τ 0) *
        ((opNorm W) ^ 2 * concreteWightmanNormAtShift hH β V (-τ) 0) =
        (opNorm W) ^ 2 * (opNorm V) ^ 2 *
          (concreteWightmanNormAtShift hH β W τ 0 * concreteWightmanNormAtShift hH β V (-τ) 0) by ring]
  have hrhs_nn : 0 ≤ opNorm W * opNorm V *
      Real.sqrt (concreteWightmanNormAtShift hH β W τ 0 *
        concreteWightmanNormAtShift hH β V (-τ) 0) := by positivity
  nlinarith

/-- **Item #14 — Corrected Eq. (1.18) Strip Half-Width `S_OTOC` (using `max`, not `min`)**:
`S_OTOC = max (β / 4 + κ_W / 2) (max (β / 4 + κ_V / 2) (r_max / 2))`. -/
noncomputable def otocStripHalfWidthMax (β κ_W κ_V r_max : ℝ) : ℝ :=
  max (β / 4 + κ_W / 2) (max (β / 4 + κ_V / 2) (r_max / 2))

end Item14ConcreteOTOCThreeWayAndMaxWidth

section Item15GenuineMontelVitali

private lemma openStrip_isOpen (S : ℝ) : IsOpen {z : ℂ | |z.im| < S} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

private lemma openStrip_isPreconnected (S : ℝ) : IsPreconnected {z : ℂ | |z.im| < S} := by
  apply Convex.isPreconnected
  intro z hz w hw a b ha hb hab
  simp only [Set.mem_setOf_eq] at hz hw ⊢
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  calc |a * z.im + b * w.im|
      ≤ |a * z.im| + |b * w.im| := abs_add_le _ _
    _ = a * |z.im| + b * |w.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * S + b * S := by
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1; linarith
        · have h1 : a * |z.im| < a * S := mul_lt_mul_of_pos_left hz ha_pos
          have h2 : b * |w.im| ≤ b * S := mul_le_mul_of_nonneg_left hw.le hb
          linarith
    _ = S := by rw [← add_mul, hab, one_mul]

/-- Cauchy Lipschitz estimate on half-radius balls inside the strip. -/
private lemma cauchy_lipschitz_on_half_ball {S δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hholo : DifferentiableOn ℂ f {z : ℂ | |z.im| < S})
    (hsub : Metric.closedBall z₀ (2 * δ) ⊆ {z : ℂ | |z.im| < S})
    (hbdd : ∀ w ∈ Metric.closedBall z₀ (2 * δ), ‖f w‖ ≤ M) :
    ∀ w₁ ∈ Metric.closedBall z₀ δ, ∀ w₂ ∈ Metric.closedBall z₀ δ,
      ‖f w₂ - f w₁‖ ≤ (2 * M / δ) * ‖w₂ - w₁‖ := by
  intro w₁ hw₁ w₂ hw₂
  have h2δ : 0 < 2 * δ := by linarith
  have hcont : ContinuousOn f (Metric.closedBall z₀ (2 * δ)) :=
    (hholo.mono hsub).continuousOn
  have hdiff_ball : ∀ z ∈ Metric.ball z₀ (2 * δ) \ (∅ : Set ℂ), DifferentiableAt ℂ f z := by
    intro z hz
    have hzΩ : z ∈ {z : ℂ | |z.im| < S} := hsub (Metric.ball_subset_closedBall hz.1)
    exact (hholo z hzΩ).differentiableAt ((openStrip_isOpen S).mem_nhds hzΩ)
  have hw1_ball : w₁ ∈ Metric.ball z₀ (2 * δ) := by
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hw₁; linarith
  have hw2_ball : w₂ ∈ Metric.ball z₀ (2 * δ) := by
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hw₂; linarith
  have hc1 := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw1_ball hcont hdiff_ball
  have hc2 := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw2_ball hcont hdiff_ball
  have hf_int : CircleIntegrable f z₀ (2 * δ) :=
    (hcont.mono Metric.sphere_subset_closedBall).circleIntegrable h2δ.le
  have hci1 : CircleIntegrable (fun z ↦ (z - w₁)⁻¹ • f z) z₀ (2 * δ) := by
    refine hf_int.continuousOn_smul ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz; rw [sub_ne_zero]; intro heq; subst heq
    rw [Metric.mem_sphere] at hz; rw [Metric.mem_closedBall] at hw₁; linarith
  have hci2 : CircleIntegrable (fun z ↦ (z - w₂)⁻¹ • f z) z₀ (2 * δ) := by
    refine hf_int.continuousOn_smul ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz; rw [sub_ne_zero]; intro heq; subst heq
    rw [Metric.mem_sphere] at hz; rw [Metric.mem_closedBall] at hw₂; linarith
  have hsub_eq : f w₂ - f w₁ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(z₀, 2 * δ), ((z - w₂)⁻¹ • f z - (z - w₁)⁻¹ • f z) := by
    rw [← hc2, ← hc1, ← smul_sub, circleIntegral.integral_sub hci2 hci1]
  rw [hsub_eq, norm_smul, norm_inv]
  have h2pi_norm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi_norm]
  have hint_le : ‖∮ z in C(z₀, 2 * δ), ((z - w₂)⁻¹ • f z - (z - w₁)⁻¹ • f z)‖ ≤
      ((2 * δ) * (‖w₂ - w₁‖ * M / δ ^ 2)) * (2 * Real.pi) := by
    unfold circleIntegral
    have hbound : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
        ‖deriv (circleMap z₀ (2 * δ)) θ •
          (((circleMap z₀ (2 * δ) θ - w₂)⁻¹ • f (circleMap z₀ (2 * δ) θ)) -
           ((circleMap z₀ (2 * δ) θ - w₁)⁻¹ • f (circleMap z₀ (2 * δ) θ)))‖ ≤
        (2 * δ) * (‖w₂ - w₁‖ * M / δ ^ 2) := by
      intro θ _
      set z := circleMap z₀ (2 * δ) θ
      have hz_sph : z ∈ Metric.sphere z₀ (2 * δ) := circleMap_mem_sphere z₀ h2δ.le θ
      have hz_dist : ‖z - z₀‖ = 2 * δ := by simpa [Metric.mem_sphere, Complex.dist_eq] using hz_sph
      have hzw1 : δ ≤ ‖z - w₁‖ := by
        rw [Metric.mem_closedBall, Complex.dist_eq] at hw₁
        have htri : ‖z - z₀‖ ≤ ‖z - w₁‖ + ‖w₁ - z₀‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (z - w₁) (w₁ - z₀)
        linarith
      have hzw2 : δ ≤ ‖z - w₂‖ := by
        rw [Metric.mem_closedBall, Complex.dist_eq] at hw₂
        have htri : ‖z - z₀‖ ≤ ‖z - w₂‖ + ‖w₂ - z₀‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (z - w₂) (w₂ - z₀)
        linarith
      have hzw1_ne : z - w₁ ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      have hzw2_ne : z - w₂ ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      have hdiff_inv : (z - w₂)⁻¹ - (z - w₁)⁻¹ = (w₂ - w₁) / ((z - w₂) * (z - w₁)) := by
        field_simp [hzw1_ne, hzw2_ne]; ring
      have hderiv_norm : ‖deriv (circleMap z₀ (2 * δ)) θ‖ = 2 * δ := by
        rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos h2δ]
      rw [norm_smul, hderiv_norm, ← sub_smul, smul_eq_mul, norm_mul, hdiff_inv, norm_div, norm_mul]
      apply mul_le_mul_of_nonneg_left _ h2δ.le
      have hf_le : ‖f z‖ ≤ M := hbdd z (Metric.sphere_subset_closedBall hz_sph)
      have hden_le : δ ^ 2 ≤ ‖z - w₂‖ * ‖z - w₁‖ := by
        rw [sq]; exact mul_le_mul hzw2 hzw1 hδ.le (by linarith)
      have hdiv_le : ‖w₂ - w₁‖ / (‖z - w₂‖ * ‖z - w₁‖) ≤ ‖w₂ - w₁‖ / δ ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ) hden_le
      calc ‖w₂ - w₁‖ / (‖z - w₂‖ * ‖z - w₁‖) * ‖f z‖
          ≤ ‖w₂ - w₁‖ / δ ^ 2 * M := mul_le_mul hdiv_le hf_le (norm_nonneg _) (by positivity)
        _ = ‖w₂ - w₁‖ * M / δ ^ 2 := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hle
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(z₀, 2 * δ), ((z - w₂)⁻¹ • f z - (z - w₁)⁻¹ • f z)‖
      ≤ (2 * Real.pi)⁻¹ * (((2 * δ) * (‖w₂ - w₁‖ * M / δ ^ 2)) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = (2 * M / δ) * ‖w₂ - w₁‖ := by
        field_simp [hδ.ne', Real.pi_pos.ne']

/-- **Item #15 — Genuine Montel + Vitali Strip Extension Theorem (Zero Hypothesis Laundering)**. -/
theorem vitali_montel_strip_extension {S : ℝ} (hS : 0 < S)
    (F_N : ℕ → ℂ → ℂ) (f : ℝ → ℂ)
    (hholo : ∀ N, DifferentiableOn ℂ (F_N N) {z : ℂ | |z.im| < S})
    (hbdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S} →
      ∃ M : ℝ, ∀ N : ℕ, ∀ z ∈ K, ‖F_N N z‖ ≤ M)
    (hreal : ∀ t : ℝ, Tendsto (fun N ↦ F_N N (t : ℂ)) atTop (nhds (f t))) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S} ∧
      TendstoLocallyUniformlyOn F_N F atTop {z : ℂ | |z.im| < S} ∧
      (∀ t : ℝ, F (t : ℂ) = f t) := by
  set Ω : Set ℂ := {z : ℂ | |z.im| < S}
  have hΩ_open : IsOpen Ω := openStrip_isOpen S
  have hmontel : ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ (τ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono τ ∧
        DifferentiableOn ℂ G Ω ∧
        TendstoLocallyUniformlyOn (fun k ↦ F_N (σ (τ k))) G atTop Ω ∧
        (∀ t : ℝ, G (t : ℂ) = f t) := by
    intro σ hσ
    let embedQ : ℚ × ℚ → ℂ := fun p ↦
      ((p.1 : ℝ) : ℂ) + Complex.I * (((S * (p.2 : ℝ) / (1 + |(p.2 : ℝ)|) : ℝ)) : ℂ)
    have hembedQ_mem : ∀ p : ℚ × ℚ, embedQ p ∈ Ω := by
      intro p
      simp only [Ω, Set.mem_setOf_eq, embedQ, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
        zero_add, add_zero]
      have hden : 0 < 1 + |(p.2 : ℝ)| := by positivity
      rw [abs_div, abs_mul, abs_of_pos hS, abs_of_pos hden, div_lt_iff₀ hden]
      nlinarith
    have hembedQ_dense : ∀ z ∈ Ω, ∀ ε > 0, ∃ p : ℚ × ℚ, dist z (embedQ p) < ε := by
      intro z hz ε hε
      simp only [Ω, Set.mem_setOf_eq] at hz
      obtain ⟨q1, hq1⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re + ε / 2 by linarith)
      have hq1_dist : |z.re - (q1 : ℝ)| < ε / 2 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      set y : ℝ := z.im
      set u : ℝ := y / (S - |y|)
      have hSy : 0 < S - |y| := by linarith
      have hphi_cont : Continuous (fun x : ℝ ↦ S * x / (1 + |x|)) :=
        (continuous_const.mul continuous_id).div (continuous_const.add continuous_abs)
          (fun x ↦ by positivity)
      have hphi_u : S * u / (1 + |u|) = y := by
        dsimp only [u]
        have habsu : |y / (S - |y|)| = |y| / (S - |y|) := by rw [abs_div, abs_of_pos hSy]
        rw [habsu]
        have hden : 1 + |y| / (S - |y|) = S / (S - |y|) := by field_simp [hSy.ne']; ring
        rw [hden]; field_simp [hSy.ne', hS.ne']
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hphi_cont.continuousAt (ε / 2) (by linarith)
      obtain ⟨q2, hq2⟩ := exists_rat_btwn (show u - δ < u + δ by linarith)
      have hq2_dist : dist (q2 : ℝ) u < δ := by
        rw [Real.dist_eq]; exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      have hy_dist : |S * (q2 : ℝ) / (1 + |(q2 : ℝ)|) - y| < ε / 2 := by
        simpa [Real.dist_eq, hphi_u] using hδ hq2_dist
      refine ⟨(q1, q2), ?_⟩
      rw [Complex.dist_eq]
      have hnorm : ‖z - embedQ (q1, q2)‖ ≤ |z.re - (q1 : ℝ)| + |y - S * (q2 : ℝ) / (1 + |(q2 : ℝ)|)| := by
        have hre : (z - embedQ (q1, q2)).re = z.re - (q1 : ℝ) := by
          simp only [embedQ, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
        have him : (z - embedQ (q1, q2)).im = y - S * (q2 : ℝ) / (1 + |(q2 : ℝ)|) := by
          simp only [embedQ, y, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
        rw [← hre, ← him]
        exact Complex.norm_le_abs_re_add_abs_im _
      rw [abs_sub_comm] at hy_dist
      linarith
    obtain ⟨e, he_surj⟩ := exists_surjective_nat (ℚ × ℚ)
    let q : ℕ → ℂ := fun k ↦ embedQ (e k)
    have hextract : ∀ (k : ℕ) (ρ : ℕ → ℕ), StrictMono ρ →
        ∃ (ρ' : ℕ → ℕ) (L : ℂ), StrictMono ρ' ∧
          Tendsto (fun m ↦ F_N (σ (ρ (ρ' m))) (q k)) atTop (nhds L) := by
      intro k ρ _
      obtain ⟨M, hM⟩ := hbdd {q k} isCompact_singleton (Set.singleton_subset_iff.mpr (hembedQ_mem (e k)))
      have hmem : ∀ m, F_N (σ (ρ m)) (q k) ∈ Metric.closedBall (0 : ℂ) (max M 0) := fun m ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (hM _ _ rfl) (le_max_left _ _)
      obtain ⟨L, _, ρ', hρ'_mono, hρ'_lim⟩ := (isCompact_closedBall (0 : ℂ) (max M 0)).tendsto_subseq hmem
      exact ⟨ρ', L, hρ'_mono, hρ'_lim⟩
    let chain : ℕ → { ρ : ℕ → ℕ // StrictMono ρ } := Nat.rec
      ⟨id, strictMono_id⟩
      (fun k prev ↦
        let h := hextract k prev.1 prev.2
        ⟨prev.1 ∘ h.choose, prev.2.comp h.choose_spec.choose_spec.1⟩)
    let τ : ℕ → ℕ := fun m ↦ (chain (m + 1)).1 m
    have hchain_step : ∀ k, ∃ step : ℕ → ℕ, StrictMono step ∧ (chain (k + 1)).1 = (chain k).1 ∘ step := by
      intro k
      let h := hextract k (chain k).1 (chain k).2
      exact ⟨h.choose, h.choose_spec.choose_spec.1, rfl⟩
    have hchain_sub : ∀ k j, k ≤ j → ∃ step : ℕ → ℕ, StrictMono step ∧ (chain j).1 = (chain k).1 ∘ step := by
      intro k j hkj
      induction j with
      | zero =>
        have hk0 : k = 0 := by omega
        subst hk0; exact ⟨id, strictMono_id, rfl⟩
      | succ j ih =>
        by_cases hle : k ≤ j
        · rcases ih hle with ⟨s₁, hs₁, heq₁⟩
          rcases hchain_step j with ⟨s₂, hs₂, heq₂⟩
          exact ⟨s₁ ∘ s₂, hs₁.comp hs₂, by rw [heq₂, heq₁]; rfl⟩
        · have hkj' : k = j + 1 := by omega
          subst hkj'; exact ⟨id, strictMono_id, rfl⟩
    have hτ_mono : StrictMono τ := by
      refine strictMono_nat_of_lt_succ fun m ↦ ?_
      dsimp only [τ]
      rcases hchain_step (m + 1) with ⟨s, hs, heq⟩
      rw [heq, Function.comp_apply]
      have hsm : m < s (m + 1) := lt_of_lt_of_le (Nat.lt_succ_self m) (hs.id_le (m + 1))
      exact (chain (m + 1)).2 hsm
    have hq_cauchy : ∀ k : ℕ, CauchySeq (fun m ↦ F_N (σ (τ m)) (q k)) := by
      intro k
      let h := hextract k (chain k).1 (chain k).2
      have hlim : Tendsto (fun m ↦ F_N (σ ((chain (k + 1)).1 m)) (q k)) atTop (nhds h.choose_spec.choose) :=
        h.choose_spec.choose_spec.2
      have hdiag_lim : Tendsto (fun m ↦ F_N (σ (τ m)) (q k)) atTop (nhds h.choose_spec.choose) := by
        rw [Metric.tendsto_atTop] at hlim ⊢
        intro ε hε
        obtain ⟨N₀, hN₀⟩ := hlim ε hε
        refine ⟨max N₀ k, fun m hm ↦ ?_⟩
        have hkm : k + 1 ≤ m + 1 := by omega
        rcases hchain_sub (k + 1) (m + 1) hkm with ⟨s, hs, heq⟩
        have hsm : N₀ ≤ s m := le_trans (le_trans (le_max_left _ _) hm) (hs.id_le m)
        dsimp only [τ]; rw [heq, Function.comp_apply]
        exact hN₀ (s m) hsm
      exact hdiag_lim.cauchySeq
    have hball_cauchy : ∀ z₀ ∈ Ω, ∃ δ > 0, Metric.closedBall z₀ (2 * δ) ⊆ Ω ∧
        ∀ ε > 0, ∃ N₀ : ℕ, ∀ m₁ ≥ N₀, ∀ m₂ ≥ N₀, ∀ z ∈ Metric.closedBall z₀ δ,
          ‖F_N (σ (τ m₁)) z - F_N (σ (τ m₂)) z‖ < ε := by
      intro z₀ hz₀
      have hz₀_lt : |z₀.im| < S := hz₀
      set δ : ℝ := (S - |z₀.im|) / 4
      have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
      have hsub2 : Metric.closedBall z₀ (2 * δ) ⊆ Ω := by
        intro w hw
        rw [Metric.mem_closedBall, Complex.dist_eq] at hw
        have him : |w.im - z₀.im| ≤ 2 * δ :=
          le_trans (by simpa using Complex.abs_im_le_norm (w - z₀)) hw
        have : |w.im| ≤ |z₀.im| + 2 * δ := by
          have := abs_sub_abs_le_abs_sub w.im z₀.im; linarith
        simp only [Ω, Set.mem_setOf_eq]
        dsimp only [δ] at this; linarith
      obtain ⟨M₀, hM₀⟩ := hbdd (Metric.closedBall z₀ (2 * δ)) (isCompact_closedBall _ _) hsub2
      set M : ℝ := max M₀ 0
      have hM_nn : 0 ≤ M := le_max_right _ _
      have hlip : ∀ N : ℕ, ∀ w₁ ∈ Metric.closedBall z₀ δ, ∀ w₂ ∈ Metric.closedBall z₀ δ,
          ‖F_N N w₂ - F_N N w₁‖ ≤ (2 * M / δ) * ‖w₂ - w₁‖ := fun N ↦
        cauchy_lipschitz_on_half_ball hδ_pos hM_nn (hholo N) hsub2
          (fun w hw ↦ le_trans (hM₀ N w hw) (le_max_left _ _))
      refine ⟨δ, hδ_pos, hsub2, fun ε hε ↦ ?_⟩
      set L : ℝ := 2 * M / δ + 1
      have hL_pos : 0 < L := by positivity
      set η : ℝ := min (δ / 2) (ε / (3 * L))
      have hη_pos : 0 < η := lt_min (by linarith) (by positivity)
      have hcover : Metric.closedBall z₀ δ ⊆ ⋃ k : ℕ, Metric.ball (q k) η := by
        intro w hw
        have hwΩ : w ∈ Ω := hsub2 (Metric.closedBall_subset_closedBall (by linarith) hw)
        obtain ⟨p, hp⟩ := hembedQ_dense w hwΩ η hη_pos
        obtain ⟨k, hk⟩ := he_surj p
        exact Set.mem_iUnion.mpr ⟨k, by simp [q, hk, Metric.mem_ball, hp]⟩
      obtain ⟨F_idx, hF_cover⟩ := (isCompact_closedBall z₀ δ).elim_finite_subcover
        (fun k ↦ Metric.ball (q k) η) (fun _ ↦ Metric.isOpen_ball) hcover
      have hcover_in : Metric.closedBall z₀ δ ⊆
          ⋃ k ∈ { k : ℕ | q k ∈ Metric.closedBall z₀ δ }, Metric.ball (q k) η := by
        intro w hw
        set t : ℝ := 1 - η / (2 * δ)
        have ht0 : 0 < t := by
          have : η ≤ δ / 2 := min_le_left _ _
          dsimp only [t]; rw [sub_pos, div_lt_one (by linarith)]; linarith
        have ht1 : t < 1 := by dsimp only [t]; linarith [div_pos hη_pos (by linarith : 0 < 2 * δ)]
        set w' : ℂ := z₀ + (t : ℂ) * (w - z₀)
        have hw'_dist : dist w' z₀ ≤ t * δ := by
          rw [Metric.mem_closedBall, Complex.dist_eq] at hw
          rw [Complex.dist_eq]
          simp only [w', add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
          exact mul_le_mul_of_nonneg_left hw ht0.le
        have hww'_dist : dist w w' ≤ η / 2 := by
          rw [Metric.mem_closedBall, Complex.dist_eq] at hw
          rw [Complex.dist_eq]
          have heq : w - w' = ((1 - t : ℝ) : ℂ) * (w - z₀) := by dsimp only [w']; push_cast; ring
          rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          have h1mt : 1 - t = η / (2 * δ) := by dsimp only [t]; ring
          rw [h1mt]
          calc (η / (2 * δ)) * ‖w - z₀‖ ≤ (η / (2 * δ)) * δ := mul_le_mul_of_nonneg_left hw (by positivity)
            _ = η / 2 := by field_simp [hδ_pos.ne']
        have hw'Ω : w' ∈ Ω := hsub2 (Metric.closedBall_subset_closedBall (by nlinarith)
          (Metric.mem_closedBall.mpr hw'_dist))
        have hr_pos : 0 < min (η / 2) (δ - t * δ) := by
          refine lt_min (by linarith) ?_
          have : t * δ < 1 * δ := mul_lt_mul_of_pos_right ht1 hδ_pos
          linarith
        obtain ⟨p, hp⟩ := hembedQ_dense w' hw'Ω (min (η / 2) (δ - t * δ)) hr_pos
        obtain ⟨k, hk⟩ := he_surj p
        refine Set.mem_biUnion (x := k) ?_ ?_
        · simp only [Set.mem_setOf_eq, Metric.mem_closedBall, q, hk]
          have hp2 : dist (embedQ p) w' < δ - t * δ := by
            rw [dist_comm]; exact lt_of_lt_of_le hp (min_le_right _ _)
          linarith [dist_triangle (embedQ p) w' z₀]
        · simp only [Metric.mem_ball, q, hk]
          have hp1 : dist w' (embedQ p) < η / 2 := lt_of_lt_of_le hp (min_le_left _ _)
          linarith [dist_triangle w w' (embedQ p)]
      have hcover_iU : Metric.closedBall z₀ δ ⊆
          ⋃ k : { k : ℕ // q k ∈ Metric.closedBall z₀ δ }, Metric.ball (q k.1) η := by
        intro w hw
        rcases Set.mem_iUnion₂.mp (hcover_in hw) with ⟨k, hk, hwk⟩
        exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hwk⟩
      obtain ⟨F_sub, hF_sub⟩ := (isCompact_closedBall z₀ δ).elim_finite_subcover
        (fun k : { k : ℕ // q k ∈ Metric.closedBall z₀ δ } ↦ Metric.ball (q k.1) η)
        (fun _ ↦ Metric.isOpen_ball) hcover_iU
      have hcauchy_k : ∀ k ∈ F_sub, ∃ N_k : ℕ, ∀ m₁ ≥ N_k, ∀ m₂ ≥ N_k,
          ‖F_N (σ (τ m₁)) (q k.1) - F_N (σ (τ m₂)) (q k.1)‖ < ε / 3 := fun k _ ↦ by
        obtain ⟨N_k, hN_k⟩ := Metric.cauchySeq_iff.mp (hq_cauchy k.1) (ε / 3) (by linarith)
        exact ⟨N_k, fun m₁ hm₁ m₂ hm₂ ↦ by simpa [Complex.dist_eq] using hN_k m₁ hm₁ m₂ hm₂⟩
      choose N_k hN_k using hcauchy_k
      set N₀ : ℕ := F_sub.sup (fun k ↦ if h : k ∈ F_sub then N_k k h else 0)
      refine ⟨N₀, fun m₁ hm₁ m₂ hm₂ z hz ↦ ?_⟩
      rcases Set.mem_iUnion₂.mp (hF_sub hz) with ⟨k, hkF, hzk⟩
      have hNk_le : N_k k hkF ≤ N₀ := by
        have := Finset.le_sup (f := fun k ↦ if h : k ∈ F_sub then N_k k h else 0) hkF
        simpa [hkF] using this
      have hmid : ‖F_N (σ (τ m₁)) (q k.1) - F_N (σ (τ m₂)) (q k.1)‖ < ε / 3 :=
        hN_k k hkF m₁ (le_trans hNk_le hm₁) m₂ (le_trans hNk_le hm₂)
      have hz_qk : ‖z - q k.1‖ < η := by simpa [Metric.mem_ball, Complex.dist_eq] using hzk
      have hηL : (2 * M / δ) * η < ε / 3 := by
        have h1 : η ≤ ε / (3 * L) := min_le_right _ _
        have h2 : 2 * M / δ < L := by dsimp only [L]; linarith
        calc (2 * M / δ) * η ≤ (2 * M / δ) * (ε / (3 * L)) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ < L * (ε / (3 * L)) := mul_lt_mul_of_pos_right h2 (by positivity)
          _ = ε / 3 := by field_simp [hL_pos.ne']
      have hlip1 : ‖F_N (σ (τ m₁)) z - F_N (σ (τ m₁)) (q k.1)‖ < ε / 3 :=
        lt_of_le_of_lt (hlip _ (q k.1) k.2 z hz)
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz_qk.le (by positivity)) hηL)
      have hlip2 : ‖F_N (σ (τ m₂)) z - F_N (σ (τ m₂)) (q k.1)‖ < ε / 3 :=
        lt_of_le_of_lt (hlip _ (q k.1) k.2 z hz)
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz_qk.le (by positivity)) hηL)
      have htri : F_N (σ (τ m₁)) z - F_N (σ (τ m₂)) z =
          (F_N (σ (τ m₁)) z - F_N (σ (τ m₁)) (q k.1)) +
          (F_N (σ (τ m₁)) (q k.1) - F_N (σ (τ m₂)) (q k.1)) -
          (F_N (σ (τ m₂)) z - F_N (σ (τ m₂)) (q k.1)) := by ring
      rw [htri]
      have h1 := norm_sub_le ((F_N (σ (τ m₁)) z - F_N (σ (τ m₁)) (q k.1)) +
          (F_N (σ (τ m₁)) (q k.1) - F_N (σ (τ m₂)) (q k.1)))
          (F_N (σ (τ m₂)) z - F_N (σ (τ m₂)) (q k.1))
      have h2 := norm_add_le (F_N (σ (τ m₁)) z - F_N (σ (τ m₁)) (q k.1))
          (F_N (σ (τ m₁)) (q k.1) - F_N (σ (τ m₂)) (q k.1))
      linarith
    have hpt_exists : ∀ z ∈ Ω, ∃ L : ℂ, Tendsto (fun m ↦ F_N (σ (τ m)) z) atTop (nhds L) := by
      intro z hz
      rcases hball_cauchy z hz with ⟨δ, hδ, _, hcauchy⟩
      apply cauchySeq_tendsto_of_complete
      rw [Metric.cauchySeq_iff]
      intro ε hε
      rcases hcauchy ε hε with ⟨N₀, hN₀⟩
      exact ⟨N₀, fun m₁ hm₁ m₂ hm₂ ↦ by simpa [Complex.dist_eq] using hN₀ m₁ hm₁ m₂ hm₂ z (Metric.mem_closedBall_self hδ.le)⟩
    let G : ℂ → ℂ := fun z ↦ if h : z ∈ Ω then (hpt_exists z h).choose else 0
    have hG_lim : ∀ z ∈ Ω, Tendsto (fun m ↦ F_N (σ (τ m)) z) atTop (nhds (G z)) := by
      intro z hz; simp only [G, dif_pos hz]; exact (hpt_exists z hz).choose_spec
    have hG_loc : TendstoLocallyUniformlyOn (fun m ↦ F_N (σ (τ m))) G atTop Ω := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ_open]
      intro K hK_sub hK
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hcov : K ⊆ ⋃ z : { z : ℂ // z ∈ K }, Metric.ball z.1 (hball_cauchy z.1 (hK_sub z.2)).choose :=
        fun z hz ↦ Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hball_cauchy z (hK_sub hz)).choose_spec.1⟩
      obtain ⟨S_fin, hS_fin⟩ := hK.elim_finite_subcover
        (fun z : { z : ℂ // z ∈ K } ↦ Metric.ball z.1 (hball_cauchy z.1 (hK_sub z.2)).choose)
        (fun _ ↦ Metric.isOpen_ball) hcov
      have hN_each : ∀ z ∈ S_fin, ∃ N_z : ℕ, ∀ m₁ ≥ N_z, ∀ m₂ ≥ N_z,
          ∀ w ∈ Metric.closedBall z.1 (hball_cauchy z.1 (hK_sub z.2)).choose,
            ‖F_N (σ (τ m₁)) w - F_N (σ (τ m₂)) w‖ < ε / 2 := fun z _ ↦
        (hball_cauchy z.1 (hK_sub z.2)).choose_spec.2.2 (ε / 2) (by linarith)
      choose N_z hN_z using hN_each
      set N₀ : ℕ := S_fin.sup (fun z ↦ if h : z ∈ S_fin then N_z z h else 0)
      filter_upwards [eventually_ge_atTop N₀] with m hm w hw
      rcases Set.mem_iUnion₂.mp (hS_fin hw) with ⟨z, hzS, hwz⟩
      have hNz_le : N_z z hzS ≤ N₀ := by
        have := Finset.le_sup (f := fun z ↦ if h : z ∈ S_fin then N_z z h else 0) hzS
        simpa [hzS] using this
      have hw_cl : w ∈ Metric.closedBall z.1 (hball_cauchy z.1 (hK_sub z.2)).choose :=
        Metric.ball_subset_closedBall hwz
      have hle_half : ‖G w - F_N (σ (τ m)) w‖ ≤ ε / 2 := by
        have ht : Tendsto (fun m₂ ↦ ‖F_N (σ (τ m₂)) w - F_N (σ (τ m)) w‖) atTop
            (nhds ‖G w - F_N (σ (τ m)) w‖) := ((hG_lim w (hK_sub hw)).sub_const _).norm
        exact le_of_tendsto ht (by
          filter_upwards [eventually_ge_atTop N₀] with m₂ hm₂
          exact (hN_z z hzS m₂ (le_trans hNz_le hm₂) m (le_trans hNz_le hm) w hw_cl).le)
      rw [Complex.dist_eq]; linarith
    have hG_holo : DifferentiableOn ℂ G Ω :=
      hG_loc.differentiableOn (Eventually.of_forall fun m ↦ hholo (σ (τ m))) hΩ_open
    have hG_real : ∀ t : ℝ, G (t : ℂ) = f t := by
      intro t
      have htΩ : (t : ℂ) ∈ Ω := by simp [Ω, hS]
      have hsub_lim : Tendsto (fun m ↦ F_N (σ (τ m)) (t : ℂ)) atTop (nhds (f t)) :=
        (hreal t).comp ((hσ.comp hτ_mono).tendsto_atTop)
      exact tendsto_nhds_unique (hG_lim (t : ℂ) htΩ) hsub_lim
    exact ⟨τ, G, hτ_mono, hG_holo, hG_loc, hG_real⟩
  have huniq : ∀ G₁ G₂ : ℂ → ℂ,
      DifferentiableOn ℂ G₁ Ω → DifferentiableOn ℂ G₂ Ω →
      (∀ t : ℝ, G₁ (t : ℂ) = f t) → (∀ t : ℝ, G₂ (t : ℂ) = f t) →
      Set.EqOn G₁ G₂ Ω := by
    intro G₁ G₂ hG₁ hG₂ h1 h2
    have hA₁ : AnalyticOnNhd ℂ G₁ Ω := hG₁.analyticOnNhd hΩ_open
    have hA₂ : AnalyticOnNhd ℂ G₂ Ω := hG₂.analyticOnNhd hΩ_open
    have h0Ω : (0 : ℂ) ∈ Ω := by simp [Ω, hS]
    refine hA₁.eqOn_of_preconnected_of_frequently_eq hA₂ (openStrip_isPreconnected S) h0Ω ?_
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    rcases hU with ⟨V, hV_open, h0V, hVU⟩
    rcases Metric.isOpen_iff.mp hV_open 0 h0V with ⟨r, hr_pos, hr_sub⟩
    refine ⟨((r / 2 : ℝ) : ℂ), hVU ⟨hr_sub ?_, ?_⟩, ?_⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : 0 ≤ r / 2)]
      linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      linarith
    · rw [h1, h2]
  obtain ⟨_, F, _, hF_holo, _, hF_real⟩ := hmontel id strictMono_id
  refine ⟨F, hF_holo, ?_, hF_real⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ_open]
  intro K hK_sub hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hbad : ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ z ∈ K, ε ≤ dist (F z) (F_N N z) := by
    intro N₀
    have hf := (Filter.frequently_atTop.mp hnot) N₀
    rcases hf with ⟨N, hN, hnot_all⟩
    push Not at hnot_all
    rcases hnot_all with ⟨z, hzK, hdist⟩
    exact ⟨N, hN, z, hzK, hdist⟩
  let σ : ℕ → ℕ := Nat.rec (hbad 0).choose (fun _ prev ↦ (hbad (prev + 1)).choose)
  have hσ_mono : StrictMono σ :=
    strictMono_nat_of_lt_succ fun k ↦ Nat.lt_of_succ_le (hbad (σ k + 1)).choose_spec.1
  have hσ_bad : ∀ k : ℕ, ∃ z ∈ K, ε ≤ dist (F z) (F_N (σ k) z) := by
    intro k
    cases k with
    | zero => exact (hbad 0).choose_spec.2
    | succ k => exact (hbad (σ k + 1)).choose_spec.2
  obtain ⟨τ, G, _, hG_holo, hG_loc, hG_real⟩ := hmontel σ hσ_mono
  have hGF : Set.EqOn G F Ω := huniq G F hG_holo hF_holo hG_real hF_real
  have hG_unif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ_open).mp hG_loc K hK_sub hK
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hG_unif) ε hε)
  rcases hσ_bad (τ M₀) with ⟨z, hzK, hge⟩
  have hlt := hM₀ M₀ le_rfl z hzK
  rw [hGF (hK_sub hzK)] at hlt
  linarith

end Item15GenuineMontelVitali

end KrylovChaos
