/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.DoubleWellTunneling
import KrylovChaos.Milestone4Section9AppB
import KrylovChaos.Milestone2AnalyticFoundations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Proposition 9.1(1): Bochner-to-Spectral-Measure Bridge and 2D Finite-Window Gaussian OTOC Convolution

Establishes two concrete upgrades for Proposition 9.1(1):
1. **Bochner-to-Spectral-Measure Bridge (`gaussianSmearBochner_eq_gaussianSmear`)**:
   Proves that for every `σ > 0`, Hermitian `H : QubitOp N`, and operator `O : QubitOp N`,
   the Bochner-integral Gaussian time-smeared operator `gaussianSmearBochner hH σ O` equals
   the spectral-basis operator `gaussianSmear hH σ O`, and consequently its Wightman spectral
   weights and spectral measure obey `w_σ(a, b) = exp(-σ² (E_a - E_b)²) w_0(a, b)` and
   `wightmanSpectralMeasure hH β W_σ = (wightmanSpectralMeasure hH β W₀).withDensity (exp(-σ² ω²))`.
2. **2D Double-Time Finite-Window Gaussian OTOC Convolution (`prop_9_1_part1_2d_finite_window_otoc`)**:
   For a bounded double-time OTOC `|F(t₁, t₂)| ≤ M_bound` obeying the finite-window scrambling
   asymptotics `|F(t + s₁, t + s₂) - (F_d - ε e^{λ_L (t + (s₁ + s₂)/2)})| ≤ C_R` on
   `|s₁|, |s₂| ≤ Δt` (`Δt > σ² λ_L / 2`), proves that the 2D Gaussian-smeared OTOC satisfies
   `|F_σ(t) - (F_d - ε e^{σ² λ_L² / 4} e^{λ_L t})| ≤ C_R + tail_bound` with explicit Gaussian tail
   cutoff `O(e^{-Δt² / (2 σ²)})` and exact prefactor `exp(σ² λ_L² / 4)`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section GaussianFourierBridge

private lemma gaussianKernel_pos {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    0 < gaussianKernel σ s := by
  unfold gaussianKernel; positivity

private lemma integrable_gaussianKernel {σ : ℝ} (hσ : 0 < σ) :
    Integrable (gaussianKernel σ) := by
  simpa using integrable_gaussianKernel_mul_exp hσ 0

private lemma integrable_abs_mul_gaussianKernel {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun s : ℝ ↦ |s| * gaussianKernel σ s) := by
  have hdom : Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.exp (1 * s) +
      gaussianKernel σ s * Real.exp ((-1) * s)) :=
    (integrable_gaussianKernel_mul_exp hσ 1).add (integrable_gaussianKernel_mul_exp hσ (-1))
  refine hdom.mono' ?_ ?_
  · exact (continuous_abs.mul (by unfold gaussianKernel; fun_prop)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg s) (gaussianKernel_pos hσ s).le)]
    have h1 : |s| ≤ Real.exp s + Real.exp (-s) := by
      rcases le_total 0 s with hs | hs
      · rw [abs_of_nonneg hs]
        have := Real.add_one_le_exp s
        have := Real.exp_pos (-s)
        linarith
      · rw [abs_of_nonpos hs]
        have := Real.add_one_le_exp (-s)
        have := Real.exp_pos s
        linarith
    have hg := (gaussianKernel_pos hσ s).le
    have hmul := mul_le_mul_of_nonneg_left h1 hg
    simpa [mul_comm, mul_add] using hmul

/-- Oddness: `∫ s, gaussianKernel σ s * sin (ω * s) = 0`. -/
lemma integral_gaussianKernel_mul_sin {σ : ℝ} (hσ : 0 < σ) (ω : ℝ) :
    ∫ s : ℝ, gaussianKernel σ s * Real.sin (ω * s) = 0 := by
  have hodd : ∀ s : ℝ, gaussianKernel σ (-s) * Real.sin (ω * (-s)) =
      -(gaussianKernel σ s * Real.sin (ω * s)) := by
    intro s
    unfold gaussianKernel
    rw [neg_sq, mul_neg, Real.sin_neg]
    ring
  have h1 : ∫ s : ℝ, gaussianKernel σ s * Real.sin (ω * s) =
      ∫ s : ℝ, gaussianKernel σ (-s) * Real.sin (ω * (-s)) :=
    (MeasureTheory.integral_neg_eq_self (fun s ↦ gaussianKernel σ s * Real.sin (ω * s)) volume).symm
  simp_rw [hodd, integral_neg] at h1
  linarith

/-- Cosine Fourier transform of the Gaussian kernel via ODE uniqueness:
`∫ s, gaussianKernel σ s * cos (ω * s) = exp (-(σ² / 2) * ω²)`. -/
theorem integral_gaussianKernel_mul_cos {σ : ℝ} (hσ : 0 < σ) (ω : ℝ) :
    ∫ s : ℝ, gaussianKernel σ s * Real.cos (ω * s) = Real.exp (-(σ ^ 2 / 2) * ω ^ 2) := by
  let f : ℝ → ℝ := fun u ↦ ∫ s : ℝ, gaussianKernel σ s * Real.cos (u * s)
  have hf0 : f 0 = 1 := by
    dsimp only [f]; simp [integral_gaussianKernel_eq_one hσ]
  have hf_deriv : ∀ u : ℝ, HasDerivAt f (-(σ ^ 2) * u * f u) u := by
    intro u
    -- Step 1: Differentiate under the integral sign.
    have hparam : HasDerivAt f (∫ s : ℝ, -(gaussianKernel σ s * s * Real.sin (u * s))) u := by
      have h1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun u s ↦ gaussianKernel σ s * Real.cos (u * s))
        (F' := fun u s ↦ -(gaussianKernel σ s * s * Real.sin (u * s)))
        (s := Set.univ) (x₀ := u) (bound := fun s ↦ |s| * gaussianKernel σ s)
        (Filter.univ_mem)
        (Filter.Eventually.of_forall fun v ↦
          ((by unfold gaussianKernel; fun_prop : Continuous fun s ↦ gaussianKernel σ s * Real.cos (v * s)).aestronglyMeasurable))
        (by
          refine (integrable_gaussianKernel hσ).mono' ?_ ?_
          · exact (by unfold gaussianKernel; fun_prop : Continuous fun s ↦ gaussianKernel σ s * Real.cos (u * s)).aestronglyMeasurable
          · filter_upwards with s
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ s).le]
            exact mul_le_of_le_one_right (gaussianKernel_pos hσ s).le (Real.abs_cos_le_one _))
        ((by unfold gaussianKernel; fun_prop : Continuous fun s ↦ -(gaussianKernel σ s * s * Real.sin (u * s))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun s v _ ↦ by
          rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ s).le]
          calc gaussianKernel σ s * |s| * |Real.sin (v * s)|
              ≤ gaussianKernel σ s * |s| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
                  (mul_nonneg (gaussianKernel_pos hσ s).le (abs_nonneg s))
            _ = |s| * gaussianKernel σ s := by ring)
        (integrable_abs_mul_gaussianKernel hσ)
        (Filter.Eventually.of_forall fun s v _ ↦ by
          have hc : HasDerivAt (fun w : ℝ ↦ Real.cos (w * s)) (-Real.sin (v * s) * s) v := by
            simpa using ((hasDerivAt_id v).mul_const s).cos
          convert hc.const_mul (gaussianKernel σ s) using 1; ring)
      exact h1.2
    -- Step 2: Integration by parts on `[-R, R]` and `R → ∞`.
    have hibp : ∫ s : ℝ, -(gaussianKernel σ s * s * Real.sin (u * s)) = -(σ ^ 2) * u * f u := by
      have hg_deriv : ∀ s : ℝ, HasDerivAt (gaussianKernel σ) (-(s / σ ^ 2) * gaussianKernel σ s) s := by
        intro s
        have hlin : HasDerivAt (fun x : ℝ ↦ -(x ^ 2) / (2 * σ ^ 2)) (-(s / σ ^ 2)) s := by
          have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * s) s := by
            simpa using hasDerivAt_pow 2 s
          refine ((hsq.neg).div_const (2 * σ ^ 2)).congr_deriv ?_
          field_simp [hσ.ne']
        have hexp := hlin.exp
        have hdiv := hexp.div_const (Real.sqrt (2 * Real.pi) * σ)
        refine hdiv.congr_deriv ?_
        unfold gaussianKernel; ring
      have hsin_deriv : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ Real.sin (u * x)) (u * Real.cos (u * s)) s := by
        intro s
        have hlin : HasDerivAt (fun x : ℝ ↦ u * x) u s := by
          simpa using (hasDerivAt_id s).const_mul u
        simpa [mul_comm] using hlin.sin
      have hseg : ∀ R : ℝ,
          (∫ s in (-R)..R, (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s)) +
          (∫ s in (-R)..R, gaussianKernel σ s * (u * Real.cos (u * s))) =
          gaussianKernel σ R * Real.sin (u * R) - gaussianKernel σ (-R) * Real.sin (u * (-R)) := by
        intro R
        have hprod := intervalIntegral.integral_mul_deriv_eq_deriv_mul
          (u := gaussianKernel σ) (v := fun x ↦ Real.sin (u * x))
          (u' := fun s ↦ -(s / σ ^ 2) * gaussianKernel σ s)
          (v' := fun s ↦ u * Real.cos (u * s))
          (a := -R) (b := R)
          (fun s _ ↦ hg_deriv s) (fun s _ ↦ hsin_deriv s)
          ((by unfold gaussianKernel; fun_prop : Continuous fun s ↦ -(s / σ ^ 2) * gaussianKernel σ s).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun s ↦ u * Real.cos (u * s)).intervalIntegrable _ _)
        linarith
      have hint1 : Integrable (fun s : ℝ ↦ (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s)) := by
        refine ((integrable_abs_mul_gaussianKernel hσ).const_mul (1 / σ ^ 2)).mono' ?_ ?_
        · exact (by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable
        · filter_upwards with s
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_div,
            abs_of_pos (sq_pos_of_pos hσ), abs_of_nonneg (gaussianKernel_pos hσ s).le]
          calc |s| / σ ^ 2 * gaussianKernel σ s * |Real.sin (u * s)|
              ≤ |s| / σ ^ 2 * gaussianKernel σ s * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
                  (mul_nonneg (div_nonneg (abs_nonneg s) (sq_nonneg σ)) (gaussianKernel_pos hσ s).le)
            _ = 1 / σ ^ 2 * (|s| * gaussianKernel σ s) := by ring
      have hint2 : Integrable (fun s : ℝ ↦ gaussianKernel σ s * (u * Real.cos (u * s))) := by
        refine ((integrable_gaussianKernel hσ).const_mul |u|).mono' ?_ ?_
        · exact (by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable
        · filter_upwards with s
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ s).le]
          calc gaussianKernel σ s * (|u| * |Real.cos (u * s)|)
              ≤ gaussianKernel σ s * (|u| * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
                  (gaussianKernel_pos hσ s).le
            _ = |u| * gaussianKernel σ s := by ring
      have htend1 : Tendsto (fun R : ℝ ↦ ∫ s in (-R)..R, (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s))
          atTop (nhds (∫ s : ℝ, (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s))) :=
        intervalIntegral_tendsto_integral hint1 tendsto_neg_atTop_atBot tendsto_id
      have htend2 : Tendsto (fun R : ℝ ↦ ∫ s in (-R)..R, gaussianKernel σ s * (u * Real.cos (u * s)))
          atTop (nhds (∫ s : ℝ, gaussianKernel σ s * (u * Real.cos (u * s)))) :=
        intervalIntegral_tendsto_integral hint2 tendsto_neg_atTop_atBot tendsto_id
      have htend_bd : Tendsto (fun R : ℝ ↦
          gaussianKernel σ R * Real.sin (u * R) - gaussianKernel σ (-R) * Real.sin (u * (-R)))
          atTop (nhds 0) := by
        have hg0 : Tendsto (fun R : ℝ ↦ gaussianKernel σ R) atTop (nhds 0) := by
          unfold gaussianKernel
          have hsq : Tendsto (fun R : ℝ ↦ -(R ^ 2) / (2 * σ ^ 2)) atTop atBot := by
            have h1 : Tendsto (fun R : ℝ ↦ R ^ 2) atTop atTop :=
              tendsto_pow_atTop (by norm_num)
            have h2 : Tendsto (fun R : ℝ ↦ R ^ 2 / (2 * σ ^ 2)) atTop atTop :=
              h1.atTop_div_const (by positivity)
            have h3 := tendsto_neg_atTop_atBot.comp h2
            simpa only [Function.comp_def, neg_div] using h3
          simpa using (Real.tendsto_exp_atBot.comp hsq).div_const (Real.sqrt (2 * Real.pi) * σ)
        have hterm : Tendsto (fun R : ℝ ↦ 2 * gaussianKernel σ R) atTop (nhds 0) := by
          simpa using hg0.const_mul 2
        refine squeeze_zero_norm ?_ hterm
        intro R
        rw [Real.norm_eq_abs]
        have heven : gaussianKernel σ (-R) = gaussianKernel σ R := by
          unfold gaussianKernel; rw [neg_sq]
        rw [heven]
        calc |gaussianKernel σ R * Real.sin (u * R) - gaussianKernel σ R * Real.sin (u * (-R))|
            ≤ |gaussianKernel σ R * Real.sin (u * R)| + |gaussianKernel σ R * Real.sin (u * (-R))| :=
              abs_sub _ _
          _ = gaussianKernel σ R * |Real.sin (u * R)| + gaussianKernel σ R * |Real.sin (u * (-R))| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ R).le]
          _ ≤ gaussianKernel σ R * 1 + gaussianKernel σ R * 1 :=
              add_le_add
                (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (gaussianKernel_pos hσ R).le)
                (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (gaussianKernel_pos hσ R).le)
          _ = 2 * gaussianKernel σ R := by ring
      have hlim_eq : (∫ s : ℝ, (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s)) +
          (∫ s : ℝ, gaussianKernel σ s * (u * Real.cos (u * s))) = 0 :=
        tendsto_nhds_unique ((htend1.add htend2).congr hseg) htend_bd
      have hfactor1 : (∫ s : ℝ, (-(s / σ ^ 2) * gaussianKernel σ s) * Real.sin (u * s)) =
          (1 / σ ^ 2) * (∫ s : ℝ, -(gaussianKernel σ s * s * Real.sin (u * s))) := by
        rw [← integral_const_mul]
        congr 1; funext s; ring
      have hfactor2 : (∫ s : ℝ, gaussianKernel σ s * (u * Real.cos (u * s))) = u * f u := by
        dsimp only [f]; rw [← integral_const_mul]; congr 1; funext s; ring
      rw [hfactor1, hfactor2] at hlim_eq
      have hσ2 : σ ^ 2 ≠ 0 := (sq_pos_of_pos hσ).ne'
      have hmul : (∫ s : ℝ, -(gaussianKernel σ s * s * Real.sin (u * s))) + σ ^ 2 * u * f u = 0 := by
        have h := congrArg (fun x ↦ σ ^ 2 * x) hlim_eq
        simp only [mul_add, mul_zero, ← mul_assoc, mul_one_div_cancel hσ2, one_mul] at h
        exact h
      linarith
    rw [← hibp]; exact hparam
  -- Step 3: Conclude `exp (σ² u² / 2) * f u = 1` for all `u`.
  let g : ℝ → ℝ := fun u ↦ Real.exp (σ ^ 2 * u ^ 2 / 2) * f u
  have hg_deriv : ∀ u : ℝ, HasDerivAt g 0 u := by
    intro u
    have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (σ ^ 2 * v ^ 2 / 2))
        (Real.exp (σ ^ 2 * u ^ 2 / 2) * (σ ^ 2 * u)) u := by
      have hpoly : HasDerivAt (fun v : ℝ ↦ σ ^ 2 * v ^ 2 / 2) (σ ^ 2 * u) u := by
        have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u) u := by
          simpa using hasDerivAt_pow 2 u
        convert (hsq.const_mul (σ ^ 2)).div_const 2 using 1; ring
      exact (Real.hasDerivAt_exp _).comp u hpoly
    convert hexp.mul (hf_deriv u) using 1
    ring
  have hg_const : g ω = g 0 :=
    is_const_of_deriv_eq_zero (fun u ↦ (hg_deriv u).differentiableAt)
      (fun u ↦ (hg_deriv u).deriv) ω 0
  have hg0 : g 0 = 1 := by dsimp only [g]; rw [hf0]; simp
  rw [hg0] at hg_const
  dsimp only [g] at hg_const
  calc f ω = Real.exp (-(σ ^ 2 / 2) * ω ^ 2) * (Real.exp (σ ^ 2 * ω ^ 2 / 2) * f ω) := by
        rw [← mul_assoc, ← Real.exp_add]
        have : -(σ ^ 2 / 2) * ω ^ 2 + σ ^ 2 * ω ^ 2 / 2 = 0 := by ring
        rw [this, Real.exp_zero, one_mul]
    _ = Real.exp (-(σ ^ 2 / 2) * ω ^ 2) * 1 := by rw [hg_const]
    _ = Real.exp (-(σ ^ 2 / 2) * ω ^ 2) := mul_one _

/-- Complex Gaussian Fourier transform:
`∫ s : ℝ, ((gaussianKernel σ s : ℝ) : ℂ) * cexp (I * ω * s) = exp (-(σ² / 2) * ω²)`. -/
theorem integral_gaussianKernel_mul_cexp {σ : ℝ} (hσ : 0 < σ) (ω : ℝ) :
    ∫ s : ℝ, ((gaussianKernel σ s : ℝ) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)) =
      ((Real.exp (-(σ ^ 2 / 2) * ω ^ 2) : ℝ) : ℂ) := by
  have hrew : (fun s : ℝ ↦ ((gaussianKernel σ s : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ))) =
      fun s : ℝ ↦ (((gaussianKernel σ s * Real.cos (ω * s) : ℝ) : ℂ) +
        Complex.I * ((gaussianKernel σ s * Real.sin (ω * s) : ℝ) : ℂ)) := by
    funext s
    rw [show Complex.I * (ω : ℂ) * (s : ℂ) = ((ω * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have hcos_r : Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.cos (ω * s)) := by
    refine (integrable_gaussianKernel hσ).mono' ?_ ?_
    · exact (by unfold gaussianKernel; fun_prop : Continuous fun s ↦ gaussianKernel σ s * Real.cos (ω * s)).aestronglyMeasurable
    · filter_upwards with s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ s).le]
      exact mul_le_of_le_one_right (gaussianKernel_pos hσ s).le (Real.abs_cos_le_one _)
  have hsin_r : Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.sin (ω * s)) := by
    refine (integrable_gaussianKernel hσ).mono' ?_ ?_
    · exact (by unfold gaussianKernel; fun_prop : Continuous fun s ↦ gaussianKernel σ s * Real.sin (ω * s)).aestronglyMeasurable
    · filter_upwards with s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianKernel_pos hσ s).le]
      exact mul_le_of_le_one_right (gaussianKernel_pos hσ s).le (Real.abs_sin_le_one _)
  have hcos_int : Integrable (fun s : ℝ ↦ ((gaussianKernel σ s * Real.cos (ω * s) : ℝ) : ℂ)) :=
    hcos_r.ofReal
  have hsin_int : Integrable (fun s : ℝ ↦ Complex.I * ((gaussianKernel σ s * Real.sin (ω * s) : ℝ) : ℂ)) :=
    hsin_r.ofReal.const_mul Complex.I
  have hc_coe : (∫ a : ℝ, ((gaussianKernel σ a * Real.cos (ω * a) : ℝ) : ℂ)) =
      ((∫ a : ℝ, gaussianKernel σ a * Real.cos (ω * a) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hcos_r
  have hs_coe : (∫ a : ℝ, ((gaussianKernel σ a * Real.sin (ω * a) : ℝ) : ℂ)) =
      ((∫ a : ℝ, gaussianKernel σ a * Real.sin (ω * a) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hsin_r
  rw [hrew, integral_add hcos_int hsin_int, integral_const_mul,
    hc_coe, hs_coe,
    integral_gaussianKernel_mul_cos hσ ω, integral_gaussianKernel_mul_sin hσ ω]
  simp

/-- **Proposition 9.1(1) — Exact Bochner-to-Spectral Operator Bridge**:
For every `σ > 0`, Hermitian `H : QubitOp N`, and `O : QubitOp N`:
`gaussianSmearBochner hH σ O = gaussianSmear hH σ O`. -/
theorem gaussianSmearBochner_eq_gaussianSmear {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    {σ : ℝ} (hσ : 0 < σ) (O : QubitOp N) :
    gaussianSmearBochner hH σ O = gaussianSmear hH σ O := by
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  let B : QubitOp N := Uᴴ * O * U
  have hU_mul : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hU_star : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hevol_entry : ∀ (s : ℝ) (i j : QubitIdx N),
      (heisenbergEvol hH (s : ℂ) O) i j =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        (U i a * B a b * Uᴴ b j) *
          Complex.exp (Complex.I * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) * (s : ℂ)) := by
    intro s i j
    unfold heisenbergEvol complexPropagator hermFunc
    dsimp only
    have hO : O = U * B * Uᴴ := by
      dsimp only [B]
      calc O = 1 * O * 1 := by simp
        _ = (U * Uᴴ) * O * (U * Uᴴ) := by rw [hU_mul]
        _ = U * (Uᴴ * O * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    have hmat : U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
        O * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ) =
        U * (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * B *
          Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ)))) * Uᴴ := by
      conv_lhs => rw [hO]
      calc U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
            (U * B * Uᴴ) *
            (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)
          = U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) *
            (Uᴴ * U) * B * (Uᴴ * U) *
            Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * B *
            Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ)))) * Uᴴ := by
            rw [hU_star, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    change (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
        O * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)) i j = _
    rw [hmat]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [show U i a * (Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ)) * B a b *
          Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ b j =
        (U i a * B a b * Uᴴ b j) *
          (Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ)) *
           Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) by ring,
      ← Complex.exp_add]
    congr 2; push_cast; ring
  have hint_term : ∀ (c : ℂ) (ω : ℝ),
      Integrable (fun s : ℝ ↦ ((gaussianKernel σ s : ℝ) : ℂ) *
        (c * Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)))) := by
    intro c ω
    refine ((integrable_gaussianKernel hσ).const_mul ‖c‖).mono' ?_ ?_
    · exact ((by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable)
    · filter_upwards with s
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gaussianKernel_pos hσ s).le,
        show Complex.I * (ω : ℂ) * (s : ℂ) = ((ω * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, mul_comm]
  ext i j
  unfold gaussianSmearBochner gaussianSmear
  simp_rw [hevol_entry _ i j, Finset.mul_sum]
  rw [integral_finset_sum _ fun a _ ↦
    integrable_finset_sum _ fun b _ ↦ hint_term _ _]
  have hinner : ∀ a : QubitIdx N,
      (∫ s : ℝ, ∑ b : QubitIdx N, ((gaussianKernel σ s : ℝ) : ℂ) *
        (U i a * B a b * Uᴴ b j *
          Complex.exp (Complex.I * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) * (s : ℂ)))) =
      ∑ b : QubitIdx N, (U i a * B a b * Uᴴ b j) *
        ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) : ℝ) : ℂ) := by
    intro a
    rw [integral_finset_sum _ fun b _ ↦ hint_term _ _]
    apply Finset.sum_congr rfl; intro b _
    have hrew : (fun s : ℝ ↦ ((gaussianKernel σ s : ℝ) : ℂ) *
        (U i a * B a b * Uᴴ b j *
          Complex.exp (Complex.I * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) * (s : ℂ)))) =
        fun s : ℝ ↦ (U i a * B a b * Uᴴ b j) *
          (((gaussianKernel σ s : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) * (s : ℂ))) := by
      funext s; ring
    rw [hrew, integral_const_mul, integral_gaussianKernel_mul_cexp hσ]
  simp_rw [hinner]
  -- Match the RHS `(U * Matrix.of (...) * Uᴴ) i j`.
  change ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      U i a * B a b * Uᴴ b j *
        ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) : ℝ) : ℂ) =
    (U * Matrix.of (fun a b : QubitIdx N ↦
      ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) : ℝ) : ℂ) * B a b) * Uᴴ) i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- **Bochner-Integral Spectral-Weight Bridge**:
The Bochner-integral Gaussian time-smeared operator `W_σ = gaussianSmearBochner hH σ W₀` has
exact Wightman spectral weights `w_σ(a, b) = exp(-σ² (E_a - E_b)²) w_0(a, b)`. -/
theorem gaussianSmearBochner_spectral_weight {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) {σ : ℝ} (hσ : 0 < σ) (O : QubitOp N) (a b : QubitIdx N) :
    wightmanSpectralWeight hH β (gaussianSmearBochner hH σ O) a b =
      Real.exp (-(σ ^ 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) *
        wightmanSpectralWeight hH β O a b := by
  rw [gaussianSmearBochner_eq_gaussianSmear hH hσ O]
  exact prop_9_1_part1_spectral_density hH β σ O a b

end GaussianFourierBridge

section TwoDimFiniteWindowOTOC

/-- Elementary 1D Gaussian tail bound: for `σ > 0` and `Δt > 0`,
`∫ s in {s | Δt < |s|}, gaussianKernel σ s ≤ exp (-Δt² / (2 σ²))`. -/
lemma gaussianKernel_tail_le {σ Δt : ℝ} (hσ : 0 < σ) (hΔ : 0 ≤ Δt) :
    ∫ s in {s : ℝ | Δt < |s|}, gaussianKernel σ s ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) := by
  have hdom : ∀ s : ℝ, s ∈ {s : ℝ | Δt < |s|} →
      gaussianKernel σ s ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) *
        (gaussianKernel σ (s - Δt) + gaussianKernel σ (s + Δt)) := by
    intro s hs
    have habs : Δt < |s| := hs
    rcases le_or_gt 0 s with hs0 | hs0
    · rw [abs_of_nonneg hs0] at habs
      have hle : gaussianKernel σ s ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * gaussianKernel σ (s - Δt) := by
        unfold gaussianKernel
        rw [mul_div_assoc', ← Real.exp_add]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.exp_le_exp.mpr
        have hsq : Δt ^ 2 + (s - Δt) ^ 2 ≤ s ^ 2 := by nlinarith
        have hden : 0 < 2 * σ ^ 2 := by positivity
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hden.le
      have hnn : 0 ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * gaussianKernel σ (s + Δt) := by
        have := (gaussianKernel_pos hσ (s + Δt)).le; positivity
      linarith
    · rw [abs_of_neg hs0] at habs
      have hle : gaussianKernel σ s ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * gaussianKernel σ (s + Δt) := by
        unfold gaussianKernel
        rw [mul_div_assoc', ← Real.exp_add]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.exp_le_exp.mpr
        have hsq : Δt ^ 2 + (s + Δt) ^ 2 ≤ s ^ 2 := by nlinarith
        have hden : 0 < 2 * σ ^ 2 := by positivity
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hden.le
      have hnn : 0 ≤ Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * gaussianKernel σ (s - Δt) := by
        have := (gaussianKernel_pos hσ (s - Δt)).le; positivity
      linarith
  have hint_shift1 : Integrable (fun s : ℝ ↦ gaussianKernel σ (s - Δt)) :=
    (integrable_gaussianKernel hσ).comp_sub_right Δt
  have hint_shift2 : Integrable (fun s : ℝ ↦ gaussianKernel σ (s + Δt)) :=
    (integrable_gaussianKernel hσ).comp_add_right Δt
  -- Split `{Δt < |s|} = Ioi Δt ∪ Iio (-Δt)`.
  have hset_eq : {s : ℝ | Δt < |s|} = Set.Ioi Δt ∪ Set.Iio (-Δt) := by
    ext s; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
    constructor
    · rintro (h | h)
      · left; exact h
      · right; linarith
    · rintro (h | h)
      · left; exact h
      · right; linarith
  have hdisj : Disjoint (Set.Ioi Δt) (Set.Iio (-Δt)) := by
    rw [Set.disjoint_left]; intro s h1 h2
    simp only [Set.mem_Ioi, Set.mem_Iio] at h1 h2; linarith
  rw [hset_eq, setIntegral_union hdisj measurableSet_Iio
    (integrable_gaussianKernel hσ).integrableOn (integrable_gaussianKernel hσ).integrableOn]
  have hpos_part : ∫ s in Set.Ioi Δt, gaussianKernel σ s ≤
      Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * ∫ s in Set.Ioi 0, gaussianKernel σ s := by
    have hshift : ∫ s in Set.Ioi Δt, gaussianKernel σ (s - Δt) = ∫ u in Set.Ioi 0, gaussianKernel σ u := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
      have h1 := MeasureTheory.integral_sub_right_eq_self
        (fun u ↦ Set.indicator (Set.Ioi (0 : ℝ)) (gaussianKernel σ) u) Δt
      convert h1 using 2
      funext s; simp only [Set.indicator, Set.mem_Ioi, sub_pos]
    calc ∫ s in Set.Ioi Δt, gaussianKernel σ s
        ≤ ∫ s in Set.Ioi Δt, Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * gaussianKernel σ (s - Δt) := by
          refine setIntegral_mono_on (integrable_gaussianKernel hσ).integrableOn
            (hint_shift1.const_mul _).integrableOn measurableSet_Ioi fun s hs ↦ ?_
          have hgt : Δt < s := hs
          unfold gaussianKernel
          rw [mul_div_assoc', ← Real.exp_add]
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Real.exp_le_exp.mpr
          have hsq : Δt ^ 2 + (s - Δt) ^ 2 ≤ s ^ 2 := by nlinarith
          have hden : 0 < 2 * σ ^ 2 := by positivity
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hden.le
      _ = Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * ∫ s in Set.Ioi Δt, gaussianKernel σ (s - Δt) :=
          integral_const_mul _ _
      _ = Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) * ∫ u in Set.Ioi 0, gaussianKernel σ u := by
          rw [hshift]
  have hneg_part : ∫ s in Set.Iio (-Δt), gaussianKernel σ s = ∫ s in Set.Ioi Δt, gaussianKernel σ s := by
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
    have h1 := integral_comp_neg_Ioi (f := gaussianKernel σ) Δt
    have heven : ∀ s, gaussianKernel σ (-s) = gaussianKernel σ s := fun s ↦ by
      unfold gaussianKernel; rw [neg_sq]
    simpa [heven] using h1.symm
  have hhalf : ∫ u in Set.Ioi (0 : ℝ), gaussianKernel σ u = 1 / 2 := by
    have hneg0 : ∫ u in Set.Iic (0 : ℝ), gaussianKernel σ u = ∫ u in Set.Ioi (0 : ℝ), gaussianKernel σ u := by
      have h1 := integral_comp_neg_Ioi (f := gaussianKernel σ) 0
      have heven : ∀ s, gaussianKernel σ (-s) = gaussianKernel σ s := fun s ↦ by
        unfold gaussianKernel; rw [neg_sq]
      simpa [heven] using h1.symm
    have hfull : (∫ u in Set.Iic (0 : ℝ), gaussianKernel σ u) +
        (∫ u in Set.Ioi (0 : ℝ), gaussianKernel σ u) = ∫ u : ℝ, gaussianKernel σ u := by
      rw [← setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; simp at h1 h2; linarith)
        measurableSet_Ioi (integrable_gaussianKernel hσ).integrableOn
        (integrable_gaussianKernel hσ).integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
    rw [hneg0, integral_gaussianKernel_eq_one hσ] at hfull
    linarith
  rw [hhalf] at hpos_part
  rw [hneg_part]
  linarith

/-- Weighted 1D Gaussian tail bound for `a ≥ 0` and `Δt ≥ σ² * a`:
`∫ s in {s | Δt < |s|}, gaussianKernel σ s * exp (a * s) ≤ exp (σ² a² / 2) * exp (-(Δt - σ² a)² / (2 σ²))`. -/
lemma gaussianKernel_mul_exp_tail_le {σ a Δt : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a)
    (hΔ : σ ^ 2 * a ≤ Δt) :
    ∫ s in {s : ℝ | Δt < |s|}, gaussianKernel σ s * Real.exp (a * s) ≤
      Real.exp (σ ^ 2 * a ^ 2 / 2) * Real.exp (-((Δt - σ ^ 2 * a) ^ 2) / (2 * σ ^ 2)) := by
  have hrew : ∀ s : ℝ, gaussianKernel σ s * Real.exp (a * s) =
      Real.exp (σ ^ 2 * a ^ 2 / 2) * gaussianKernel σ (s - σ ^ 2 * a) := by
    intro s
    unfold gaussianKernel
    rw [div_mul_eq_mul_div, ← Real.exp_add, mul_div_assoc', ← Real.exp_add]
    congr 1; congr 1
    field_simp [hσ.ne']; ring
  simp_rw [hrew]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hsub : {s : ℝ | Δt < |s|} ⊆ {s : ℝ | Δt - σ ^ 2 * a < |s - σ ^ 2 * a|} := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    have htri : |s| ≤ |s - σ ^ 2 * a| + |σ ^ 2 * a| := by
      have h1 := abs_add_le (s - σ ^ 2 * a) (σ ^ 2 * a)
      rwa [sub_add_cancel] at h1
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg σ) ha)] at htri
    linarith
  have hmono : ∫ s in {s : ℝ | Δt < |s|}, gaussianKernel σ (s - σ ^ 2 * a) ≤
      ∫ s in {s : ℝ | Δt - σ ^ 2 * a < |s - σ ^ 2 * a|}, gaussianKernel σ (s - σ ^ 2 * a) := by
    refine setIntegral_mono_set ((integrable_gaussianKernel hσ).comp_sub_right _).integrableOn
      (Filter.Eventually.of_forall fun s ↦ (gaussianKernel_pos hσ _).le)
      (Filter.Eventually.of_forall hsub)
  have hshift : ∫ s in {s : ℝ | Δt - σ ^ 2 * a < |s - σ ^ 2 * a|}, gaussianKernel σ (s - σ ^ 2 * a) =
      ∫ u in {u : ℝ | Δt - σ ^ 2 * a < |u|}, gaussianKernel σ u := by
    have h1 := MeasureTheory.integral_sub_right_eq_self
      (fun u ↦ Set.indicator {u : ℝ | Δt - σ ^ 2 * a < |u|} (gaussianKernel σ) u) (σ ^ 2 * a)
    have hmeas1 : MeasurableSet {u : ℝ | Δt - σ ^ 2 * a < |u|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hmeas2 : MeasurableSet {s : ℝ | Δt - σ ^ 2 * a < |s - σ ^ 2 * a|} :=
      measurableSet_lt measurable_const (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    rw [← integral_indicator hmeas2, ← integral_indicator hmeas1]
    convert h1 using 2
    funext s
    simp [Set.indicator]
  rw [hshift] at hmono
  exact le_trans hmono (gaussianKernel_tail_le hσ (by linarith))

/-- **Proposition 9.1(1) — 2D Double-Time Finite-Window Gaussian OTOC Convolution**:
Let `F : ℝ → ℝ → ℝ` be a bounded double-time OTOC (`|F(t₁, t₂)| ≤ M_bound`) satisfying the
finite-window scrambling form on `|s₁|, |s₂| ≤ Δt` (with `Δt ≥ σ² λ_L / 2`):
`|F(t + s₁, t + s₂) - (F_d - ε e^{λ_L (t + (s₁ + s₂)/2)})| ≤ C_R`.
Then the 2D Gaussian-smeared OTOC
`F_σ(t) = ∫ s₁, g_σ(s₁) * (∫ s₂, g_σ(s₂) * F(t + s₁, t + s₂))`
obeys the exact `exp(σ² λ_L² / 4)` prefactor law with explicit Gaussian tail cutoff:
`|F_σ(t) - (F_d - ε * exp(σ² λ_L² / 4) * exp(λ_L * t))| ≤
  C_R + 2 * (M_bound + |F_d|) * exp(-Δt² / (2 σ²))
      + 2 * |ε| * exp(λ_L * t) * exp(σ² λ_L² / 4) * exp(-(Δt - σ² λ_L / 2)² / (2 σ²))`. -/
theorem prop_9_1_part1_2d_finite_window_otoc
    {σ Δt lamL F_d ε M_bound C_R t : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lamL) (hΔ : σ ^ 2 * (lamL / 2) ≤ Δt)
    (hM : 0 ≤ M_bound) (hCR : 0 ≤ C_R)
    (F : ℝ → ℝ → ℝ)
    (hF_meas : ∀ s₁ : ℝ, AEStronglyMeasurable (fun s₂ : ℝ ↦ F (t + s₁) (t + s₂)) volume)
    (hF_outer_meas : AEStronglyMeasurable
      (fun s₁ : ℝ ↦ ∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂)) volume)
    (hF_bdd : ∀ t₁ t₂ : ℝ, |F t₁ t₂| ≤ M_bound)
    (hF_win : ∀ s₁ s₂ : ℝ, |s₁| ≤ Δt → |s₂| ≤ Δt →
      |F (t + s₁) (t + s₂) - (F_d - ε * Real.exp (lamL * (t + (s₁ + s₂) / 2)))| ≤ C_R) :
    |(∫ s₁ : ℝ, gaussianKernel σ s₁ * (∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂))) -
      (F_d - ε * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * Real.exp (lamL * t))| ≤
      C_R +
      2 * (M_bound + |F_d|) * Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) +
      2 * |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) *
        Real.exp (-((Δt - σ ^ 2 * (lamL / 2)) ^ 2) / (2 * σ ^ 2)) := by
  have hΔ_nn : 0 ≤ Δt := le_trans (by positivity) hΔ
  have hg_nn : ∀ s, 0 ≤ gaussianKernel σ s := fun s ↦ (gaussianKernel_pos hσ s).le
  have hg_int : Integrable (gaussianKernel σ) := integrable_gaussianKernel hσ
  have hexp_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.exp ((lamL / 2) * s)) :=
    integrable_gaussianKernel_mul_exp hσ (lamL / 2)
  have hexp_val : ∫ s : ℝ, gaussianKernel σ s * Real.exp ((lamL / 2) * s) =
      Real.exp (σ ^ 2 * lamL ^ 2 / 8) := by
    rw [integral_gaussianKernel_mul_exp hσ (lamL / 2)]
    congr 1; ring
  let model : ℝ → ℝ → ℝ := fun s₁ s₂ ↦
    F_d - ε * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂)
  have hmodel_eq : ∀ s₁ s₂ : ℝ,
      model s₁ s₂ = F_d - ε * Real.exp (lamL * (t + (s₁ + s₂) / 2)) := by
    intro s₁ s₂; dsimp only [model]
    rw [mul_assoc (ε * Real.exp (lamL * t)), ← Real.exp_add, mul_assoc ε, ← Real.exp_add]
    congr 2; congr 1; ring
  have hinner_F_int : ∀ s₁ : ℝ, Integrable (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * F (t + s₁) (t + s₂)) := by
    intro s₁
    refine (hg_int.const_mul M_bound).mono' ?_ ?_
    · exact ((by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable).mul (hF_meas s₁)
    · filter_upwards with s₂
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn s₂), mul_comm]
      exact mul_le_mul_of_nonneg_right (hF_bdd _ _) (hg_nn s₂)
  have hinner_model_int : ∀ s₁ : ℝ, Integrable (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * model s₁ s₂) := by
    intro s₁
    have hrew : (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * model s₁ s₂) =
        fun s₂ ↦ F_d * gaussianKernel σ s₂ -
          (ε * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
            (gaussianKernel σ s₂ * Real.exp ((lamL / 2) * s₂)) := by
      funext s₂; dsimp only [model]; ring
    rw [hrew]
    exact (hg_int.const_mul F_d).sub (hexp_int.const_mul _)
  have hinner_model_val : ∀ s₁ : ℝ,
      ∫ s₂ : ℝ, gaussianKernel σ s₂ * model s₁ s₂ =
        F_d - ε * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) *
          Real.exp ((lamL / 2) * s₁) := by
    intro s₁
    have hrew : (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * model s₁ s₂) =
        fun s₂ ↦ F_d * gaussianKernel σ s₂ -
          (ε * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
            (gaussianKernel σ s₂ * Real.exp ((lamL / 2) * s₂)) := by
      funext s₂; dsimp only [model]; ring
    rw [hrew, integral_sub (hg_int.const_mul F_d) (hexp_int.const_mul _),
      integral_const_mul, integral_const_mul, integral_gaussianKernel_eq_one hσ, hexp_val]
    ring
  have houter_model_int : Integrable (fun s₁ : ℝ ↦
      gaussianKernel σ s₁ * ∫ s₂ : ℝ, gaussianKernel σ s₂ * model s₁ s₂) := by
    simp_rw [hinner_model_val]
    have hrew : (fun s₁ : ℝ ↦ gaussianKernel σ s₁ *
        (F_d - ε * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) *
          Real.exp ((lamL / 2) * s₁))) =
        fun s₁ ↦ F_d * gaussianKernel σ s₁ -
          (ε * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8)) *
            (gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁)) := by
      funext s₁; ring
    rw [hrew]
    exact (hg_int.const_mul F_d).sub (hexp_int.const_mul _)
  have houter_model_val :
      ∫ s₁ : ℝ, gaussianKernel σ s₁ * (∫ s₂ : ℝ, gaussianKernel σ s₂ * model s₁ s₂) =
        F_d - ε * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * Real.exp (lamL * t) := by
    simp_rw [hinner_model_val]
    have hrew : (fun s₁ : ℝ ↦ gaussianKernel σ s₁ *
        (F_d - ε * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) *
          Real.exp ((lamL / 2) * s₁))) =
        fun s₁ ↦ F_d * gaussianKernel σ s₁ -
          (ε * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8)) *
            (gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁)) := by
      funext s₁; ring
    rw [hrew, integral_sub (hg_int.const_mul F_d) (hexp_int.const_mul _),
      integral_const_mul, integral_const_mul, integral_gaussianKernel_eq_one hσ, hexp_val]
    have hmul : Real.exp (σ ^ 2 * lamL ^ 2 / 8) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) =
        Real.exp (σ ^ 2 * lamL ^ 2 / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination -ε * Real.exp (lamL * t) * hmul
  have houter_F_int : Integrable (fun s₁ : ℝ ↦
      gaussianKernel σ s₁ * ∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂)) := by
    refine (hg_int.const_mul M_bound).mono' ?_ ?_
    · exact ((by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable).mul hF_outer_meas
    · filter_upwards with s₁
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn s₁), mul_comm]
      apply mul_le_mul_of_nonneg_right _ (hg_nn s₁)
      calc |∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂)|
          ≤ ∫ s₂ : ℝ, |gaussianKernel σ s₂ * F (t + s₁) (t + s₂)| := abs_integral_le_integral_abs
        _ ≤ ∫ s₂ : ℝ, M_bound * gaussianKernel σ s₂ := by
            refine integral_mono (hinner_F_int s₁).abs (hg_int.const_mul M_bound) fun s₂ ↦ ?_
            rw [abs_mul, abs_of_nonneg (hg_nn s₂), mul_comm]
            exact mul_le_mul_of_nonneg_right (hF_bdd _ _) (hg_nn s₂)
        _ = M_bound := by rw [integral_const_mul, integral_gaussianKernel_eq_one hσ, mul_one]
  -- Pointwise bound on `|∫ s₂, g(s₂) (F - model)|` for `|s₁| ≤ Δt` vs `|s₁| > Δt`.
  let E_tail : ℝ := Real.exp (-(Δt ^ 2) / (2 * σ ^ 2))
  let E_exp_tail : ℝ := Real.exp (-((Δt - σ ^ 2 * (lamL / 2)) ^ 2) / (2 * σ ^ 2))
  have hinner_diff_le : ∀ s₁ : ℝ,
      |∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)| ≤
        if |s₁| ≤ Δt then
          C_R + (M_bound + |F_d|) * E_tail +
          |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
            Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail
        else
          (M_bound + |F_d|) +
          |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
            Real.exp (σ ^ 2 * lamL ^ 2 / 8) := by
    intro s₁
    have hdiff_int : Integrable (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)) := by
      have hrew : (fun s₂ : ℝ ↦ gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)) =
          fun s₂ ↦ gaussianKernel σ s₂ * F (t + s₁) (t + s₂) - gaussianKernel σ s₂ * model s₁ s₂ := by
        funext s₂; ring
      rw [hrew]; exact (hinner_F_int s₁).sub (hinner_model_int s₁)
    have hpoint_all : ∀ s₂ : ℝ,
        |F (t + s₁) (t + s₂) - model s₁ s₂| ≤
        (M_bound + |F_d|) +
          |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂) := by
      intro s₂
      dsimp only [model]
      calc |F (t + s₁) (t + s₂) - (F_d - ε * Real.exp (lamL * t) *
              Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂))|
          ≤ |F (t + s₁) (t + s₂)| + |F_d - ε * Real.exp (lamL * t) *
              Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂)| := abs_sub _ _
        _ ≤ M_bound + (|F_d| + |ε * Real.exp (lamL * t) *
              Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂)|) := by
            gcongr; exact hF_bdd _ _; exact abs_sub _ _
        _ = (M_bound + |F_d|) +
              |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) * Real.exp ((lamL / 2) * s₂) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]; ring
    split_ifs with hs1
    · -- Case `|s₁| ≤ Δt`: split `s₂` into `|s₂| ≤ Δt` and `|s₂| > Δt`.
      have hmeas_win : MeasurableSet {s₂ : ℝ | |s₂| ≤ Δt} :=
        measurableSet_le continuous_abs.measurable measurable_const
      have hmeas_tail : MeasurableSet {s₂ : ℝ | Δt < |s₂|} :=
        measurableSet_lt measurable_const continuous_abs.measurable
      have hcompl : {s₂ : ℝ | |s₂| ≤ Δt}ᶜ = {s₂ : ℝ | Δt < |s₂|} := by
        ext s₂; simp [not_le]
      calc |∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|
          ≤ ∫ s₂ : ℝ, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)| :=
            abs_integral_le_integral_abs
        _ = (∫ s₂ in {s₂ : ℝ | |s₂| ≤ Δt}, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|) +
            (∫ s₂ in {s₂ : ℝ | Δt < |s₂|}, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|) := by
            rw [← hcompl, integral_add_compl hmeas_win hdiff_int.abs]
        _ ≤ C_R + ((M_bound + |F_d|) * E_tail +
            |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
              Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail) := by
            apply add_le_add
            · calc ∫ s₂ in {s₂ : ℝ | |s₂| ≤ Δt}, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|
                  ≤ ∫ s₂ in {s₂ : ℝ | |s₂| ≤ Δt}, C_R * gaussianKernel σ s₂ := by
                    refine setIntegral_mono_on hdiff_int.abs.integrableOn
                      (hg_int.const_mul C_R).integrableOn hmeas_win fun s₂ hs₂ ↦ ?_
                    rw [abs_mul, abs_of_nonneg (hg_nn s₂), hmodel_eq, mul_comm]
                    exact mul_le_mul_of_nonneg_right (hF_win s₁ s₂ hs1 hs₂) (hg_nn s₂)
                _ ≤ ∫ s₂ : ℝ, C_R * gaussianKernel σ s₂ :=
                    setIntegral_le_integral (hg_int.const_mul C_R)
                      (Filter.Eventually.of_forall fun s₂ ↦ mul_nonneg hCR (hg_nn s₂))
                _ = C_R := by rw [integral_const_mul, integral_gaussianKernel_eq_one hσ, mul_one]
            · calc ∫ s₂ in {s₂ : ℝ | Δt < |s₂|}, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|
                  ≤ ∫ s₂ in {s₂ : ℝ | Δt < |s₂|},
                      ((M_bound + |F_d|) * gaussianKernel σ s₂ +
                       (|ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
                         (gaussianKernel σ s₂ * Real.exp ((lamL / 2) * s₂))) := by
                    refine setIntegral_mono_on hdiff_int.abs.integrableOn
                      ((hg_int.const_mul _).add (hexp_int.const_mul _)).integrableOn hmeas_tail
                      fun s₂ _ ↦ ?_
                    rw [abs_mul, abs_of_nonneg (hg_nn s₂)]
                    have hp := mul_le_mul_of_nonneg_left (hpoint_all s₂) (hg_nn s₂)
                    linarith
                _ = (M_bound + |F_d|) * (∫ s₂ in {s₂ : ℝ | Δt < |s₂|}, gaussianKernel σ s₂) +
                    (|ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
                      (∫ s₂ in {s₂ : ℝ | Δt < |s₂|}, gaussianKernel σ s₂ * Real.exp ((lamL / 2) * s₂)) := by
                    rw [integral_add (hg_int.const_mul _).integrableOn (hexp_int.const_mul _).integrableOn,
                      integral_const_mul, integral_const_mul]
                _ ≤ (M_bound + |F_d|) * E_tail +
                    (|ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
                      (Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail) := by
                    apply add_le_add
                    · exact mul_le_mul_of_nonneg_left (gaussianKernel_tail_le hσ hΔ_nn) (by positivity)
                    · apply mul_le_mul_of_nonneg_left _ (by positivity)
                      have htail := gaussianKernel_mul_exp_tail_le hσ (by positivity : 0 ≤ lamL / 2) hΔ
                      have heq1 : σ ^ 2 * (lamL / 2) ^ 2 / 2 = σ ^ 2 * lamL ^ 2 / 8 := by ring
                      rwa [heq1] at htail
                _ = (M_bound + |F_d|) * E_tail +
                    |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
                      Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail := by ring
        _ = C_R + (M_bound + |F_d|) * E_tail +
            |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
              Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail := by ring
    · -- Case `|s₁| > Δt`: bound globally over `s₂`.
      calc |∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)|
          ≤ ∫ s₂ : ℝ, |gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ s₂ : ℝ, ((M_bound + |F_d|) * gaussianKernel σ s₂ +
              (|ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁)) *
                (gaussianKernel σ s₂ * Real.exp ((lamL / 2) * s₂))) := by
            refine integral_mono hdiff_int.abs ((hg_int.const_mul _).add (hexp_int.const_mul _))
              fun s₂ ↦ ?_
            rw [abs_mul, abs_of_nonneg (hg_nn s₂)]
            have hp := mul_le_mul_of_nonneg_left (hpoint_all s₂) (hg_nn s₂)
            linarith
        _ = (M_bound + |F_d|) +
            |ε| * Real.exp (lamL * t) * Real.exp ((lamL / 2) * s₁) *
              Real.exp (σ ^ 2 * lamL ^ 2 / 8) := by
            rw [integral_add (hg_int.const_mul _) (hexp_int.const_mul _),
              integral_const_mul, integral_const_mul,
              integral_gaussianKernel_eq_one hσ, hexp_val]
            ring
  -- Integrate the outer difference over `s₁ ∈ ℝ` by splitting `|s₁| ≤ Δt` and `|s₁| > Δt`.
  have houter_sub : (∫ s₁ : ℝ, gaussianKernel σ s₁ * ∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂)) -
      (F_d - ε * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * Real.exp (lamL * t)) =
      ∫ s₁ : ℝ, gaussianKernel σ s₁ *
        (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂)) := by
    rw [← houter_model_val, ← integral_sub houter_F_int houter_model_int]
    congr 1; funext s₁
    rw [← mul_sub, ← integral_sub (hinner_F_int s₁) (hinner_model_int s₁)]
    congr 1; congr 1; funext s₂; ring
  have houter_diff_int : Integrable (fun s₁ : ℝ ↦ gaussianKernel σ s₁ *
      (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))) := by
    have hrew : (fun s₁ : ℝ ↦ gaussianKernel σ s₁ *
        (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))) =
        fun s₁ ↦ gaussianKernel σ s₁ * (∫ s₂ : ℝ, gaussianKernel σ s₂ * F (t + s₁) (t + s₂)) -
          gaussianKernel σ s₁ * (∫ s₂ : ℝ, gaussianKernel σ s₂ * model s₁ s₂) := by
      funext s₁
      rw [← mul_sub, ← integral_sub (hinner_F_int s₁) (hinner_model_int s₁)]
      congr 1; congr 1; funext s₂; ring
    rw [hrew]; exact houter_F_int.sub houter_model_int
  have hmeas_win : MeasurableSet {s₁ : ℝ | |s₁| ≤ Δt} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hmeas_tail : MeasurableSet {s₁ : ℝ | Δt < |s₁|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hcompl : {s₁ : ℝ | |s₁| ≤ Δt}ᶜ = {s₁ : ℝ | Δt < |s₁|} := by
    ext s₁; simp [not_le]
  have hexp_mul8 : Real.exp (σ ^ 2 * lamL ^ 2 / 8) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) =
      Real.exp (σ ^ 2 * lamL ^ 2 / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [houter_sub]
  calc |∫ s₁ : ℝ, gaussianKernel σ s₁ *
          (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))|
      ≤ ∫ s₁ : ℝ, |gaussianKernel σ s₁ *
          (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))| :=
        abs_integral_le_integral_abs
    _ = (∫ s₁ in {s₁ : ℝ | |s₁| ≤ Δt}, |gaussianKernel σ s₁ *
          (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))|) +
        (∫ s₁ in {s₁ : ℝ | Δt < |s₁|}, |gaussianKernel σ s₁ *
          (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))|) := by
        rw [← hcompl, integral_add_compl hmeas_win houter_diff_int.abs]
    _ ≤ (C_R + (M_bound + |F_d|) * E_tail +
          |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * E_exp_tail) +
        ((M_bound + |F_d|) * E_tail +
          |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * E_exp_tail) := by
        apply add_le_add
        · calc ∫ s₁ in {s₁ : ℝ | |s₁| ≤ Δt}, |gaussianKernel σ s₁ *
                (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))|
              ≤ ∫ s₁ in {s₁ : ℝ | |s₁| ≤ Δt},
                  ((C_R + (M_bound + |F_d|) * E_tail) * gaussianKernel σ s₁ +
                   (|ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail) *
                     (gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁))) := by
                refine setIntegral_mono_on houter_diff_int.abs.integrableOn
                  ((hg_int.const_mul _).add (hexp_int.const_mul _)).integrableOn hmeas_win
                  fun s₁ hs₁ ↦ ?_
                rw [abs_mul, abs_of_nonneg (hg_nn s₁)]
                have h1 := hinner_diff_le s₁
                have hs₁' : |s₁| ≤ Δt := hs₁
                rw [if_pos hs₁'] at h1
                have h2 := mul_le_mul_of_nonneg_left h1 (hg_nn s₁)
                linarith
            _ ≤ ∫ s₁ : ℝ, ((C_R + (M_bound + |F_d|) * E_tail) * gaussianKernel σ s₁ +
                   (|ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail) *
                     (gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁))) :=
                setIntegral_le_integral ((hg_int.const_mul _).add (hexp_int.const_mul _))
                  (Filter.Eventually.of_forall fun s₁ ↦ by
                    have := hg_nn s₁; positivity)
            _ = C_R + (M_bound + |F_d|) * E_tail +
                |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * E_exp_tail := by
                rw [integral_add (hg_int.const_mul _) (hexp_int.const_mul _),
                  integral_const_mul, integral_const_mul,
                  integral_gaussianKernel_eq_one hσ, hexp_val]
                linear_combination |ε| * Real.exp (lamL * t) * E_exp_tail * hexp_mul8
        · calc ∫ s₁ in {s₁ : ℝ | Δt < |s₁|}, |gaussianKernel σ s₁ *
                (∫ s₂ : ℝ, gaussianKernel σ s₂ * (F (t + s₁) (t + s₂) - model s₁ s₂))|
              ≤ ∫ s₁ in {s₁ : ℝ | Δt < |s₁|},
                  ((M_bound + |F_d|) * gaussianKernel σ s₁ +
                   (|ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8)) *
                     (gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁))) := by
                refine setIntegral_mono_on houter_diff_int.abs.integrableOn
                  ((hg_int.const_mul _).add (hexp_int.const_mul _)).integrableOn hmeas_tail
                  fun s₁ hs₁ ↦ ?_
                rw [abs_mul, abs_of_nonneg (hg_nn s₁)]
                have h1 := hinner_diff_le s₁
                have hnot : ¬(|s₁| ≤ Δt) := not_le.mpr hs₁
                rw [if_neg hnot] at h1
                have h2 := mul_le_mul_of_nonneg_left h1 (hg_nn s₁)
                linarith
            _ = (M_bound + |F_d|) * (∫ s₁ in {s₁ : ℝ | Δt < |s₁|}, gaussianKernel σ s₁) +
                (|ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8)) *
                  (∫ s₁ in {s₁ : ℝ | Δt < |s₁|}, gaussianKernel σ s₁ * Real.exp ((lamL / 2) * s₁)) := by
                rw [integral_add (hg_int.const_mul _).integrableOn (hexp_int.const_mul _).integrableOn,
                  integral_const_mul, integral_const_mul]
            _ ≤ (M_bound + |F_d|) * E_tail +
                (|ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 8)) *
                  (Real.exp (σ ^ 2 * lamL ^ 2 / 8) * E_exp_tail) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left (gaussianKernel_tail_le hσ hΔ_nn) (by positivity)
                · apply mul_le_mul_of_nonneg_left _ (by positivity)
                  have htail := gaussianKernel_mul_exp_tail_le hσ (by positivity : 0 ≤ lamL / 2) hΔ
                  have heq1 : σ ^ 2 * (lamL / 2) ^ 2 / 2 = σ ^ 2 * lamL ^ 2 / 8 := by ring
                  rwa [heq1] at htail
            _ = (M_bound + |F_d|) * E_tail +
                |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * E_exp_tail := by
                linear_combination |ε| * Real.exp (lamL * t) * E_exp_tail * hexp_mul8
    _ = C_R + 2 * (M_bound + |F_d|) * E_tail +
        2 * |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * E_exp_tail := by ring

end TwoDimFiniteWindowOTOC

end KrylovChaos
