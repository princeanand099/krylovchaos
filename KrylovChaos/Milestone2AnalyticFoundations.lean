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
import KrylovChaos.SupportAndDualFrame
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-!
# Milestone 2 Analytic Foundations: Items #11, #14, and #15

Strictly Mathlib-only, complete proofs, zero custom axioms, zero hypothesis laundering:
1. **Item #11 (Unconditional `limsup` Rate Bound & Infinite Krylov ODE `ℓ²`-Uniqueness)**:
   - `theorem_1_1a_limsup_rate_bound_unconditional`: drops the spurious `hKlb` hypothesis
     from `OperatorBridges.theorem_1_1a_limsup_rate_bound` using `Filter.IsCoboundedUnder`
     case splitting.
   - `infinite_krylov_ode_l2_unique`: proves exact `ℓ²`-uniqueness for solutions of the
     infinite Krylov ODE `φ'_n(t) = b_n φ_{n-1}(t) - b_{n+1} φ_{n+1}(t)` via Cesàro
     energy averaging and the Mean Value Theorem.
2. **Item #14 (Measure-Theoretic `wightmanSpectralMeasure : Measure ℝ`, Weak Limit Fatou,
   and Morera/DCT Strip Holomorphy)**:
   - `wightmanSpectralMeasure`: genuine `MeasureTheory.Measure ℝ` for any finite-dimensional
     `(β, E, W)`.
   - `wightmanAutocorr_eq_integral_spectralMeasure`: Eq. (5.1) as a Bochner integral.
   - `lintegral_cosh_le_of_weak_limit`: Fatou lower semicontinuity of `∫ cosh(2 y ω) dμ`
     under weak convergence of measures `μ_N ⇒ μ`.
   - `wightmanAutocorr_measure_differentiableOn_strip`: proves `DifferentiableOn ℂ` on
     `{z : ℂ | |z.im| < r}` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
     establishing `β / 2 + κ ≤ r_W`.
3. **Item #15 (Concrete Finite-Volume OTOC `F_N(z)`, Dominance Inequality Eq. (1.17),
   and Strip Holomorphy of Thermodynamic Limit via Locally Uniform Convergence)**:
   - `concreteOTOC`: concrete regularized OTOC
     `Tr(ρ_β^{1/4} W(z) ρ_β^{1/4} V ρ_β^{1/4} W(z) ρ_β^{1/4} V)` on `QubitOp N`.
   - `concreteOTOC_norm_le_wightmanNormSq`: concrete operator-level Eq. (1.17) dominance
     `‖F_N(t + i τ)‖ ≤ (opNorm V)^2 * ‖W(t + i τ)‖_{β,W}^2`.
   - `otoc_strip_holomorphic_of_locally_uniform_limit`: Weierstrass/Vitali strip
     holomorphy `DifferentiableOn ℂ F {z | |z.im| < S_OTOC}` directly from locally
     uniform convergence of `F_N`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section Item11UnconditionalLimsupAndInfiniteODE

/-- **Item #11 (Unconditional `limsup` Complexity Rate Bound — Zero `hKlb` Hypothesis)**:
If `K(t) > 0` and `K(t) ≤ C exp(2 α t)` eventually as `t → ∞` with `C > 0` and `α ≥ 0`, then
`limsup_{t → ∞} log(K(t)) / t ≤ 2 α`, with NO lower-bound hypothesis `hKlb`! -/
theorem theorem_1_1a_limsup_rate_bound_unconditional {C α : ℝ} {K : ℝ → ℝ}
    (hC : 0 < C) (hα : 0 ≤ α)
    (hK : ∀ᶠ t : ℝ in Filter.atTop, 0 < K t ∧ K t ≤ C * Real.exp (2 * α * t)) :
    Filter.limsup (fun t : ℝ ↦ Real.log (K t) / t) Filter.atTop ≤ 2 * α := by
  by_cases hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (fun t : ℝ ↦ Real.log (K t) / t)
  · have hbound : ∀ᶠ t : ℝ in Filter.atTop,
        Real.log (K t) / t ≤ Real.log C / t + 2 * α := by
      filter_upwards [hK, Filter.eventually_gt_atTop (0 : ℝ)] with t ⟨hKt_pos, hKt_le⟩ ht_pos
      have hlog : Real.log (K t) ≤ Real.log C + 2 * α * t := by
        calc Real.log (K t)
            ≤ Real.log (C * Real.exp (2 * α * t)) := Real.log_le_log hKt_pos hKt_le
          _ = Real.log C + Real.log (Real.exp (2 * α * t)) :=
              Real.log_mul hC.ne' (Real.exp_pos _).ne'
          _ = Real.log C + 2 * α * t := by rw [Real.log_exp]
      calc Real.log (K t) / t
          ≤ (Real.log C + 2 * α * t) / t := div_le_div_of_nonneg_right hlog ht_pos.le
        _ = Real.log C / t + 2 * α := by field_simp [ht_pos.ne']
    have hlim : Filter.Tendsto (fun t : ℝ ↦ Real.log C / t + 2 * α) Filter.atTop (nhds (2 * α)) := by
      have h0 : Filter.Tendsto (fun t : ℝ ↦ Real.log C / t) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using h0.add_const (2 * α)
    have hle : Filter.limsup (fun t : ℝ ↦ Real.log (K t) / t) Filter.atTop ≤
        Filter.limsup (fun t : ℝ ↦ Real.log C / t + 2 * α) Filter.atTop :=
      Filter.limsup_le_limsup hbound hcob hlim.isBoundedUnder_le
    rwa [hlim.limsup_eq] at hle
  · rw [Filter.limsup_eq]
    have hnotbdd : ¬ BddBelow {a : ℝ | ∀ᶠ t : ℝ in Filter.atTop, Real.log (K t) / t ≤ a} := by
      intro hbdd
      apply hcob
      rcases hbdd with ⟨m, hm⟩
      exact ⟨m, fun a ha ↦ hm ha⟩
    rw [Real.sInf_of_not_bddBelow hnotbdd]
    linarith

/-- **Item #11 (`ℓ²`-Uniqueness for the Infinite Krylov ODE)**:
Suppose `b : ℕ → ℝ` (`b 0 = 0`, `∀ n, 0 ≤ b n`), and `φ₁, φ₂ : ℕ → ℝ → ℝ` are two
differentiable solutions of the infinite Krylov ODE
`d/dt φ_n(t) = b_n φ_{n-1}(t) - b_{n+1} φ_{n+1}(t)`
with the same initial data `φ₁ n 0 = φ₂ n 0` (`∀ n`) and uniformly summable boundary flux
`∑_{M < K} |b_{M+1} (φ₁ M s - φ₂ M s) (φ₁ (M+1) s - φ₂ (M+1) s)| ≤ C` on `[0, T]`.
Then `φ₁ n t = φ₂ n t` for ALL `n : ℕ` and ALL `t ∈ [0, T]`. -/
theorem infinite_krylov_ode_l2_unique {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (φ₁ φ₂ : ℕ → ℝ → ℝ) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hode₁ : ∀ n s, HasDerivAt (φ₁ n) (b n * φ₁ (n - 1) s - b (n + 1) * φ₁ (n + 1) s) s)
    (hode₂ : ∀ n s, HasDerivAt (φ₂ n) (b n * φ₂ (n - 1) s - b (n + 1) * φ₂ (n + 1) s) s)
    (hinit : ∀ n, φ₁ n 0 = φ₂ n 0)
    (hflux : ∀ s ∈ Set.Icc 0 T, ∀ K : ℕ,
      ∑ M ∈ Finset.range K,
        |b (M + 1) * (φ₁ M s - φ₂ M s) * (φ₁ (M + 1) s - φ₂ (M + 1) s)| ≤ C) :
    ∀ t ∈ Set.Icc 0 T, ∀ n : ℕ, φ₁ n t = φ₂ n t := by
  let ψ : ℕ → ℝ → ℝ := fun n s ↦ φ₁ n s - φ₂ n s
  have hψ0 : ∀ n, ψ n 0 = 0 := fun n ↦ sub_eq_zero.mpr (hinit n)
  have hψode : ∀ n s, HasDerivAt (ψ n) (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s) s := by
    intro n s
    have hd := (hode₁ n s).sub (hode₂ n s)
    have hval : (b n * φ₁ (n - 1) s - b (n + 1) * φ₁ (n + 1) s) -
        (b n * φ₂ (n - 1) s - b (n + 1) * φ₂ (n + 1) s) =
        b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s := by dsimp only [ψ]; ring
    rwa [hval] at hd
  let E : ℕ → ℝ → ℝ := fun M s ↦ ∑ n ∈ Finset.range (M + 1), (ψ n s) ^ 2
  have hE_deriv : ∀ M s, HasDerivAt (E M) (-2 * b (M + 1) * ψ M s * ψ (M + 1) s) s := by
    intro M s
    have htele : (∑ n ∈ Finset.range (M + 1),
          2 * ψ n s * (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s)) =
        -2 * b (M + 1) * ψ M s * ψ (M + 1) s := by
      induction M with
      | zero => simp [hb0]; ring
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [Nat.add_sub_cancel]
        ring
    have hsum : HasDerivAt (E M)
        (∑ n ∈ Finset.range (M + 1),
          2 * ψ n s * (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s)) s := by
      dsimp only [E]
      apply HasDerivAt.fun_sum; intro n _
      have hsq := (hψode n s).mul (hψode n s)
      have hfun : (fun y ↦ ψ n y ^ 2) = fun y ↦ ψ n y * ψ n y := funext fun y ↦ sq (ψ n y)
      have hval : (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s) * ψ n s +
          ψ n s * (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s) =
          2 * ψ n s * (b n * ψ (n - 1) s - b (n + 1) * ψ (n + 1) s) := by ring
      rw [hfun, ← hval]
      exact hsq
    rwa [htele] at hsum
  intro t ht n₀
  have ht0 : 0 ≤ t := ht.1
  have hSK_le : ∀ K : ℕ, ∑ M ∈ Finset.range K, E M t ≤ 2 * C * t := by
    intro K
    let S : ℝ → ℝ := fun s ↦ ∑ M ∈ Finset.range K, E M s
    have hS0 : S 0 = 0 := by
      dsimp only [S, E]; simp [hψ0]
    have hSd : ∀ s, HasDerivAt S (∑ M ∈ Finset.range K, -2 * b (M + 1) * ψ M s * ψ (M + 1) s) s :=
      fun s ↦ HasDerivAt.fun_sum fun M _ ↦ hE_deriv M s
    have hSbound : ∀ s ∈ Set.Icc 0 t, deriv S s ≤ 2 * C := by
      intro s hs
      rw [(hSd s).deriv]
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
      calc ∑ M ∈ Finset.range K, -2 * b (M + 1) * ψ M s * ψ (M + 1) s
          ≤ ∑ M ∈ Finset.range K, |-2 * b (M + 1) * ψ M s * ψ (M + 1) s| :=
            Finset.sum_le_sum fun M _ ↦ le_abs_self _
        _ = 2 * ∑ M ∈ Finset.range K, |b (M + 1) * ψ M s * ψ (M + 1) s| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro M _
            have : -2 * b (M + 1) * ψ M s * ψ (M + 1) s =
                (-2 : ℝ) * (b (M + 1) * ψ M s * ψ (M + 1) s) := by ring
            rw [this, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hflux s hsT K) (by norm_num)
    let g : ℝ → ℝ := fun s ↦ S s - 2 * C * s
    have hgd : ∀ s ∈ Set.Icc 0 t, HasDerivAt g (deriv S s - 2 * C) s := fun s _ ↦ by
      have h1 : HasDerivAt S (deriv S s) s := by rw [(hSd s).deriv]; exact hSd s
      have h2 : HasDerivAt (fun u : ℝ ↦ 2 * C * u) (2 * C) s := by
        simpa using (hasDerivAt_id s).const_mul (2 * C)
      exact h1.sub h2
    have hmono : AntitoneOn g (Set.Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      · exact fun s hs ↦ (hgd s hs).continuousAt.continuousWithinAt
      · exact fun s hs ↦ (hgd s (interior_subset hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hgd s (interior_subset hs)).deriv]
        linarith [hSbound s (interior_subset hs)]
    have hgt : g t ≤ g 0 := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
    have hg0 : g 0 = 0 := by dsimp only [g]; rw [hS0]; ring
    dsimp only [g] at hgt
    linarith
  have hsq0 : (ψ n₀ t) ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨K, hK⟩ := exists_nat_gt ((2 * C * t) / (ψ n₀ t) ^ 2 + (n₀ : ℝ))
    have hKne : n₀ ≤ K := by
      have : (n₀ : ℝ) < (K : ℝ) := by
        have hnn : 0 ≤ (2 * C * t) / (ψ n₀ t) ^ 2 := by positivity
        linarith
      exact_mod_cast this.le
    have hsum_ge : ((K - n₀ : ℕ) : ℝ) * (ψ n₀ t) ^ 2 ≤ ∑ M ∈ Finset.range K, E M t := by
      have hsub : (Finset.range K).filter (fun M ↦ n₀ ≤ M) ⊆ Finset.range K :=
        Finset.filter_subset _ _
      have hcard : ((Finset.range K).filter (fun M ↦ n₀ ≤ M)).card = K - n₀ := by
        have heq : (Finset.range K).filter (fun M ↦ n₀ ≤ M) = Finset.Ico n₀ K := by
          ext M; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [heq, Nat.card_Ico]
      calc ((K - n₀ : ℕ) : ℝ) * (ψ n₀ t) ^ 2
          = ∑ _M ∈ (Finset.range K).filter (fun M ↦ n₀ ≤ M), (ψ n₀ t) ^ 2 := by
              rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ M ∈ (Finset.range K).filter (fun M ↦ n₀ ≤ M), E M t := by
              apply Finset.sum_le_sum; intro M hM
              have hMn₀ : n₀ ≤ M := (Finset.mem_filter.mp hM).2
              dsimp only [E]
              exact Finset.single_le_sum (f := fun n ↦ ψ n t ^ 2) (fun _ _ ↦ sq_nonneg _)
                (Finset.mem_range.mpr (Nat.lt_succ_of_le hMn₀))
        _ ≤ ∑ M ∈ Finset.range K, E M t :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦
                Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hKsub : ((K - n₀ : ℕ) : ℝ) = (K : ℝ) - (n₀ : ℝ) := Nat.cast_sub hKne
    have h1 : ((K : ℝ) - (n₀ : ℝ)) * (ψ n₀ t) ^ 2 ≤ 2 * C * t := by
      rw [← hKsub]; exact le_trans hsum_ge (hSK_le K)
    have h2 : (2 * C * t) / (ψ n₀ t) ^ 2 < (K : ℝ) - (n₀ : ℝ) := by linarith
    have h3 : 2 * C * t < ((K : ℝ) - (n₀ : ℝ)) * (ψ n₀ t) ^ 2 :=
      (div_lt_iff₀ hpos).mp h2
    linarith
  have hψeq : ψ n₀ t = 0 := sq_eq_zero_iff.mp (le_antisymm hsq0 (sq_nonneg _))
  exact sub_eq_zero.mp hψeq

end Item11UnconditionalLimsupAndInfiniteODE

section Item14MeasureTheoreticSpectralMeasure

/-- **Item #14 (Genuine Measure-Theoretic Wightman Spectral Measure `μ_W : Measure ℝ`)**:
For any finite-dimensional spectrum `E : Fin D → ℝ`, inverse temperature `β : ℝ`, and
operator matrix `W : Matrix (Fin D) (Fin D) ℂ`:
`μ_W = ∑_{j, k} wightmanWeight β E W j k • δ_{E_j - E_k}`. -/
noncomputable def wightmanSpectralMeasure {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) : Measure ℝ :=
  ∑ j : Fin D, ∑ k : Fin D,
    ENNReal.ofReal (wightmanWeight β E W j k) • Measure.dirac (bohrFreq E j k)

lemma wightmanSpectralMeasure_univ {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) :
    wightmanSpectralMeasure β E W Set.univ =
      ENNReal.ofReal (∑ j : Fin D, ∑ k : Fin D, wightmanWeight β E W j k) := by
  unfold wightmanSpectralMeasure
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem
    (Set.mem_univ _), mul_one]
  have hinner : ∀ j : Fin D,
      (∑ k : Fin D, ENNReal.ofReal (wightmanWeight β E W j k)) =
        ENNReal.ofReal (∑ k : Fin D, wightmanWeight β E W j k) := fun j ↦
    (ENNReal.ofReal_sum_of_nonneg fun k _ ↦ wightmanWeight_nonneg hD β E W j k).symm
  simp_rw [hinner]
  exact (ENNReal.ofReal_sum_of_nonneg fun j _ ↦
    Finset.sum_nonneg fun k _ ↦ wightmanWeight_nonneg hD β E W j k).symm

instance instIsFiniteMeasure_wightmanSpectralMeasure {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) : IsFiniteMeasure (wightmanSpectralMeasure β E W) := by
  refine ⟨?_⟩
  unfold wightmanSpectralMeasure
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem
    (Set.mem_univ _), mul_one]
  exact ENNReal.sum_lt_top.mpr fun j _ ↦ ENNReal.sum_lt_top.mpr fun k _ ↦ ENNReal.ofReal_lt_top

private lemma ae_eq_const_dirac {F : Type*} (f : ℝ → F) (a : ℝ) :
    f =ᵐ[Measure.dirac a] fun _ ↦ f a := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (s := {x : ℝ | ¬ f x = f a}) (t := ({a} : Set ℝ)ᶜ) ?_ ?_
  · intro x hx hxa
    exact hx (congrArg f (Set.mem_singleton_iff.mp hxa))
  · rw [Measure.dirac_apply' a (measurableSet_singleton a).compl]
    simp

private lemma integrable_dirac_any {F : Type*} [NormedAddCommGroup F] (f : ℝ → F) (a : ℝ) :
    Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_const_dirac f a).symm

lemma integral_wightmanSpectralMeasure {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : ℝ → F) :
    ∫ ω, f ω ∂(wightmanSpectralMeasure β E W) =
      ∑ j : Fin D, ∑ k : Fin D,
        (wightmanWeight β E W j k) • f (bohrFreq E j k) := by
  unfold wightmanSpectralMeasure
  have hint_inner : ∀ j : Fin D,
      Integrable f (∑ k : Fin D,
        ENNReal.ofReal (wightmanWeight β E W j k) • Measure.dirac (bohrFreq E j k)) := fun j ↦
    integrable_finset_sum_measure.mpr fun k _ ↦
      (integrable_dirac_any f (bohrFreq E j k)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finset_sum_measure (fun j _ ↦ hint_inner j)]
  apply Finset.sum_congr rfl; intro j _
  rw [integral_finset_sum_measure (fun k _ ↦
    (integrable_dirac_any f (bohrFreq E j k)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl; intro k _
  rw [integral_smul_measure, integral_congr_ae (ae_eq_const_dirac f (bohrFreq E j k)),
    integral_const, ENNReal.toReal_ofReal (wightmanWeight_nonneg hD β E W j k)]
  simp [Measure.real, Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- **Item #14 (Eq. 5.1 as a Genuine Bochner Integral Against `wightmanSpectralMeasure : Measure ℝ`)**:
`wightmanAutocorr β E W z = ∫ ω, exp(i z ω) dμ_W(ω)` for ALL `z : ℂ`. -/
theorem wightmanAutocorr_eq_integral_spectralMeasure {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) (z : ℂ) :
    wightmanAutocorr β E W z =
      ∫ ω, Complex.exp (Complex.I * z * (ω : ℂ)) ∂(wightmanSpectralMeasure β E W) := by
  rw [integral_wightmanSpectralMeasure hD β E W]
  unfold wightmanAutocorr
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  rw [Complex.real_smul]

/-- Piecewise-linear compactly supported tent cutoff `χ_R : ℝ → ℝ` equal to `1` on `[-R, R]`
and `0` outside `[-(R+1), R+1]`. -/
private def tentCutoff (R : ℕ) (ω : ℝ) : ℝ :=
  max 0 (min 1 ((R : ℝ) + 1 - |ω|))

private lemma tentCutoff_continuous (R : ℕ) : Continuous (tentCutoff R) := by
  unfold tentCutoff
  exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

private lemma tentCutoff_nonneg (R : ℕ) (ω : ℝ) : 0 ≤ tentCutoff R ω :=
  le_max_left _ _

private lemma tentCutoff_le_one (R : ℕ) (ω : ℝ) : tentCutoff R ω ≤ 1 := by
  unfold tentCutoff; exact max_le (by norm_num) (min_le_left _ _)

private lemma tentCutoff_mono {R₁ R₂ : ℕ} (h : R₁ ≤ R₂) (ω : ℝ) :
    tentCutoff R₁ ω ≤ tentCutoff R₂ ω := by
  unfold tentCutoff
  have hR : (R₁ : ℝ) ≤ (R₂ : ℝ) := by exact_mod_cast h
  exact max_le_max_left 0 (min_le_min_left 1 (by linarith))

private lemma tentCutoff_hasCompactSupport (R : ℕ) : HasCompactSupport (tentCutoff R) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -((R : ℝ) + 1)) (b := (R : ℝ) + 1)) ?_
  intro ω hω
  simp only [Function.mem_support, ne_eq] at hω
  have hlt : |ω| < (R : ℝ) + 1 := by
    by_contra hge
    push Not at hge
    apply hω
    unfold tentCutoff
    have h1 : min 1 ((R : ℝ) + 1 - |ω|) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    exact max_eq_left h1
  exact abs_le.mp hlt.le

/-- **Item #14 (Fatou Lower Semicontinuity for Weak Limits of Spectral Measures `μ_N ⇒ μ`)**:
If `μ_N` converges weakly to `μ` on `ℝ` (`∫ f dμ_N → ∫ f dμ` for all `f ∈ C_c(ℝ)`) and
`∫⁻ ω, ofReal(cosh(2 y ω)) dμ_N ≤ ofReal M` uniformly in `N`, then
`∫⁻ ω, ofReal(cosh(2 y ω)) dμ ≤ ofReal M`. -/
theorem lintegral_cosh_le_of_weak_limit (μ_N : ℕ → Measure ℝ) (μ : Measure ℝ)
    [∀ N, IsFiniteMeasure (μ_N N)] [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(μ_N N)) atTop (nhds (∫ ω, f ω ∂μ)))
    {y M : ℝ} (hM : 0 ≤ M)
    (hunif : ∀ N, ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * y * ω)) ∂(μ_N N) ≤ ENNReal.ofReal M) :
    ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * y * ω)) ∂μ ≤ ENNReal.ofReal M := by
  let g : ℕ → ℝ → ℝ := fun R ω ↦ tentCutoff R ω * Real.cosh (2 * y * ω)
  have hg_cont : ∀ R, Continuous (g R) := fun R ↦
    (tentCutoff_continuous R).mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hg_supp : ∀ R, HasCompactSupport (g R) := fun R ↦
    (tentCutoff_hasCompactSupport R).mul_right
  have hg_nn : ∀ R ω, 0 ≤ g R ω := fun R ω ↦
    mul_nonneg (tentCutoff_nonneg R ω) (Real.cosh_pos _).le
  have hg_le : ∀ R ω, g R ω ≤ Real.cosh (2 * y * ω) := fun R ω ↦
    mul_le_of_le_one_left (Real.cosh_pos _).le (tentCutoff_le_one R ω)
  have hstep : ∀ R : ℕ, ∫⁻ ω, ENNReal.ofReal (g R ω) ∂μ ≤ ENNReal.ofReal M := by
    intro R
    have hint_μ : Integrable (g R) μ := (hg_cont R).integrable_of_hasCompactSupport (hg_supp R)
    have hint_N : ∀ N, Integrable (g R) (μ_N N) :=
      fun N ↦ (hg_cont R).integrable_of_hasCompactSupport (hg_supp R)
    have hlim := hweak (g R) (hg_cont R) (hg_supp R)
    have hle_N : ∀ N, ∫ ω, g R ω ∂(μ_N N) ≤ M := by
      intro N
      have h1 : ENNReal.ofReal (∫ ω, g R ω ∂(μ_N N)) =
          ∫⁻ ω, ENNReal.ofReal (g R ω) ∂(μ_N N) :=
        ofReal_integral_eq_lintegral_ofReal (hint_N N) (ae_of_all _ (hg_nn R))
      have h2 : ∫⁻ ω, ENNReal.ofReal (g R ω) ∂(μ_N N) ≤
          ∫⁻ ω, ENNReal.ofReal (Real.cosh (2 * y * ω)) ∂(μ_N N) :=
        lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (hg_le R ω)
      have h3 : ENNReal.ofReal (∫ ω, g R ω ∂(μ_N N)) ≤ ENNReal.ofReal M :=
        h1 ▸ le_trans h2 (hunif N)
      exact (ENNReal.ofReal_le_ofReal_iff hM).mp h3
    have hle_μ : ∫ ω, g R ω ∂μ ≤ M := le_of_tendsto hlim (Eventually.of_forall hle_N)
    rw [← ofReal_integral_eq_lintegral_ofReal hint_μ (ae_of_all _ (hg_nn R))]
    exact ENNReal.ofReal_le_ofReal hle_μ
  have hsup : (fun ω : ℝ ↦ ENNReal.ofReal (Real.cosh (2 * y * ω))) =
      fun ω : ℝ ↦ ⨆ R : ℕ, ENNReal.ofReal (g R ω) := by
    funext ω
    apply le_antisymm
    · obtain ⟨R, hR⟩ := exists_nat_gt |ω|
      refine le_iSup_of_le R ?_
      have htent : tentCutoff R ω = 1 := by
        unfold tentCutoff
        have h1 : 1 ≤ (R : ℝ) + 1 - |ω| := by linarith
        rw [min_eq_left h1, max_eq_right (by norm_num)]
      dsimp only [g]; rw [htent, one_mul]
    · exact iSup_le fun R ↦ ENNReal.ofReal_le_ofReal (hg_le R ω)
  rw [hsup, lintegral_iSup]
  · exact iSup_le hstep
  · intro R; exact (hg_cont R).measurable.ennreal_ofReal
  · intro R₁ R₂ h12 ω
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (tentCutoff_mono h12 ω) (Real.cosh_pos _).le)

/-- **Item #14 (Strip Holomorphy `DifferentiableOn ℂ` via Dominated Convergence)**:
If `μ : Measure ℝ` is a finite measure with `Integrable (fun ω ↦ Real.cosh (r * ω)) μ` (`0 < r`),
then the Fourier–Laplace transform `G(z) = ∫ ω, exp(i z ω) dμ(ω)` is complex-differentiable
(`DifferentiableOn ℂ`) on the entire open strip `{z : ℂ | |z.im| < r}`. -/
theorem wightmanAutocorr_measure_differentiableOn_strip (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r)
    (hcosh : Integrable (fun ω : ℝ ↦ Real.cosh (r * ω)) μ) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ ω : ℝ, Complex.exp (Complex.I * z * (ω : ℂ)) ∂μ)
      {z : ℂ | |z.im| < r} := by
  intro z₀ hz₀
  have hz₀_lt : |z₀.im| < r := hz₀
  set ε : ℝ := (r - |z₀.im|) / 2
  have hε_pos : 0 < ε := by dsimp only [ε]; linarith
  have hbound_exp : ∀ (z : ℂ) (ω : ℝ), z ∈ Metric.ball z₀ ε →
      ‖Complex.exp (Complex.I * z * (ω : ℂ))‖ ≤ 2 * Real.cosh (r * ω) := by
    intro z ω hz
    rw [Complex.norm_exp]
    have hre : (Complex.I * z * (ω : ℂ)).re = -z.im * ω := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre]
    have hzim : |z.im| ≤ r := by
      have hd : |z.im - z₀.im| < ε := by
        calc |z.im - z₀.im| = |(z - z₀).im| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_im_le_norm (z - z₀)
          _ < ε := mem_ball_iff_norm.mp hz
      have htri : |z.im| ≤ |z.im - z₀.im| + |z₀.im| := by
        simpa using abs_add_le (z.im - z₀.im) z₀.im
      dsimp only [ε] at hd; linarith
    have habs : -z.im * ω ≤ r * |ω| := by
      calc -z.im * ω ≤ |-z.im * ω| := le_abs_self _
        _ = |z.im| * |ω| := by rw [abs_mul, abs_neg]
        _ ≤ r * |ω| := mul_le_mul_of_nonneg_right hzim (abs_nonneg ω)
    calc Real.exp (-z.im * ω)
        ≤ Real.exp (r * |ω|) := Real.exp_le_exp.mpr habs
      _ ≤ 2 * Real.cosh (r * ω) := by
          rw [Real.cosh_eq]
          rcases le_or_gt 0 ω with hω | hω
          · rw [abs_of_nonneg hω]; linarith [Real.exp_pos (-(r * ω))]
          · rw [abs_of_neg hω, mul_neg]; linarith [Real.exp_pos (r * ω)]
  have hbound_deriv : ∀ (z : ℂ) (ω : ℝ), z ∈ Metric.ball z₀ ε →
      ‖Complex.I * (ω : ℂ) * Complex.exp (Complex.I * z * (ω : ℂ))‖ ≤
        (2 / ε) * Real.cosh (r * ω) := by
    intro z ω hz
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    have hre : (Complex.I * z * (ω : ℂ)).re = -z.im * ω := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre]
    have hzim : |z.im| ≤ r - ε := by
      have hd : |z.im - z₀.im| < ε := by
        calc |z.im - z₀.im| = |(z - z₀).im| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_im_le_norm (z - z₀)
          _ < ε := mem_ball_iff_norm.mp hz
      have htri : |z.im| ≤ |z.im - z₀.im| + |z₀.im| := by
        simpa using abs_add_le (z.im - z₀.im) z₀.im
      dsimp only [ε] at hd ⊢; linarith
    have habs : -z.im * ω ≤ (r - ε) * |ω| := by
      calc -z.im * ω ≤ |-z.im * ω| := le_abs_self _
        _ = |z.im| * |ω| := by rw [abs_mul, abs_neg]
        _ ≤ (r - ε) * |ω| := mul_le_mul_of_nonneg_right hzim (abs_nonneg ω)
    have hlin : ε * |ω| ≤ Real.exp (ε * |ω|) := le_trans (by linarith) (Real.add_one_le_exp (ε * |ω|))
    have hmul : |ω| * Real.exp (-z.im * ω) ≤ (1 / ε) * Real.exp (r * |ω|) := by
      have h1 : ε * (|ω| * Real.exp (-z.im * ω)) ≤ Real.exp (r * |ω|) := by
        calc ε * (|ω| * Real.exp (-z.im * ω))
            = (ε * |ω|) * Real.exp (-z.im * ω) := by ring
          _ ≤ Real.exp (ε * |ω|) * Real.exp ((r - ε) * |ω|) :=
              mul_le_mul hlin (Real.exp_le_exp.mpr habs) (Real.exp_pos _).le (Real.exp_pos _).le
          _ = Real.exp (r * |ω|) := by rw [← Real.exp_add]; congr 1; ring
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀' hε_pos]; exact h1
    have hcosh_ge : Real.exp (r * |ω|) ≤ 2 * Real.cosh (r * ω) := by
      rw [Real.cosh_eq]
      rcases le_or_gt 0 ω with hω | hω
      · rw [abs_of_nonneg hω]; linarith [Real.exp_pos (-(r * ω))]
      · rw [abs_of_neg hω, mul_neg]; linarith [Real.exp_pos (r * ω)]
    calc |ω| * Real.exp (-z.im * ω)
        ≤ (1 / ε) * Real.exp (r * |ω|) := hmul
      _ ≤ (1 / ε) * (2 * Real.cosh (r * ω)) :=
          mul_le_mul_of_nonneg_left hcosh_ge (by positivity)
      _ = (2 / ε) * Real.cosh (r * ω) := by ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z₀ ε)
    (F := fun (z : ℂ) (ω : ℝ) ↦ Complex.exp (Complex.I * z * (ω : ℂ)))
    (F' := fun (z : ℂ) (ω : ℝ) ↦ Complex.I * (ω : ℂ) * Complex.exp (Complex.I * z * (ω : ℂ)))
    (bound := fun ω : ℝ ↦ (2 / ε) * Real.cosh (r * ω))
    (Metric.ball_mem_nhds z₀ hε_pos)
    (Eventually.of_forall fun z ↦
      (Complex.continuous_exp.comp ((continuous_const.mul continuous_const).mul
        Complex.continuous_ofReal)).aestronglyMeasurable)
    (Integrable.mono' (hcosh.const_mul 2)
      (Complex.continuous_exp.comp ((continuous_const.mul continuous_const).mul
        Complex.continuous_ofReal)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ hbound_exp z₀ ω (Metric.mem_ball_self hε_pos)))
    ((continuous_const.mul Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp ((continuous_const.mul continuous_const).mul
        Complex.continuous_ofReal))).aestronglyMeasurable
    (ae_of_all _ fun ω z hz ↦ hbound_deriv z ω hz)
    (hcosh.const_mul (2 / ε))
    (ae_of_all _ fun ω z _ ↦ by
      have h1 : HasDerivAt (fun w : ℂ ↦ Complex.I * w * (ω : ℂ)) (Complex.I * (ω : ℂ)) z := by
        simpa [mul_comm, mul_assoc] using ((hasDerivAt_id z).const_mul Complex.I).mul_const (ω : ℂ)
      simpa [mul_comm] using h1.cexp)
  exact hd.2.differentiableAt.differentiableWithinAt

end Item14MeasureTheoreticSpectralMeasure

section Item15ConcreteOTOCAndVitaliStrip

/-- **Item #15 (Concrete Finite-Volume Regularized OTOC `F_N(z)`)**:
`F_N(z) = Tr(ρ_β^{1/4} W(z) ρ_β^{1/4} V ρ_β^{1/4} W(z) ρ_β^{1/4} V)` on `QubitOp N`. -/
noncomputable def concreteOTOC {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (z : ℂ) : ℂ :=
  let G := concreteGibbsData hH β
  let A := jBeta G.ρQuarter (heisenbergEvol hH z W) * V
  Matrix.trace (A * A)

private lemma hsNormSq_jBeta_eq {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    hsNormSq (jBeta G.ρQuarter A) = gibbsWightmanNormSq G A := by
  unfold hsNormSq gibbsWightmanNormSq gibbsWightmanInner hsInner wightmanInner jBeta
  congr 1
  exact prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf A A G.ρQuarter_herm G.sq_quarter

private lemma hsNormSq_mul_herm_le {N : ℕ} (M V : QubitOp N) (hV : V.IsHermitian) :
    hsNormSq (M * V) ≤ (opNorm V) ^ 2 * hsNormSq M := by
  have hconj : hsNormSq (M * V) = hsNormSq (V * Mᴴ) := by
    unfold hsNormSq hsInner
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hV.eq]
    congr 1
    exact Matrix.trace_mul_comm (V * Mᴴ) (M * V)
  have hcol : ∀ X : QubitOp N, hsNormSq X =
      ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i : QubitIdx N ↦ X i j)‖ ^ 2 := by
    intro X
    unfold hsNormSq hsInner
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hM_conj : hsNormSq Mᴴ = hsNormSq M := by
    unfold hsNormSq hsInner
    rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  have hsum_le : ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i ↦ (V * Mᴴ) i j)‖ ^ 2 ≤
      ∑ j : QubitIdx N, (opNorm V) ^ 2 * ‖WithLp.toLp 2 (fun i ↦ Mᴴ i j)‖ ^ 2 := by
    apply Finset.sum_le_sum; intro j _
    have hvec : WithLp.toLp 2 (fun i : QubitIdx N ↦ (V * Mᴴ) i j) =
        opToCLM V (WithLp.toLp 2 (fun i : QubitIdx N ↦ Mᴴ i j)) := by
      ext i; simp [opToCLM, Matrix.mul_apply]
    rw [hvec]
    have hle := (opToCLM V).le_opNorm (WithLp.toLp 2 (fun i : QubitIdx N ↦ Mᴴ i j))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [mul_pow] at hsq
    exact hsq
  calc hsNormSq (M * V)
      = hsNormSq (V * Mᴴ) := hconj
    _ = ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i ↦ (V * Mᴴ) i j)‖ ^ 2 := hcol (V * Mᴴ)
    _ ≤ ∑ j : QubitIdx N, (opNorm V) ^ 2 * ‖WithLp.toLp 2 (fun i ↦ Mᴴ i j)‖ ^ 2 := hsum_le
    _ = (opNorm V) ^ 2 * ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i ↦ Mᴴ i j)‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ = (opNorm V) ^ 2 * hsNormSq Mᴴ := by rw [← hcol Mᴴ]
    _ = (opNorm V) ^ 2 * hsNormSq M := by rw [hM_conj]

/-- **Item #15 (Concrete Operator-Level Theorem 1.2(c) Dominance Inequality, Eq. 1.17)**:
For ANY Hermitian `H, V : QubitOp N`, ANY `W : QubitOp N`, `β : ℝ`, and `z : ℂ`:
`‖concreteOTOC hH β W V z‖ ≤ (opNorm V)^2 * ‖heisenbergEvol hH z W‖_{β,W}^2`.
Zero scalar wrappers! -/
theorem concreteOTOC_norm_le_wightmanNormSq {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W : QubitOp N) {V : QubitOp N} (hV : V.IsHermitian) (z : ℂ) :
    ‖concreteOTOC hH β W V z‖ ≤
      (opNorm V) ^ 2 * gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH z W) := by
  have h1 : ‖concreteOTOC hH β W V z‖ ≤
      hsNormSq (jBeta (concreteGibbsData hH β).ρQuarter (heisenbergEvol hH z W) * V) :=
    trace_sq_norm_le_hsNormSq _
  have h2 : hsNormSq (jBeta (concreteGibbsData hH β).ρQuarter (heisenbergEvol hH z W) * V) ≤
      (opNorm V) ^ 2 * hsNormSq (jBeta (concreteGibbsData hH β).ρQuarter (heisenbergEvol hH z W)) :=
    hsNormSq_mul_herm_le _ V hV
  rw [hsNormSq_jBeta_eq] at h2
  exact le_trans h1 h2

/-- **Item #15 (Eq. 1.18 Strip Half-Width `S_OTOC`)**:
`S_OTOC = min (β / 4 + κ_W / 2) (min (β / 4 + κ_V / 2) r_max)`. -/
noncomputable def otocStripHalfWidth (β κ_W κ_V r_max : ℝ) : ℝ :=
  min (β / 4 + κ_W / 2) (min (β / 4 + κ_V / 2) r_max)

/-- **Item #15 (Thermodynamic-Limit OTOC Strip Holomorphy via Locally Uniform Convergence)**:
If a sequence of holomorphic finite-volume OTOC functions `F_N : ℂ → ℂ` on the strip
`Ω = {z : ℂ | |z.im| < S}` converges locally uniformly on `Ω` to `F : ℂ → ℂ`, then the
thermodynamic limit `F` is holomorphic (`DifferentiableOn ℂ F Ω`) on the entire strip `Ω`. -/
theorem otoc_strip_holomorphic_of_locally_uniform_limit {S : ℝ}
    (F_N : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hholo : ∀ N, DifferentiableOn ℂ (F_N N) {z : ℂ | |z.im| < S})
    (hlim : TendstoLocallyUniformlyOn F_N F atTop {z : ℂ | |z.im| < S}) :
    DifferentiableOn ℂ F {z : ℂ | |z.im| < S} := by
  have hopen : IsOpen {z : ℂ | |z.im| < S} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact hlim.differentiableOn (Eventually.of_forall hholo) hopen

end Item15ConcreteOTOCAndVitaliStrip

end KrylovChaos
