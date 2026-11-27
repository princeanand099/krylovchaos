/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.KrylovTail
import KrylovChaos.CarlemanJacobi
import KrylovChaos.Milestone2AnalyticFoundations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Milestone 1 Infinite-Chain Remediation: Items #5, #6, #7, and #8

Strictly Mathlib-only, complete proofs, zero `sorry`, zero custom axioms, zero hypothesis laundering:
1. **Item #5 (`infinite_krylov_ode_of_pointwise_limit`)**:
   Any pointwise limit `φ m t = lim_{N → ∞} φ_N m t` of uniformly bounded (`|φ_N m t| ≤ 1`)
   finite-chain Krylov ODE solutions satisfies the initial condition `φ m 0 = δ_{m0}`,
   is Lipschitz continuous in `t`, and satisfies the exact infinite-chain Krylov ODE
   `HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t` for all `m : ℕ`, `t : ℝ`.
2. **Item #6 (`infinite_krylov_ode_carleman_l2_unique`, `infinite_krylov_ode_linear_growth_l2_unique`)**:
   Genuine `ℓ²`-uniqueness for the infinite Krylov ODE under Carleman's divergence condition
   `¬ Summable (fun M ↦ (max (b (M + 1)) 1)⁻¹)` — and in particular under linear growth
   `0 ≤ b n ≤ α n + γ` — completely eliminating the laundered `hflux` hypothesis.
3. **Item #7 (`theorem_1_1a_infinite_exact_eqs_1_12_1_13`, `theorem_1_1a_limsup_rate_bound_nonneg`)**:
   Exact Eqs. (1.12)–(1.13) with `charTheta_ge_four_tanh` expanded, plus the `limsup` rate bound
   `limsup_{t → ∞} log(K(t)) / t ≤ 2 α` holding for all `0 ≤ K(t)` (including the `b 1 = 0`
   degenerate case where `K(t) = 0`).
4. **Item #8 (`theorem_1_1a_infinite_fatou_exact_single_exp`)**:
   Exact single-exponential Fatou limit of finite-chain solutions yielding sharp Eqs. (1.12)–(1.13),
   superseding the legacy double-exponential `theorem_1_1a_infinite_fatou_proved`.
-/

namespace KrylovChaos

open MeasureTheory Filter Topology

section Item5InfiniteChainODE

/-- **Item #5 — Infinite-Chain Krylov ODE Satisfaction & Initial Condition**:
If `φ_N : ℕ → ℕ → ℝ → ℝ` is a sequence of finite-chain Krylov wavefunctions satisfying:
- the finite Krylov ODE for `m ≤ N` (`HasDerivAt (φ_N N m) (b m * φ_N N (m - 1) t - b (m + 1) * φ_N N (m + 1) t) t`),
- the initial condition `φ_N N m 0 = if m = 0 then 1 else 0` for `m ≤ N`,
- the uniform bound `|φ_N N m t| ≤ 1`,
and converging pointwise `φ_N N m t → φ m t` as `N → ∞`, then for every `m : ℕ` and `t : ℝ`:
1. `φ m 0 = if m = 0 then 1 else 0`,
2. `Continuous (φ m)`,
3. `HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t`. -/
theorem infinite_krylov_ode_of_pointwise_limit (b : ℕ → ℝ)
    (φ_N : ℕ → ℕ → ℝ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hode_N : ∀ N m, m ≤ N → ∀ t,
      HasDerivAt (φ_N N m) (b m * φ_N N (m - 1) t - b (m + 1) * φ_N N (m + 1) t) t)
    (hinit_N : ∀ N m, m ≤ N → φ_N N m 0 = if m = 0 then 1 else 0)
    (hbound_N : ∀ N m t, |φ_N N m t| ≤ 1)
    (htendsto : ∀ m t, Tendsto (fun N ↦ φ_N N m t) atTop (nhds (φ m t))) :
    (∀ m, φ m 0 = if m = 0 then 1 else 0) ∧
    (∀ m, Continuous (φ m)) ∧
    (∀ m t, HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t) := by
  have hinit : ∀ m, φ m 0 = if m = 0 then 1 else 0 := by
    intro m
    have hconst : Tendsto (fun N ↦ φ_N N m 0) atTop (nhds (if m = 0 then (1 : ℝ) else 0)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with N hN
      exact (hinit_N N m hN).symm
    exact tendsto_nhds_unique (htendsto m 0) hconst
  have hlip : ∀ m t₁ t₂, |φ m t₂ - φ m t₁| ≤ (|b m| + |b (m + 1)|) * |t₂ - t₁| := by
    intro m t₁ t₂
    set L : ℝ := |b m| + |b (m + 1)|
    have hL_nn : 0 ≤ L := by positivity
    have hlip_N : ∀ N ≥ m, |φ_N N m t₂ - φ_N N m t₁| ≤ L * |t₂ - t₁| := by
      intro N hN
      have hdiff : ∀ s, HasDerivAt (φ_N N m) (b m * φ_N N (m - 1) s - b (m + 1) * φ_N N (m + 1) s) s :=
        hode_N N m hN
      have hd_le : ∀ s, ‖deriv (φ_N N m) s‖ ≤ L := by
        intro s
        rw [(hdiff s).deriv, Real.norm_eq_abs]
        calc |b m * φ_N N (m - 1) s - b (m + 1) * φ_N N (m + 1) s|
            ≤ |b m * φ_N N (m - 1) s| + |b (m + 1) * φ_N N (m + 1) s| := abs_sub _ _
          _ = |b m| * |φ_N N (m - 1) s| + |b (m + 1)| * |φ_N N (m + 1) s| := by
              rw [abs_mul, abs_mul]
          _ ≤ |b m| * 1 + |b (m + 1)| * 1 := by
              gcongr
              · exact hbound_N N (m - 1) s
              · exact hbound_N N (m + 1) s
          _ = L := by ring
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := φ_N N m)
        (fun s _ ↦ (hdiff s).differentiableAt) (fun s _ ↦ hd_le s) convex_univ (Set.mem_univ t₁) (Set.mem_univ t₂)
      simpa [Real.norm_eq_abs] using hmvt
    have htend : Tendsto (fun N ↦ |φ_N N m t₂ - φ_N N m t₁|) atTop (nhds |φ m t₂ - φ m t₁|) :=
      ((htendsto m t₂).sub (htendsto m t₁)).abs
    exact le_of_tendsto htend (by filter_upwards [eventually_ge_atTop m] with N hN; exact hlip_N N hN)
  have hcont : ∀ m, Continuous (φ m) := by
    intro m
    rw [Metric.continuous_iff]
    intro t ε hε
    set L : ℝ := |b m| + |b (m + 1)| + 1
    have hL_pos : 0 < L := by positivity
    refine ⟨ε / L, div_pos hε hL_pos, fun s hs ↦ ?_⟩
    rw [Real.dist_eq] at hs ⊢
    have h1 := hlip m t s
    have h2 : (|b m| + |b (m + 1)|) * |s - t| ≤ L * |s - t| := by
      have : |b m| + |b (m + 1)| ≤ L := by dsimp only [L]; linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h3 : L * |s - t| < L * (ε / L) := mul_lt_mul_of_pos_left hs hL_pos
    rw [mul_div_cancel₀ _ hL_pos.ne'] at h3
    linarith
  have hint_eq : ∀ m t, φ m t - φ m 0 =
      ∫ s in (0 : ℝ)..t, (b m * φ (m - 1) s - b (m + 1) * φ (m + 1) s) := by
    intro m t
    let g_N : ℕ → ℝ → ℝ := fun N s ↦ b m * φ_N N (m - 1) s - b (m + 1) * φ_N N (m + 1) s
    let g : ℝ → ℝ := fun s ↦ b m * φ (m - 1) s - b (m + 1) * φ (m + 1) s
    have hftc : ∀ N ≥ m + 1, ∫ s in (0 : ℝ)..t, g_N N s = φ_N N m t - φ_N N m 0 := by
      intro N hN
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s _; exact hode_N N m (by omega) s
      · apply Continuous.intervalIntegrable
        have hc1 : Continuous (φ_N N (m - 1)) :=
          continuous_iff_continuousAt.mpr fun s ↦ (hode_N N (m - 1) (by omega) s).continuousAt
        have hc2 : Continuous (φ_N N (m + 1)) :=
          continuous_iff_continuousAt.mpr fun s ↦ (hode_N N (m + 1) (by omega) s).continuousAt
        exact (continuous_const.mul hc1).sub (continuous_const.mul hc2)
    have htend_int : Tendsto (fun N ↦ ∫ s in (0 : ℝ)..t, g_N N s) atTop
        (nhds (∫ s in (0 : ℝ)..t, g s)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ ↦ |b m| + |b (m + 1)|) ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [eventually_ge_atTop (m + 1)] with N hN
        have hc1 : Continuous (φ_N N (m - 1)) :=
          continuous_iff_continuousAt.mpr fun s ↦ (hode_N N (m - 1) (by omega) s).continuousAt
        have hc2 : Continuous (φ_N N (m + 1)) :=
          continuous_iff_continuousAt.mpr fun s ↦ (hode_N N (m + 1) (by omega) s).continuousAt
        exact ((continuous_const.mul hc1).sub (continuous_const.mul hc2)).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (m + 1)] with N _
        filter_upwards with s _
        rw [Real.norm_eq_abs]
        dsimp only [g_N]
        calc |b m * φ_N N (m - 1) s - b (m + 1) * φ_N N (m + 1) s|
            ≤ |b m * φ_N N (m - 1) s| + |b (m + 1) * φ_N N (m + 1) s| := abs_sub _ _
          _ = |b m| * |φ_N N (m - 1) s| + |b (m + 1)| * |φ_N N (m + 1) s| := by
              rw [abs_mul, abs_mul]
          _ ≤ |b m| * 1 + |b (m + 1)| * 1 := by
              gcongr
              · exact hbound_N N (m - 1) s
              · exact hbound_N N (m + 1) s
          _ = |b m| + |b (m + 1)| := by ring
      · filter_upwards with s _
        dsimp only [g_N, g]
        exact (tendsto_const_nhds.mul (htendsto (m - 1) s)).sub
          (tendsto_const_nhds.mul (htendsto (m + 1) s))
    have htend_rhs : Tendsto (fun N ↦ ∫ s in (0 : ℝ)..t, g_N N s) atTop (nhds (φ m t - φ m 0)) := by
      refine ((htendsto m t).sub (htendsto m 0)).congr' ?_
      filter_upwards [eventually_ge_atTop (m + 1)] with N hN
      exact (hftc N hN).symm
    exact tendsto_nhds_unique htend_rhs htend_int
  refine ⟨hinit, hcont, fun m t ↦ ?_⟩
  let g : ℝ → ℝ := fun s ↦ b m * φ (m - 1) s - b (m + 1) * φ (m + 1) s
  have hg_cont : Continuous g :=
    (continuous_const.mul (hcont (m - 1))).sub (continuous_const.mul (hcont (m + 1)))
  have hderiv_int : HasDerivAt (fun x ↦ ∫ s in (0 : ℝ)..x, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
  have hfun : φ m = fun x ↦ (∫ s in (0 : ℝ)..x, g s) + φ m 0 := by
    ext x; linarith [hint_eq m x]
  rw [hfun]
  simpa using hderiv_int.add_const (φ m 0)

end Item5InfiniteChainODE

section Item6CarlemanL2Uniqueness

/-- **Item #6 — Genuine Carleman `ℓ²`-Uniqueness for the Infinite Krylov ODE (Zero `hflux`)**:
For ANY sequence `b : ℕ → ℝ` with `b 0 = 0`, `∀ n, 0 ≤ b n`, and Carleman's divergence
criterion `¬ Summable (fun M ↦ (max (b (M + 1)) 1)⁻¹)`, if `φ₁, φ₂ : ℕ → ℝ → ℝ` are two
solutions of the infinite Krylov ODE with `φ₁ n 0 = φ₂ n 0` and uniformly bounded `ℓ²`
norm on `[0, T]` (`∀ s ∈ Icc 0 T, Summable (fun n ↦ (φ₁ n s - φ₂ n s)^2) ∧ ∑' n, (φ₁ n s - φ₂ n s)^2 ≤ C`),
then `φ₁ n t = φ₂ n t` for ALL `t ∈ [0, T]` and ALL `n : ℕ`. -/
theorem infinite_krylov_ode_carleman_l2_unique {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hb_nn : ∀ n, 0 ≤ b n)
    (hcarleman : ¬ Summable (fun M : ℕ ↦ (max (b (M + 1)) 1)⁻¹))
    (φ₁ φ₂ : ℕ → ℝ → ℝ) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hode₁ : ∀ n s, HasDerivAt (φ₁ n) (b n * φ₁ (n - 1) s - b (n + 1) * φ₁ (n + 1) s) s)
    (hode₂ : ∀ n s, HasDerivAt (φ₂ n) (b n * φ₂ (n - 1) s - b (n + 1) * φ₂ (n + 1) s) s)
    (hinit : ∀ n, φ₁ n 0 = φ₂ n 0)
    (hl2 : ∀ s ∈ Set.Icc 0 T,
      Summable (fun n ↦ (φ₁ n s - φ₂ n s) ^ 2) ∧ ∑' n, (φ₁ n s - φ₂ n s) ^ 2 ≤ C) :
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
  let w : ℕ → ℝ := fun M ↦ (max (b (M + 1)) 1)⁻¹
  have hw_pos : ∀ M, 0 < w M := fun M ↦ inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hwb_le : ∀ M, w M * b (M + 1) ≤ 1 := by
    intro M
    dsimp only [w]
    rw [inv_mul_le_one₀ (lt_of_lt_of_le one_pos (le_max_right _ _))]
    exact le_max_left _ _
  intro t ht n₀
  have ht0 : 0 ≤ t := ht.1
  have hSK_le : ∀ K : ℕ, ∑ M ∈ Finset.range K, w M * E M t ≤ 2 * C * t := by
    intro K
    let S : ℝ → ℝ := fun s ↦ ∑ M ∈ Finset.range K, w M * E M s
    have hS0 : S 0 = 0 := by dsimp only [S, E]; simp [hψ0]
    have hSd : ∀ s, HasDerivAt S
        (∑ M ∈ Finset.range K, w M * (-2 * b (M + 1) * ψ M s * ψ (M + 1) s)) s :=
      fun s ↦ HasDerivAt.fun_sum fun M _ ↦ (hE_deriv M s).const_mul (w M)
    have hSbound : ∀ s ∈ Set.Icc 0 t, deriv S s ≤ 2 * C := by
      intro s hs
      rw [(hSd s).deriv]
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
      have hterm : ∀ M ∈ Finset.range K,
          w M * (-2 * b (M + 1) * ψ M s * ψ (M + 1) s) ≤ (ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2 := by
        intro M _
        have ham : -2 * ψ M s * ψ (M + 1) s ≤ (ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2 := by
          nlinarith [sq_nonneg (ψ M s + ψ (M + 1) s)]
        have hwb_nn : 0 ≤ w M * b (M + 1) := mul_nonneg (hw_pos M).le (hb_nn (M + 1))
        have h1 : w M * (-2 * b (M + 1) * ψ M s * ψ (M + 1) s) =
            (w M * b (M + 1)) * (-2 * ψ M s * ψ (M + 1) s) := by ring
        rw [h1]
        calc (w M * b (M + 1)) * (-2 * ψ M s * ψ (M + 1) s)
            ≤ (w M * b (M + 1)) * ((ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2) :=
              mul_le_mul_of_nonneg_left ham hwb_nn
          _ ≤ 1 * ((ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2) :=
              mul_le_mul_of_nonneg_right (hwb_le M) (by positivity)
          _ = (ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2 := one_mul _
      have hsum_le : ∑ M ∈ Finset.range K, ((ψ M s) ^ 2 + (ψ (M + 1) s) ^ 2) ≤ 2 * C := by
        rw [Finset.sum_add_distrib]
        have h1 : ∑ M ∈ Finset.range K, (ψ M s) ^ 2 ≤ ∑' n, (ψ n s) ^ 2 :=
          (hl2 s hsT).1.sum_le_tsum (Finset.range K) (fun n _ ↦ sq_nonneg _)
        have h2 : ∑ M ∈ Finset.range K, (ψ (M + 1) s) ^ 2 ≤ ∑' n, (ψ n s) ^ 2 := by
          have hshift : ∑ M ∈ Finset.range K, (ψ (M + 1) s) ^ 2 ≤
              ∑ n ∈ Finset.range (K + 1), (ψ n s) ^ 2 := by
            rw [Finset.sum_range_succ']
            linarith [sq_nonneg (ψ 0 s)]
          exact le_trans hshift ((hl2 s hsT).1.sum_le_tsum (Finset.range (K + 1)) (fun n _ ↦ sq_nonneg _))
        linarith [(hl2 s hsT).2]
      exact le_trans (Finset.sum_le_sum hterm) hsum_le
    by_cases ht_eq : t = 0
    · subst ht_eq; simpa [S, hS0]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope S ht_pos
        (fun s _ ↦ (hSd s).continuousAt.continuousWithinAt)
        (fun s _ ↦ (hSd s).differentiableAt.differentiableWithinAt)
      have hc_le : deriv S c ≤ 2 * C := hSbound c ⟨hc_mem.1.le, hc_mem.2.le⟩
      rw [hS0, sub_zero, sub_zero] at hc_eq
      have hdiv : S t / t ≤ 2 * C := hc_eq ▸ hc_le
      exact (div_le_iff₀ ht_pos).mp hdiv
  by_contra hne
  have hψ_ne : ψ n₀ t ≠ 0 := sub_ne_zero.mpr hne
  have hψ_sq_pos : 0 < (ψ n₀ t) ^ 2 := sq_pos_of_ne_zero hψ_ne
  have htail_bdd : ∀ K : ℕ, ∑ M ∈ Finset.range K, w (n₀ + M) ≤ 2 * C * t / (ψ n₀ t) ^ 2 := by
    intro K
    rw [le_div_iff₀ hψ_sq_pos]
    calc (∑ M ∈ Finset.range K, w (n₀ + M)) * (ψ n₀ t) ^ 2
        = ∑ M ∈ Finset.range K, w (n₀ + M) * (ψ n₀ t) ^ 2 := Finset.sum_mul _ _ _
      _ ≤ ∑ M ∈ Finset.range K, w (n₀ + M) * E (n₀ + M) t := by
          apply Finset.sum_le_sum; intro M _
          apply mul_le_mul_of_nonneg_left _ (hw_pos _).le
          dsimp only [E]
          exact Finset.single_le_sum (fun n _ ↦ sq_nonneg (ψ n t))
            (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ M ∈ Finset.range (n₀ + K), w M * E M t := by
          have hsub : (Finset.range K).image (fun M ↦ n₀ + M) ⊆ Finset.range (n₀ + K) := by
            intro x hx; rcases Finset.mem_image.mp hx with ⟨M, hM, rfl⟩
            exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hM; omega)
          have hinj : Set.InjOn (fun M ↦ n₀ + M) (Finset.range K : Set ℕ) :=
            fun a _ b _ hab ↦ Nat.add_left_cancel hab
          have hsum_img : ∑ M ∈ Finset.range K, w (n₀ + M) * E (n₀ + M) t =
              ∑ x ∈ (Finset.range K).image (fun M ↦ n₀ + M), w x * E x t :=
            (Finset.sum_image (f := fun x ↦ w x * E x t) (fun a ha b hb hab ↦ hinj ha hb hab)).symm
          rw [hsum_img]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun M _ _ ↦
            mul_nonneg (hw_pos M).le (Finset.sum_nonneg fun n _ ↦ sq_nonneg _))
      _ ≤ 2 * C * t := hSK_le (n₀ + K)
  have hsumm_shift : Summable (fun M : ℕ ↦ w (n₀ + M)) :=
    summable_of_sum_range_le (fun M ↦ (hw_pos _).le) htail_bdd
  have hsumm : Summable w := (summable_nat_add_iff n₀).mp (by simpa [add_comm] using hsumm_shift)
  exact hcarleman hsumm

/-- **Item #6 — Linear-Growth Specialization (`0 ≤ b n ≤ α n + γ` → Genuine `ℓ²`-Uniqueness)**:
Connects directly to harmonic divergence without any `hflux` hypothesis. -/
theorem infinite_krylov_ode_linear_growth_l2_unique {b : ℕ → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hb0 : b 0 = 0)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, 1 ≤ n → b n ≤ α * (n : ℝ) + γ)
    (φ₁ φ₂ : ℕ → ℝ → ℝ) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hode₁ : ∀ n s, HasDerivAt (φ₁ n) (b n * φ₁ (n - 1) s - b (n + 1) * φ₁ (n + 1) s) s)
    (hode₂ : ∀ n s, HasDerivAt (φ₂ n) (b n * φ₂ (n - 1) s - b (n + 1) * φ₂ (n + 1) s) s)
    (hinit : ∀ n, φ₁ n 0 = φ₂ n 0)
    (hl2 : ∀ s ∈ Set.Icc 0 T,
      Summable (fun n ↦ (φ₁ n s - φ₂ n s) ^ 2) ∧ ∑' n, (φ₁ n s - φ₂ n s) ^ 2 ≤ C) :
    ∀ t ∈ Set.Icc 0 T, ∀ n : ℕ, φ₁ n t = φ₂ n t := by
  refine infinite_krylov_ode_carleman_l2_unique hb0 hb_nn ?_ φ₁ φ₂ hT hC hode₁ hode₂ hinit hl2
  intro hsumm
  set A : ℝ := α + γ + 1
  have hA_pos : 0 < A := by dsimp only [A]; linarith
  have hle : ∀ M : ℕ, (1 / A) * (1 / ((M + 1 : ℕ) : ℝ)) ≤ (max (b (M + 1)) 1)⁻¹ := by
    intro M
    have hM1_pos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    have hmax_le : max (b (M + 1)) 1 ≤ A * ((M + 1 : ℕ) : ℝ) := by
      have hM1_ge1 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M + 1)
      apply max_le
      · have h1 := hb_lin (M + 1) (by omega)
        dsimp only [A]; nlinarith
      · dsimp only [A]; nlinarith
    have hinv : (A * ((M + 1 : ℕ) : ℝ))⁻¹ ≤ (max (b (M + 1)) 1)⁻¹ :=
      inv_anti₀ (lt_of_lt_of_le one_pos (le_max_right _ _)) hmax_le
    calc (1 / A) * (1 / ((M + 1 : ℕ) : ℝ))
        = (A * ((M + 1 : ℕ) : ℝ))⁻¹ := by field_simp [hA_pos.ne', hM1_pos.ne']
      _ ≤ (max (b (M + 1)) 1)⁻¹ := hinv
  have hharm_shift : Summable (fun M : ℕ ↦ (1 / A) * (1 / ((M + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun M ↦ by positivity) hle hsumm
  have hharm1 : Summable (fun M : ℕ ↦ 1 / ((M + 1 : ℕ) : ℝ)) := by
    have h := hharm_shift.mul_left A
    refine h.congr fun M ↦ ?_
    field_simp [hA_pos.ne']
  have hharm : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff 1).mp (by simpa [add_comm] using hharm1)
  exact Real.not_summable_one_div_natCast hharm

end Item6CarlemanL2Uniqueness

section Item7And8ExactInfiniteBoundsAndLimsup

/-- **Item #7 — Unconditional `limsup` Rate Bound Including `b 1 = 0` (`K(t) = 0`)**:
For ANY `K : ℝ → ℝ` with `0 ≤ K t` and `K t ≤ C * exp(2 α t)` eventually (`C > 0`, `α > 0`),
`limsup_{t → ∞} log(K(t)) / t ≤ 2 α` — covering BOTH `0 < K(t)` and the degenerate `b 1 = 0`
case where `K(t) = 0` (since `Real.log 0 = 0`). -/
theorem theorem_1_1a_limsup_rate_bound_nonneg {C α : ℝ} {K : ℝ → ℝ}
    (hC : 0 < C) (hα : 0 < α)
    (hK : ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ K t ∧ K t ≤ C * Real.exp (2 * α * t)) :
    Filter.limsup (fun t : ℝ ↦ Real.log (K t) / t) Filter.atTop ≤ 2 * α := by
  by_cases hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (fun t : ℝ ↦ Real.log (K t) / t)
  · have hbound : ∀ᶠ t : ℝ in Filter.atTop,
        Real.log (K t) / t ≤ max (Real.log C) 0 / t + 2 * α := by
      filter_upwards [hK, Filter.eventually_gt_atTop (0 : ℝ)] with t ⟨hKt_nn, hKt_le⟩ ht_pos
      by_cases h0 : K t = 0
      · rw [h0, Real.log_zero, zero_div]
        have : 0 ≤ max (Real.log C) 0 / t := div_nonneg (le_max_right _ _) ht_pos.le
        linarith
      · have hKt_pos : 0 < K t := lt_of_le_of_ne hKt_nn (Ne.symm h0)
        have hlog : Real.log (K t) ≤ max (Real.log C) 0 + 2 * α * t := by
          calc Real.log (K t)
              ≤ Real.log (C * Real.exp (2 * α * t)) := Real.log_le_log hKt_pos hKt_le
            _ = Real.log C + 2 * α * t := by
                rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
            _ ≤ max (Real.log C) 0 + 2 * α * t := by linarith [le_max_left (Real.log C) 0]
        calc Real.log (K t) / t
            ≤ (max (Real.log C) 0 + 2 * α * t) / t := div_le_div_of_nonneg_right hlog ht_pos.le
          _ = max (Real.log C) 0 / t + 2 * α := by field_simp [ht_pos.ne']
    have hlim : Filter.Tendsto (fun t : ℝ ↦ max (Real.log C) 0 / t + 2 * α) Filter.atTop (nhds (2 * α)) := by
      have h0 : Filter.Tendsto (fun t : ℝ ↦ max (Real.log C) 0 / t) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using h0.add_const (2 * α)
    have hle : Filter.limsup (fun t : ℝ ↦ Real.log (K t) / t) Filter.atTop ≤
        Filter.limsup (fun t : ℝ ↦ max (Real.log C) 0 / t + 2 * α) Filter.atTop :=
      Filter.limsup_le_limsup hbound hcob hlim.isBoundedUnder_le
    rwa [hlim.limsup_eq] at hle
  · rw [Filter.limsup_eq]
    have hnotbdd : ¬ BddBelow {a : ℝ | ∀ᶠ t : ℝ in Filter.atTop, Real.log (K t) / t ≤ a} := by
      intro hbdd; apply hcob; rcases hbdd with ⟨m, hm⟩; exact ⟨m, fun a ha ↦ hm ha⟩
    rw [Real.sInf_of_not_bddBelow hnotbdd]
    linarith

/-- **Items #7 & #8 — Exact Single-Exponential Infinite-Chain Eqs. (1.12)–(1.13) & `limsup` Rate Bound**:
From pointwise convergence `φ_N N m t → φ m t` of finite-chain solutions with `0 ≤ b n ≤ α n + γ`,
derives by Fatou's lemma the sharp single-exponential Eq. (1.12) tail bound, sharp Eq. (1.13)
complexity bound `K(t) ≤ (exp((1/2 + γ/α) θ₀) / (4 e tanh(θ₀/4))) exp(2 α t)` (superseding
the legacy double-exponential `theorem_1_1a_infinite_fatou_proved`), and the `limsup` rate
bound `limsup_{t → ∞} log(K(t)) / t ≤ 2 α` for all `b 1 ≥ 0` (including `b 1 = 0`). -/
theorem theorem_1_1a_infinite_fatou_exact_single_exp {α γ θ₀ : ℝ}
    (b : ℕ → ℝ) (φ_N : ℕ → ℕ → ℝ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb0 : b 0 = 0)
    (hb_nn : ∀ n, 1 ≤ n → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → b n ≤ α * (n : ℝ) + γ)
    (hode_N : ∀ N m, m ≤ N → ∀ t,
      HasDerivAt (φ_N N m)
        ((if m = 0 then 0 else b m) * φ_N N (m - 1) t -
         (if m = N then 0 else b (m + 1)) * φ_N N (m + 1) t) t)
    (hinit_N : ∀ N m, m ≤ N → φ_N N m 0 = if m = 0 then 1 else 0)
    (htendsto : ∀ m t, Tendsto (fun N ↦ φ_N N m t) atTop (nhds (φ m t))) :
    (∀ t ≥ 0,
      (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
        Real.exp ((1 / 2 + γ / α) * θ₀) *
          Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
      (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2 ≤
        (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
          Real.exp (2 * α * t))) ∧
    Filter.limsup (fun t : ℝ ↦ Real.log (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2) / t) Filter.atTop ≤ 2 * α := by
  have hmain : ∀ t ≥ 0,
      (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
        Real.exp ((1 / 2 + γ / α) * θ₀) *
          Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
      (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2 ≤
        (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
          Real.exp (2 * α * t)) := by
    intro t ht
    refine theorem_1_1a_infinite_tail_and_complexity φ hα hγ hθ₀ t ht ?_
    intro M
    have hM_bound : ∀ N ≥ M,
        ∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ_N N m t) ^ 2 ≤
          Real.exp ((1 / 2 + γ / α) * θ₀) := by
      intro N hNM
      let bN : ℕ → ℝ := fun k ↦ if k ≤ N then b k else 0
      have hbN0 : bN 0 = 0 := by simp [bN, hb0]
      have hbNN : bN (N + 1) = 0 := by simp [bN]
      have hbN_nn : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ bN n := fun n hn1 hnN ↦ by
        simp [bN, hnN, hb_nn n hn1]
      have hbN_lin : ∀ n, 1 ≤ n → n ≤ N → bN n ≤ α * (n : ℝ) + γ := fun n hn1 hnN ↦ by
        simp [bN, hnN, hb_lin n hn1]
      have hode_bN : ∀ m ≤ N, ∀ s,
          HasDerivAt (φ_N N m) (bN m * φ_N N (m - 1) s - bN (m + 1) * φ_N N (m + 1) s) s := by
        intro m hm s
        have h := hode_N N m hm s
        have h1 : bN m = if m = 0 then 0 else b m := by
          by_cases hm0 : m = 0
          · simp [bN, hm0, hb0]
          · simp [bN, hm, hm0]
        have h2 : bN (m + 1) = if m = N then 0 else b (m + 1) := by
          by_cases hmN : m = N
          · subst hmN; simp [bN]
          · have : m + 1 ≤ N := by omega
            simp [bN, hmN, this]
        rwa [h1, h2]
      have hmgf := lemma_3_1_finite_chain_mgf bN (φ_N N) hα hγ hθ₀ hbN0 hbNN hbN_nn hbN_lin
        hode_bN (hinit_N N) t ht
      have hle_full : ∑ m ∈ Finset.range M,
            Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ_N N m t) ^ 2 ≤
          finiteMGF N (φ_N N) (charTheta α θ₀ t) t := by
        unfold finiteMGF
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (by omega)
        · intro m _ _; positivity
      exact le_trans hle_full (le_trans hmgf.1 hmgf.2)
    have htend_sum : Tendsto
        (fun N ↦ ∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ_N N m t) ^ 2)
        atTop
        (nhds (∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2)) :=
      tendsto_finset_sum _ fun m _ ↦ tendsto_const_nhds.mul ((htendsto m t).pow 2)
    exact le_of_tendsto htend_sum (by filter_upwards [eventually_ge_atTop M] with N hN; exact hM_bound N hN)
  refine ⟨hmain, ?_⟩
  have htanh_pos : 0 < Real.tanh (θ₀ / 4) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
    apply div_pos _ (Real.cosh_pos _)
    have : Real.exp (-(θ₀ / 4)) < Real.exp (θ₀ / 4) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  set C : ℝ := Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))
  have hC_pos : 0 < C := by dsimp only [C]; positivity
  refine theorem_1_1a_limsup_rate_bound_nonneg hC_pos hα ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact ⟨tsum_nonneg fun m ↦ by positivity, (hmain t ht).2⟩

end Item7And8ExactInfiniteBoundsAndLimsup

end KrylovChaos
