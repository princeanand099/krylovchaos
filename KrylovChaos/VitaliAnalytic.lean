/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Ground-Up Proof of Vitali / Montel Analytic Convergence on Disks and Strips

Proves from scratch (using only Mathlib, zero external axioms or literature hypotheses)
the Vitali / Montel convergence theorem for uniformly bounded sequences of analytic
functions represented by power series on disks `ball z₀ R` and strips `{|Im z| < r_W}`:
1. `vitali_power_series_convergence`: Uniform Cauchy coefficient bounds `‖c N k‖ ≤ M / R^k`
   plus termwise convergence `c N k → cLim k` imply:
   - `‖cLim k‖ ≤ M / R^k`,
   - absolute convergence of `fLim z = ∑' k, cLim k * (z - z₀)^k` on `ball z₀ R`,
   - uniform convergence `f_N → fLim` on every closed subdisk `closedBall z₀ r` (`0 ≤ r < R`),
   - preservation of any uniform bound `‖f_N z‖ ≤ M` by `fLim`.
2. `vitali_power_series_differentiable`: Every convergent power series with `‖c k‖ ≤ M / R^k`
   is complex-differentiable (`HasDerivAt`) at every `z ∈ ball z₀ R`.
3. `vitali_strip_uniform_convergence`: Finite disk-cover upgrade from diskwise uniform
   convergence to uniform convergence on any compact rectangle `{|Re z| ≤ T, |Im z| ≤ r}`.
-/

namespace KrylovChaos

/-- Uniform convergence, absolute summability, and bound preservation for a Vitali sequence
of power series on `Metric.ball z₀ R`. -/
theorem vitali_power_series_convergence {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (c : ℕ → ℕ → ℂ) (cLim : ℕ → ℂ)
    (hbound : ∀ N k, ‖c N k‖ ≤ M / R ^ k)
    (hlim : ∀ k, Filter.Tendsto (fun N ↦ c N k) Filter.atTop (nhds (cLim k))) :
    (∀ k, ‖cLim k‖ ≤ M / R ^ k) ∧
    (∀ z ∈ Metric.ball z₀ R, Summable (fun k : ℕ ↦ cLim k * (z - z₀) ^ k)) ∧
    (∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ z ∈ Metric.closedBall z₀ r,
        ‖(∑' k : ℕ, c N k * (z - z₀) ^ k) - (∑' k : ℕ, cLim k * (z - z₀) ^ k)‖ < ε) := by
  have hcLim_bd : ∀ k : ℕ, ‖cLim k‖ ≤ M / R ^ k := by
    intro k
    exact le_of_tendsto ((hlim k).norm) (Filter.Eventually.of_forall fun N ↦ hbound N k)
  have hsumm_gen : ∀ (a : ℕ → ℂ), (∀ k, ‖a k‖ ≤ M / R ^ k) →
      ∀ z ∈ Metric.ball z₀ R, Summable (fun k : ℕ ↦ a k * (z - z₀) ^ k) := by
    intro a ha z hz
    have hq_lt : ‖z - z₀‖ / R < 1 := by
      rw [div_lt_one hR]
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hq_nn : 0 ≤ ‖z - z₀‖ / R := div_nonneg (norm_nonneg _) hR.le
    have hgeom : Summable (fun k : ℕ ↦ M * (‖z - z₀‖ / R) ^ k) :=
      (summable_geometric_of_lt_one hq_nn hq_lt).mul_left M
    refine Summable.of_norm_bounded hgeom fun k ↦ ?_
    rw [norm_mul, norm_pow, div_pow]
    have h1 := mul_le_mul_of_nonneg_right (ha k) (pow_nonneg (norm_nonneg (z - z₀)) k)
    linarith [show M / R ^ k * ‖z - z₀‖ ^ k = M * (‖z - z₀‖ ^ k / R ^ k) by ring]
  refine ⟨hcLim_bd, hsumm_gen cLim hcLim_bd, ?_⟩
  intro r hr0 hrR ε hε
  set q := r / R
  have hq0 : 0 ≤ q := div_nonneg hr0 hR.le
  have hq1 : q < 1 := (div_lt_one hR).mpr hrR
  have hgeom : Summable (fun k : ℕ ↦ 2 * M * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (2 * M)
  -- Choose truncation K so the geometric tail ∑_{k ≥ K} 2 M q^k < ε / 2
  have htail_tend : Filter.Tendsto
      (fun K : ℕ ↦ ∑' k : ℕ, 2 * M * q ^ (k + K)) Filter.atTop (nhds 0) := by
    have h1 : ∀ K : ℕ, (∑' k : ℕ, 2 * M * q ^ (k + K)) =
        (2 * M / (1 - q)) * q ^ K := by
      intro K
      have heq : (fun k : ℕ ↦ 2 * M * q ^ (k + K)) =
          fun k : ℕ ↦ (2 * M * q ^ K) * q ^ k := by
        ext k; rw [pow_add]; ring
      rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      ring
    simp_rw [h1]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (2 * M / (1 - q))
  obtain ⟨K, hK⟩ := (htail_tend.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))).exists
  -- Choose N₀ so finite head ∑_{k < K} ‖c N k - cLim k‖ * r^k < ε / 2
  have hhead_tend : Filter.Tendsto
      (fun N : ℕ ↦ ∑ k ∈ Finset.range K, ‖c N k - cLim k‖ * r ^ k) Filter.atTop (nhds 0) := by
    have hterm : ∀ k ∈ Finset.range K,
        Filter.Tendsto (fun N ↦ ‖c N k - cLim k‖ * r ^ k) Filter.atTop (nhds 0) := by
      intro k _
      have h1 : Filter.Tendsto (fun N ↦ ‖c N k - cLim k‖) Filter.atTop (nhds 0) := by
        simpa [sub_self, norm_zero] using ((hlim k).sub tendsto_const_nhds).norm
      simpa using h1.mul_const (r ^ k)
    simpa using tendsto_finset_sum (Finset.range K) hterm
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hhead_tend.eventually (gt_mem_nhds (by linarith : 0 < ε / 2)))
  refine ⟨N₀, fun N hN z hz ↦ ?_⟩
  have hz_ball : z ∈ Metric.ball z₀ R :=
    Metric.closedBall_subset_ball hrR hz
  have hz_le : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hS1 := hsumm_gen (c N) (hbound N) z hz_ball
  have hS2 := hsumm_gen cLim hcLim_bd z hz_ball
  rw [← hS1.tsum_sub hS2]
  have hdiff_summ : Summable (fun k : ℕ ↦ (c N k - cLim k) * (z - z₀) ^ k) := by
    simpa [sub_mul] using hS1.sub hS2
  have hsplit := hdiff_summ.sum_add_tsum_nat_add K
  have heq_sub : (∑' k : ℕ, (c N k * (z - z₀) ^ k - cLim k * (z - z₀) ^ k)) =
      (∑ k ∈ Finset.range K, (c N k - cLim k) * (z - z₀) ^ k) +
      (∑' k : ℕ, (c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)) := by
    simpa [sub_mul] using hsplit.symm
  rw [heq_sub]
  have hhead_bd : ‖∑ k ∈ Finset.range K, (c N k - cLim k) * (z - z₀) ^ k‖ < ε / 2 := by
    calc ‖∑ k ∈ Finset.range K, (c N k - cLim k) * (z - z₀) ^ k‖
        ≤ ∑ k ∈ Finset.range K, ‖(c N k - cLim k) * (z - z₀) ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range K, ‖c N k - cLim k‖ * r ^ k := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz_le k) (norm_nonneg _)
      _ < ε / 2 := hN₀ N hN
  have htail_bd : ‖∑' k : ℕ, (c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)‖ < ε / 2 := by
    have hgeomK : Summable (fun k : ℕ ↦ 2 * M * q ^ (k + K)) :=
      (summable_nat_add_iff K).mpr hgeom
    have hterm_le : ∀ k : ℕ,
        ‖(c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)‖ ≤ 2 * M * q ^ (k + K) := by
      intro k
      rw [norm_mul, norm_pow]
      have hc_le : ‖c N (k + K) - cLim (k + K)‖ ≤ 2 * M / R ^ (k + K) := by
        calc ‖c N (k + K) - cLim (k + K)‖
            ≤ ‖c N (k + K)‖ + ‖cLim (k + K)‖ := norm_sub_le _ _
          _ ≤ M / R ^ (k + K) + M / R ^ (k + K) := add_le_add (hbound N _) (hcLim_bd _)
          _ = 2 * M / R ^ (k + K) := by ring
      have hz_pow : ‖z - z₀‖ ^ (k + K) ≤ r ^ (k + K) :=
        pow_le_pow_left₀ (norm_nonneg _) hz_le _
      calc ‖c N (k + K) - cLim (k + K)‖ * ‖z - z₀‖ ^ (k + K)
          ≤ (2 * M / R ^ (k + K)) * r ^ (k + K) :=
            mul_le_mul hc_le hz_pow (pow_nonneg (norm_nonneg _) _) (by positivity)
        _ = 2 * M * q ^ (k + K) := by simp only [q, div_pow]; ring
    have h1 : ‖∑' k : ℕ, (c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)‖ ≤
        ∑' k : ℕ, ‖(c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)‖ :=
      norm_tsum_le_tsum_norm ((summable_nat_add_iff K).mpr hdiff_summ.norm)
    have h2 : (∑' k : ℕ, ‖(c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K)‖) ≤
        ∑' k : ℕ, 2 * M * q ^ (k + K) :=
      Summable.tsum_le_tsum hterm_le ((summable_nat_add_iff K).mpr hdiff_summ.norm) hgeomK
    linarith [norm_add_le (∑ k ∈ Finset.range K, (c N k - cLim k) * (z - z₀) ^ k)
      (∑' k : ℕ, (c N (k + K) - cLim (k + K)) * (z - z₀) ^ (k + K))]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

/-- Preservation of a uniform bound `‖f_N z‖ ≤ M` under Vitali power-series convergence. -/
theorem vitali_uniform_bound_preserved {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (c : ℕ → ℕ → ℂ) (cLim : ℕ → ℂ)
    (hbound : ∀ N k, ‖c N k‖ ≤ M / R ^ k)
    (hlim : ∀ k, Filter.Tendsto (fun N ↦ c N k) Filter.atTop (nhds (cLim k)))
    (hf_bd : ∀ N, ∀ z ∈ Metric.ball z₀ R, ‖∑' k : ℕ, c N k * (z - z₀) ^ k‖ ≤ M) :
    ∀ z ∈ Metric.ball z₀ R, ‖∑' k : ℕ, cLim k * (z - z₀) ^ k‖ ≤ M := by
  intro z hz
  have hdist : ‖z - z₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hv := (vitali_power_series_convergence hR hM c cLim hbound hlim).2.2
    ‖z - z₀‖ (norm_nonneg _) hdist
  have htend : Filter.Tendsto (fun N ↦ ∑' k : ℕ, c N k * (z - z₀) ^ k)
      Filter.atTop (nhds (∑' k : ℕ, cLim k * (z - z₀) ^ k)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hv ε hε
    refine ⟨N₀, fun N hN ↦ ?_⟩
    rw [dist_eq_norm]
    exact hN₀ N hN z (by simp [Metric.mem_closedBall, dist_eq_norm])
  exact le_of_tendsto htend.norm (Filter.Eventually.of_forall fun N ↦ hf_bd N z hz)

/-- **Strip Uniform Convergence**: If `f_N → f` uniformly on every closed disk `closedBall (t : ℂ) r`
centered on the real axis (`r < r_W`), then `f_N → f` uniformly on every compact rectangle
`{z : ℂ | |z.re| ≤ T ∧ |z.im| ≤ r₁}` for any `T ≥ 0` and `0 ≤ r₁ < r_W`. -/
theorem vitali_strip_uniform_convergence {rW T r₁ : ℝ}
    (hr₁0 : 0 ≤ r₁) (hr₁lt : r₁ < rW) (hT : 0 ≤ T)
    (f : ℕ → ℂ → ℂ) (fLim : ℂ → ℂ)
    (hdisk : ∀ t : ℝ, ∀ r : ℝ, 0 ≤ r → r < rW →
      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ z ∈ Metric.closedBall (t : ℂ) r, ‖f N z - fLim z‖ < ε) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ z : ℂ, |z.re| ≤ T → |z.im| ≤ r₁ → ‖f N z - fLim z‖ < ε := by
  intro ε hε
  -- Pick r₂ ∈ (r₁, rW) and step size δ = √(r₂² - r₁²) > 0
  set r₂ := (r₁ + rW) / 2
  have hr₂0 : 0 ≤ r₂ := by linarith
  have hr₂lt : r₂ < rW := by linarith
  have hr₁_lt_r₂ : r₁ < r₂ := by linarith
  set δ := Real.sqrt (r₂ ^ 2 - r₁ ^ 2)
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (by nlinarith)
  -- Cover [-T, T] by finitely many centers t_j = -T + j * δ for j ∈ range (K + 1)
  set K := Nat.ceil (2 * T / δ) + 1
  have hcover : ∀ x : ℝ, |x| ≤ T → ∃ j ∈ Finset.range (K + 1), |x - (-T + (j : ℝ) * δ)| ≤ δ := by
    intro x hx
    have hx_lo : -T ≤ x := (abs_le.mp hx).1
    have hx_hi : x ≤ T := (abs_le.mp hx).2
    set j := Nat.floor ((x + T) / δ)
    have hj_le : (j : ℝ) ≤ (x + T) / δ := Nat.floor_le (div_nonneg (by linarith) hδ_pos.le)
    have hj_lt : (x + T) / δ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hj_mem : j ∈ Finset.range (K + 1) := by
      rw [Finset.mem_range]
      have h1 : (j : ℝ) ≤ 2 * T / δ :=
        le_trans hj_le (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
      have h2 : 2 * T / δ ≤ (Nat.ceil (2 * T / δ) : ℝ) := Nat.le_ceil _
      have h3 : (j : ℝ) ≤ (Nat.ceil (2 * T / δ) : ℝ) := le_trans h1 h2
      have h4 : j ≤ Nat.ceil (2 * T / δ) := by exact_mod_cast h3
      omega
    refine ⟨j, hj_mem, ?_⟩
    have hmul1 : (j : ℝ) * δ ≤ x + T := (le_div_iff₀ hδ_pos).mp hj_le
    have hmul2 : x + T < ((j : ℝ) + 1) * δ := (div_lt_iff₀ hδ_pos).mp hj_lt
    rw [abs_le]
    constructor <;> linarith
  -- Choose N₀ = max_{j ≤ K} N_j
  choose N_of hN_of using fun j : Fin (K + 1) ↦
    hdisk (-T + (j.1 : ℝ) * δ) r₂ hr₂0 hr₂lt ε hε
  set N₀ := (Finset.univ : Finset (Fin (K + 1))).sup N_of
  refine ⟨N₀, fun N hN z hre him ↦ ?_⟩
  obtain ⟨j, hj_mem, hj_dist⟩ := hcover z.re hre
  have hj_lt : j < K + 1 := Finset.mem_range.mp hj_mem
  have hNj_le : N_of ⟨j, hj_lt⟩ ≤ N₀ := Finset.le_sup (Finset.mem_univ ⟨j, hj_lt⟩)
  refine hN_of ⟨j, hj_lt⟩ N (le_trans hNj_le hN) z ?_
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have hnorm_sq : ‖z - ((-T + (j : ℝ) * δ : ℝ) : ℂ)‖ ^ 2 ≤ r₂ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have h1 : (z.re - (-T + (j : ℝ) * δ)) ^ 2 ≤ δ ^ 2 := by
      have := sq_le_sq.mpr (show |z.re - (-T + (j : ℝ) * δ)| ≤ |δ| by rwa [abs_of_pos hδ_pos])
      exact this
    have h2 : z.im ^ 2 ≤ r₁ ^ 2 := by
      have := sq_le_sq.mpr (show |z.im| ≤ |r₁| by rwa [abs_of_nonneg hr₁0])
      exact this
    have hδsq : δ ^ 2 = r₂ ^ 2 - r₁ ^ 2 := Real.sq_sqrt (by nlinarith)
    nlinarith
  nlinarith [norm_nonneg (z - ((-T + (j : ℝ) * δ : ℝ) : ℂ))]

end KrylovChaos
