/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Section 4.1–4.2: Wightman Filtration Dominance and Static Reduction

Formalizes:
- **Proposition 4.1**: Locality inclusion for the Wightman Krylov basis
  `𝒪_n^{(β)} ∈ 𝒱_{min(N, s₀ + (r-1)n)}` and the finite-temperature `q`-complexity bound
  `(𝒪(t) | 𝒬^{(β)} | 𝒪(t))_β^W ≤ (r - 1) K_β^W(t) + s₀` (Eq. 4.2).
- **Lemma 4.2**: Thermal-size truncation inequality
  `𝒮_β(𝒪(t)) ≤ Λ_β^MSS(s_M) + 2 N ε_M(t) + N ε_M(t)²` (Eq. 4.3).
- **Theorem 1.1(b)**: Static reduction proving `λ_L ≤ 2 α_T^{(W)}` under (H1) and (H2).
-/

namespace KrylovChaos

section FiltrationDominance

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **Proposition 4.1(1)**: Under an ascending filtration `V : ℕ → Submodule ℂ E`
with locality shift `L(V_s) ⊆ V_{min(N, s + r - 1)}`, any Lanczos sequence starting
in `V_{s₀}` satisfies `O_n ∈ V_{min(N, s₀ + (r - 1) * n)}` for all `n`. -/
theorem prop_4_1_krylov_filtration {N r s₀ : ℕ}
    (V : ℕ → Submodule ℂ E) (hV_mono : Monotone V)
    (L : E →ₗ[ℂ] E) (hL : ∀ s x, x ∈ V s → L x ∈ V (min N (s + (r - 1))))
    (O : ℕ → E) (hO0 : O 0 ∈ V (min N s₀))
    (hstep : ∀ n, ∃ a b : ℂ, O (n + 1) = a • L (O n) + (if n = 0 then 0 else b • O (n - 1))) :
    ∀ n : ℕ, O n ∈ V (min N (s₀ + (r - 1) * n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hO0
    | succ m =>
      obtain ⟨a, b, hab⟩ := hstep m
      rw [hab]
      have hm : O m ∈ V (min N (s₀ + (r - 1) * m)) := ih m (Nat.lt_succ_self m)
      have hLm : L (O m) ∈ V (min N (min N (s₀ + (r - 1) * m) + (r - 1))) := hL _ _ hm
      have hidx1 : min N (min N (s₀ + (r - 1) * m) + (r - 1)) ≤ min N (s₀ + (r - 1) * (m + 1)) := by
        have h1 : min N (s₀ + (r - 1) * m) + (r - 1) ≤ s₀ + (r - 1) * (m + 1) := by
          have : min N (s₀ + (r - 1) * m) ≤ s₀ + (r - 1) * m := min_le_right _ _
          nlinarith
        exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) h1)
      have hterm1 : a • L (O m) ∈ V (min N (s₀ + (r - 1) * (m + 1))) :=
        Submodule.smul_mem _ a (hV_mono hidx1 hLm)
      have hterm2 : (if m = 0 then (0 : E) else b • O (m - 1)) ∈
          V (min N (s₀ + (r - 1) * (m + 1))) := by
        split_ifs with hm0
        · exact Submodule.zero_mem _
        · have hprev : O (m - 1) ∈ V (min N (s₀ + (r - 1) * (m - 1))) :=
            ih (m - 1) (by omega)
          have hidx2 : min N (s₀ + (r - 1) * (m - 1)) ≤ min N (s₀ + (r - 1) * (m + 1)) :=
            min_le_min_left N (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) s₀)
          exact Submodule.smul_mem _ b (hV_mono hidx2 hprev)
      exact Submodule.add_mem _ hterm1 hterm2

/-- **Proposition 4.1(2)** (Finite-Temperature `q`-Complexity Bound, Eq. 4.2):
Given tail weights `p : ℕ → ℝ` (`p n = |φ_n(t)|² ≥ 0`) and filtration tail norms
`q : ℕ → ℝ` (`q s = ‖(1 - Π_s) O(t)‖² ≤ 1`) obeying the subspace-monotone projection
inequality `q s ≤ ∑_{n ∈ (k, Kmax)} p n` whenever `s₀ + (r - 1) * k ≤ s`, we have
`∑_{s=0}^{N-1} q s ≤ (r - 1) * (∑_{n=0}^{Kmax-1} n * p n) + s₀`. -/
theorem prop_4_1_q_complexity_bound {N Kmax r s₀ : ℕ} (hr : 1 ≤ r)
    (p q : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hq_le_one : ∀ s, q s ≤ 1)
    (hq_proj : ∀ k s, s₀ + (r - 1) * k ≤ s →
      q s ≤ ∑ n ∈ (Finset.range Kmax).filter (fun n ↦ k < n), p n) :
    (∑ s ∈ Finset.range N, q s) ≤
      ((r - 1 : ℕ) : ℝ) * (∑ n ∈ Finset.range Kmax, (n : ℝ) * p n) + (s₀ : ℝ) := by
  by_cases hr1 : r = 1
  · subst hr1
    simp only [tsub_self, Nat.cast_zero, zero_mul, zero_add]
    have hzero : ∀ s, s₀ ≤ s → q s ≤ 0 := by
      intro s hs
      have h := hq_proj Kmax s (by simpa using hs)
      have hempty : (Finset.range Kmax).filter (fun n ↦ Kmax < n) = ∅ := by
        ext n; simp; omega
      rw [hempty, Finset.sum_empty] at h
      exact h
    have hsplit : ∑ s ∈ Finset.range N, q s ≤ ∑ _ ∈ Finset.range (min N s₀), (1 : ℝ) := by
      calc ∑ s ∈ Finset.range N, q s
          = ∑ s ∈ (Finset.range N).filter (fun s ↦ s < s₀), q s +
            ∑ s ∈ (Finset.range N).filter (fun s ↦ ¬ s < s₀), q s :=
            (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        _ ≤ ∑ _ ∈ (Finset.range N).filter (fun s ↦ s < s₀), (1 : ℝ) + 0 := by
            apply add_le_add
            · exact Finset.sum_le_sum fun s _ ↦ hq_le_one s
            · exact Finset.sum_nonpos fun s hs ↦ hzero s (Nat.le_of_not_lt (Finset.mem_filter.mp hs).2)
        _ = ∑ _ ∈ Finset.range (min N s₀), (1 : ℝ) := by
            rw [add_zero]
            congr 1
            ext s
            simp [Nat.lt_min]
    calc ∑ s ∈ Finset.range N, q s
        ≤ ∑ _ ∈ Finset.range (min N s₀), (1 : ℝ) := hsplit
      _ = ((min N s₀ : ℕ) : ℝ) := by simp
      _ ≤ (s₀ : ℝ) := Nat.cast_le.mpr (min_le_right N s₀)
  · have hr1_pos : 0 < r - 1 := by omega
    have hsplit : ∑ s ∈ Finset.range N, q s =
        ∑ s ∈ (Finset.range N).filter (fun s ↦ s < s₀), q s +
        ∑ s ∈ (Finset.range N).filter (fun s ↦ s₀ ≤ s), q s := by
      have h := (Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun s ↦ s < s₀) q).symm
      convert h using 2
      ext s; simp [Nat.not_lt]
    rw [hsplit]
    have hpart1 : ∑ s ∈ (Finset.range N).filter (fun s ↦ s < s₀), q s ≤ (s₀ : ℝ) := by
      calc ∑ s ∈ (Finset.range N).filter (fun s ↦ s < s₀), q s
          ≤ ∑ _ ∈ (Finset.range N).filter (fun s ↦ s < s₀), (1 : ℝ) :=
            Finset.sum_le_sum fun s _ ↦ hq_le_one s
        _ = (((Finset.range N).filter (fun s ↦ s < s₀)).card : ℝ) := by simp
        _ ≤ ((Finset.range s₀).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (fun s hs ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hs).2)
        _ = (s₀ : ℝ) := by simp
    have hpart2 : ∑ s ∈ (Finset.range N).filter (fun s ↦ s₀ ≤ s), q s ≤
        ((r - 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range Kmax, (n : ℝ) * p n := by
      have hstep : ∀ s ∈ (Finset.range N).filter (fun s ↦ s₀ ≤ s),
          q s ≤ ∑ n ∈ (Finset.range Kmax).filter (fun n ↦ (s - s₀) / (r - 1) < n), p n := by
        intro s hs
        have hs0 : s₀ ≤ s := (Finset.mem_filter.mp hs).2
        apply hq_proj ((s - s₀) / (r - 1)) s
        have hdiv := Nat.mul_div_le (s - s₀) (r - 1)
        omega
      calc ∑ s ∈ (Finset.range N).filter (fun s ↦ s₀ ≤ s), q s
          ≤ ∑ s ∈ (Finset.range N).filter (fun s ↦ s₀ ≤ s),
              ∑ n ∈ (Finset.range Kmax).filter (fun n ↦ (s - s₀) / (r - 1) < n), p n :=
            Finset.sum_le_sum hstep
        _ = ∑ n ∈ Finset.range Kmax,
              (((Finset.range N).filter (fun s ↦ s₀ ≤ s ∧ (s - s₀) / (r - 1) < n)).card : ℝ) *
                p n := by
            simp_rw [Finset.sum_filter]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro n _
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            congr 2
            ext s
            simp [and_assoc]
        _ ≤ ∑ n ∈ Finset.range Kmax, (((r - 1) * n : ℕ) : ℝ) * p n := by
            apply Finset.sum_le_sum
            intro n _
            apply mul_le_mul_of_nonneg_right _ (hp n)
            have hsub : (Finset.range N).filter (fun s ↦ s₀ ≤ s ∧ (s - s₀) / (r - 1) < n) ⊆
                Finset.Ico s₀ (s₀ + (r - 1) * n) := by
              intro s hs
              have ⟨hs0, hlt⟩ := (Finset.mem_filter.mp hs).2
              rw [Finset.mem_Ico]
              refine ⟨hs0, ?_⟩
              have hlt' : s - s₀ < n * (r - 1) := (Nat.div_lt_iff_lt_mul hr1_pos).mp hlt
              rw [mul_comm] at hlt'
              omega
            have hcard := Finset.card_le_card hsub
            rw [Nat.card_Ico] at hcard
            have hcard' : s₀ + (r - 1) * n - s₀ = (r - 1) * n := Nat.add_sub_cancel_left _ _
            rw [hcard'] at hcard
            exact_mod_cast hcard
        _ = ((r - 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range Kmax, (n : ℝ) * p n := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            push_cast
            ring
    linarith

end FiltrationDominance

section ThermalTruncation

/-- **Lemma 4.2** (Thermal-Size Truncation Inequality, Eq. 4.3). -/
theorem lemma_4_2_thermal_size_truncation
    {N : ℕ} {ε Λ bg qA qR reCross : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hbg : 0 ≤ bg) (hΛ : 0 ≤ Λ)
    (hcross : |reCross| ≤ (N : ℝ) * Real.sqrt (1 - ε ^ 2) * ε)
    (hqR : qR ≤ (N : ℝ) * ε ^ 2)
    (hlead : qA - bg ≤ (1 - ε ^ 2) * Λ - ε ^ 2 * bg) :
    (qA + 2 * reCross + qR) - bg ≤ Λ + 2 * (N : ℝ) * ε + (N : ℝ) * ε ^ 2 := by
  have hsqrt : Real.sqrt (1 - ε ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  have hre : reCross ≤ (N : ℝ) * ε := by
    have h1 : reCross ≤ |reCross| := le_abs_self reCross
    have h2 : (N : ℝ) * Real.sqrt (1 - ε ^ 2) * ε ≤ (N : ℝ) * 1 * ε := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    linarith
  have hlead' : qA - bg ≤ Λ := by
    have h1 : (1 - ε ^ 2) * Λ ≤ Λ := by nlinarith
    have h2 : 0 ≤ ε ^ 2 * bg := by positivity
    linarith
  linarith

/-- **Theorem 1.1(b)** (Static Reduction of `λ_L ≤ 2 α`, Eq. 1.14). -/
theorem theorem_1_1b_static_reduction
    {α λL δ C₀ C₁ C₂ : ℝ} {r s₀ : ℕ}
    (hr : 1 ≤ r) (hα : 0 < α) (hλ : 0 < λL) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / λL) * Real.log (N : ℝ)
        let MN := (1 / Real.tanh 1) * Real.exp (2 * α * tN) * Real.log (N : ℝ) + 1
        let sN := (s₀ : ℝ) + ((r : ℝ) - 1) * MN
        c * (N : ℝ) ^ (1 - ε) ≤
          C₁ * sN + C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ) +
          2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ)) :
    λL ≤ 2 * α := by
  by_contra hlt
  push_neg at hlt
  set ρ := 2 * α / λL
  have hρ_pos : 0 < ρ := div_pos (by linarith) hλ
  have hρ_lt : ρ < 1 := (div_lt_one hλ).mpr hlt
  set gap := (1 - δ) * (1 - ρ)
  have hgap_pos : 0 < gap := mul_pos (by linarith) (by linarith)
  set ε₀ := min (1 / 2) (gap / 2)
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (by linarith)
  obtain ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩ := hH1 ε₀ hε₀_pos
  have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_gap : ε < gap / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  set η := δ + (1 - δ) * ρ * (1 - ε)
  have hη_lt : η < 1 - ε := by
    have h1 : 1 - ε - η = (1 - δ) * (1 - ρ) - ε * (1 - (1 - δ) * ρ) := by
      simp only [η]; ring
    have h2 : 1 - (1 - δ) * ρ ≤ 1 := by nlinarith
    have h3 : ε * (1 - (1 - δ) * ρ) ≤ ε := by nlinarith
    have h4 : ε < (1 - δ) * (1 - ρ) := by linarith
    linarith
  set diff := (1 - ε) - η
  have hdiff_pos : 0 < diff := by linarith
  have h1mε_pos : 0 < 1 - ε := by linarith
  have hρ1mε_le_η : ρ * (1 - ε) ≤ η := by
    simp only [η]; nlinarith
  have htanh1_pos : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr zero_lt_one) (Real.cosh_pos 1)
  set K := (1 / Real.tanh 1) * (max 1 ((r : ℝ) - 1)) + (s₀ : ℝ) + (max 1 ((r : ℝ) - 1))
  have hK_pos : 0 < K := by
    have : 0 < 1 / Real.tanh 1 := by positivity
    have : (1 : ℝ) ≤ max 1 ((r : ℝ) - 1) := le_max_left _ _
    have : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg s₀
    simp only [K]; nlinarith
  have hlog_o : (fun N : ℕ ↦ Real.log (N : ℝ)) =o[Filter.atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ (diff / 2)) := by
    have h := (isLittleO_log_rpow_atTop (by linarith : (0 : ℝ) < diff / 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hev_log : ∀ᶠ N : ℕ in Filter.atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (diff / 2) := by
    filter_upwards [hlog_o.bound zero_lt_one, Filter.eventually_ge_atTop 2] with N hN hN2
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hrpow_nn : 0 ≤ (N : ℝ) ^ (diff / 2) := Real.rpow_nonneg hNpos.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog_nn, abs_of_nonneg hrpow_nn,
      one_mul] at hN
    exact hN
  have hpow_zero : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(diff / 2))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < diff / 2)).comp tendsto_natCast_atTop_atTop
  have hinv_zero : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  set A := C₁ * K + C₂ * K ^ (1 - δ) + 1
  have hA_pos : 0 < A := by positivity
  have hev_small1 : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ (-(diff / 2)) < c / (2 * A) :=
    hpow_zero.eventually (gt_mem_nhds (by positivity : 0 < c / (2 * A)))
  have hev_small2 : ∀ᶠ N : ℕ in Filter.atTop,
      2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ) < c / 2 := by
    have h1 : Filter.Tendsto (fun N : ℕ ↦ 2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ))
        Filter.atTop (nhds 0) := by
      have ht1 : Filter.Tendsto (fun N : ℕ ↦ 2 * C₀ * (N : ℝ)⁻¹) Filter.atTop (nhds 0) := by
        simpa using hinv_zero.const_mul (2 * C₀)
      have ht2 : Filter.Tendsto (fun N : ℕ ↦ C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ)) Filter.atTop (nhds 0) := by
        have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp tendsto_natCast_atTop_atTop
        simpa using h3.const_mul (C₀ ^ 2)
      simpa using ht1.add ht2
    exact h1.eventually (gt_mem_nhds (by linarith : 0 < c / 2))
  have hev_all : ∀ᶠ N : ℕ in Filter.atTop,
      N ≥ max N₁ 3 ∧
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (diff / 2) ∧
      (N : ℝ) ^ (-(diff / 2)) < c / (2 * A) ∧
      2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ) < c / 2 :=
    (Filter.eventually_ge_atTop (max N₁ 3)).and (hev_log.and (hev_small1.and hev_small2))
  obtain ⟨N, hNge, hlogN, hsm1, hsm2⟩ := hev_all.exists
  have hN1 : N ≥ N₁ := le_trans (le_max_left _ _) hNge
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hNge
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hN3' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      linarith
    exact (Real.le_log_iff_exp_le hNpos).mpr h3
  have hineq := hN₁ N hN1
  dsimp only at hineq
  have hexp_eq : Real.exp (2 * α * (((1 - ε) / λL) * Real.log (N : ℝ))) =
      (N : ℝ) ^ (ρ * (1 - ε)) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1
    simp only [ρ]
    ring
  rw [hexp_eq] at hineq
  set sN := (s₀ : ℝ) + ((r : ℝ) - 1) *
    ((1 / Real.tanh 1) * (N : ℝ) ^ (ρ * (1 - ε)) * Real.log (N : ℝ) + 1)
  have hr1_nn : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hsN_nn : 0 ≤ sN := by
    simp only [sN]
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := by linarith
    have hpow_nn : 0 ≤ (N : ℝ) ^ (ρ * (1 - ε)) := Real.rpow_nonneg hNpos.le _
    positivity
  have hpow_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (ρ * (1 - ε)) :=
    Real.one_le_rpow hNge1 (mul_nonneg hρ_pos.le h1mε_pos.le)
  have hprod_ge1 : 1 ≤ (N : ℝ) ^ (ρ * (1 - ε)) * Real.log (N : ℝ) := by nlinarith
  have hsN_le : sN ≤ K * ((N : ℝ) ^ (ρ * (1 - ε)) * Real.log (N : ℝ)) := by
    simp only [sN, K]
    have hr_le : (r : ℝ) - 1 ≤ max 1 ((r : ℝ) - 1) := le_max_right _ _
    have h1_le : (1 : ℝ) ≤ max 1 ((r : ℝ) - 1) := le_max_left _ _
    have hs0_nn : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg s₀
    have ht1_nn : 0 ≤ 1 / Real.tanh 1 := by positivity
    nlinarith
  have hsN_le2 : sN ≤ K * (N : ℝ) ^ (ρ * (1 - ε) + diff / 2) := by
    calc sN ≤ K * ((N : ℝ) ^ (ρ * (1 - ε)) * Real.log (N : ℝ)) := hsN_le
      _ ≤ K * ((N : ℝ) ^ (ρ * (1 - ε)) * (N : ℝ) ^ (diff / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hK_pos.le
          exact mul_le_mul_of_nonneg_left hlogN (Real.rpow_nonneg hNpos.le _)
      _ = K * (N : ℝ) ^ (ρ * (1 - ε) + diff / 2) := by
          rw [← Real.rpow_add hNpos]
  have hterm1 : C₁ * sN ≤ C₁ * K * (N : ℝ) ^ (1 - ε - diff / 2) := by
    have hexp_le : ρ * (1 - ε) + diff / 2 ≤ 1 - ε - diff / 2 := by
      simp only [diff]; linarith
    calc C₁ * sN ≤ C₁ * (K * (N : ℝ) ^ (ρ * (1 - ε) + diff / 2)) :=
          mul_le_mul_of_nonneg_left hsN_le2 hC₁
      _ = C₁ * K * (N : ℝ) ^ (ρ * (1 - ε) + diff / 2) := by ring
      _ ≤ C₁ * K * (N : ℝ) ^ (1 - ε - diff / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNge1 hexp_le) (by positivity)
  have hterm2 : C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ) ≤
      C₂ * K ^ (1 - δ) * (N : ℝ) ^ (1 - ε - diff / 2) := by
    have h1mδ_nn : 0 ≤ 1 - δ := by linarith
    have hsN_rpow : sN ^ (1 - δ) ≤ K ^ (1 - δ) * (N : ℝ) ^ ((ρ * (1 - ε) + diff / 2) * (1 - δ)) := by
      calc sN ^ (1 - δ)
          ≤ (K * (N : ℝ) ^ (ρ * (1 - ε) + diff / 2)) ^ (1 - δ) :=
            Real.rpow_le_rpow hsN_nn hsN_le2 h1mδ_nn
        _ = K ^ (1 - δ) * ((N : ℝ) ^ (ρ * (1 - ε) + diff / 2)) ^ (1 - δ) :=
            Real.mul_rpow hK_pos.le (Real.rpow_nonneg hNpos.le _)
        _ = K ^ (1 - δ) * (N : ℝ) ^ ((ρ * (1 - ε) + diff / 2) * (1 - δ)) := by
            rw [← Real.rpow_mul hNpos.le]
    have hexp_le2 : δ + (ρ * (1 - ε) + diff / 2) * (1 - δ) ≤ 1 - ε - diff / 2 := by
      have hrew : δ + (ρ * (1 - ε) + diff / 2) * (1 - δ) = η + (diff / 2) * (1 - δ) := by
        simp only [η]; ring
      have hmul : (diff / 2) * (1 - δ) ≤ diff / 2 := by nlinarith
      simp only [diff] at *; linarith
    calc C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ)
        ≤ C₂ * (N : ℝ) ^ δ * (K ^ (1 - δ) * (N : ℝ) ^ ((ρ * (1 - ε) + diff / 2) * (1 - δ))) :=
          mul_le_mul_of_nonneg_left hsN_rpow (by positivity)
      _ = C₂ * K ^ (1 - δ) * ((N : ℝ) ^ δ * (N : ℝ) ^ ((ρ * (1 - ε) + diff / 2) * (1 - δ))) := by ring
      _ = C₂ * K ^ (1 - δ) * (N : ℝ) ^ (δ + (ρ * (1 - ε) + diff / 2) * (1 - δ)) := by
          rw [← Real.rpow_add hNpos]
      _ ≤ C₂ * K ^ (1 - δ) * (N : ℝ) ^ (1 - ε - diff / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNge1 hexp_le2) (by positivity)
  have hN1mε_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - ε) := Real.one_le_rpow hNge1 h1mε_pos.le
  have hNsplit : (N : ℝ) ^ (1 - ε - diff / 2) = (N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (-(diff / 2)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hmain_lt : (C₁ * K + C₂ * K ^ (1 - δ)) * (N : ℝ) ^ (1 - ε - diff / 2) <
      (c / 2) * (N : ℝ) ^ (1 - ε) := by
    have hleA : C₁ * K + C₂ * K ^ (1 - δ) ≤ A := by simp only [A]; linarith
    have hmul : A * (N : ℝ) ^ (-(diff / 2)) < c / 2 := by
      have := mul_lt_mul_of_pos_left hsm1 hA_pos
      have hrew : A * (c / (2 * A)) = c / 2 := by field_simp [hA_pos.ne']
      linarith
    rw [hNsplit]
    have hstep : (C₁ * K + C₂ * K ^ (1 - δ)) * ((N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (-(diff / 2))) ≤
        A * ((N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (-(diff / 2))) :=
      mul_le_mul_of_nonneg_right hleA (by positivity)
    have hstep2 : A * ((N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (-(diff / 2))) =
        (A * (N : ℝ) ^ (-(diff / 2))) * (N : ℝ) ^ (1 - ε) := by ring
    have hstep3 : (A * (N : ℝ) ^ (-(diff / 2))) * (N : ℝ) ^ (1 - ε) <
        (c / 2) * (N : ℝ) ^ (1 - ε) :=
      mul_lt_mul_of_pos_right hmul (by linarith)
    linarith
  have htail_lt : 2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ) <
      (c / 2) * (N : ℝ) ^ (1 - ε) := by nlinarith
  linarith

end ThermalTruncation

end KrylovChaos
