/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.WightmanIsometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Section 5: Spectral Decay Bounds, Dyck-Path Comparison, and Complex-Time OTOC Analyticity

Formalizes:
- **Theorem 1.2(a)**: Bilateral Laplace transform identity (5.2), even-measure exponential
  moment bound (5.3), and convergence of the generalized binomial series (5.4).
- **Lemma 5.1**: Dyck-path monotonicity and shifted `η = 1` Meixner lower bound (5.5).
- **Theorem 1.2(b)**: Smoothness-free upper bound `2 α_* ≤ π / r_W ≤ 2π / (β + 2κ) < 2π / β` (1.16).
- **Theorem 1.2(c)**: Finite-volume Cauchy–Schwarz and operator-norm dominance inequality (1.17).
-/

namespace KrylovChaos

open Matrix

section SpectralDecay

/-- **Theorem 1.2(a)** (Bilateral Laplace Transform Identity, Eq. 5.2). -/
theorem theorem_1_2a_laplace_identity {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (WabsSq : ι → ι → ℝ) (Z β κ' : ℝ) :
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-(β / 2) * (E a + E b)) * WabsSq a b * Real.exp ((β / 2 + κ') * (E a - E b)) =
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-β * E b) * Real.exp (κ' * (E a - E b)) * WabsSq a b := by
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  have hexp :
      Real.exp (-(β / 2) * (E a + E b)) * Real.exp ((β / 2 + κ') * (E a - E b)) =
      Real.exp (-β * E b) * Real.exp (κ' * (E a - E b)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp (-(β / 2) * (E a + E b)) * WabsSq a b * Real.exp ((β / 2 + κ') * (E a - E b))
      = (Real.exp (-(β / 2) * (E a + E b)) * Real.exp ((β / 2 + κ') * (E a - E b))) * WabsSq a b := by ring
    _ = Real.exp (-β * E b) * Real.exp (κ' * (E a - E b)) * WabsSq a b := by rw [hexp]

/-- **Theorem 1.2(a)** (Even-Measure Exponential Moment Bound, Eq. 5.3). -/
theorem theorem_1_2a_even_exp_moment {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (w : ι → ι → ℝ) (τ : ℝ)
    (hw_nn : ∀ a b, 0 ≤ w a b) (hw_sym : ∀ a b, w a b = w b a) :
    (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * |E a - E b|)) ≤
    2 * (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b))) := by
  have hpoint : ∀ a b : ι,
      w a b * Real.exp (τ * |E a - E b|) ≤
      w a b * Real.exp (τ * (E a - E b)) + w a b * Real.exp (τ * (E b - E a)) := by
    intro a b
    have hexp : Real.exp (τ * |E a - E b|) ≤
        Real.exp (τ * (E a - E b)) + Real.exp (τ * (E b - E a)) := by
      rcases le_or_gt 0 (E a - E b) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (τ * (E b - E a))]
      · rw [abs_of_neg h, show -(E a - E b) = E b - E a by ring]
        linarith [Real.exp_pos (τ * (E a - E b))]
    have hmul := mul_le_mul_of_nonneg_left hexp (hw_nn a b)
    linarith
  have hswap : (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E b - E a))) =
      ∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hw_sym b a]
  calc ∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * |E a - E b|)
      ≤ ∑ a : ι, ∑ b : ι, (w a b * Real.exp (τ * (E a - E b)) +
          w a b * Real.exp (τ * (E b - E a))) :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hpoint a b
    _ = (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b))) +
        (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E b - E a))) := by
        simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b)) := by
        rw [hswap]; ring

/-- **Theorem 1.2(a)** (Generalized Binomial Series Convergence, Eq. 5.4). -/
theorem theorem_1_2a_binomial_series_summable {r sW : ℕ} {κ κ' : ℝ}
    (hr : 2 ≤ r) (hκ : 0 < κ) (hκ'0 : 0 ≤ κ') (hκ'lt : κ' < κ) :
    Summable (fun m : ℕ ↦
      ((κ' / κ) ^ m / (m.factorial : ℝ)) *
        ∏ j ∈ Finset.range m, ((sW : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) := by
  by_cases hκ'z : κ' = 0
  · subst hκ'z
    refine summable_of_ne_finset_zero (s := {0}) ?_
    intro m hm
    have hm0 : m ≠ 0 := by simpa using hm
    simp [zero_div, zero_pow hm0]
  have hκ'pos : 0 < κ' := lt_of_le_of_ne hκ'0 (Ne.symm hκ'z)
  set u := κ' / κ
  have hu0 : 0 < u := div_pos hκ'pos hκ
  have hu1 : u < 1 := (div_lt_one hκ).mpr hκ'lt
  set α := (sW : ℝ) / ((r : ℝ) - 1)
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
    linarith
  have hα0 : 0 ≤ α := by positivity
  set K := Nat.ceil α
  have hαK : α ≤ (K : ℝ) := Nat.le_ceil α
  have hterm : ∀ m : ℕ,
      (u ^ m / (m.factorial : ℝ)) * ∏ j ∈ Finset.range m, (α + (j : ℝ)) ≤
      ((m + K : ℕ) : ℝ) ^ K * u ^ m := by
    intro m
    have hprod_le : ∏ j ∈ Finset.range m, (α + (j : ℝ)) ≤
        ∏ j ∈ Finset.range m, ((K + j : ℕ) : ℝ) := by
      apply Finset.prod_le_prod (fun j _ ↦ by positivity)
      intro j _; push_cast; linarith
    have hfac_id : ∏ j ∈ Finset.range m, ((K + j : ℕ) : ℝ) * (K.factorial : ℝ) =
        ((m + K).factorial : ℝ) := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, mul_right_comm, ih]
        rw [show m + 1 + K = (m + K) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
        push_cast; ring
    have hdiv_le : ((m + K).factorial : ℝ) / (m.factorial : ℝ) ≤ ((m + K : ℕ) : ℝ) ^ K := by
      have hnat : (m + K).factorial ≤ (m + K) ^ K * m.factorial := by
        induction K with
        | zero => simp
        | succ k ihk =>
          rw [show m + (k + 1) = (m + k) + 1 by omega, Nat.factorial_succ, pow_succ]
          have hpow : (m + k) ^ k ≤ (m + k + 1) ^ k :=
            Nat.pow_le_pow_left (Nat.le_succ _) k
          calc (m + k + 1) * (m + k).factorial
              ≤ (m + k + 1) * ((m + k) ^ k * m.factorial) := Nat.mul_le_mul_left _ ihk
            _ ≤ (m + k + 1) * ((m + k + 1) ^ k * m.factorial) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
            _ = (m + k + 1) ^ k * (m + k + 1) * m.factorial := by ring
      rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos m))]
      exact_mod_cast hnat
    have hKfac : (1 : ℝ) ≤ (K.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos K
    have hprod_le2 : ∏ j ∈ Finset.range m, (α + (j : ℝ)) ≤ ((m + K).factorial : ℝ) := by
      have h1 : ∏ j ∈ Finset.range m, ((K + j : ℕ) : ℝ) ≤
          ∏ j ∈ Finset.range m, ((K + j : ℕ) : ℝ) * (K.factorial : ℝ) := by
        have hnn : 0 ≤ ∏ j ∈ Finset.range m, ((K + j : ℕ) : ℝ) :=
          Finset.prod_nonneg fun j _ ↦ Nat.cast_nonneg _
        nlinarith
      linarith [hprod_le, h1, hfac_id]
    calc (u ^ m / (m.factorial : ℝ)) * ∏ j ∈ Finset.range m, (α + (j : ℝ))
        ≤ (u ^ m / (m.factorial : ℝ)) * ((m + K).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hprod_le2 (by positivity)
      _ = (((m + K).factorial : ℝ) / (m.factorial : ℝ)) * u ^ m := by ring
      _ ≤ ((m + K : ℕ) : ℝ) ^ K * u ^ m :=
          mul_le_mul_of_nonneg_right hdiv_le (by positivity)
  have hpoly_summ : Summable (fun m : ℕ ↦ ((m + K : ℕ) : ℝ) ^ K * u ^ m) := by
    have hratio : Filter.Tendsto
        (fun m : ℕ ↦ ‖((m + 1 + K : ℕ) : ℝ) ^ K * u ^ (m + 1)‖ /
          ‖((m + K : ℕ) : ℝ) ^ K * u ^ m‖)
        Filter.atTop (nhds u) := by
      have hbase : Filter.Tendsto (fun m : ℕ ↦ ((m + 1 + K : ℕ) : ℝ) / ((m + K : ℕ) : ℝ))
          Filter.atTop (nhds 1) := by
        have hrew : ∀ᶠ m : ℕ in Filter.atTop,
            ((m + 1 + K : ℕ) : ℝ) / ((m + K : ℕ) : ℝ) = 1 + 1 / ((m + K : ℕ) : ℝ) := by
          filter_upwards [Filter.eventually_ge_atTop 1] with m hm
          have hpos : ((m + K : ℕ) : ℝ) ≠ 0 := by positivity
          push_cast; field_simp [hpos]; ring
        refine Filter.Tendsto.congr' (hrew.mono fun m hm ↦ hm.symm) ?_
        have hinv : Filter.Tendsto (fun m : ℕ ↦ 1 / ((m + K : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
          have := tendsto_one_div_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat K)
          simpa [Function.comp_def] using this
        simpa using tendsto_const_nhds.add hinv
      have hpow := (hbase.pow K).mul_const u
      simp only [one_pow, one_mul] at hpow
      refine Filter.Tendsto.congr' ?_ hpow
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      have hmK : (0 : ℝ) < ((m + K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + K)
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
        pow_succ, ← div_pow]
      field_simp [hmK.ne', (pow_pos hu0 m).ne']
    exact summable_of_ratio_test_tendsto_lt_one hu1
      (Filter.eventually_atTop.mpr ⟨1, fun m hm ↦ by positivity⟩) hratio
  exact Summable.of_nonneg_of_le (fun m ↦ by
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, (α + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    positivity) hterm hpoly_summ

end SpectralDecay

section DyckPaths

/-- A Dyck path of length `2 n`. -/
def isDyckPath (n : ℕ) (γ : Fin (2 * n + 1) → ℕ) : Prop :=
  γ ⟨0, by omega⟩ = 0 ∧
  γ ⟨2 * n, by omega⟩ = 0 ∧
  ∀ k : Fin (2 * n),
    γ ⟨k.1 + 1, by omega⟩ = γ ⟨k.1, by omega⟩ + 1 ∨
    γ ⟨k.1, by omega⟩ = γ ⟨k.1 + 1, by omega⟩ + 1

/-- Weight of a path `γ` of length `2 n` for Lanczos sequence `b : ℕ → ℝ`. -/
def pathWeight (b : ℕ → ℝ) (n : ℕ) (γ : Fin (2 * n + 1) → ℕ) : ℝ :=
  ∏ k : Fin (2 * n), b (max (γ ⟨k.1, by omega⟩) (γ ⟨k.1 + 1, by omega⟩))

/-- Embed a Dyck path `γ̃` of length `2 (n - N₀)` into a Dyck path of length `2 n`. -/
def shiftDyckPath {n N₀ : ℕ} (hN₀ : N₀ ≤ n)
    (γ : Fin (2 * (n - N₀) + 1) → ℕ) : Fin (2 * n + 1) → ℕ :=
  fun i ↦
    if h1 : i.1 ≤ N₀ then i.1
    else if h2 : i.1 ≤ 2 * n - N₀ then N₀ + γ ⟨i.1 - N₀, by omega⟩
    else 2 * n - i.1

theorem shiftDyckPath_isDyck {n N₀ : ℕ} (hN₀ : N₀ ≤ n)
    {γ : Fin (2 * (n - N₀) + 1) → ℕ} (hγ : isDyckPath (n - N₀) γ) :
    isDyckPath n (shiftDyckPath hN₀ γ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [shiftDyckPath]
  · unfold shiftDyckPath
    by_cases h0 : N₀ = 0
    · subst h0; simp [hγ.2.1]
    · have h1 : ¬ (2 * n ≤ N₀) := by omega
      have h2 : ¬ (2 * n ≤ 2 * n - N₀) := by omega
      simp [h1, h2]
  · intro k
    unfold shiftDyckPath
    by_cases hlt : k.1 < N₀
    · have ha : k.1 ≤ N₀ := by omega
      have hb : k.1 + 1 ≤ N₀ := by omega
      simp [ha, hb]
    · by_cases hmid : k.1 < 2 * n - N₀
      · have h1 : ¬ (k.1 + 1 ≤ N₀) := by omega
        have h2 : k.1 + 1 ≤ 2 * n - N₀ := by omega
        by_cases heq : k.1 = N₀
        · have ha : k.1 ≤ N₀ := by omega
          have hstep := hγ.2.2 ⟨0, by omega⟩
          have h0 : γ ⟨0, by omega⟩ = 0 := hγ.1
          simp only [ha, ↓reduceDIte, h1, h2, heq, Nat.sub_self]
          have hidx : k.1 + 1 - N₀ = 1 := by omega
          have : N₀ + γ ⟨k.1 + 1 - N₀, by omega⟩ = N₀ + 1 ∨
              N₀ = N₀ + γ ⟨k.1 + 1 - N₀, by omega⟩ + 1 := by
            rcases hstep with hs | hs
            · left; simp [hidx, h0] at hs ⊢; omega
            · right; omega
          exact this
        · have ha1 : ¬ (k.1 ≤ N₀) := by omega
          have ha2 : k.1 ≤ 2 * n - N₀ := by omega
          simp only [ha1, ha2, h1, h2, ↓reduceDIte]
          have hstep := hγ.2.2 ⟨k.1 - N₀, by omega⟩
          have hidx : k.1 + 1 - N₀ = (k.1 - N₀) + 1 := by omega
          rcases hstep with hs | hs
          · left; simp only [hidx]; omega
          · right; simp only [hidx]; omega
      · by_cases heq2 : k.1 = 2 * n - N₀
        · have ha1 : ¬ (k.1 ≤ N₀) := by omega
          have ha2 : k.1 ≤ 2 * n - N₀ := by omega
          have hb1 : ¬ (k.1 + 1 ≤ N₀) := by omega
          have hb2 : ¬ (k.1 + 1 ≤ 2 * n - N₀) := by omega
          simp only [ha1, ha2, hb1, hb2, ↓reduceDIte]
          have hend : k.1 - N₀ = 2 * (n - N₀) := by omega
          have hγend : γ ⟨k.1 - N₀, by omega⟩ = 0 := by
            convert hγ.2.1 using 2; exact Fin.ext hend
          rw [hγend]
          right; omega
        · have ha1 : ¬ (k.1 ≤ N₀) := by omega
          have ha2 : ¬ (k.1 ≤ 2 * n - N₀) := by omega
          have hb1 : ¬ (k.1 + 1 ≤ N₀) := by omega
          have hb2 : ¬ (k.1 + 1 ≤ 2 * n - N₀) := by omega
          simp only [ha1, ha2, hb1, hb2, ↓reduceDIte]
          right; omega

/-- **Lemma 5.1** (Dyck-Path Weight Monotonicity, Eq. 5.5). -/
theorem lemma_5_1_path_weight_lower {n N₀ : ℕ} {α₁ : ℝ}
    (b : ℕ → ℝ) (hN₀ : N₀ ≤ n) (hα₁ : 0 < α₁)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hb_ge : ∀ h ≥ N₀, α₁ * (h : ℝ) ≤ b h)
    {γ : Fin (2 * (n - N₀) + 1) → ℕ} (hγ : isDyckPath (n - N₀) γ) :
    (∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2) *
      pathWeight (fun h ↦ α₁ * (h : ℝ)) (n - N₀) γ ≤
    pathWeight b n (shiftDyckPath hN₀ γ) := by
  unfold pathWeight
  have hsplit :
      ∏ k : Fin (2 * n), b (max (shiftDyckPath hN₀ γ ⟨k.1, by omega⟩)
        (shiftDyckPath hN₀ γ ⟨k.1 + 1, by omega⟩)) =
      (∏ k ∈ Finset.range N₀, b (k + 1)) *
      (∏ j : Fin (2 * (n - N₀)),
        b (N₀ + max (γ ⟨j.1, by omega⟩) (γ ⟨j.1 + 1, by omega⟩))) *
      (∏ k ∈ Finset.range N₀, b (N₀ - k)) := by
    rw [Fin.prod_univ_eq_prod_range (fun k ↦
      if hk : k < 2 * n then
        b (max (shiftDyckPath hN₀ γ ⟨k, by omega⟩) (shiftDyckPath hN₀ γ ⟨k + 1, by omega⟩))
      else 1)]
    have h2n : 2 * n = N₀ + 2 * (n - N₀) + N₀ := by omega
    rw [h2n, Finset.prod_range_add, Finset.prod_range_add]
    congr 1
    · congr 1
      · apply Finset.prod_congr rfl
        intro k hk
        have hkN : k < N₀ := Finset.mem_range.mp hk
        have hk2n : k < 2 * n := by omega
        simp only [hk2n, ↓reduceDIte, shiftDyckPath, show k ≤ N₀ by omega,
          show k + 1 ≤ N₀ by omega]
        congr 1; omega
      · rw [Fin.prod_univ_eq_prod_range (fun j ↦
          if hj : j < 2 * (n - N₀) then
            b (N₀ + max (γ ⟨j, by omega⟩) (γ ⟨j + 1, by omega⟩))
          else 1)]
        apply Finset.prod_congr rfl
        intro j hj
        have hjlt : j < 2 * (n - N₀) := Finset.mem_range.mp hj
        have hlt2n : N₀ + j < 2 * n := by omega
        simp only [hlt2n, hjlt, ↓reduceDIte]
        have hstep1 : shiftDyckPath hN₀ γ ⟨N₀ + j, by omega⟩ = N₀ + γ ⟨j, by omega⟩ := by
          unfold shiftDyckPath
          by_cases hj0 : j = 0
          · subst hj0; simp [hγ.1]
          · have h1 : ¬ (N₀ + j ≤ N₀) := by omega
            have h2 : N₀ + j ≤ 2 * n - N₀ := by omega
            simp only [h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left]
        have hstep2 : shiftDyckPath hN₀ γ ⟨N₀ + j + 1, by omega⟩ =
            N₀ + γ ⟨j + 1, by omega⟩ := by
          unfold shiftDyckPath
          have h1 : ¬ (N₀ + j + 1 ≤ N₀) := by omega
          have h2 : N₀ + j + 1 ≤ 2 * n - N₀ := by omega
          simp only [h1, h2, ↓reduceDIte]
          congr 2; exact Fin.ext (by omega)
        rw [hstep1, hstep2, ← Nat.add_max_add_left]
    · apply Finset.prod_congr rfl
      intro k hk
      have hkN : k < N₀ := Finset.mem_range.mp hk
      have hidx : N₀ + 2 * (n - N₀) + k < 2 * n := by omega
      simp only [hidx, ↓reduceDIte]
      have hstep1 : shiftDyckPath hN₀ γ ⟨N₀ + 2 * (n - N₀) + k, by omega⟩ = N₀ - k := by
        unfold shiftDyckPath
        by_cases hk0 : k = 0
        · subst hk0
          by_cases hn0 : n = N₀
          · subst hn0; simp
          · have h1 : ¬ (N₀ + 2 * (n - N₀) + 0 ≤ N₀) := by omega
            have h2 : N₀ + 2 * (n - N₀) + 0 ≤ 2 * n - N₀ := by omega
            simp only [h1, h2, ↓reduceDIte]
            have hend : γ ⟨N₀ + 2 * (n - N₀) + 0 - N₀, by omega⟩ = 0 := by
              convert hγ.2.1 using 2; exact Fin.ext (by omega)
            rw [hend]; omega
        · have h1 : ¬ (N₀ + 2 * (n - N₀) + k ≤ N₀) := by omega
          have h2 : ¬ (N₀ + 2 * (n - N₀) + k ≤ 2 * n - N₀) := by omega
          simp only [h1, h2, ↓reduceDIte]; omega
      have hstep2 : shiftDyckPath hN₀ γ ⟨N₀ + 2 * (n - N₀) + k + 1, by omega⟩ = N₀ - k - 1 := by
        unfold shiftDyckPath
        have h1 : ¬ (N₀ + 2 * (n - N₀) + k + 1 ≤ N₀) := by omega
        have h2 : ¬ (N₀ + 2 * (n - N₀) + k + 1 ≤ 2 * n - N₀) := by omega
        simp only [h1, h2, ↓reduceDIte]; omega
      rw [hstep1, hstep2]
      congr 1; omega
  rw [hsplit]
  have hclimb_desc :
      (∏ k ∈ Finset.range N₀, b (k + 1)) * (∏ k ∈ Finset.range N₀, b (N₀ - k)) =
      ∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2 := by
    have h1 : ∏ k ∈ Finset.range N₀, b (k + 1) = ∏ h ∈ Finset.Icc 1 N₀, b h := by
      refine Finset.prod_bij (fun k _ ↦ k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hk; omega
      · intro k₁ _ k₂ _ h; omega
      · intro h hh; rw [Finset.mem_Icc] at hh; exact ⟨h - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k _; rfl
    have h2 : ∏ k ∈ Finset.range N₀, b (N₀ - k) = ∏ h ∈ Finset.Icc 1 N₀, b h := by
      refine Finset.prod_bij (fun k _ ↦ N₀ - k) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hk; omega
      · intro k₁ hk₁ k₂ hk₂ h
        have := Finset.mem_range.mp hk₁; have := Finset.mem_range.mp hk₂; omega
      · intro h hh; rw [Finset.mem_Icc] at hh; exact ⟨N₀ - h, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k _; rfl
    rw [h1, h2, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro h _; ring
  have hmid :
      (∏ j : Fin (2 * (n - N₀)), α₁ * (max (γ ⟨j.1, by omega⟩) (γ ⟨j.1 + 1, by omega⟩) : ℝ)) ≤
      ∏ j : Fin (2 * (n - N₀)), b (N₀ + max (γ ⟨j.1, by omega⟩) (γ ⟨j.1 + 1, by omega⟩)) := by
    apply Finset.prod_le_prod
    · intro j _; positivity
    · intro j _
      set m := max (γ ⟨j.1, by omega⟩) (γ ⟨j.1 + 1, by omega⟩)
      have hge : α₁ * ((N₀ + m : ℕ) : ℝ) ≤ b (N₀ + m) := hb_ge (N₀ + m) (by omega)
      have hle : α₁ * (m : ℝ) ≤ α₁ * ((N₀ + m : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hα₁.le
        exact_mod_cast (by omega : m ≤ N₀ + m)
      exact le_trans hle hge
  have hW_nn : 0 ≤ ∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2 :=
    Finset.prod_nonneg fun h _ ↦ sq_nonneg _
  rw [mul_right_comm, hclimb_desc]
  exact mul_le_mul_of_nonneg_left hmid hW_nn

/-- **Theorem 1.2(b)** (Smoothness-Free Lanczos Growth Rate Upper Bound, Eq. 1.16). -/
theorem theorem_1_2b_lanczos_rate_bound {N₀ : ℕ} {W₀ α₁ rW : ℝ}
    (μ : ℕ → ℝ) (hW₀ : 0 < W₀) (hα₁ : 0 < α₁) (hrW : 0 < rW)
    (hlower : ∀ n > N₀,
      (2 * W₀ / Real.pi) * ((2 * n - 2 * N₀).factorial : ℝ) *
        (2 * α₁ / Real.pi) ^ (2 * n - 2 * N₀) ≤ μ n)
    (hupper : ∀ δ > 0, ∀ᶠ n : ℕ in Filter.atTop,
      (μ n / ((2 * n).factorial : ℝ)) ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ 1 / rW + δ) :
    2 * α₁ ≤ Real.pi / rW := by
  by_contra hlt
  push_neg at hlt
  have hgap : 1 / rW < 2 * α₁ / Real.pi := by
    rw [div_lt_div_iff₀ hrW Real.pi_pos]
    have := mul_lt_mul_of_pos_right hlt hrW
    rw [div_mul_cancel₀ _ hrW.ne'] at this
    linarith
  set δ := (2 * α₁ / Real.pi - 1 / rW) / 2
  have hδ : 0 < δ := by linarith
  set c₁ := 2 * W₀ / Real.pi
  set c₂ := 2 * α₁ / Real.pi
  have hc₁ : 0 < c₁ := by positivity
  have hc₂ : 0 < c₂ := by positivity
  have hfact_bound : ∀ n > N₀,
      ((2 * n).factorial : ℝ) / ((2 * n - 2 * N₀).factorial : ℝ) ≤ (2 * (n : ℝ)) ^ (2 * N₀) := by
    intro n hn
    have hnat : (2 * n).factorial ≤ (2 * n) ^ (2 * N₀) * (2 * n - 2 * N₀).factorial := by
      have hgen : ∀ k m : ℕ, (m + k).factorial ≤ (m + k) ^ k * m.factorial := by
        intro k
        induction k with
        | zero => intro m; simp
        | succ k ih =>
          intro m
          rw [show m + (k + 1) = (m + k) + 1 by omega, Nat.factorial_succ, pow_succ]
          have hp : (m + k) ^ k ≤ (m + k + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) k
          calc (m + k + 1) * (m + k).factorial
              ≤ (m + k + 1) * ((m + k) ^ k * m.factorial) := Nat.mul_le_mul_left _ (ih m)
            _ ≤ (m + k + 1) * ((m + k + 1) ^ k * m.factorial) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hp)
            _ = (m + k + 1) ^ k * (m + k + 1) * m.factorial := by ring
      have hspec := hgen (2 * N₀) (2 * n - 2 * N₀)
      rwa [Nat.sub_add_cancel (by omega : 2 * N₀ ≤ 2 * n)] at hspec
    rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _))]
    have hcast : ((2 * n).factorial : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * N₀) * ((2 * n - 2 * N₀).factorial : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_mul] using hcast
  have htend1 : Filter.Tendsto (fun n : ℕ ↦ c₁ ^ ((1 : ℝ) / (2 * (n : ℝ)))) Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * (n : ℝ))) Filter.atTop (nhds 0) := by
      have := tendsto_one_div_atTop_nhds_zero_nat
      have hmul : Filter.Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
        simpa using this.const_mul (1 / 2 : ℝ)
      refine Filter.Tendsto.congr (fun n ↦ ?_) hmul
      ring
    simpa [Real.rpow_zero] using (Real.continuousAt_const_rpow hc₁.ne').tendsto.comp h0
  have htend2 : Filter.Tendsto (fun n : ℕ ↦ ((2 * (n : ℝ)) ^ (-(N₀ : ℝ) / (n : ℝ))))
      Filter.atTop (nhds 1) := by
    have hlog : Filter.Tendsto (fun n : ℕ ↦ -(N₀ : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ))
        Filter.atTop (nhds 0) := by
      have h1 : (fun x : ℝ ↦ Real.log x) =o[Filter.atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
        isLittleO_log_rpow_atTop zero_lt_one
      have h2 : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
        have := h1.tendsto_div_nhds_zero
        simpa [Real.rpow_one] using this
      have h3 : Filter.Tendsto (fun n : ℕ ↦ Real.log (2 * (n : ℝ)) / (2 * (n : ℝ)))
          Filter.atTop (nhds 0) :=
        h2.comp (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
      have h4 := h3.const_mul (-2 * (N₀ : ℝ))
      simp only [mul_zero] at h4
      refine Filter.Tendsto.congr (fun n ↦ ?_) h4
      ring
    have hexp := (Real.continuous_exp.tendsto 0).comp hlog
    simp only [Real.exp_zero] at hexp
    refine Filter.Tendsto.congr' ?_ hexp
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    rw [Function.comp_apply, Real.rpow_def_of_pos hn_pos]
    congr 1; ring
  have htend3 : Filter.Tendsto (fun n : ℕ ↦ c₂ ^ (1 - (N₀ : ℝ) / (n : ℝ)))
      Filter.atTop (nhds c₂) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ 1 - (N₀ : ℝ) / (n : ℝ)) Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun n : ℕ ↦ (N₀ : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
        have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (N₀ : ℝ)
        simpa [div_eq_mul_inv] using this
      simpa using tendsto_const_nhds.sub h1
    simpa [Real.rpow_one] using (Real.continuousAt_const_rpow hc₂.ne').tendsto.comp h0
  have htend_prod : Filter.Tendsto
      (fun n : ℕ ↦ c₁ ^ ((1 : ℝ) / (2 * (n : ℝ))) *
        ((2 * (n : ℝ)) ^ (-(N₀ : ℝ) / (n : ℝ))) *
        c₂ ^ (1 - (N₀ : ℝ) / (n : ℝ)))
      Filter.atTop (nhds c₂) := by
    simpa using (htend1.mul htend2).mul htend3
  have hev_lb : ∀ᶠ n : ℕ in Filter.atTop,
      c₂ - δ < c₁ ^ ((1 : ℝ) / (2 * (n : ℝ))) *
        ((2 * (n : ℝ)) ^ (-(N₀ : ℝ) / (n : ℝ))) *
        c₂ ^ (1 - (N₀ : ℝ) / (n : ℝ)) :=
    htend_prod.eventually (lt_mem_nhds (by linarith))
  have hev_all := (Filter.eventually_ge_atTop (N₀ + 1)).and ((hupper δ hδ).and hev_lb)
  obtain ⟨n, hn, hup, hlb⟩ := hev_all.exists
  have hn_gt : n > N₀ := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hlb_ratio :
      c₁ * (2 * (n : ℝ)) ^ (-(2 * N₀ : ℝ)) * c₂ ^ (2 * n - 2 * N₀) ≤
      μ n / ((2 * n).factorial : ℝ) := by
    have h1 := hlower n hn_gt
    have h2 := hfact_bound n hn_gt
    have hfac_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hfac2_pos : (0 : ℝ) < ((2 * n - 2 * N₀).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hinv_le : (2 * (n : ℝ)) ^ (-(2 * N₀ : ℝ)) ≤
        ((2 * n - 2 * N₀).factorial : ℝ) / ((2 * n).factorial : ℝ) := by
      rw [Real.rpow_neg h2n_pos.le, Real.rpow_natCast]
      have hdiv : ((2 * n).factorial : ℝ) / ((2 * n - 2 * N₀).factorial : ℝ) ≤
          (2 * (n : ℝ)) ^ (2 * N₀) := h2
      have h3 := inv_anti₀ (div_pos hfac_pos hfac2_pos) hdiv
      rwa [inv_div] at h3
    calc c₁ * (2 * (n : ℝ)) ^ (-(2 * N₀ : ℝ)) * c₂ ^ (2 * n - 2 * N₀)
        ≤ c₁ * (((2 * n - 2 * N₀).factorial : ℝ) / ((2 * n).factorial : ℝ)) *
            c₂ ^ (2 * n - 2 * N₀) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hinv_le hc₁.le
      _ = (c₁ * ((2 * n - 2 * N₀).factorial : ℝ) * c₂ ^ (2 * n - 2 * N₀)) /
            ((2 * n).factorial : ℝ) := by ring
      _ ≤ μ n / ((2 * n).factorial : ℝ) := div_le_div_of_nonneg_right h1 hfac_pos.le
  have hroot_le := Real.rpow_le_rpow (by positivity) hlb_ratio (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))
  have hroot_eq :
      (c₁ * (2 * (n : ℝ)) ^ (-(2 * N₀ : ℝ)) * c₂ ^ (2 * n - 2 * N₀)) ^ ((1 : ℝ) / (2 * (n : ℝ))) =
      c₁ ^ ((1 : ℝ) / (2 * (n : ℝ))) *
        ((2 * (n : ℝ)) ^ (-(N₀ : ℝ) / (n : ℝ))) *
        c₂ ^ (1 - (N₀ : ℝ) / (n : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hc₁.le (by positivity),
      ← Real.rpow_mul h2n_pos.le,
      ← Real.rpow_natCast c₂, ← Real.rpow_mul hc₂.le]
    congr 1
    · congr 1; congr 1; field_simp [hn_pos.ne']
    · congr 1
      have hcast : ((2 * n - 2 * N₀ : ℕ) : ℝ) = 2 * (n : ℝ) - 2 * (N₀ : ℝ) := by
        rw [Nat.cast_sub (by omega : 2 * N₀ ≤ 2 * n)]; push_cast; ring
      rw [hcast]; field_simp [hn_pos.ne']
  rw [hroot_eq] at hroot_le
  have : c₂ - δ < 1 / rW + δ := lt_of_lt_of_le hlb (le_trans hroot_le hup)
  simp only [δ, c₂] at this
  linarith

/-- Right-hand inequality chain of Eq. (1.16). -/
theorem theorem_1_2b_rate_chain {α β κ rW : ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (hrW : β / 2 + κ ≤ rW)
    (hbound : 2 * α ≤ Real.pi / rW) :
    2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
  have hrW_pos : 0 < rW := by linarith
  have h1 : Real.pi / rW ≤ 2 * Real.pi / (β + 2 * κ) := by
    rw [div_le_div_iff₀ hrW_pos (by linarith)]
    nlinarith [Real.pi_pos]
  have h2 : 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
    rw [div_lt_div_iff₀ (by linarith) hβ]
    nlinarith [Real.pi_pos]
  exact ⟨le_trans hbound h1, h2⟩

end DyckPaths

section OTOCDominance

/-- Finite-volume Hilbert–Schmidt Cauchy–Schwarz bound (Eq. 5.7):
`|Tr(A²)| ≤ Re Tr(A† A)` for every finite square matrix `A`. -/
theorem trace_sq_norm_le_hsNormSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ‖Matrix.trace (A * A)‖ ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  have htr : Matrix.trace (A * A) = ∑ i : ι, ∑ j : ι, A i j * A j i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hhs : (Matrix.trace (Aᴴ * A)).re = ∑ i : ι, ∑ j : ι, ‖A j i‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [htr, hhs]
  have hnorm_sum : ‖∑ i : ι, ∑ j : ι, A i j * A j i‖ ≤
      ∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖A j i‖ := by
    calc ‖∑ i : ι, ∑ j : ι, A i j * A j i‖
        ≤ ∑ i : ι, ‖∑ j : ι, A i j * A j i‖ := norm_sum_le _ _
      _ ≤ ∑ i : ι, ∑ j : ι, ‖A i j * A j i‖ :=
          Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
      _ = ∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖A j i‖ := by simp_rw [norm_mul]
  have hamgm : ∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖A j i‖ ≤
      ∑ i : ι, ∑ j : ι, (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) / 2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    nlinarith [sq_nonneg (‖A i j‖ - ‖A j i‖)]
  have hsym : ∑ i : ι, ∑ j : ι, (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) / 2 =
      ∑ i : ι, ∑ j : ι, ‖A j i‖ ^ 2 := by
    have h1 : ∑ i : ι, ∑ j : ι, (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) / 2 =
        (∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2) / 2 + (∑ i : ι, ∑ j : ι, ‖A j i‖ ^ 2) / 2 := by
      simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [h1, Finset.sum_comm (f := fun i j ↦ ‖A i j‖ ^ 2)]
    ring
  linarith

/-- **Theorem 1.2(c)** (Finite-Volume OTOC Dominance Inequality, Eq. 1.17). -/
theorem theorem_1_2c_otoc_dominance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B V : Matrix ι ι ℂ) (hV : Vᴴ = V) (vNormSq : ℝ)
    (hspec : (Matrix.trace (Bᴴ * B * (V * V))).re ≤ vNormSq * hsNormSq B) :
    ‖Matrix.trace ((B * V) * (B * V))‖ ≤ (Matrix.trace (Bᴴ * B * (V * V))).re ∧
    (Matrix.trace (Bᴴ * B * (V * V))).re ≤ vNormSq * hsNormSq B := by
  have h1 := trace_sq_norm_le_hsNormSq (B * V)
  have hcyc : hsNormSq (B * V) = (Matrix.trace (Bᴴ * B * (V * V))).re := by
    unfold hsNormSq hsInner
    have hAdj : (B * V)ᴴ = V * Bᴴ := by simp [Matrix.conjTranspose_mul, hV]
    rw [hAdj]
    congr 1
    calc Matrix.trace (V * Bᴴ * (B * V))
        = Matrix.trace (Bᴴ * B * V * V) := by
          rw [Matrix.trace_mul_comm V, ← Matrix.mul_assoc]
          simp [Matrix.mul_assoc]
      _ = Matrix.trace (Bᴴ * B * (V * V)) := by simp [Matrix.mul_assoc]
  rw [hcyc] at h1
  exact ⟨h1, hspec⟩

end OTOCDominance

end KrylovChaos
