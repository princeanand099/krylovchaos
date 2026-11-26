/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Basic Scales and Elementary Analytic Inequalities

Defines the inverse locality scale `κ = (2 (r - 1) J_site)⁻¹`, the high-temperature
threshold `β_wc = (4 e² r 6^r J_site)⁻¹`, and proves the elementary analytic and
combinatorial inequalities used across Sections 2–9 and Appendix A.
-/

namespace KrylovChaos

/-- Inverse locality scale `κ := (2 (r - 1) J_site)⁻¹` (Eq. 1.5). -/
noncomputable def invLocalityScale (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (2 * ((r : ℝ) - 1) * Jsite)

/-- High-temperature weak-clustering threshold `β_wc := (4 e² r 6^r J_site)⁻¹` (Eq. 1.19). -/
noncomputable def betaWC (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite)

/-- Positivity of the inverse locality scale `κ` for `r ≥ 2` and `J_site > 0`. -/
theorem invLocalityScale_pos {r : ℕ} {Jsite : ℝ} (hr : 2 ≤ r) (hJ : 0 < Jsite) :
    0 < invLocalityScale r Jsite := by
  unfold invLocalityScale
  have hr' : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
  positivity

/-- Positivity of `β_wc` for `r ≥ 2` and `J_site > 0`. -/
theorem betaWC_pos {r : ℕ} {Jsite : ℝ} (hr : 2 ≤ r) (hJ : 0 < Jsite) :
    0 < betaWC r Jsite := by
  unfold betaWC
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  positivity

/-- **Eq. (1.19)**: `β_wc < 2 κ` for every `r ≥ 2` and `J_site > 0`. -/
theorem betaWC_lt_two_kappa {r : ℕ} {Jsite : ℝ} (hr : 2 ≤ r) (hJ : 0 < Jsite) :
    betaWC r Jsite < 2 * invLocalityScale r Jsite := by
  unfold betaWC invLocalityScale
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
    linarith
  have h2k : 2 * (1 / (2 * ((r : ℝ) - 1) * Jsite)) = 1 / (((r : ℝ) - 1) * Jsite) := by
    field_simp
  rw [h2k]
  apply one_div_lt_one_div_of_lt (mul_pos hr1 hJ)
  have he : (1 : ℝ) < Real.exp 2 := by
    simpa using Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)
  have h6 : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
    have : (6 : ℝ) ^ 2 ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    linarith [show (6 : ℝ) ^ 2 = 36 by norm_num]
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : 4 * (r : ℝ) < 4 * Real.exp 2 * (r : ℝ) := by nlinarith
  have hcoeff : ((r : ℝ) - 1) < 4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r := by nlinarith
  exact mul_lt_mul_of_pos_right hcoeff hJ

/-- `β_wc ≤ (8 e² r J_site)⁻¹` (used in Proposition 6.4 and Theorem 1.3(c)). -/
theorem betaWC_le_cumulant_thresh {r : ℕ} {Jsite : ℝ} (hr : 2 ≤ r) (hJ : 0 < Jsite) :
    betaWC r Jsite ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) := by
  unfold betaWC
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  apply one_div_le_one_div_of_le (by positivity)
  have h6 : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
    have : (6 : ℝ) ^ 2 ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    linarith [show (6 : ℝ) ^ 2 = 36 by norm_num]
  have he : 0 < Real.exp 2 := Real.exp_pos 2
  nlinarith [mul_pos (mul_pos he hr0) hJ]

/-- Elementary inequality `e^u - 1 ≤ u e^u` for all `u ≥ 0`. -/
theorem exp_sub_one_le_mul_exp {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u - 1 ≤ u * Real.exp u := by
  have h := Real.add_one_le_exp (-u)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos u).le
  rw [show Real.exp (-u) * Real.exp u = 1 by rw [← Real.exp_add]; simp] at hmul
  linarith

/-- Elementary inequality `x ≤ (e θ)⁻¹ e^{θ x}` for all `x ≥ 0` and `θ > 0`. -/
theorem le_exp_div_e_mul {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 < θ) :
    x ≤ Real.exp (θ * x) / (Real.exp 1 * θ) := by
  have h := Real.add_one_le_exp (θ * x - 1)
  have h1 : θ * x ≤ Real.exp (θ * x) / Real.exp 1 := by
    rw [Real.exp_sub] at h
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h2 : θ * x * Real.exp 1 ≤ Real.exp (θ * x) := by
    rwa [le_div_iff₀ (Real.exp_pos 1)] at h1
  nlinarith

/-- Elementary inequality `2 / (e^u + e^{-u}) ≥ e^{-u}` for all `u ≥ 0`. -/
theorem sech_ge_exp_neg {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 2 / (Real.exp u + Real.exp (-u)) := by
  have hpos : 0 < Real.exp u + Real.exp (-u) := by positivity
  rw [le_div_iff₀ hpos]
  have hle : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hsq : Real.exp (-u) * Real.exp (-u) ≤ Real.exp (-u) * Real.exp u :=
    mul_le_mul_of_nonneg_left hle (Real.exp_pos (-u)).le
  linarith

/-- Elementary inequality `sinh x ≤ x * cosh x` for all `x ≥ 0`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  let f : ℝ → ℝ := fun t ↦
    t * ((Real.exp t + Real.exp (-t)) / 2) - (Real.exp t - Real.exp (-t)) / 2
  have hderiv : ∀ t : ℝ, HasDerivAt f (t * ((Real.exp t - Real.exp (-t)) / 2)) t := by
    intro t
    have hpos : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hneg : HasDerivAt (fun s ↦ Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have hcosh : HasDerivAt (fun s ↦ (Real.exp s + Real.exp (-s)) / 2)
        ((Real.exp t - Real.exp (-t)) / 2) t := by
      convert (hpos.fun_add hneg).div_const 2 using 1; ring
    have hsinh : HasDerivAt (fun s ↦ (Real.exp s - Real.exp (-s)) / 2)
        ((Real.exp t + Real.exp (-t)) / 2) t := by
      convert (hpos.fun_sub hneg).div_const 2 using 1; ring
    have hprod := (hasDerivAt_id t).fun_mul hcosh
    convert hprod.fun_sub hsinh using 1
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      rw [(hderiv t).deriv]
      have hge : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
      nlinarith
  have h0 : f 0 ≤ f x := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [f, Real.sinh_eq, Real.cosh_eq] at h0 ⊢
  simp only [zero_mul, neg_zero, sub_self, zero_div, sub_zero] at h0
  linarith

/-- Elementary inequality `tanh x ≤ x` for all `x ≥ 0` (used in Theorem 1.1(a)). -/
theorem tanh_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  exact sinh_le_mul_cosh hx

/-- Elementary factorial bound `k^(k-1) / k! ≤ e^k` for `k ≥ 1` (used in Lemma A.2). -/
theorem pow_pred_div_factorial_le_exp {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ (k - 1) / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsum : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg hk0 (k + 1)
    have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
    have hle := Finset.single_le_sum (f := fun i ↦ (k : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ ↦ by positivity) hmem
    exact le_trans hle h
  have hpow : (k : ℝ) ^ (k - 1) ≤ (k : ℝ) ^ k := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact pow_le_pow_right₀ hk1 (Nat.sub_le k 1)
  exact le_trans (div_le_div_of_nonneg_right hpow (by positivity)) hsum

/-- Catalan upper bound `(2*(m-1)).choose (m-1) / m ≤ 4^(m-1)` for `m ≥ 1` (used in Lemma A.1). -/
theorem catalan_le_four_pow {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.choose (2 * (m - 1)) (m - 1) : ℝ) / (m : ℝ)) ≤ (4 : ℝ) ^ (m - 1) := by
  have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hchoose : Nat.choose (2 * (m - 1)) (m - 1) ≤ 2 ^ (2 * (m - 1)) := by
    rw [← Nat.sum_range_choose]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hpow : (2 ^ (2 * (m - 1)) : ℝ) = (4 : ℝ) ^ (m - 1) := by
    rw [pow_mul]
    norm_num
  have hcast : (Nat.choose (2 * (m - 1)) (m - 1) : ℝ) ≤ (4 : ℝ) ^ (m - 1) := by
    rw [← hpow]
    exact_mod_cast hchoose
  calc (Nat.choose (2 * (m - 1)) (m - 1) : ℝ) / (m : ℝ)
      ≤ (Nat.choose (2 * (m - 1)) (m - 1) : ℝ) / 1 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one hm0
    _ = (Nat.choose (2 * (m - 1)) (m - 1) : ℝ) := div_one _
    _ ≤ (4 : ℝ) ^ (m - 1) := hcast

end KrylovChaos
