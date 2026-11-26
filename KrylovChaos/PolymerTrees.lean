/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Appendix A & High-Temperature Cluster Expansion Bounds

Formalizes:
- **Lemma A.1**: Rooted plane-tree polymer sum bound `η₀ (4 r η₀)^{m-1}` (Eq. A.1)
  and its geometric convergence for `β ≤ β_wc` (used in Lemma 7.2).
- **Lemma A.2**: Cayley spanning-tree root-reversal estimate `(e r J_site)^k` (Eq. A.2).
- **Lemma A.3**: Multi-type unordered spanning-tree polymer induction `S_h(E) ≤ μ(E) e^{c₀ |E|}`
  and pinned polymer sum bound `≤ Φ` (Eqs. A.3–A.4).
- **Lemma 6.3 & Lemma 7.2**: Exact Kotecký–Preiss pinning verifications for the trace cumulant
  expansion and the depolarized 2-design cluster expansion.
-/

namespace KrylovChaos

section AppendixA

/-- **Lemma A.1** (Rooted Plane-Tree Polymer Sum, Eq. A.1). -/
theorem lemma_A_1_plane_tree_polymer_sum {m r : ℕ} {η₀ polySum : ℝ}
    (hm : 1 ≤ m) (hη : 0 ≤ η₀)
    (htree : polySum ≤ ((Nat.choose (2 * (m - 1)) (m - 1) : ℝ) / (m : ℝ)) *
      ((r : ℝ) * η₀) ^ (m - 1) * η₀) :
    polySum ≤ η₀ * (4 * (r : ℝ) * η₀) ^ (m - 1) := by
  have hcat := catalan_le_four_pow hm
  have hnn : 0 ≤ ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by positivity
  calc polySum
      ≤ ((Nat.choose (2 * (m - 1)) (m - 1) : ℝ) / (m : ℝ)) * (((r : ℝ) * η₀) ^ (m - 1) * η₀) := by
        linarith
    _ ≤ (4 : ℝ) ^ (m - 1) * (((r : ℝ) * η₀) ^ (m - 1) * η₀) :=
        mul_le_mul_of_nonneg_right hcat hnn
    _ = η₀ * (4 * (r : ℝ) * η₀) ^ (m - 1) := by
        rw [mul_comm η₀, mul_assoc, ← mul_pow]; ring

/-- **Lemma A.2** (Cayley Spanning-Tree Root-Reversal Estimate, Eq. A.2). -/
theorem lemma_A_2_cayley_root_reversal {k r : ℕ} {Jsite revSum : ℝ}
    (hk : 1 ≤ k) (hJ : 0 ≤ Jsite)
    (hcayley : revSum ≤ ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * ((r : ℝ) * Jsite) ^ k) :
    revSum ≤ (Real.exp 1 * (r : ℝ) * Jsite) ^ k := by
  have hfac := pow_pred_div_factorial_le_exp hk
  have hnn : 0 ≤ ((r : ℝ) * Jsite) ^ k := by positivity
  have hexp : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul]; simp
  calc revSum
      ≤ ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * ((r : ℝ) * Jsite) ^ k := hcayley
    _ ≤ Real.exp (k : ℝ) * ((r : ℝ) * Jsite) ^ k := mul_le_mul_of_nonneg_right hfac hnn
    _ = (Real.exp 1) ^ k * ((r : ℝ) * Jsite) ^ k := by rw [hexp]
    _ = (Real.exp 1 * (r : ℝ) * Jsite) ^ k := by rw [← mul_pow]; ring

/-- **Lemma A.3** (Multi-Type Unordered Spanning-Tree Induction, Eqs. A.3–A.4). -/
theorem lemma_A_3_unordered_tree_induction {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (supp : E → Finset V) (μ : E → ℝ) (c₀ Φ : ℝ)
    (hμ : ∀ e, 0 ≤ μ e) (hΦ_lt : Φ < c₀)
    (hpin : ∀ y : V, ∑ e ∈ Finset.univ.filter (fun e ↦ y ∈ supp e),
      μ e * Real.exp (c₀ * ((supp e).card : ℝ)) ≤ Φ)
    (S : ℕ → E → ℝ)
    (hS0 : ∀ e, S 0 e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ)))
    (hSstep : ∀ h e, S (h + 1) e ≤
      μ e * Real.exp (∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
        S h e')) :
    (∀ h e, S h e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ))) ∧
    (∀ h y, ∑ e ∈ Finset.univ.filter (fun e ↦ y ∈ supp e), S h e ≤ Φ) := by
  have hind : ∀ h e, S h e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ)) := by
    intro h
    induction h with
    | zero => exact hS0
    | succ h ih =>
      intro e
      have hsum_le :
          ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)), S h e' ≤
          ((supp e).card : ℝ) * Φ := by
        have h1 : ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)), S h e' ≤
            ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
              μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) :=
          Finset.sum_le_sum fun e' _ ↦ ih e'
        have h2 : ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
              μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) ≤
            ∑ y ∈ supp e, ∑ e' ∈ Finset.univ.filter (fun e' ↦ y ∈ supp e'),
              μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) := by
          have hrew : ∑ e' : E, ∑ y ∈ supp e,
                (if y ∈ supp e' then μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) else 0) =
              ∑ y ∈ supp e, ∑ e' ∈ Finset.univ.filter (fun e' ↦ y ∈ supp e'),
                μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _
            rw [Finset.sum_filter]
          rw [← hrew]
          calc ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
                μ e' * Real.exp (c₀ * ((supp e').card : ℝ))
              ≤ ∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
                  ∑ y ∈ supp e,
                    (if y ∈ supp e' then μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) else 0) := by
                apply Finset.sum_le_sum
                intro e' he'
                have hnd : ¬ Disjoint (supp e') (supp e) := (Finset.mem_filter.mp he').2
                rw [Finset.not_disjoint_iff] at hnd
                obtain ⟨y₀, hy₀', hy₀⟩ := hnd
                have hsingle := Finset.single_le_sum
                  (f := fun y ↦ if y ∈ supp e' then μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) else 0)
                  (fun y _ ↦ by split_ifs <;> positivity) hy₀
                simpa [hy₀'] using hsingle
            _ ≤ ∑ e' : E, ∑ y ∈ supp e,
                  (if y ∈ supp e' then μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) else 0) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro e' _ _
                exact Finset.sum_nonneg fun y _ ↦ by split_ifs <;> positivity
        have h3 : ∑ y ∈ supp e, ∑ e' ∈ Finset.univ.filter (fun e' ↦ y ∈ supp e'),
              μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) ≤
            ((supp e).card : ℝ) * Φ := by
          calc ∑ y ∈ supp e, ∑ e' ∈ Finset.univ.filter (fun e' ↦ y ∈ supp e'),
                μ e' * Real.exp (c₀ * ((supp e').card : ℝ))
              ≤ ∑ _ ∈ supp e, Φ := Finset.sum_le_sum fun y _ ↦ hpin y
            _ = ((supp e).card : ℝ) * Φ := by simp
        linarith
      calc S (h + 1) e
          ≤ μ e * Real.exp (∑ e' ∈ Finset.univ.filter (fun e' ↦ ¬ Disjoint (supp e') (supp e)),
              S h e') := hSstep h e
        _ ≤ μ e * Real.exp (((supp e).card : ℝ) * Φ) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_le) (hμ e)
        _ ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (hμ e)
            apply Real.exp_le_exp.mpr
            have hc : (0 : ℝ) ≤ ((supp e).card : ℝ) := Nat.cast_nonneg _
            nlinarith
  refine ⟨hind, fun h y ↦ ?_⟩
  calc ∑ e ∈ Finset.univ.filter (fun e ↦ y ∈ supp e), S h e
      ≤ ∑ e ∈ Finset.univ.filter (fun e ↦ y ∈ supp e),
          μ e * Real.exp (c₀ * ((supp e).card : ℝ)) := Finset.sum_le_sum fun e _ ↦ hind h e
    _ ≤ Φ := hpin y

end AppendixA

section KoteckyPreissVerification

/-- **Lemma 7.2** (Kotecký–Preiss Convergence Verification at `β ≤ β_wc`). -/
theorem lemma_7_2_kp_verification {r : ℕ} {β Jsite : ℝ}
    (hr : 2 ≤ r) (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ betaWC r Jsite) :
    let η₀ := (β / 2) * Jsite * (6 : ℝ) ^ r * Real.exp (1 + (β / 2) * Jsite)
    η₀ < 1 / (8 * (r : ℝ)) ∧
    η₀ / (1 - 4 * (r : ℝ) * η₀) < 1 / (4 * (r : ℝ)) := by
  intro η₀
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h6 : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
    have : (6 : ℝ) ^ 2 ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    linarith [show (6 : ℝ) ^ 2 = 36 by norm_num]
  have he2 : (1 : ℝ) < Real.exp 2 := by
    simpa using Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)
  have hsmall : (β / 2) * Jsite < 1 := by
    have h1 : (β / 2) * Jsite ≤ (betaWC r Jsite / 2) * Jsite := by nlinarith
    have h2 : (betaWC r Jsite / 2) * Jsite = 1 / (8 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r) := by
      unfold betaWC
      field_simp [hJ.ne', (Real.exp_pos 2).ne', hr0.ne', (pow_pos (by norm_num : (0 : ℝ) < 6) r).ne']
      ring
    rw [h2] at h1
    have hden : 1 < 8 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have h1' : 8 * (r : ℝ) < 8 * Real.exp 2 * (r : ℝ) := by nlinarith
      nlinarith
    have hlt : 1 / (8 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r) < 1 := by
      rw [div_lt_one (by positivity)]; exact hden
    linarith
  have hexp_lt : Real.exp (1 + (β / 2) * Jsite) < Real.exp 2 :=
    Real.exp_lt_exp.mpr (by linarith)
  have hη_lt : η₀ < 1 / (8 * (r : ℝ)) := by
    have hstep1 : η₀ ≤ (betaWC r Jsite / 2) * Jsite * (6 : ℝ) ^ r * Real.exp (1 + (β / 2) * Jsite) := by
      simp only [η₀]
      have hnn : 0 ≤ Jsite * (6 : ℝ) ^ r * Real.exp (1 + (β / 2) * Jsite) := by positivity
      nlinarith
    have hstep2 : (betaWC r Jsite / 2) * Jsite * (6 : ℝ) ^ r * Real.exp (1 + (β / 2) * Jsite) <
        (betaWC r Jsite / 2) * Jsite * (6 : ℝ) ^ r * Real.exp 2 := by
      apply mul_lt_mul_of_pos_left hexp_lt
      have := betaWC_pos hr hJ
      positivity
    have heq : (betaWC r Jsite / 2) * Jsite * (6 : ℝ) ^ r * Real.exp 2 = 1 / (8 * (r : ℝ)) := by
      unfold betaWC
      field_simp [hJ.ne', (Real.exp_pos 2).ne', hr0.ne', (pow_pos (by norm_num : (0 : ℝ) < 6) r).ne']
      ring
    linarith
  have h4rη : 4 * (r : ℝ) * η₀ < 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_left hη_lt (by positivity : 0 < 4 * (r : ℝ))
    have heq : 4 * (r : ℝ) * (1 / (8 * (r : ℝ))) = 1 / 2 := by field_simp [hr0.ne']; ring
    linarith
  have hfrac : η₀ / (1 - 4 * (r : ℝ) * η₀) < 1 / (4 * (r : ℝ)) := by
    rw [div_lt_div_iff₀ (by linarith) (by positivity)]
    have h1 : η₀ * (4 * (r : ℝ)) < 1 / 2 := by linarith
    linarith
  exact ⟨hη_lt, hfrac⟩

/-- **Lemma 6.3** (Trace Cumulant Exponential-Pinning Verification). -/
theorem lemma_6_3_kp_pinning_verification {r kr : ℕ} {β Jsite gX : ℝ}
    (hr : 2 ≤ r) (hkr : r ≤ kr) (hJ : 0 < Jsite) (hg : 0 < gX)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite)) :
    let Λ0 := 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * gX)
    Real.exp 1 * β * Jsite * Real.exp (β * Jsite) < 1 / (8 * (r : ℝ)) ∧
    Real.exp ((kr : ℝ) / (r : ℝ)) * Λ0 * gX * Real.exp (Λ0 * gX) < 1 / (8 * (r : ℝ)) := by
  intro Λ0
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hkr0 : (0 : ℝ) < (kr : ℝ) := by exact_mod_cast (by omega : 0 < kr)
  have hkr_ge : (r : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr
  have he2 : (1 : ℝ) < Real.exp 2 := by
    simpa using Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)
  have hβJ_lt : β * Jsite < 1 := by
    have h1 : β * Jsite ≤ 1 / (8 * Real.exp 2 * (r : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hβ hJ.le
      have heq : 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) * Jsite = 1 / (8 * Real.exp 2 * (r : ℝ)) := by
        field_simp [hJ.ne', (Real.exp_pos 2).ne', hr0.ne']
      linarith
    have hden : 1 < 8 * Real.exp 2 * (r : ℝ) := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    have hlt : 1 / (8 * Real.exp 2 * (r : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; exact hden
    linarith
  have hpart1 : Real.exp 1 * β * Jsite * Real.exp (β * Jsite) < 1 / (8 * (r : ℝ)) := by
    have hexp_lt : Real.exp 1 * Real.exp (β * Jsite) < Real.exp 2 := by
      rw [← Real.exp_add]; exact Real.exp_lt_exp.mpr (by linarith)
    have h1 : Real.exp 1 * β * Jsite * Real.exp (β * Jsite) =
        (β * Jsite) * (Real.exp 1 * Real.exp (β * Jsite)) := by ring
    rw [h1]
    by_cases hβz : β = 0
    · subst hβz; simp; positivity
    · have hβp : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβz)
      have hmul : (β * Jsite) * (Real.exp 1 * Real.exp (β * Jsite)) <
          (β * Jsite) * Real.exp 2 := mul_lt_mul_of_pos_left hexp_lt (mul_pos hβp hJ)
      have hle : (β * Jsite) * Real.exp 2 ≤ 1 / (8 * (r : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hβ (mul_pos hJ (Real.exp_pos 2)).le
        have heq : 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) * (Jsite * Real.exp 2) =
            1 / (8 * (r : ℝ)) := by
          field_simp [hJ.ne', (Real.exp_pos 2).ne', hr0.ne']
        linarith
      linarith
  have hpart2 : Real.exp ((kr : ℝ) / (r : ℝ)) * Λ0 * gX * Real.exp (Λ0 * gX) < 1 / (8 * (r : ℝ)) := by
    have hΛg : Λ0 * gX = 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ))) := by
      simp only [Λ0]
      field_simp [hg.ne', hkr0.ne', (Real.exp_pos _).ne']
    have hΛg_lt1 : Λ0 * gX < 1 := by
      rw [hΛg, div_lt_one (by positivity)]
      have he1 : (1 : ℝ) < Real.exp (1 + (kr : ℝ) / (r : ℝ)) :=
        Real.one_lt_exp_iff.mpr (by positivity)
      have hkr2 : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (le_trans hr hkr)
      nlinarith
    have hrew : Real.exp ((kr : ℝ) / (r : ℝ)) * Λ0 * gX * Real.exp (Λ0 * gX) =
        Real.exp (Λ0 * gX) / (16 * (kr : ℝ) * Real.exp 1) := by
      simp only [Λ0]
      rw [Real.exp_add]
      field_simp [hg.ne', hkr0.ne', (Real.exp_pos 1).ne', (Real.exp_pos ((kr : ℝ) / (r : ℝ))).ne']
    rw [hrew]
    have hnum : Real.exp (Λ0 * gX) < Real.exp 1 := Real.exp_lt_exp.mpr hΛg_lt1
    have hstep1 : Real.exp (Λ0 * gX) / (16 * (kr : ℝ) * Real.exp 1) <
        Real.exp 1 / (16 * (kr : ℝ) * Real.exp 1) :=
      div_lt_div_of_pos_right hnum (by positivity)
    have hstep2 : Real.exp 1 / (16 * (kr : ℝ) * Real.exp 1) = 1 / (16 * (kr : ℝ)) := by
      field_simp [(Real.exp_pos 1).ne', hkr0.ne']
    have hstep3 : 1 / (16 * (kr : ℝ)) ≤ 1 / (8 * (r : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  exact ⟨hpart1, hpart2⟩

end KoteckyPreissVerification

end KrylovChaos
