/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Section 4.3: Product-State Static Complexity Bound (Proposition 4.3)

Formalizes **Proposition 4.3** (Eq. 4.5): For an `N`-qubit product state
`ρ = ⨂_{x=1}^N (I + m_x Z_x)/2` with `|m_x| ≤ m_max < 1`, the thermal-size
expectation on any unit Wightman-norm operator `A` supported on Pauli strings of
weight `≤ s` satisfies
`𝒮_β(A) ≤ s + m_max √(N s)`.
-/

namespace KrylovChaos

section ProductStateBound

/-- Single-site parameter `σ(m) = √(1 - m²)`. -/
noncomputable def prodSigma (m : ℝ) : ℝ := Real.sqrt (1 - m ^ 2)

/-- Single-site parameter `q(m) = √((1 + m)/2) - √((1 - m)/2)`. -/
noncomputable def prodQ (m : ℝ) : ℝ :=
  Real.sqrt ((1 + m) / 2) - Real.sqrt ((1 - m) / 2)

/-- Exact single-site `4 × 4` thermal-size matrix `M_x` in the Pauli basis
`{0 = I, 1 = X, 2 = Y, 3 = Z}` (Eq. 4.6). -/
noncomputable def singleSiteM (m : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0
  | 1, 1 => 1 - (prodQ m) ^ 2 / 2
  | 2, 2 => 1 - (prodQ m) ^ 2 / 2
  | 3, 3 => prodSigma m
  | 0, 3 => m / 2
  | 3, 0 => m / 2
  | _, _ => 0

/-- Hamming weight `|a|` of a Pauli string `a : Fin N → Fin 4`. -/
def stringWeight {N : ℕ} (a : Fin N → Fin 4) : ℕ :=
  (Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0)).card

theorem singleSiteM_diag_le_one {m : ℝ} (hm : |m| < 1) (α : Fin 4) :
    singleSiteM m α α ≤ 1 := by
  fin_cases α
  · simp [singleSiteM]
  · change 1 - (prodQ m) ^ 2 / 2 ≤ 1
    nlinarith [sq_nonneg (prodQ m)]
  · change 1 - (prodQ m) ^ 2 / 2 ≤ 1
    nlinarith [sq_nonneg (prodQ m)]
  · change Real.sqrt (1 - m ^ 2) ≤ 1
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg m]

private lemma update_bijection_sum {N : ℕ} (x : Fin N) (u v : Fin 4) (huv : u ≠ v)
    (f : (Fin N → Fin 4) → ℝ) :
    (∑ a : Fin N → Fin 4, if a x = u then f (Function.update a x v) else 0) =
    ∑ b : Fin N → Fin 4, if b x = v then f b else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ ↦ Function.update a x v) ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 : a₁ x = u := (Finset.mem_filter.mp ha₁).2
    have h2 : a₂ x = u := (Finset.mem_filter.mp ha₂).2
    funext y
    by_cases hy : y = x
    · subst hy; rw [h1, h2]
    · have := congrFun heq y
      simpa [Function.update_of_ne hy] using this
  · intro b hb
    have hbv : b x = v := (Finset.mem_filter.mp hb).2
    refine ⟨Function.update b x u, by simp, ?_⟩
    funext y
    by_cases hy : y = x
    · subst hy; simp [hbv]
    · simp [Function.update_of_ne hy]
  · intro a _; rfl

/-- **Proposition 4.3** (Product-State Static Complexity Bound, Eq. 4.5):
For any `N, s : ℕ`, single-site magnetizations `|m_x| ≤ m_max < 1`, and normalized
Pauli-string amplitudes `c : (Fin N → Fin 4) → ℂ` supported on weight `≤ s`
(`∑_a ‖c a‖² = 1`), the exact product-state thermal-size quadratic form satisfies
`∑_x ∑_{a, b : a|_{≠x} = b|_{≠x}} Re(c_a* c_b) (M_x)_{a_x, b_x} ≤ s + m_max √(N s)`. -/
theorem prop_4_3_product_state_static_bound {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1)
    (c : (Fin N → Fin 4) → ℂ)
    (hsupp : ∀ a, s < stringWeight a → c a = 0)
    (hnorm : ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 = 1) :
    (∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
      if ∀ y : Fin N, y ≠ x → a y = b y then
        (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
      else 0) ≤
    (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  have hm_lt : ∀ x, |m x| < 1 := fun x ↦ lt_of_le_of_lt (hm_le x) hmmax
  have hinner : ∀ x a,
      (∑ b : Fin N → Fin 4,
        if ∀ y : Fin N, y ≠ x → a y = b y then
          (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
        else 0) =
      ∑ k : Fin 4, (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k := by
    intro x a
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun k _ ↦ Function.update a x k) ?_ ?_ ?_ ?_
    · intro k _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun y hy ↦ by simp [Function.update_of_ne hy]⟩
    · intro k₁ _ k₂ _ heq
      have := congrFun heq x
      simpa using this
    · intro b hb
      have hagree := (Finset.mem_filter.mp hb).2
      refine ⟨b x, Finset.mem_univ _, ?_⟩
      funext y
      by_cases hy : y = x
      · subst hy; simp
      · simp [Function.update_of_ne hy, hagree y hy]
    · intro k _; simp
  simp_rw [hinner]
  have hbound_site : ∀ x a,
      ∑ k : Fin 4, (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k ≤
      ((if a x ≠ 0 then ‖c a‖ ^ 2 else 0) +
       (if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0)) +
       (if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) := by
    intro x a
    have hre_self : (star (c a) * c a).re = ‖c a‖ ^ 2 := by
      change ((starRingEnd ℂ) (c a) * c a).re = ‖c a‖ ^ 2
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hre_cross : ∀ z w : ℂ, |(star z * w).re| ≤ ‖z‖ * ‖w‖ := by
      intro z w
      calc |(star z * w).re| ≤ ‖star z * w‖ := Complex.abs_re_le_norm _
        _ = ‖star z‖ * ‖w‖ := norm_mul _ _
        _ = ‖z‖ * ‖w‖ := by simp
    rw [Fin.sum_univ_four]
    have hcases : a x = 0 ∨ a x = 1 ∨ a x = 2 ∨ a x = 3 := by
      have hv := (a x).2
      interval_cases h : (a x).1
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; left; exact Fin.ext h
      · right; right; right; exact Fin.ext h
    rcases hcases with h0 | h1 | h2 | h3
    · rw [h0]
      have hM0 : singleSiteM (m x) 0 0 = 0 := rfl
      have hM1 : singleSiteM (m x) 0 1 = 0 := rfl
      have hM2 : singleSiteM (m x) 0 2 = 0 := rfl
      have hM3 : singleSiteM (m x) 0 3 = m x / 2 := rfl
      rw [hM0, hM1, hM2, hM3]
      simp only [Fin.isValue, ne_eq, not_true_eq_false, ↓reduceIte, Fin.reduceEq,
        mul_zero, zero_add, add_zero]
      have hc := hre_cross (c a) (c (Function.update a x 3))
      have h1' : (star (c a) * c (Function.update a x 3)).re * (m x / 2) ≤
          |(star (c a) * c (Function.update a x 3)).re * (m x / 2)| := le_abs_self _
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1'
      have h2' : |(star (c a) * c (Function.update a x 3)).re| * (|m x| / 2) ≤
          (‖c a‖ * ‖c (Function.update a x 3)‖) * (|m x| / 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      linarith
    · have hupd1 : Function.update a x 1 = a := by
        funext y; by_cases hy : y = x <;> simp [Function.update, hy, h1]
      rw [h1]
      have hM0 : singleSiteM (m x) 1 0 = 0 := rfl
      have hM1 : singleSiteM (m x) 1 1 = 1 - (prodQ (m x)) ^ 2 / 2 := rfl
      have hM2 : singleSiteM (m x) 1 2 = 0 := rfl
      have hM3 : singleSiteM (m x) 1 3 = 0 := rfl
      rw [hM0, hM1, hM2, hM3, hupd1, hre_self]
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, ↓reduceIte,
        mul_zero, zero_add, add_zero]
      nlinarith [sq_nonneg (prodQ (m x)), sq_nonneg ‖c a‖]
    · have hupd2 : Function.update a x 2 = a := by
        funext y; by_cases hy : y = x <;> simp [Function.update, hy, h2]
      rw [h2]
      have hM0 : singleSiteM (m x) 2 0 = 0 := rfl
      have hM1 : singleSiteM (m x) 2 1 = 0 := rfl
      have hM2 : singleSiteM (m x) 2 2 = 1 - (prodQ (m x)) ^ 2 / 2 := rfl
      have hM3 : singleSiteM (m x) 2 3 = 0 := rfl
      rw [hM0, hM1, hM2, hM3, hupd2, hre_self]
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, ↓reduceIte,
        mul_zero, zero_add, add_zero]
      nlinarith [sq_nonneg (prodQ (m x)), sq_nonneg ‖c a‖]
    · have hupd3 : Function.update a x 3 = a := by
        funext y; by_cases hy : y = x <;> simp [Function.update, hy, h3]
      rw [h3]
      have hM0 : singleSiteM (m x) 3 0 = m x / 2 := rfl
      have hM1 : singleSiteM (m x) 3 1 = 0 := rfl
      have hM2 : singleSiteM (m x) 3 2 = 0 := rfl
      have hM3 : singleSiteM (m x) 3 3 = prodSigma (m x) := rfl
      rw [hM0, hM1, hM2, hM3, hupd3, hre_self]
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, ↓reduceIte,
        mul_zero, zero_add, add_zero]
      have hle : prodSigma (m x) ≤ 1 := singleSiteM_diag_le_one (hm_lt x) 3
      have hdiag : ‖c a‖ ^ 2 * prodSigma (m x) ≤ ‖c a‖ ^ 2 := by nlinarith [sq_nonneg ‖c a‖]
      have hc := hre_cross (c a) (c (Function.update a x 0))
      have h1' : (star (c a) * c (Function.update a x 0)).re * (m x / 2) ≤
          |(star (c a) * c (Function.update a x 0)).re * (m x / 2)| := le_abs_self _
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1'
      have h2' : |(star (c a) * c (Function.update a x 0)).re| * (|m x| / 2) ≤
          (‖c a‖ * ‖c (Function.update a x 0)‖) * (|m x| / 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      linarith
  have hsum_le :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        ∑ k : Fin 4, (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k) ≤
      ((∑ x : Fin N, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) +
       (∑ x : Fin N, ∑ a : Fin N → Fin 4,
          if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0)) +
       (∑ x : Fin N, ∑ a : Fin N → Fin 4,
          if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) := by
    calc ∑ x : Fin N, ∑ a : Fin N → Fin 4,
          ∑ k : Fin 4, (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k
        ≤ ∑ x : Fin N, ∑ a : Fin N → Fin 4,
          (((if a x ≠ 0 then ‖c a‖ ^ 2 else 0) +
            (if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0)) +
            (if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0)) :=
          Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun a _ ↦ hbound_site x a
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hdiag : (∑ x : Fin N, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) ≤ (s : ℝ) := by
    rw [Finset.sum_comm]
    have hrew : ∀ a : Fin N → Fin 4,
        (∑ x : Fin N, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) = (stringWeight a : ℝ) * ‖c a‖ ^ 2 := by
      intro a
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; rfl
    simp_rw [hrew]
    calc ∑ a : Fin N → Fin 4, (stringWeight a : ℝ) * ‖c a‖ ^ 2
        ≤ ∑ a : Fin N → Fin 4, (s : ℝ) * ‖c a‖ ^ 2 := by
          apply Finset.sum_le_sum; intro a _
          by_cases hle : stringWeight a ≤ s
          · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (sq_nonneg _)
          · rw [hsupp a (Nat.lt_of_not_ge hle), norm_zero, sq, mul_zero, mul_zero, mul_zero]
      _ = (s : ℝ) * ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (s : ℝ) := by rw [hnorm, mul_one]
  have hoff_eq :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) =
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    symm
    have hbij := update_bijection_sum x 0 3 (by decide)
      (fun b ↦ (|m x| / 2) * (‖c b‖ * ‖c (Function.update b x 0)‖))
    rw [← hbij]
    apply Finset.sum_congr rfl; intro a _
    split_ifs with h0
    · have hback : Function.update (Function.update a x 3) x 0 = a := by
        funext y; by_cases hy : y = x <;> simp [Function.update, hy, h0]
      rw [hback, mul_comm ‖c a‖]
    · rfl
  have hoff_bound :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) ≤
      (mmax / 2) * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
    by_cases hN0 : N = 0
    · subst hN0; simp
    · have hmmax_nn : 0 ≤ mmax :=
        le_trans (abs_nonneg (m ⟨0, Nat.pos_of_ne_zero hN0⟩)) (hm_le ⟨0, Nat.pos_of_ne_zero hN0⟩)
      have hstep1 :
          (∑ x : Fin N, ∑ a : Fin N → Fin 4,
            if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) ≤
          (mmax / 2) * ∑ x : Fin N, ∑ a : Fin N → Fin 4,
            (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro a _
        split_ifs
        · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hm_le x) (by norm_num))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · simp
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N × (Fin N → Fin 4)))
        (fun p ↦ if p.2 p.1 = 0 then ‖c p.2‖ else 0)
        (fun p ↦ if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)
      have hfac1 : (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c p.2‖ else 0) ^ 2) ≤ (N : ℝ) := by
        rw [Fintype.sum_prod_type]
        calc ∑ x : Fin N, ∑ a : Fin N → Fin 4, (if a x = 0 then ‖c a‖ else 0) ^ 2
            ≤ ∑ _ : Fin N, ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := by
              apply Finset.sum_le_sum; intro x _
              apply Finset.sum_le_sum; intro a _
              split_ifs
              · exact le_refl _
              · simp [sq_nonneg]
          _ = ∑ _ : Fin N, (1 : ℝ) := by simp_rw [hnorm]
          _ = (N : ℝ) := by simp
      have hfac2 : (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0) ^ 2) ≤ (s : ℝ) := by
        rw [Fintype.sum_prod_type]
        have hsq_ite : ∀ (x : Fin N) (a : Fin N → Fin 4),
            (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) ^ 2 =
            if a x = 0 then ‖c (Function.update a x 3)‖ ^ 2 else 0 := by
          intro x a; split_ifs <;> simp
        simp_rw [hsq_ite]
        have hshift : ∀ x : Fin N,
            (∑ a : Fin N → Fin 4, if a x = 0 then ‖c (Function.update a x 3)‖ ^ 2 else 0) =
            ∑ b : Fin N → Fin 4, if b x = 3 then ‖c b‖ ^ 2 else 0 :=
          fun x ↦ update_bijection_sum x 0 3 (by decide) (fun b ↦ ‖c b‖ ^ 2)
        simp_rw [hshift]
        calc ∑ x : Fin N, ∑ b : Fin N → Fin 4, (if b x = 3 then ‖c b‖ ^ 2 else 0)
            ≤ ∑ x : Fin N, ∑ b : Fin N → Fin 4, (if b x ≠ 0 then ‖c b‖ ^ 2 else 0) := by
              apply Finset.sum_le_sum; intro x _
              apply Finset.sum_le_sum; intro b _
              split_ifs with h3 hne
              · exact le_refl _
              · exact absurd h3 (by rw [not_not.mp hne]; decide)
              · exact sq_nonneg _
              · exact le_refl _
          _ ≤ (s : ℝ) := hdiag
      have hsqrt_bound :
          (∑ x : Fin N, ∑ a : Fin N → Fin 4,
            (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0)) ≤
          Real.sqrt ((N : ℝ) * (s : ℝ)) := by
        have hprod_eq :
            (∑ x : Fin N, ∑ a : Fin N → Fin 4,
              (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0)) =
            ∑ p : Fin N × (Fin N → Fin 4),
              (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
              (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0) :=
          (Fintype.sum_prod_type (fun p : Fin N × (Fin N → Fin 4) ↦
            (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
            (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0))).symm
        rw [hprod_eq]
        have hsum_nn : 0 ≤ ∑ p : Fin N × (Fin N → Fin 4),
            (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
            (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0) :=
          Finset.sum_nonneg fun p _ ↦ mul_nonneg
            (by split_ifs; exact norm_nonneg _; exact le_refl 0)
            (by split_ifs; exact norm_nonneg _; exact le_refl 0)
        have hsq_le : (∑ p : Fin N × (Fin N → Fin 4),
            (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
            (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)) ^ 2 ≤
            (N : ℝ) * (s : ℝ) :=
          le_trans hcs (mul_le_mul hfac1 hfac2 (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
            (Nat.cast_nonneg N))
        calc ∑ p : Fin N × (Fin N → Fin 4),
              (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
              (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)
            = Real.sqrt ((∑ p : Fin N × (Fin N → Fin 4),
                (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
                (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)) ^ 2) :=
              (Real.sqrt_sq hsum_nn).symm
          _ ≤ Real.sqrt ((N : ℝ) * (s : ℝ)) := Real.sqrt_le_sqrt hsq_le
      calc (∑ x : Fin N, ∑ a : Fin N → Fin 4,
            if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0)
          ≤ (mmax / 2) * ∑ x : Fin N, ∑ a : Fin N → Fin 4,
              (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) :=
            hstep1
        _ ≤ (mmax / 2) * Real.sqrt ((N : ℝ) * (s : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrt_bound (by linarith)
  linarith

end ProductStateBound

end KrylovChaos
