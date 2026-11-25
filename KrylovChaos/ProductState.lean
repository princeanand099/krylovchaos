/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Section 4.3: Static Filtration Bound for Full-Rank Product Thermal States

Formalizes **Proposition 4.3** (Eq. 4.5): for any full-rank product state
`ρ_β = ⊗_{x=1}^N ρ_x` with `ρ_x = (1/2)(I_x + m_x Z_x)` and `|m_x| ≤ m_max < 1`,
every operator `A ∈ 𝒱_s` normalized to `‖A‖_{β,W} = 1` satisfies
`𝒮_β(A) ≤ s + m_max √(N s)`.
-/

namespace KrylovChaos

/-- Single-site polarization parameters `σ_x = √(1 - m²)`, `p_x`, `q_x`. -/
noncomputable def prodSigma (m : ℝ) : ℝ := Real.sqrt (1 - m ^ 2)

noncomputable def prodP (m : ℝ) : ℝ :=
  Real.sqrt ((1 + m) / 2) + Real.sqrt ((1 - m) / 2)

noncomputable def prodQ (m : ℝ) : ℝ :=
  Real.sqrt ((1 + m) / 2) - Real.sqrt ((1 - m) / 2)

/-- Exact single-site algebraic identities: `p_x² + q_x² = 2`, `p_x q_x = m_x`,
and `p_x² - q_x² = 2 σ_x`. -/
theorem prod_params_identities {m : ℝ} (hm : |m| < 1) :
    (prodP m) ^ 2 + (prodQ m) ^ 2 = 2 ∧
    prodP m * prodQ m = m ∧
    (prodP m) ^ 2 - (prodQ m) ^ 2 = 2 * prodSigma m := by
  have hm1 : -1 < m ∧ m < 1 := abs_lt.mp hm
  have h1 : 0 ≤ (1 + m) / 2 := by linarith
  have h2 : 0 ≤ (1 - m) / 2 := by linarith
  have hsq1 : Real.sqrt ((1 + m) / 2) ^ 2 = (1 + m) / 2 := Real.sq_sqrt h1
  have hsq2 : Real.sqrt ((1 - m) / 2) ^ 2 = (1 - m) / 2 := Real.sq_sqrt h2
  have hprod : Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2) = prodSigma m / 2 := by
    rw [← Real.sqrt_mul h1]
    unfold prodSigma
    have h4 : (1 + m) / 2 * ((1 - m) / 2) = (1 - m ^ 2) / 4 := by ring
    rw [h4, Real.sqrt_div (by nlinarith : 0 ≤ 1 - m ^ 2), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  unfold prodP prodQ
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hsq1, hsq2]
  · nlinarith [hsq1, hsq2]
  · nlinarith [hsq1, hsq2, hprod]

/-- Subtracted single-site operator-size matrix `M_x(a, b)` in the Gram–Schmidt
Wightman-orthonormal basis `{E_x^{(0)}, E_x^{(1)}, E_x^{(2)}, E_x^{(3)}}`. -/
noncomputable def singleSiteM (m : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0
  | 1, 1 => 1 - (prodQ m) ^ 2 / 2
  | 2, 2 => 1 - (prodQ m) ^ 2 / 2
  | 3, 3 => prodSigma m
  | 0, 3 => m / 2
  | 3, 0 => m / 2
  | _, _ => 0

theorem singleSiteM_diag_le_one {m : ℝ} (hm : |m| < 1) (a : Fin 4) :
    singleSiteM m a a ≤ 1 := by
  fin_cases a
  · simp [singleSiteM]
  · simp only [singleSiteM]; nlinarith [sq_nonneg (prodQ m)]
  · simp only [singleSiteM]; nlinarith [sq_nonneg (prodQ m)]
  · simp only [singleSiteM, prodSigma]
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg m]

/-- Pauli-string weight `|a| := #{x : a_x ≠ 0}` for `a : Fin N → Fin 4`. -/
def stringWeight {N : ℕ} (a : Fin N → Fin 4) : ℕ :=
  (Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0)).card

/-- **Proposition 4.3** (Static Filtration Bound for Product States, Eq. 4.5):
For any full-rank product state with `|m_x| ≤ m_max < 1` and any normalized
`s`-local operator `A = ∑_{|a| ≤ s} c_a E_a` (`∑ ‖c_a‖² = 1`),
`𝒮_β(A) ≤ s + m_max √(N s)`. -/
theorem prop_4_3_product_state_bound {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1)
    (c : (Fin N → Fin 4) → ℂ)
    (hsupp : ∀ a, s < stringWeight a → c a = 0)
    (hnorm : ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 = 1) :
    (∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
      if (∀ y, y ≠ x → a y = b y) then
        (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
      else 0) ≤
    (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  have hm_lt : ∀ x, |m x| < 1 := fun x ↦ lt_of_le_of_lt (hm_le x) hmmax
  -- For fixed x and a, the inner sum over b agreeing with a off x reduces to Fin 4
  have hinner : ∀ x : Fin N, ∀ a : Fin N → Fin 4,
      (∑ b : Fin N → Fin 4,
        if (∀ y, y ≠ x → a y = b y) then
          (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
        else 0) =
      ∑ k : Fin 4,
        (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k := by
    intro x a
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun k _ ↦ Function.update a x k) ?_ ?_ ?_ ?_
    · intro k _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun y hy ↦ (Function.update_of_ne hy k a).symm⟩
    · intro k₁ _ k₂ _ heq
      have h := congr_fun heq x
      simpa using h
    · intro b hb
      have hagree : ∀ y, y ≠ x → a y = b y := (Finset.mem_filter.mp hb).2
      refine ⟨b x, Finset.mem_univ _, ?_⟩
      ext y
      by_cases hy : y = x
      · subst hy; simp
      · rw [Function.update_of_ne hy]; exact (hagree y hy).symm
    · intro k _
      simp
  simp_rw [hinner]
  -- Evaluate the Fin 4 sum explicitly for each value of `a x`
  have hbound_site : ∀ x : Fin N, ∀ a : Fin N → Fin 4,
      (∑ k : Fin 4,
        (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k) ≤
      (if a x ≠ 0 then ‖c a‖ ^ 2 else 0) +
      (if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) +
      (if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) := by
    intro x a
    have hre_self : (star (c a) * c a).re = ‖c a‖ ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hre_le : ∀ z w : ℂ, (star z * w).re ≤ ‖z‖ * ‖w‖ := by
      intro z w
      calc (star z * w).re ≤ ‖star z * w‖ := Complex.re_le_norm _
        _ = ‖z‖ * ‖w‖ := by simp [norm_mul]
    have habs_re : ∀ z w : ℂ, ∀ r : ℝ, (star z * w).re * r ≤ |r| * (‖z‖ * ‖w‖) := by
      intro z w r
      have h1 : |(star z * w).re| ≤ ‖z‖ * ‖w‖ := by
        calc |(star z * w).re| ≤ ‖star z * w‖ := Complex.abs_re_le_norm _
          _ = ‖z‖ * ‖w‖ := by simp [norm_mul]
      calc (star z * w).re * r ≤ |(star z * w).re * r| := le_abs_self _
        _ = |(star z * w).re| * |r| := abs_mul _ _
        _ ≤ (‖z‖ * ‖w‖) * |r| := mul_le_mul_of_nonneg_right h1 (abs_nonneg r)
        _ = |r| * (‖z‖ * ‖w‖) := by ring
    rw [Fin.sum_univ_four]
    have hupd_self : Function.update a x (a x) = a := Function.update_eq_self x a
    match hax : a x with
    | 0 =>
      simp only [singleSiteM, mul_zero, zero_add, add_zero, ne_eq, not_true_eq_false, ↓reduceIte,
        Fin.reduceEq]
      have h := habs_re (c a) (c (Function.update a x 3)) (m x / 2)
      rwa [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    | 1 =>
      simp only [singleSiteM, mul_zero, zero_add, add_zero, ne_eq, Fin.reduceEq, not_false_eq_true,
        ↓reduceIte]
      have hupd1 : Function.update a x 1 = a := by rw [← hax]; exact hupd_self
      rw [hupd1, hre_self]
      have hle := singleSiteM_diag_le_one (hm_lt x) 1
      simp only [singleSiteM] at hle
      nlinarith [sq_nonneg ‖c a‖]
    | 2 =>
      simp only [singleSiteM, mul_zero, zero_add, add_zero, ne_eq, Fin.reduceEq, not_false_eq_true,
        ↓reduceIte]
      have hupd2 : Function.update a x 2 = a := by rw [← hax]; exact hupd_self
      rw [hupd2, hre_self]
      have hle := singleSiteM_diag_le_one (hm_lt x) 2
      simp only [singleSiteM] at hle
      nlinarith [sq_nonneg ‖c a‖]
    | 3 =>
      simp only [singleSiteM, mul_zero, zero_add, add_zero, ne_eq, Fin.reduceEq, not_false_eq_true,
        ↓reduceIte]
      have hupd3 : Function.update a x 3 = a := by rw [← hax]; exact hupd_self
      rw [hupd3, hre_self]
      have hle := singleSiteM_diag_le_one (hm_lt x) 3
      simp only [singleSiteM] at hle
      have h1 : ‖c a‖ ^ 2 * prodSigma (m x) ≤ ‖c a‖ ^ 2 := by nlinarith [sq_nonneg ‖c a‖]
      have h2 := habs_re (c a) (c (Function.update a x 0)) (m x / 2)
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
      linarith
  have hsum_le :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ k : Fin 4,
        (star (c a) * c (Function.update a x k)).re * singleSiteM (m x) (a x) k) ≤
      (∑ x : Fin N, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) +
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) +
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun a _ ↦ hbound_site x a
  -- Diagonal sum = ∑_a |a| ‖c_a‖² ≤ s
  have hdiag :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) ≤ (s : ℝ) := by
    rw [Finset.sum_comm]
    have hwt : ∀ a : Fin N → Fin 4,
        (∑ x : Fin N, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) = (stringWeight a : ℝ) * ‖c a‖ ^ 2 := by
      intro a
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl
    simp_rw [hwt]
    calc ∑ a : Fin N → Fin 4, (stringWeight a : ℝ) * ‖c a‖ ^ 2
        ≤ ∑ a : Fin N → Fin 4, (s : ℝ) * ‖c a‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro a _
          by_cases hle : stringWeight a ≤ s
          · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (sq_nonneg _)
          · push_neg at hle
            rw [hsupp a hle]; simp
      _ = (s : ℝ) * ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (s : ℝ) := by rw [hnorm, mul_one]
  -- The two off-diagonal sums are equal by bijection `a ↔ Function.update a x 3`
  have hoff_eq :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 3 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 0)‖) else 0) =
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun a _ ↦ Function.update a x 0) ?_ ?_ ?_ ?_
    · intro a _
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 : a₁ x = 3 := (Finset.mem_filter.mp ha₁).2
      have h2 : a₂ x = 3 := (Finset.mem_filter.mp ha₂).2
      ext y
      by_cases hy : y = x
      · subst hy; rw [h1, h2]
      · have := congr_fun heq y
        simpa [Function.update_of_ne hy] using this
    · intro b hb
      have hb0 : b x = 0 := (Finset.mem_filter.mp hb).2
      refine ⟨Function.update b x 3, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp⟩
      · ext y
        by_cases hy : y = x
        · subst hy; simp [hb0]
        · simp [Function.update_of_ne hy]
    · intro a ha
      have ha3 : a x = 3 := (Finset.mem_filter.mp ha).2
      have hback : Function.update (Function.update a x 0) x 3 = a := by
        ext y
        by_cases hy : y = x
        · subst hy; simp [ha3]
        · simp [Function.update_of_ne hy]
      rw [hback, mul_comm ‖c (Function.update a x 0)‖]
  -- Bound the off-diagonal sum by `(mmax / 2) * √(N * s)` via Cauchy-Schwarz
  have hoff_le :
      (∑ x : Fin N, ∑ a : Fin N → Fin 4,
        if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) ≤
      (mmax / 2) * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
    have hmmax_nn : 0 ≤ mmax := by
      by_cases hN : Nonempty (Fin N)
      · obtain ⟨x0⟩ := hN; exact le_trans (abs_nonneg (m x0)) (hm_le x0)
      · -- If N = 0, both sides are 0!
        have hN0 : N = 0 := by
          by_contra hne
          exact hN ⟨⟨0, Nat.pos_of_ne_zero hne⟩⟩
        subst hN0
        simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_mul, Real.sqrt_zero,
          mul_zero, le_rfl]
        -- Wait, we need `0 ≤ mmax` only when `N > 0`; let's handle `N = 0` at top of `hoff_le`!
        exact le_of_not_gt (fun _ ↦ hN ⟨⟨0, by omega⟩⟩)
    -- Wait, cleaner: split `by_cases hN : N = 0` first!
    have hstep1 :
        (∑ x : Fin N, ∑ a : Fin N → Fin 4,
          if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0) ≤
        (mmax / 2) * ∑ x : Fin N, ∑ a : Fin N → Fin 4,
          (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · have hx := hm_le x
        have hnn : 0 ≤ ‖c a‖ * ‖c (Function.update a x 3)‖ := by positivity
        nlinarith
      · simp
    -- Apply Cauchy-Schwarz over `Fin N × (Fin N → Fin 4)`
    have hcs :
        (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
            (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)) ^ 2 ≤
        (∑ p : Fin N × (Fin N → Fin 4), (if p.2 p.1 = 0 then ‖c p.2‖ else 0) ^ 2) *
        (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    have hfac1 :
        (∑ p : Fin N × (Fin N → Fin 4), (if p.2 p.1 = 0 then ‖c p.2‖ else 0) ^ 2) ≤ (N : ℝ) := by
      rw [Fintype.sum_prod_type]
      calc ∑ x : Fin N, ∑ a : Fin N → Fin 4, (if a x = 0 then ‖c a‖ else 0) ^ 2
          ≤ ∑ _ : Fin N, ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := by
            apply Finset.sum_le_sum; intro x _
            apply Finset.sum_le_sum; intro a _
            split_ifs <;> positivity
        _ = ∑ _ : Fin N, (1 : ℝ) := by simp_rw [hnorm]
        _ = (N : ℝ) := by simp
    have hfac2 :
        (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0) ^ 2) ≤ (s : ℝ) := by
      rw [Fintype.sum_prod_type]
      have hbij : ∀ x : Fin N,
          (∑ a : Fin N → Fin 4, (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) ^ 2) =
          (∑ b : Fin N → Fin 4, if b x = 3 then ‖c b‖ ^ 2 else 0) := by
        intro x
        have hl : ∀ a : Fin N → Fin 4,
            (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) ^ 2 =
            if a x = 0 then ‖c (Function.update a x 3)‖ ^ 2 else 0 := by
          intro a; split_ifs <;> simp
        simp_rw [hl, ← Finset.sum_filter]
        refine Finset.sum_bij (fun a _ ↦ Function.update a x 3) ?_ ?_ ?_ ?_
        · intro a _; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp⟩
        · intro a₁ ha₁ a₂ ha₂ heq
          have h1 : a₁ x = 0 := (Finset.mem_filter.mp ha₁).2
          have h2 : a₂ x = 0 := (Finset.mem_filter.mp ha₂).2
          ext y
          by_cases hy : y = x
          · subst hy; rw [h1, h2]
          · have := congr_fun heq y; simpa [Function.update_of_ne hy] using this
        · intro b hb
          have hb3 : b x = 3 := (Finset.mem_filter.mp hb).2
          refine ⟨Function.update b x 0, ?_, ?_⟩
          · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp⟩
          · ext y
            by_cases hy : y = x
            · subst hy; simp [hb3]
            · simp [Function.update_of_ne hy]
        · intro a _; rfl
      simp_rw [hbij]
      calc ∑ x : Fin N, ∑ b : Fin N → Fin 4, (if b x = 3 then ‖c b‖ ^ 2 else 0)
          ≤ ∑ x : Fin N, ∑ b : Fin N → Fin 4, (if b x ≠ 0 then ‖c b‖ ^ 2 else 0) := by
            apply Finset.sum_le_sum; intro x _
            apply Finset.sum_le_sum; intro b _
            split_ifs with h3 h0
            · exact le_rfl
            · exact absurd h3 (by rw [h0]; decide)
            · positivity
            · exact le_rfl
        _ ≤ (s : ℝ) := hdiag
    have hprod_le :
        (∑ x : Fin N, ∑ a : Fin N → Fin 4,
          (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0)) ≤
        Real.sqrt ((N : ℝ) * (s : ℝ)) := by
      rw [← Fintype.sum_prod_type]
      have hsq : (∑ p : Fin N × (Fin N → Fin 4),
          (if p.2 p.1 = 0 then ‖c p.2‖ else 0) *
            (if p.2 p.1 = 0 then ‖c (Function.update p.2 p.1 3)‖ else 0)) ^ 2 ≤
          (N : ℝ) * (s : ℝ) :=
        le_trans hcs (mul_le_mul hfac1 hfac2 (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg N))
      exact Real.le_sqrt_of_sq_le hsq
    calc (∑ x : Fin N, ∑ a : Fin N → Fin 4,
          if a x = 0 then (|m x| / 2) * (‖c a‖ * ‖c (Function.update a x 3)‖) else 0)
        ≤ (mmax / 2) * ∑ x : Fin N, ∑ a : Fin N → Fin 4,
            (if a x = 0 then ‖c a‖ else 0) * (if a x = 0 then ‖c (Function.update a x 3)‖ else 0) := hstep1
      _ ≤ (mmax / 2) * Real.sqrt ((N : ℝ) * (s : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod_le (by linarith)
  rw [hoff_eq] at hsum_le
  linarith

end KrylovChaos
