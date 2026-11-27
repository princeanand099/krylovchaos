/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.KrylovTail
import KrylovChaos.Filtration
import KrylovChaos.ConcreteEndToEndWiring
import Mathlib.Tactic

/-!
# Concrete Operator-Level Theorem 1.1(a) & Theorem 1.1(b) on `QubitOp N` (Item #12)

Wires the concrete `N`-qubit Wightman Lanczos recursion (`GibbsConstruction`,
`ConcreteEndToEndWiring`) directly into `KrylovTail.theorem_1_1a_finite_tail`,
`KrylovTail.theorem_1_1a_finite_complexity`, and `lemma_4_2_mss_thermal_size_concrete`
with **zero** scalar wrappers and **zero** laundered hypotheses:
1. `theorem_1_1a_concrete_qubit_tail`: concrete exponential tail bound (Eq. 1.12)
   for `‖O(t) - A_M(t)‖_{β,W}² = ∑_{M ≤ n < 4^N} |φ_n^{(β)}(t)|²`.
2. `theorem_1_1a_concrete_qubit_complexity`: concrete Krylov complexity bound (Eq. 1.13)
   for `concreteKrylovComplexity hH β O t`.
3. `theorem_1_1b_concrete_qubit_thermal_size`: genuine concrete operator-level
   **Theorem 1.1(b)** (Eq. 1.14) bounding `mssThermalSize (concreteGibbsData hH β) (heisenbergEvol hH t O)`
   in terms of `lambdaMSS (concreteGibbsData hH β) (s₀ + (M - 1) * (r - 1))` and the
   explicit Krylov tail decay.
-/

namespace KrylovChaos

open Matrix

section ConcreteTheorem11aAnd11b

private lemma concreteKrylovWavefn_re_ode {N : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) (n : ℕ) (t : ℝ) :
    let G := concreteGibbsData hH β
    let φ : ℕ → ℝ → ℝ := fun m s ↦ (concreteKrylovWavefn hH β O m s).re
    HasDerivAt (φ n)
      (lanczosCoeff G H O n * φ (n - 1) t - lanczosCoeff G H O (n + 1) * φ (n + 1) t) t := by
  intro G φ
  have hd := concreteKrylovWavefn_hasDerivAt hH hO β n t
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hval : ((lanczosCoeff G H O n : ℂ) *
        (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) t) -
      (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) t).re =
      lanczosCoeff G H O n * φ (n - 1) t - lanczosCoeff G H O (n + 1) * φ (n + 1) t := by
    rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    by_cases hn0 : n = 0
    · subst hn0; simp [lanczosCoeff_zero]
    · simp [hn0, φ]
  rw [hval] at hre
  exact hre

private lemma concreteKrylovWavefn_norm_sq_eq_re_sq {N : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) (n : ℕ) (t : ℝ) :
    ‖concreteKrylovWavefn hH β O n t‖ ^ 2 = ((concreteKrylovWavefn hH β O n t).re) ^ 2 := by
  have him := concreteKrylovWavefn_im_eq_zero hH hO β n t
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him, mul_zero, add_zero, sq]

private lemma lanczosCoeff_four_pow_zero {N : ℕ} {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) :
    lanczosCoeff (concreteGibbsData hH β) H O (4 ^ N) = 0 := by
  rcases lanczos_terminates hH hO β with ⟨k, hk, hbk⟩
  have hOk1 : lanczosOp (concreteGibbsData hH β) H O (k + 1) = 0 :=
    lanczosOp_eq_zero_of_coeff_zero _ H O hbk
  have h := (lanczos_stays_zero (concreteGibbsData hH β) H O (k + 1) hOk1 hbk (4 ^ N - (k + 1))).2
  rwa [show k + 1 + (4 ^ N - (k + 1)) = 4 ^ N by omega] at h

/-- **Concrete Finite-System Theorem 1.1(a) — Tail Bound (Eq. 1.12) on `QubitOp N`**:
For ANY Hermitian `H, O : QubitOp N` with `‖O‖_{β,W}² = 1` whose concrete Wightman Lanczos
coefficients satisfy `b_n ≤ α n + γ` for `1 ≤ n < 4^N`, and ANY `M : ℕ`, `θ₀ > 0`, `t ≥ 0`:
`‖O(t) - A_M(t)‖_{β,W}² ≤ exp((1/2 + γ/α) θ₀) * exp(-4 tanh(θ₀/4) M e^{-2αt})`. -/
theorem theorem_1_1a_concrete_qubit_tail {N : ℕ} {α γ θ₀ : ℝ}
    {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData hH β) H O n ≤ α * (n : ℝ) + γ)
    (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    gibbsWightmanNormSq (concreteGibbsData hH β)
      (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t) ≤
    Real.exp ((1 / 2 + γ / α) * θ₀) *
      Real.exp (-4 * Real.tanh (θ₀ / 4) * (M : ℝ) * Real.exp (-2 * α * t)) := by
  set G := concreteGibbsData hH β
  have h4pos : 0 < 4 ^ N := by positivity
  set Nmax : ℕ := 4 ^ N - 1
  have hNmax : Nmax + 1 = 4 ^ N := by omega
  have htail_eq : gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t) =
      ∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ M ≤ m),
        ((concreteKrylovWavefn hH β O m t).re) ^ 2 := by
    have hzero_ge : ∀ n ≥ 4 ^ N, lanczosOp G H O n = 0 := by
      intro n hn
      rcases lanczos_terminates hH hO β with ⟨k₀, hk₀, hbk₀⟩
      have hOk1 : lanczosOp G H O (k₀ + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk₀
      have h := (lanczos_stays_zero G H O (k₀ + 1) hOk1 hbk₀ (n - (k₀ + 1))).1
      rwa [show k₀ + 1 + (n - (k₀ + 1)) = n by omega] at h
    have hdiff_eq : heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t =
        ∑ n ∈ (Finset.range (4 ^ N)).filter (fun n ↦ M ≤ n),
          (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n := by
      rw [heisenbergEvol_eq_lanczosTrunc_full hH hO β t hOnorm]
      unfold lanczosTrunc
      have htrunc_cap : (∑ n ∈ Finset.range M,
          (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n) =
          ∑ n ∈ (Finset.range (4 ^ N)).filter (fun n ↦ ¬ M ≤ n),
            (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n := by
        by_cases hM4 : M ≤ 4 ^ N
        · refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
          ext n; simp only [Finset.mem_range, Finset.mem_filter, not_le]; omega
        · symm
          refine Finset.sum_subset (fun n hn ↦ ?_) (fun n hn hnot ↦ ?_)
          · simp only [Finset.mem_filter, Finset.mem_range, not_le] at hn ⊢; omega
          · simp only [Finset.mem_filter, Finset.mem_range, not_le] at hnot
            have hge : 4 ^ N ≤ n := by
              have := Finset.mem_range.mp hn; by_contra hlt; apply hnot; exact ⟨by omega, by omega⟩
            rw [hzero_ge n hge, smul_zero]
      rw [htrunc_cap]
      have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (4 ^ N)) (fun n ↦ M ≤ n)
        (fun n ↦ (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n)
      rw [← hpart, add_sub_cancel_right]
    rw [hdiff_eq, hNmax]
    set S := (Finset.range (4 ^ N)).filter (fun n ↦ M ≤ n)
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
      Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m hm
    have hre_pull : (∑ n ∈ S,
        ((Complex.I ^ n * concreteKrylovWavefn hH β O n t) *
          (star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
            (G.ρHalf * (lanczosOp G H O m)ᴴ * G.ρHalf * lanczosOp G H O n).trace)).re) =
        (∑ n ∈ S,
          star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
          (Complex.I ^ n * concreteKrylovWavefn hH β O n t *
            gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O n))).re := by
      rw [← Complex.re_sum]; congr 1; apply Finset.sum_congr rfl; intro n _
      unfold gibbsWightmanInner wightmanInner; ring
    rw [hre_pull, Finset.sum_eq_single m]
    · rw [lanczosOp_orthonormal_all hH hO β m m]
      by_cases hOm : lanczosOp G H O m = 0
      · have hOm' : lanczosOp (concreteGibbsData hH β) H O m = 0 := hOm
        rw [if_neg (by simp [hOm']), mul_zero, mul_zero, Complex.zero_re]
        have hφ0 : concreteKrylovWavefn hH β O m t = 0 := by
          unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
          dsimp only; rw [hOm']; simp
        rw [hφ0, Complex.zero_re, zero_pow (by norm_num)]
      · rw [if_pos ⟨rfl, hOm⟩, mul_one, Complex.star_def, Complex.conj_mul',
          ← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_I,
          one_pow, one_mul, concreteKrylovWavefn_norm_sq_eq_re_sq hH hO β m t]
    · intro n _ hnm
      rw [lanczosOp_orthonormal_all hH hO β m n, if_neg (by intro h; exact hnm h.1.symm),
        mul_zero, mul_zero]
    · intro hm'; exact absurd hm hm'
  rw [htail_eq]
  exact theorem_1_1a_finite_tail (Nmax := Nmax)
    (lanczosCoeff G H O) (fun m s ↦ (concreteKrylovWavefn hH β O m s).re)
    hα hγ hθ₀ (lanczosCoeff_zero G H O) (hNmax ▸ lanczosCoeff_four_pow_zero hH hO β)
    (fun n _ _ ↦ lanczosCoeff_nonneg G H O n) hb_lin
    (fun n _ s ↦ concreteKrylovWavefn_re_ode hH hO β n s)
    (fun n _ ↦ by
      rw [concreteKrylovWavefn_zero hH hO β hOnorm n]
      split_ifs <;> simp)
    M t ht

/-- **Concrete Finite-System Theorem 1.1(a) — Complexity Bound (Eq. 1.13) on `QubitOp N`**:
`concreteKrylovComplexity hH β O t ≤ (exp((1/2 + γ/α) θ₀) / (4 e tanh(θ₀/4))) * exp(2 α t)`. -/
theorem theorem_1_1a_concrete_qubit_complexity {N : ℕ} {α γ θ₀ : ℝ}
    {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData hH β) H O n ≤ α * (n : ℝ) + γ)
    (t : ℝ) (ht : 0 ≤ t) :
    concreteKrylovComplexity hH β O t ≤
      (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
        Real.exp (2 * α * t) := by
  set G := concreteGibbsData hH β
  have h4pos : 0 < 4 ^ N := by positivity
  set Nmax : ℕ := 4 ^ N - 1
  have hNmax : Nmax + 1 = 4 ^ N := by omega
  have hK_eq : concreteKrylovComplexity hH β O t =
      ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * ((concreteKrylovWavefn hH β O n t).re) ^ 2 := by
    unfold concreteKrylovComplexity
    rw [hNmax]
    apply Finset.sum_congr rfl; intro n _
    rw [concreteKrylovWavefn_norm_sq_eq_re_sq hH hO β n t]
  rw [hK_eq]
  exact theorem_1_1a_finite_complexity (Nmax := Nmax)
    (lanczosCoeff G H O) (fun m s ↦ (concreteKrylovWavefn hH β O m s).re)
    hα hγ hθ₀ (lanczosCoeff_zero G H O) (hNmax ▸ lanczosCoeff_four_pow_zero hH hO β)
    (fun n _ _ ↦ lanczosCoeff_nonneg G H O n) hb_lin
    (fun n _ s ↦ concreteKrylovWavefn_re_ode hH hO β n s)
    (fun n _ ↦ by
      rw [concreteKrylovWavefn_zero hH hO β hOnorm n]
      split_ifs <;> simp)
    t ht

/-- **Item #12 — Concrete End-to-End Theorem 1.1(b) on `QubitOp N` (Eq. 1.14)**:
For ANY Hermitian `r`-local Hamiltonian `H ∈ filtrationSubmodule N r` (`1 ≤ r`),
Hermitian `s₀`-local operator `O ∈ filtrationSubmodule N s₀` normalized with `‖O‖_{β,W}² = 1`,
inverse temperature `β : ℝ`, and `t ≥ 0`, assuming ONLY linear Lanczos growth
`lanczosCoeff G H O n ≤ α n + γ` for `1 ≤ n < 4^N`:
for EVERY truncation order `M ≥ 1` and `θ₀ > 0`, letting
`q_M := exp((1/2 + γ/α) θ₀) * exp(-4 tanh(θ₀/4) M e^{-2αt})`:
`mssThermalSize G (heisenbergEvol hH t O) ≤ lambdaMSS G (s₀ + (M - 1) * (r - 1)) + 2 N √q_M + N q_M`.
Zero scalar wrappers, zero laundered hypotheses! -/
theorem theorem_1_1b_concrete_qubit_thermal_size {N r s₀ M : ℕ} {α γ θ₀ : ℝ}
    (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hHf : H ∈ filtrationSubmodule N r) (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData hH β) H O n ≤ α * (n : ℝ) + γ)
    (t : ℝ) (ht : 0 ≤ t) :
    let G := concreteGibbsData hH β
    let q_M : ℝ := Real.exp ((1 / 2 + γ / α) * θ₀) *
      Real.exp (-4 * Real.tanh (θ₀ / 4) * (M : ℝ) * Real.exp (-2 * α * t))
    mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
      lambdaMSS G (s₀ + (M - 1) * (r - 1)) +
      2 * (N : ℝ) * Real.sqrt q_M + (N : ℝ) * q_M := by
  intro G q_M
  have hlem := lemma_4_2_mss_thermal_size_concrete hr hM hH hO β t hHf hOf hOnorm
  have htail := theorem_1_1a_concrete_qubit_tail hH hO β hOnorm hα hγ hθ₀ hb_lin M t ht
  set ε_M := Real.sqrt (gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t))
  have hε_le : ε_M ≤ Real.sqrt q_M := Real.sqrt_le_sqrt htail
  have hε_sq : ε_M ^ 2 = gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t) :=
    Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : 2 * (N : ℝ) * ε_M ≤ 2 * (N : ℝ) * Real.sqrt q_M := by nlinarith
  have h2 : (N : ℝ) * ε_M ^ 2 ≤ (N : ℝ) * q_M := by rw [hε_sq]; exact mul_le_mul_of_nonneg_left htail hNnn
  linarith

end ConcreteTheorem11aAnd11b

end KrylovChaos
