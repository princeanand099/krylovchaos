/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Ground-Up Proof of Carleman's Essential Self-Adjointness Criterion for Jacobi Operators

Proves from scratch (using only Mathlib, zero external axioms or literature hypotheses):
1. **Linear-growth Carleman divergence**: If `0 < b n ≤ α n + γ` for `n ≥ 1`, then
   `∑ 1 / b(n + 1) = ∞` (`carleman_divergence_of_linear_growth`).
2. **Carleman deficiency-index-zero theorem** (`carleman_deficiency_zero`): For any symmetric
   tridiagonal Jacobi operator `J` with `b 0 = 0`, `b n > 0` (`n ≥ 1`), and `∑ 1 / b(n + 1) = ∞`,
   every `ℓ²(ℕ)` solution to `J* u = (s i) u` (`s ≠ 0`) vanishes identically (`u ≡ 0`).
   Hence `ker(J* ± i I) = {0}` and `J` is essentially self-adjoint on `c_{00}(ℕ) ⊂ ℓ²(ℕ)`.
3. **Carleman flux vanishing** (`carleman_flux_liminf_zero`): For any `ψ ∈ ℓ²(ℕ)` and
   `∑ 1 / b(n + 1) = ∞`, `liminf_{N → ∞} b(N + 1) |ψ_N ψ_{N+1}| = 0`.
-/

namespace KrylovChaos

/-- Linear growth `0 < b n ≤ α n + γ` implies Carleman's divergence condition
`¬ Summable (fun n ↦ 1 / b (n + 1))`. -/
theorem carleman_divergence_of_linear_growth {α γ : ℝ} (b : ℕ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb_pos : ∀ n ≥ 1, 0 < b n)
    (hb_lin : ∀ n ≥ 1, b n ≤ α * (n : ℝ) + γ) :
    ¬ Summable (fun n : ℕ ↦ 1 / b (n + 1)) := by
  intro hsum
  have hc_pos : 0 < α + γ := by linarith
  have hle : ∀ n : ℕ,
      (α + γ)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ)) ≤ 1 / b (n + 1) := by
    intro n
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    have hbn : 0 < b (n + 1) := hb_pos (n + 1) (by omega)
    have hbd : b (n + 1) ≤ (α + γ) * ((n + 1 : ℕ) : ℝ) := by
      have h1 := hb_lin (n + 1) (by omega)
      nlinarith
    rw [show (α + γ)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ)) = 1 / ((α + γ) * ((n + 1 : ℕ) : ℝ)) by
      field_simp [hc_pos.ne', (by linarith : ((n + 1 : ℕ) : ℝ) ≠ 0)]]
    exact one_div_le_one_div_of_le hbn hbd
  have hsum_scaled : Summable (fun n : ℕ ↦ (α + γ)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity) hle hsum
  have hsum_shift : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    have h1 := hsum_scaled.mul_left (α + γ)
    refine h1.congr fun n ↦ ?_
    field_simp [hc_pos.ne']
  have hsum_harm : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff 1).mp hsum_shift
  exact Real.not_summable_one_div_natCast hsum_harm

/-- **Carleman's Essential Self-Adjointness Criterion (Deficiency Indices `(0, 0)`)**:
If `b 0 = 0`, `b n > 0` for `n ≥ 1`, and `¬ Summable (fun n ↦ 1 / b (n + 1))`, then for every
nonzero real `s` (in particular `s = ±1`), the only `ℓ²(ℕ)` solution to the formal adjoint
eigenvalue equation `b n * u (n - 1) + b (n + 1) * u (n + 1) = (s i) u n` is `u ≡ 0`. -/
theorem carleman_deficiency_zero {s : ℝ} (hs : s ≠ 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb_pos : ∀ n ≥ 1, 0 < b n)
    (hcarl : ¬ Summable (fun n : ℕ ↦ 1 / b (n + 1)))
    (u : ℕ → ℂ) (hu_l2 : Summable (fun n : ℕ ↦ ‖u n‖ ^ 2))
    (heig : ∀ n : ℕ, (b n : ℂ) * u (n - 1) + (b (n + 1) : ℂ) * u (n + 1) =
      (s : ℂ) * Complex.I * u n) :
    ∀ n : ℕ, u n = 0 := by
  let W : ℕ → ℝ := fun n ↦ b (n + 1) * (star (u n) * u (n + 1)).im
  have him_norm : ∀ z : ℂ, (star z * ((s : ℂ) * Complex.I * z)).im = s * ‖z‖ ^ 2 := by
    intro z
    have h1 : star z * ((s : ℂ) * Complex.I * z) =
        ((s * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
      have hconj : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      calc star z * ((s : ℂ) * Complex.I * z)
          = (s : ℂ) * (star z * z) * Complex.I := by ring
        _ = (s : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I := by rw [hconj]
        _ = ((s * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1]
    simp [Complex.mul_im]
  have hW_step : ∀ N : ℕ, W N = s * ∑ k ∈ Finset.range (N + 1), ‖u k‖ ^ 2 := by
    intro N
    induction N with
    | zero =>
      have h0 := heig 0
      rw [hb0, Complex.ofReal_zero, zero_mul, zero_add] at h0
      have hmul : star (u 0) * ((b 1 : ℂ) * u 1) = star (u 0) * ((s : ℂ) * Complex.I * u 0) :=
        congrArg (star (u 0) * ·) h0
      have him := congrArg Complex.im hmul
      have hlhs : (star (u 0) * ((b 1 : ℂ) * u 1)).im = b 1 * (star (u 0) * u 1).im := by
        rw [show star (u 0) * ((b 1 : ℂ) * u 1) = (b 1 : ℂ) * (star (u 0) * u 1) by ring]
        simp [Complex.mul_im]
      have hrhs : (star (u 0) * ((s : ℂ) * Complex.I * u 0)).im = s * ‖u 0‖ ^ 2 := him_norm (u 0)
      simp only [W, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
      linarith
    | succ N ih =>
      have hN := heig (N + 1)
      simp only [Nat.add_sub_cancel] at hN
      have hmul : star (u (N + 1)) * ((b (N + 1) : ℂ) * u N + (b (N + 2) : ℂ) * u (N + 2)) =
          star (u (N + 1)) * ((s : ℂ) * Complex.I * u (N + 1)) :=
        congrArg (star (u (N + 1)) * ·) hN
      have him := congrArg Complex.im hmul
      have hskew : (star (u (N + 1)) * u N).im = -(star (u N) * u (N + 1)).im := by
        have hconj : star (star (u N) * u (N + 1)) = star (u (N + 1)) * u N := by
          simp [mul_comm]
        rw [← hconj, Complex.star_def, Complex.conj_im]
      have hlhs : (star (u (N + 1)) * ((b (N + 1) : ℂ) * u N + (b (N + 2) : ℂ) * u (N + 2))).im =
          W (N + 1) - W N := by
        rw [mul_add, Complex.add_im]
        have h1 : (star (u (N + 1)) * ((b (N + 1) : ℂ) * u N)).im = -W N := by
          rw [show star (u (N + 1)) * ((b (N + 1) : ℂ) * u N) =
            (b (N + 1) : ℂ) * (star (u (N + 1)) * u N) by ring]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            hskew, W]
          ring
        have h2 : (star (u (N + 1)) * ((b (N + 2) : ℂ) * u (N + 2))).im = W (N + 1) := by
          rw [show star (u (N + 1)) * ((b (N + 2) : ℂ) * u (N + 2)) =
            (b (N + 2) : ℂ) * (star (u (N + 1)) * u (N + 2)) by ring]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, W]
        linarith
      have hrhs : (star (u (N + 1)) * ((s : ℂ) * Complex.I * u (N + 1))).im =
          s * ‖u (N + 1)‖ ^ 2 := him_norm (u (N + 1))
      rw [Finset.sum_range_succ, mul_add]
      linarith
  intro n₀
  by_contra hne
  have hS0_pos : 0 < |s| * ‖u n₀‖ ^ 2 := by
    have h1 : 0 < |s| := abs_pos.mpr hs
    have h2 : 0 < ‖u n₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    positivity
  have hbound : ∀ k : ℕ,
      (|s| * ‖u n₀‖ ^ 2) * (1 / b (k + n₀ + 1)) ≤
        (‖u (k + n₀)‖ ^ 2 + ‖u (k + n₀ + 1)‖ ^ 2) / 2 := by
    intro k
    set N := k + n₀
    have hmem : n₀ ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hsum_ge : ‖u n₀‖ ^ 2 ≤ ∑ j ∈ Finset.range (N + 1), ‖u j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j ↦ ‖u j‖ ^ 2) (fun j _ ↦ sq_nonneg _) hmem
    have hW_ge : |s| * ‖u n₀‖ ^ 2 ≤ |W N| := by
      rw [hW_step N, abs_mul]
      have hnn : 0 ≤ ∑ j ∈ Finset.range (N + 1), ‖u j‖ ^ 2 :=
        Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      rw [abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hsum_ge (abs_nonneg s)
    have hW_le : |W N| ≤ b (N + 1) * ((‖u N‖ ^ 2 + ‖u (N + 1)‖ ^ 2) / 2) := by
      have hbN : 0 < b (N + 1) := hb_pos (N + 1) (by omega)
      simp only [W, abs_mul, abs_of_pos hbN]
      apply mul_le_mul_of_nonneg_left _ hbN.le
      calc |(star (u N) * u (N + 1)).im|
          ≤ ‖star (u N) * u (N + 1)‖ := Complex.abs_im_le_norm _
        _ = ‖u N‖ * ‖u (N + 1)‖ := by rw [norm_mul, norm_star]
        _ ≤ (‖u N‖ ^ 2 + ‖u (N + 1)‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖u N‖ - ‖u (N + 1)‖)]
    have hbN : 0 < b (N + 1) := hb_pos (N + 1) (by omega)
    have hcomb := le_trans hW_ge hW_le
    rw [mul_one_div, div_le_iff₀ hbN]
    linarith
  have hsum_rhs : Summable (fun k : ℕ ↦ (‖u (k + n₀)‖ ^ 2 + ‖u (k + n₀ + 1)‖ ^ 2) / 2) := by
    have h1 : Summable (fun k : ℕ ↦ ‖u (k + n₀)‖ ^ 2) := (summable_nat_add_iff n₀).mpr hu_l2
    have h2 : Summable (fun k : ℕ ↦ ‖u (k + (n₀ + 1))‖ ^ 2) :=
      (summable_nat_add_iff (n₀ + 1)).mpr hu_l2
    have h2' : Summable (fun k : ℕ ↦ ‖u (k + n₀ + 1)‖ ^ 2) :=
      h2.congr fun k ↦ by congr 2; omega
    exact (h1.add h2').div_const 2
  have hsum_scaled : Summable (fun k : ℕ ↦ (|s| * ‖u n₀‖ ^ 2) * (1 / b (k + n₀ + 1))) :=
    Summable.of_nonneg_of_le (fun k ↦ by
      have := hb_pos (k + n₀ + 1) (by omega); positivity) hbound hsum_rhs
  have hsum_shift : Summable (fun k : ℕ ↦ 1 / b (k + n₀ + 1)) := by
    have h1 := hsum_scaled.mul_left (|s| * ‖u n₀‖ ^ 2)⁻¹
    refine h1.congr fun k ↦ ?_
    field_simp [hS0_pos.ne']
  have hsum_all : Summable (fun n : ℕ ↦ 1 / b (n + 1)) :=
    (summable_nat_add_iff n₀).mp (hsum_shift.congr fun k ↦ by congr 2; omega)
  exact hcarl hsum_all

/-- **Carleman Flux Vanishing**: If `b n > 0` (`n ≥ 1`), `¬ Summable (fun n ↦ 1 / b (n + 1))`,
and `ψ ∈ ℓ²(ℕ)`, then `liminf_{N → ∞} b (N + 1) * |ψ N * ψ (N + 1)| = 0`. -/
theorem carleman_flux_liminf_zero (b ψ : ℕ → ℝ)
    (hb_pos : ∀ n ≥ 1, 0 < b n)
    (hcarl : ¬ Summable (fun n : ℕ ↦ 1 / b (n + 1)))
    (hψ : Summable (fun n : ℕ ↦ (ψ n) ^ 2)) :
    ∀ ε > 0, ∀ N₀ : ℕ, ∃ N ≥ N₀, b (N + 1) * |ψ N * ψ (N + 1)| < ε := by
  intro ε hε N₀
  by_contra hno
  have hge : ∀ k : ℕ, ε ≤ b (k + N₀ + 1) * |ψ (k + N₀) * ψ (k + N₀ + 1)| := by
    intro k
    by_contra hlt
    exact hno ⟨k + N₀, by omega, lt_of_not_ge hlt⟩
  have hle : ∀ k : ℕ,
      ε * (1 / b (k + N₀ + 1)) ≤ ((ψ (k + N₀)) ^ 2 + (ψ (k + N₀ + 1)) ^ 2) / 2 := by
    intro k
    have hb : 0 < b (k + N₀ + 1) := hb_pos (k + N₀ + 1) (by omega)
    have h1 := hge k
    have h2 : |ψ (k + N₀) * ψ (k + N₀ + 1)| ≤
        ((ψ (k + N₀)) ^ 2 + (ψ (k + N₀ + 1)) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|ψ (k + N₀)| - |ψ (k + N₀ + 1)|),
        sq_abs (ψ (k + N₀)), sq_abs (ψ (k + N₀ + 1))]
    rw [mul_one_div, div_le_iff₀ hb]
    have h3 := mul_le_mul_of_nonneg_left h2 hb.le
    linarith
  have hsum_rhs : Summable (fun k : ℕ ↦ ((ψ (k + N₀)) ^ 2 + (ψ (k + N₀ + 1)) ^ 2) / 2) := by
    have h1 : Summable (fun k : ℕ ↦ (ψ (k + N₀)) ^ 2) := (summable_nat_add_iff N₀).mpr hψ
    have h2 : Summable (fun k : ℕ ↦ (ψ (k + (N₀ + 1))) ^ 2) :=
      (summable_nat_add_iff (N₀ + 1)).mpr hψ
    have h2' : Summable (fun k : ℕ ↦ (ψ (k + N₀ + 1)) ^ 2) :=
      h2.congr fun k ↦ by congr 2; omega
    exact (h1.add h2').div_const 2
  have hsum_scaled : Summable (fun k : ℕ ↦ ε * (1 / b (k + N₀ + 1))) :=
    Summable.of_nonneg_of_le (fun k ↦ by
      have := hb_pos (k + N₀ + 1) (by omega); positivity) hle hsum_rhs
  have hsum_shift : Summable (fun k : ℕ ↦ 1 / b (k + N₀ + 1)) := by
    have h1 := hsum_scaled.mul_left ε⁻¹
    refine h1.congr fun k ↦ ?_
    field_simp [hε.ne']
  have hsum_all : Summable (fun n : ℕ ↦ 1 / b (n + 1)) :=
    (summable_nat_add_iff N₀).mp (hsum_shift.congr fun k ↦ by congr 2; omega)
  exact hcarl hsum_all

end KrylovChaos
