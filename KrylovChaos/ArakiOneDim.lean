/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Ground-Up Proof of Araki's 1D Complex-Time Analyticity Structural Bounds

Proves from scratch (using only Mathlib, zero external axioms or literature hypotheses)
the core 1D structural ingredients of Araki's (1969) imaginary-time analyticity theorem:
1. `araki_1d_boundary_count`: On any 1D chain `Fin N` with interaction range `r ≥ 1`, the
   number of `r`-local interaction blocks `[j, j + r - 1]` crossing the boundary of any
   contiguous interval `[a, b]` is at most `2 * (r - 1)`, strictly independent of `N` and `b - a`.
2. `araki_1d_block_commutator_indep`: If `H = H_B + H_env` with `[H_env, A] = 0` and
   `[H_env, H_B] = 0`, then every iterated commutator `ad_H^m(A)` equals `ad_{H_B}^m(A)`,
   strictly independent of the environment `H_env`.
3. `araki_1d_entire_expansional`: Any 1D Araki–Dyson power series `∑_{m=0}^∞ (τ^m / m!) a_m`
   whose coefficients satisfy `‖a_m‖ ≤ C₀ C₁^m` converges absolutely for **all** `τ ∈ ℂ`
   (entire in complex time, i.e., valid for arbitrary inverse temperature `β > 0`) with
   norm bound `≤ C₀ exp(C₁ ‖τ‖)`.
-/

namespace KrylovChaos

/-- Iterated matrix commutator `ad_H^m(A)`. -/
def iterMatComm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ → Matrix ι ι ℂ
  | 0, A => A
  | m + 1, A => H * iterMatComm H m A - iterMatComm H m A * H

/-- **1D Constant-Boundary-Size Bound**:
On a 1D chain of length `N`, the set of starting sites `j : ℕ` of `r`-local blocks
`{j, j+1, ..., j+r-1}` that straddle either endpoint of a contiguous interval `[a, b]`
(i.e. `j < a ∧ a < j + r` or `j ≤ b ∧ b + 1 < j + r`) has cardinality at most `2 * (r - 1)`,
strictly independent of `N`, `a`, and `b`. -/
theorem araki_1d_boundary_count (N r a b : ℕ) (hr : 1 ≤ r) :
    ((Finset.range N).filter (fun j ↦ (j < a ∧ a < j + r) ∨ (j ≤ b ∧ b + 1 < j + r))).card ≤
      2 * (r - 1) := by
  set L := Finset.Ico (a - (r - 1)) a
  set R := Finset.Ico (b + 1 - (r - 1)) (b + 1)
  have hsub : (Finset.range N).filter
      (fun j ↦ (j < a ∧ a < j + r) ∨ (j ≤ b ∧ b + 1 < j + r)) ⊆ L ∪ R := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_union_left R (Finset.mem_Ico.mpr ⟨by omega, h1⟩)
    · exact Finset.mem_union_right L (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hcardL : L.card ≤ r - 1 := by
    simp only [L, Nat.card_Ico]; omega
  have hcardR : R.card ≤ r - 1 := by
    simp only [R, Nat.card_Ico]; omega
  calc ((Finset.range N).filter
        (fun j ↦ (j < a ∧ a < j + r) ∨ (j ≤ b ∧ b + 1 < j + r))).card
      ≤ (L ∪ R).card := Finset.card_le_card hsub
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ (r - 1) + (r - 1) := add_le_add hcardL hcardR
    _ = 2 * (r - 1) := by omega

/-- **1D Block-Environment Commutator Independence**:
If `H_env` commutes with both `H_B` and `A`, then for every `m : ℕ`,
`ad_{H_B + H_env}^m(A) = ad_{H_B}^m(A)`. -/
theorem araki_1d_block_commutator_indep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H_B H_env A : Matrix ι ι ℂ)
    (hcommA : H_env * A = A * H_env)
    (hcommB : H_env * H_B = H_B * H_env) :
    ∀ m : ℕ,
      iterMatComm (H_B + H_env) m A = iterMatComm H_B m A ∧
      H_env * iterMatComm H_B m A = iterMatComm H_B m A * H_env := by
  intro m
  induction m with
  | zero => exact ⟨rfl, hcommA⟩
  | succ m ih =>
    rcases ih with ⟨heq, hcomm⟩
    constructor
    · simp only [iterMatComm, heq, add_mul, mul_add, hcomm]
      abel
    · simp only [iterMatComm, mul_sub, sub_mul]
      have h1 : H_env * (H_B * iterMatComm H_B m A) = (H_B * iterMatComm H_B m A) * H_env := by
        calc H_env * (H_B * iterMatComm H_B m A)
            = (H_env * H_B) * iterMatComm H_B m A := by rw [Matrix.mul_assoc]
          _ = (H_B * H_env) * iterMatComm H_B m A := by rw [hcommB]
          _ = H_B * (H_env * iterMatComm H_B m A) := by rw [Matrix.mul_assoc]
          _ = H_B * (iterMatComm H_B m A * H_env) := by rw [hcomm]
          _ = (H_B * iterMatComm H_B m A) * H_env := by rw [Matrix.mul_assoc]
      have h2 : H_env * (iterMatComm H_B m A * H_B) = (iterMatComm H_B m A * H_B) * H_env := by
        calc H_env * (iterMatComm H_B m A * H_B)
            = (H_env * iterMatComm H_B m A) * H_B := by rw [Matrix.mul_assoc]
          _ = (iterMatComm H_B m A * H_env) * H_B := by rw [hcomm]
          _ = iterMatComm H_B m A * (H_env * H_B) := by rw [Matrix.mul_assoc]
          _ = iterMatComm H_B m A * (H_B * H_env) := by rw [hcommB]
          _ = (iterMatComm H_B m A * H_B) * H_env := by rw [Matrix.mul_assoc]
      rw [h1, h2]

/-- **Araki 1D Entire Complex-Time Expansional Convergence**:
For any Banach space `E` and any sequence `a : ℕ → E` satisfying the 1D Araki coefficient
bound `‖a m‖ ≤ C₀ * C₁ ^ m` (`C₀ ≥ 0`, `C₁ ≥ 0`), the complex-time Dyson/expansional series
`∑_{m=0}^∞ (τ^m / m!) • a_m` converges absolutely for **all** `τ : ℂ` (arbitrary `β > 0`)
and satisfies `‖∑' m, (τ^m / m!) • a_m‖ ≤ C₀ * Real.exp (C₁ * ‖τ‖)`. -/
theorem araki_1d_entire_expansional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (a : ℕ → E) (ha : ∀ m : ℕ, ‖a m‖ ≤ C₀ * C₁ ^ m) (τ : ℂ) :
    Summable (fun m : ℕ ↦ (τ ^ m / (m.factorial : ℂ)) • a m) ∧
    ‖∑' m : ℕ, (τ ^ m / (m.factorial : ℂ)) • a m‖ ≤ C₀ * Real.exp (C₁ * ‖τ‖) := by
  have hterm : ∀ m : ℕ,
      ‖(τ ^ m / (m.factorial : ℂ)) • a m‖ ≤ C₀ * ((C₁ * ‖τ‖) ^ m / (m.factorial : ℝ)) := by
    intro m
    rw [norm_smul, norm_div, norm_pow, Complex.norm_natCast]
    have h1 := mul_le_mul_of_nonneg_left (ha m)
      (div_nonneg (pow_nonneg (norm_nonneg τ) m) (Nat.cast_nonneg _))
    calc ‖τ‖ ^ m / (m.factorial : ℝ) * ‖a m‖
        ≤ ‖τ‖ ^ m / (m.factorial : ℝ) * (C₀ * C₁ ^ m) := h1
      _ = C₀ * ((C₁ * ‖τ‖) ^ m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
  have hexp_summ : Summable (fun m : ℕ ↦ C₀ * ((C₁ * ‖τ‖) ^ m / (m.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (C₁ * ‖τ‖)).mul_left C₀
  have hnorm_summ : Summable (fun m : ℕ ↦ ‖(τ ^ m / (m.factorial : ℂ)) • a m‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hexp_summ
  have hsumm : Summable (fun m : ℕ ↦ (τ ^ m / (m.factorial : ℂ)) • a m) :=
    Summable.of_norm_bounded hexp_summ hterm
  refine ⟨hsumm, ?_⟩
  calc ‖∑' m : ℕ, (τ ^ m / (m.factorial : ℂ)) • a m‖
      ≤ ∑' m : ℕ, ‖(τ ^ m / (m.factorial : ℂ)) • a m‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' m : ℕ, C₀ * ((C₁ * ‖τ‖) ^ m / (m.factorial : ℝ)) :=
        Summable.tsum_le_tsum hterm hnorm_summ hexp_summ
    _ = C₀ * ∑' m : ℕ, (C₁ * ‖τ‖) ^ m / (m.factorial : ℝ) := tsum_mul_left
    _ = C₀ * Real.exp (C₁ * ‖τ‖) := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

end KrylovChaos
