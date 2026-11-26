/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 2: Wightman Isometry, MSS-OTOC Size Identities, and Nested Commutator Bounds

Formalizes:
- **Proposition 2.2**: The Wightman–Hilbert–Schmidt isometry `𝒥_β(A) = ρ^{1/4} A ρ^{1/4}`,
  its commutation with the Liouvillian `ℒ = [H, ·]`, and Liouvillian self-adjointness / zero diagonals.
- **Proposition 2.3**: Exact MSS-OTOC thermal-size identities for qubits (Eq. 2.9) and
  Majorana fermions (Eq. 2.10).
- **Lemma 2.1**: Causal nested-commutator induction (Eq. 2.3), single-site analyticity bound
  `≤ (1 - |τ|/(4κ))⁻¹` (Eq. 2.4), and `r`-local analyticity bound `≤ (1 - |τ|/(4κ))⁻²` (Eq. 2.5).
-/

open scoped Matrix

namespace KrylovChaos

section WightmanIsometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite-dimensional Wightman inner product `(A | B)_β^W = Tr(ρ^{1/2} A† ρ^{1/2} B)`. -/
def wightmanInner (ρHalf A B : Matrix ι ι ℂ) : ℂ :=
  (ρHalf * Aᴴ * ρHalf * B).trace

/-- Wightman-to-Hilbert–Schmidt isometry `𝒥_β(A) = ρ^{1/4} A ρ^{1/4}`. -/
def wightmanIsometry (ρQuarter A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ρQuarter * A * ρQuarter

/-- Liouvillian superoperator `ℒ(A) = H A - A H`. -/
def liouvillian (H A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  H * A - A * H

/-- **Proposition 2.2(1)** (Wightman–Hilbert–Schmidt Isometry):
If `ρ^{1/4}` is Hermitian and `(ρ^{1/4})² = ρ^{1/2}`, then
`Tr((𝒥_β(A))† 𝒥_β(B)) = (A | B)_β^W`. -/
theorem prop_2_2_wightman_isometry_inner (ρQuarter ρHalf A B : Matrix ι ι ℂ)
    (hHerm : ρQuarterᴴ = ρQuarter) (hSq : ρQuarter * ρQuarter = ρHalf) :
    ((wightmanIsometry ρQuarter A)ᴴ * wightmanIsometry ρQuarter B).trace =
      wightmanInner ρHalf A B := by
  unfold wightmanIsometry wightmanInner
  have h1 : (ρQuarter * A * ρQuarter)ᴴ = ρQuarter * Aᴴ * ρQuarter := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHerm, Matrix.mul_assoc]
  rw [h1]
  calc (ρQuarter * Aᴴ * ρQuarter * (ρQuarter * B * ρQuarter)).trace
      = (ρQuarter * (Aᴴ * (ρQuarter * ρQuarter) * B * ρQuarter)).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((Aᴴ * (ρQuarter * ρQuarter) * B * ρQuarter) * ρQuarter).trace :=
        Matrix.trace_mul_comm _ _
    _ = ((Aᴴ * ρHalf * B) * ρHalf).trace := by
        simp only [Matrix.mul_assoc, hSq]
    _ = (ρHalf * (Aᴴ * ρHalf * B)).trace := Matrix.trace_mul_comm _ _
    _ = (ρHalf * Aᴴ * ρHalf * B).trace := by simp only [Matrix.mul_assoc]

/-- **Proposition 2.2(2)** (Commutation of `𝒥_β` with `ℒ`):
If `H` commutes with `ρ^{1/4}`, then `𝒥_β(ℒ(A)) = ℒ(𝒥_β(A))`. -/
theorem prop_2_2_wightman_isometry_commutes_liouvillian (ρQuarter H A : Matrix ι ι ℂ)
    (hComm : H * ρQuarter = ρQuarter * H) :
    wightmanIsometry ρQuarter (liouvillian H A) =
      liouvillian H (wightmanIsometry ρQuarter A) := by
  unfold wightmanIsometry liouvillian
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc ρQuarter * (H * A) * ρQuarter
        = (ρQuarter * H) * A * ρQuarter := by simp only [Matrix.mul_assoc]
      _ = (H * ρQuarter) * A * ρQuarter := by rw [← hComm]
      _ = H * (ρQuarter * A * ρQuarter) := by simp only [Matrix.mul_assoc]
  · calc ρQuarter * (A * H) * ρQuarter
        = ρQuarter * A * (H * ρQuarter) := by simp only [Matrix.mul_assoc]
      _ = ρQuarter * A * (ρQuarter * H) := by rw [hComm]
      _ = ρQuarter * A * ρQuarter * H := by simp only [Matrix.mul_assoc]

/-- **Proposition 2.2(3)** (Self-Adjointness of `ℒ` in the Wightman Inner Product):
If `H† = H` and `H ρ^{1/2} = ρ^{1/2} H`, then `(ℒ A | B)_β^W = (A | ℒ B)_β^W`. -/
theorem prop_2_2_liouvillian_self_adjoint (ρHalf H A B : Matrix ι ι ℂ)
    (hH : Hᴴ = H) (hComm : H * ρHalf = ρHalf * H) :
    wightmanInner ρHalf (liouvillian H A) B = wightmanInner ρHalf A (liouvillian H B) := by
  unfold wightmanInner liouvillian
  have hAdj : (H * A - A * H)ᴴ = Aᴴ * H - H * Aᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH]
  rw [hAdj]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  have ht1 : (ρHalf * (Aᴴ * H) * ρHalf * B).trace = (ρHalf * Aᴴ * ρHalf * (H * B)).trace := by
    calc (ρHalf * (Aᴴ * H) * ρHalf * B).trace
        = (ρHalf * Aᴴ * (H * ρHalf) * B).trace := by simp only [Matrix.mul_assoc]
      _ = (ρHalf * Aᴴ * (ρHalf * H) * B).trace := by rw [hComm]
      _ = (ρHalf * Aᴴ * ρHalf * (H * B)).trace := by simp only [Matrix.mul_assoc]
  have ht2 : (ρHalf * (H * Aᴴ) * ρHalf * B).trace = (ρHalf * Aᴴ * ρHalf * (B * H)).trace := by
    calc (ρHalf * (H * Aᴴ) * ρHalf * B).trace
        = ((ρHalf * H) * (Aᴴ * ρHalf * B)).trace := by simp only [Matrix.mul_assoc]
      _ = ((H * ρHalf) * (Aᴴ * ρHalf * B)).trace := by rw [← hComm]
      _ = (H * (ρHalf * Aᴴ * ρHalf * B)).trace := by simp only [Matrix.mul_assoc]
      _ = ((ρHalf * Aᴴ * ρHalf * B) * H).trace := Matrix.trace_mul_comm _ _
      _ = (ρHalf * Aᴴ * ρHalf * (B * H)).trace := by simp only [Matrix.mul_assoc]
  rw [ht1, ht2]

/-- **Proposition 2.2(4)** (Zero Diagonal Lanczos Coefficients for Hermitian Operators):
If `H† = H`, `A† = A`, and `H ρ^{1/2} = ρ^{1/2} H`, then `(A | ℒ A)_β^W = 0`. -/
theorem prop_2_2_liouvillian_zero_diagonal (ρHalf H A : Matrix ι ι ℂ)
    (hH : Hᴴ = H) (hA : Aᴴ = A) (hComm : H * ρHalf = ρHalf * H) :
    wightmanInner ρHalf A (liouvillian H A) = 0 := by
  unfold wightmanInner liouvillian
  rw [hA, Matrix.mul_sub, Matrix.trace_sub]
  have h1 : (ρHalf * A * ρHalf * (H * A)).trace = (ρHalf * A * ρHalf * (A * H)).trace := by
    calc (ρHalf * A * ρHalf * (H * A)).trace
        = ((ρHalf * A) * ((ρHalf * H) * A)).trace := by simp only [Matrix.mul_assoc]
      _ = ((ρHalf * A) * ((H * ρHalf) * A)).trace := by rw [← hComm]
      _ = (((ρHalf * A) * H) * (ρHalf * A)).trace := by simp only [Matrix.mul_assoc]
      _ = ((ρHalf * A) * ((ρHalf * A) * H)).trace := Matrix.trace_mul_comm _ _
      _ = (ρHalf * A * ρHalf * (A * H)).trace := by simp only [Matrix.mul_assoc]
  rw [h1, sub_self]

end WightmanIsometry

section MSSOTOCSizeIdentities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 2.3(1)** (Single-Pauli Commutator Trace Identity, Eq. 2.9):
For Hermitian `M` and Hermitian involutory Pauli `P` (`P† = P`, `P² = 1`),
`Tr([M, P]† [M, P]) = 2 Tr(M²) - 2 Tr(P M P M)`. -/
theorem prop_2_3_commutator_size_identity (M P : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    ((M * P - P * M)ᴴ * (M * P - P * M)).trace =
      2 * (M * M).trace - 2 * (P * M * P * M).trace := by
  have hAdj : (M * P - P * M)ᴴ = P * M - M * P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM, hP]
  rw [hAdj]
  have hexp : (P * M - M * P) * (M * P - P * M) =
      P * M * M * P - P * M * P * M - M * P * M * P + M * P * P * M := by
    noncomm_ring
  rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  have ht1 : (P * M * M * P).trace = (M * M).trace := by
    calc (P * M * M * P).trace
        = (P * (M * M * P)).trace := by simp only [Matrix.mul_assoc]
      _ = ((M * M * P) * P).trace := Matrix.trace_mul_comm _ _
      _ = (M * M * (P * P)).trace := by simp only [Matrix.mul_assoc]
      _ = (M * M).trace := by rw [hP2, Matrix.mul_one]
  have ht2 : (M * P * P * M).trace = (M * M).trace := by
    calc (M * P * P * M).trace
        = (M * (P * P) * M).trace := by simp only [Matrix.mul_assoc]
      _ = (M * M).trace := by rw [hP2, Matrix.mul_one]
  have ht3 : (M * P * M * P).trace = (P * M * P * M).trace := by
    calc (M * P * M * P).trace
        = ((M * P * M) * P).trace := rfl
      _ = (P * (M * P * M)).trace := Matrix.trace_mul_comm _ _
      _ = (P * M * P * M).trace := by simp only [Matrix.mul_assoc]
  rw [ht1, ht2, ht3]
  ring

/-- **Proposition 2.3(2)** (Majorana Anticommutator Trace Identity, Eq. 2.10):
For Hermitian `M` and Hermitian involutory Majorana operator `ψ` (`ψ† = ψ`, `ψ² = 1`),
`Tr({M, ψ}† {M, ψ}) = 2 Tr(M²) + 2 Tr(ψ M ψ M)`. -/
theorem prop_2_3_majorana_size_identity (M ψ : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hψ : ψᴴ = ψ) (hψ2 : ψ * ψ = 1) :
    ((M * ψ + ψ * M)ᴴ * (M * ψ + ψ * M)).trace =
      2 * (M * M).trace + 2 * (ψ * M * ψ * M).trace := by
  have hAdj : (M * ψ + ψ * M)ᴴ = ψ * M + M * ψ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM, hψ]
  rw [hAdj]
  have hexp : (ψ * M + M * ψ) * (M * ψ + ψ * M) =
      ψ * M * M * ψ + ψ * M * ψ * M + M * ψ * M * ψ + M * ψ * ψ * M := by
    noncomm_ring
  rw [hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  have ht1 : (ψ * M * M * ψ).trace = (M * M).trace := by
    calc (ψ * M * M * ψ).trace
        = (ψ * (M * M * ψ)).trace := by simp only [Matrix.mul_assoc]
      _ = ((M * M * ψ) * ψ).trace := Matrix.trace_mul_comm _ _
      _ = (M * M * (ψ * ψ)).trace := by simp only [Matrix.mul_assoc]
      _ = (M * M).trace := by rw [hψ2, Matrix.mul_one]
  have ht2 : (M * ψ * ψ * M).trace = (M * M).trace := by
    calc (M * ψ * ψ * M).trace
        = (M * (ψ * ψ) * M).trace := by simp only [Matrix.mul_assoc]
      _ = (M * M).trace := by rw [hψ2, Matrix.mul_one]
  have ht3 : (M * ψ * M * ψ).trace = (ψ * M * ψ * M).trace := by
    calc (M * ψ * M * ψ).trace
        = ((M * ψ * M) * ψ).trace := rfl
      _ = (ψ * (M * ψ * M)).trace := Matrix.trace_mul_comm _ _
      _ = (ψ * M * ψ * M).trace := by simp only [Matrix.mul_assoc]
  rw [ht1, ht2, ht3]
  ring

end MSSOTOCSizeIdentities

section NestedCommutatorBounds

/-- **Lemma 2.1(1)** (Nested-Commutator Causal Induction, Eq. 2.3):
If `a 0 ≤ B` and `a (m + 1) ≤ 2 * Jsite * (s + m * (r - 1)) * a m`, then
`a m ≤ B * (2 (r - 1) Jsite)^m * ∏_{j=0}^{m-1} (s / (r - 1) + j)`. -/
theorem lemma_2_1_causal_commutator_induction {r s : ℕ} {Jsite B : ℝ}
    (hr : 2 ≤ r) (hJ : 0 < Jsite) (hB : 0 ≤ B)
    (a : ℕ → ℝ) (ha0 : a 0 ≤ B)
    (hstep : ∀ m : ℕ, a (m + 1) ≤ 2 * Jsite * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * a m) :
    ∀ m : ℕ, a m ≤ B * (2 * ((r : ℝ) - 1) * Jsite) ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  intro m
  induction m with
  | zero => simpa using ha0
  | succ m ih =>
    have hcoeff : 2 * Jsite * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) =
        (2 * ((r : ℝ) - 1) * Jsite) * ((s : ℝ) / ((r : ℝ) - 1) + (m : ℝ)) := by
      field_simp [hr1.ne']
    have hcoeff_nn : 0 ≤ 2 * Jsite * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) := by
      have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      positivity
    calc a (m + 1)
        ≤ 2 * Jsite * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * a m := hstep m
      _ ≤ 2 * Jsite * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) *
          (B * (2 * ((r : ℝ) - 1) * Jsite) ^ m *
            ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) :=
          mul_le_mul_of_nonneg_left ih hcoeff_nn
      _ = B * (2 * ((r : ℝ) - 1) * Jsite) ^ (m + 1) *
          ∏ j ∈ Finset.range (m + 1), ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
          rw [hcoeff, pow_succ, Finset.prod_range_succ]
          ring

private lemma rising_prod_single_site_le_factorial {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ (m.factorial : ℝ) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hfrac : (1 : ℝ) / ((r : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr hr1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
    have hterm : (1 : ℝ) / ((r : ℝ) - 1) + (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    calc (∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) *
            ((1 : ℝ) / ((r : ℝ) - 1) + (m : ℝ))
        ≤ (m.factorial : ℝ) * ((m + 1 : ℕ) : ℝ) :=
          mul_le_mul ih hterm (by positivity) (Nat.cast_nonneg _)
      _ = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by ring

private lemma rising_prod_r_local_le_factorial {r s : ℕ} (hr : 2 ≤ r) (hs : s ≤ r) (m : ℕ) :
    ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ ((m + 1).factorial : ℝ) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hfrac : (s : ℝ) / ((r : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have hs' : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
    have hterm : (s : ℝ) / ((r : ℝ) - 1) + (m : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    calc (∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) *
            ((s : ℝ) / ((r : ℝ) - 1) + (m : ℝ))
        ≤ ((m + 1).factorial : ℝ) * ((m + 1 + 1 : ℕ) : ℝ) :=
          mul_le_mul ih hterm (by positivity) (Nat.cast_nonneg _)
      _ = ((m + 1 + 1 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) := by ring

/-- **Lemma 2.1(2)** (Single-Site Analyticity Majorant, Eq. 2.4):
For `r ≥ 2`, `κ > 0`, and `|τ| < 4 κ`, the Taylor majorant series converges and satisfies
`∑' m, (|τ|/4)^m / m! * (1/κ)^m * ∏_{j=0}^{m-1} (1/(r-1) + j) ≤ (1 - |τ|/(4κ))⁻¹`. -/
theorem lemma_2_1_single_site_norm_bound {r : ℕ} {κ τ : ℝ}
    (hr : 2 ≤ r) (hκ : 0 < κ) (hτ : |τ| < 4 * κ) :
    let q := |τ| / (4 * κ)
    Summable (fun m : ℕ ↦ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ∧
    (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ≤ (1 - q)⁻¹ := by
  intro q
  have hq0 : 0 ≤ q := by simp only [q]; positivity
  have hq1 : q < 1 := by simp only [q]; exact (div_lt_one (by positivity)).mpr hτ
  have hterm : ∀ m : ℕ,
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ q ^ m := by
    intro m
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hle := rising_prod_single_site_le_factorial hr m
    have hrew : (|τ| / 4) ^ m * (1 / κ) ^ m = q ^ m := by
      rw [← mul_pow]
      congr 1; simp only [q]; ring
    calc ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
          ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
        = (q ^ m / (m.factorial : ℝ)) * ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
          rw [← hrew]; ring
      _ ≤ (q ^ m / (m.factorial : ℝ)) * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = q ^ m := div_mul_cancel₀ _ hfac.ne'
  have hnn : ∀ m : ℕ,
      0 ≤ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
    intro m
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ ↦ by positivity)
  have hsumm_q : Summable (fun m : ℕ ↦ q ^ m) := summable_geometric_of_lt_one hq0 hq1
  have hsumm : Summable (fun m : ℕ ↦ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) :=
    Summable.of_nonneg_of_le hnn hterm hsumm_q
  refine ⟨hsumm, ?_⟩
  calc ∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
      ≤ ∑' m : ℕ, q ^ m := hsumm.tsum_le_tsum hterm hsumm_q
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- **Lemma 2.1(3)** (`r`-Local Analyticity Majorant, Eq. 2.5):
For `r ≥ 2`, `s ≤ r`, `κ > 0`, and `|τ| < 4 κ`, the Taylor majorant series converges and satisfies
`∑' m, (|τ|/4)^m / m! * (1/κ)^m * ∏_{j=0}^{m-1} (s/(r-1) + j) ≤ (1 - |τ|/(4κ))⁻²`. -/
theorem lemma_2_1_r_local_norm_bound {r s : ℕ} {κ τ : ℝ}
    (hr : 2 ≤ r) (hs : s ≤ r) (hκ : 0 < κ) (hτ : |τ| < 4 * κ) :
    let q := |τ| / (4 * κ)
    Summable (fun m : ℕ ↦ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ∧
    (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ≤ (1 - q)⁻¹ ^ 2 := by
  intro q
  have hq0 : 0 ≤ q := by simp only [q]; positivity
  have hq1 : q < 1 := by simp only [q]; exact (div_lt_one (by positivity)).mpr hτ
  have hterm : ∀ m : ℕ,
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) * q ^ m := by
    intro m
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hle := rising_prod_r_local_le_factorial hr hs m
    have hrew : (|τ| / 4) ^ m * (1 / κ) ^ m = q ^ m := by
      rw [← mul_pow]; congr 1; simp only [q]; ring
    calc ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
          ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
        = (q ^ m / (m.factorial : ℝ)) * ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
          rw [← hrew]; ring
      _ ≤ (q ^ m / (m.factorial : ℝ)) * ((m + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((m + 1 : ℕ) : ℝ) * q ^ m := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          field_simp [hfac.ne']
  have hq_norm : Summable (fun n : ℕ ↦ ‖q ^ n‖) := by
    simpa [Real.norm_of_nonneg (pow_nonneg hq0 _)] using summable_geometric_of_lt_one hq0 hq1
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hq_norm hq_norm
  have hsum_eq : (fun m : ℕ ↦ ∑ k ∈ Finset.range (m + 1), q ^ k * q ^ (m - k)) =
      (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * q ^ m) := by
    funext m
    have hcongr : ∀ k ∈ Finset.range (m + 1), q ^ k * q ^ (m - k) = q ^ m := by
      intro k hk
      rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum_eq, tsum_geometric_of_lt_one hq0 hq1, ← sq] at hcauchy
  have hnn : ∀ m : ℕ,
      0 ≤ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
    intro m
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ ↦ by positivity)
  have hsumm : Summable (fun m : ℕ ↦ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) :=
    Summable.of_nonneg_of_le hnn hterm hcauchy.summable
  refine ⟨hsumm, ?_⟩
  calc ∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * (1 / κ) ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
      ≤ ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * q ^ m := hsumm.tsum_le_tsum hterm hcauchy.summable
    _ = (1 - q)⁻¹ ^ 2 := hcauchy.tsum_eq

end NestedCommutatorBounds

end KrylovChaos
