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
# Section 2: Nested-Commutator Cluster Bound, Wightman Isometry, and MSS-OTOC Identity

Formalizes:
- **Lemma 2.1**: Nested-commutator causal-sequence induction (2.3) and imaginary-time
  operator-norm convergence bounds (2.4)–(2.5).
- **Proposition 2.2**: Wightman–Hilbert–Schmidt unitary isometry `𝒥_β(A) = ρ^{1/4} A ρ^{1/4}`,
  commutation with the Liouvillian `ℒ = [H, ·]`, and self-adjointness / vanishing diagonals.
- **Proposition 2.3**: Exact MSS-regulated four-point correlator and thermal-subtracted
  operator-size identities for both `N`-qubit (2.9) and `N`-Majorana (2.10) systems.
-/

namespace KrylovChaos

open Matrix

section OperatorAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Commutator `[A, B] := A B - B A`. -/
def matComm (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

/-- Anticommutator `{A, B} := A B + B A`. -/
def matAntiComm (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B + B * A

/-- Hilbert–Schmidt inner product `⟨A, B⟩_HS := Tr(A† B)`. -/
def hsInner (A B : Matrix ι ι ℂ) : ℂ := Matrix.trace (Aᴴ * B)

/-- Squared Hilbert–Schmidt norm `‖A‖_HS² := Re Tr(A† A)`. -/
def hsNormSq (A : Matrix ι ι ℂ) : ℝ := (hsInner A A).re

/-- Wightman inner product `(A | B)_β^W := Tr(ρ^{1/2} A† ρ^{1/2} B)` (Eq. 1.2). -/
def wightmanInner (ρHalf A B : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (ρHalf * Aᴴ * ρHalf * B)

/-- Squared Wightman norm `‖A‖_{β,W}² := Re (A | A)_β^W`. -/
def wightmanNormSq (ρHalf A : Matrix ι ι ℂ) : ℝ := (wightmanInner ρHalf A A).re

/-- Wightman–Hilbert–Schmidt isometry map `𝒥_β(A) := ρ^{1/4} A ρ^{1/4}`. -/
def jBeta (ρQuarter A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ρQuarter * A * ρQuarter

/-- **Proposition 2.2(1)**: `𝒥_β` is an isometry from `(ℋ_op, (·|·)_β^W)` to
`(ℋ_op, ⟨·,·⟩_HS)` whenever `ρ^{1/4}` is Hermitian and `(ρ^{1/4})² = ρ^{1/2}`. -/
theorem prop_2_2_jBeta_isometry
    (ρQuarter ρHalf A B : Matrix ι ι ℂ)
    (hHerm : ρQuarterᴴ = ρQuarter)
    (hSq : ρQuarter * ρQuarter = ρHalf) :
    hsInner (jBeta ρQuarter A) (jBeta ρQuarter B) = wightmanInner ρHalf A B := by
  unfold hsInner jBeta wightmanInner
  have h1 : (ρQuarter * A * ρQuarter)ᴴ = ρQuarter * Aᴴ * ρQuarter := by
    simp [Matrix.conjTranspose_mul, hHerm, Matrix.mul_assoc]
  rw [h1]
  calc Matrix.trace (ρQuarter * Aᴴ * ρQuarter * (ρQuarter * B * ρQuarter))
      = Matrix.trace (ρQuarter * (ρQuarter * Aᴴ * ρQuarter * (ρQuarter * B))) := by
        rw [Matrix.trace_mul_cycle]
        simp [Matrix.mul_assoc]
    _ = Matrix.trace ((ρQuarter * ρQuarter) * Aᴴ * (ρQuarter * ρQuarter) * B) := by
        simp [Matrix.mul_assoc]
    _ = Matrix.trace (ρHalf * Aᴴ * ρHalf * B) := by rw [hSq]

/-- **Proposition 2.2(2)**: `𝒥_β` commutes with the Liouvillian `ℒ = [H, ·]`
whenever `[H, ρ^{1/4}] = 0`. -/
theorem prop_2_2_jBeta_comm_liouvillian
    (ρQuarter H A : Matrix ι ι ℂ)
    (hComm : H * ρQuarter = ρQuarter * H) :
    jBeta ρQuarter (matComm H A) = matComm H (jBeta ρQuarter A) := by
  unfold jBeta matComm
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ρQuarter H, ← hComm]
  simp only [Matrix.mul_assoc]
  rw [hComm]

/-- Self-adjointness of the Liouvillian `ℒ = [H, ·]` in the Wightman inner product
when `H` and `ρ^{1/2}` are Hermitian and commute. -/
theorem liouvillian_selfAdjoint_wightman
    (ρHalf H A B : Matrix ι ι ℂ)
    (hH : Hᴴ = H)
    (hComm : H * ρHalf = ρHalf * H) :
    wightmanInner ρHalf A (matComm H B) = wightmanInner ρHalf (matComm H A) B := by
  unfold wightmanInner matComm
  have hAdj : (H * A - A * H)ᴴ = Aᴴ * H - H * Aᴴ := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH]
  rw [hAdj]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
  have ht1 : Matrix.trace (ρHalf * (Aᴴ * (ρHalf * (H * B)))) =
      Matrix.trace (ρHalf * (Aᴴ * (H * (ρHalf * B)))) := by
    rw [← Matrix.mul_assoc ρHalf H, ← hComm, Matrix.mul_assoc]
  have ht2 : Matrix.trace (ρHalf * (Aᴴ * (ρHalf * (B * H)))) =
      Matrix.trace (ρHalf * (H * (Aᴴ * (ρHalf * B)))) := by
    calc Matrix.trace (ρHalf * (Aᴴ * (ρHalf * (B * H))))
        = Matrix.trace (H * (ρHalf * (Aᴴ * (ρHalf * B)))) := by
          rw [Matrix.trace_mul_cycle]
          simp [Matrix.mul_assoc]
      _ = Matrix.trace ((H * ρHalf) * (Aᴴ * (ρHalf * B))) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (ρHalf * (H * (Aᴴ * (ρHalf * B)))) := by
          rw [hComm]; simp [Matrix.mul_assoc]
  rw [ht1, ht2]

/-- Vanishing of the diagonal Lanczos matrix elements `(O | ℒ O)_β^W = 0` for any
Hermitian or anti-Hermitian operator `O` (`Oᴴ = s • O`). -/
theorem liouvillian_diag_zero_wightman
    (ρHalf H O : Matrix ι ι ℂ) (s : ℂ)
    (hAdj : Oᴴ = s • O)
    (hComm : H * ρHalf = ρHalf * H) :
    wightmanInner ρHalf O (matComm H O) = 0 := by
  unfold wightmanInner matComm
  rw [hAdj]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_assoc]
  have hEq : Matrix.trace (ρHalf * (O * (ρHalf * (H * O)))) =
      Matrix.trace (ρHalf * (O * (ρHalf * (O * H)))) := by
    calc Matrix.trace (ρHalf * (O * (ρHalf * (H * O))))
        = Matrix.trace (ρHalf * (O * ((ρHalf * H) * O))) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (ρHalf * (O * ((H * ρHalf) * O))) := by rw [← hComm]
      _ = Matrix.trace ((ρHalf * O * H) * (ρHalf * O)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((ρHalf * O) * (ρHalf * O * H)) := by rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (ρHalf * (O * (ρHalf * (O * H)))) := by simp [Matrix.mul_assoc]
  rw [hEq, sub_self]

/-- Single-probe Hilbert–Schmidt commutator norm identity: for Hermitian `M` and
Hermitian unitary `P` (`Pᴴ = P`, `P² = 1`),
`‖[M, P]‖_HS² = 2 Re Tr(M²) - 2 Re Tr(M P M P)`. -/
theorem hsNormSq_comm_hermitian_unitary
    (M P : Matrix ι ι ℂ) (hM : Mᴴ = M) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    hsNormSq (matComm M P) =
      2 * (Matrix.trace (M * M)).re - 2 * (Matrix.trace (M * P * M * P)).re := by
  unfold hsNormSq hsInner matComm
  have hAdj : (M * P - P * M)ᴴ = P * M - M * P := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hM, hP]
  rw [hAdj]
  have hexp : (P * M - M * P) * (M * P - P * M) =
      P * M * M * P - P * M * P * M - M * P * M * P + M * P * P * M := by
    noncomm_ring
  rw [hexp]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  have ht1 : Matrix.trace (P * M * M * P) = Matrix.trace (M * M) := by
    calc Matrix.trace (P * M * M * P)
        = Matrix.trace ((P * P) * (M * M)) := by
          rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
      _ = Matrix.trace (M * M) := by rw [hP2, Matrix.one_mul]
  have ht2 : Matrix.trace (M * P * P * M) = Matrix.trace (M * M) := by
    have : M * P * P * M = M * (P * P) * M := by simp [Matrix.mul_assoc]
    rw [this, hP2, Matrix.mul_one]
  have ht3 : Matrix.trace (P * M * P * M) = Matrix.trace (M * P * M * P) := by
    calc Matrix.trace (P * M * P * M)
        = Matrix.trace ((P * M) * (P * M)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace ((M * P) * (M * P)) := by
          calc Matrix.trace ((P * M) * (P * M))
              = Matrix.trace (M * (P * M * P)) := by
                rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
            _ = Matrix.trace ((M * P) * (M * P)) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (M * P * M * P) := by simp [Matrix.mul_assoc]
  rw [ht1, ht2, ht3]
  ring

/-- Single-probe Hilbert–Schmidt anticommutator norm identity: for Hermitian `M` and
Hermitian unitary `P` (`Pᴴ = P`, `P² = 1`),
`‖{M, P}‖_HS² = 2 Re Tr(M²) + 2 Re Tr(M P M P)`. -/
theorem hsNormSq_anticomm_hermitian_unitary
    (M P : Matrix ι ι ℂ) (hM : Mᴴ = M) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    hsNormSq (matAntiComm M P) =
      2 * (Matrix.trace (M * M)).re + 2 * (Matrix.trace (M * P * M * P)).re := by
  unfold hsNormSq hsInner matAntiComm
  have hAdj : (M * P + P * M)ᴴ = P * M + M * P := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hM, hP]
  rw [hAdj]
  have hexp : (P * M + M * P) * (M * P + P * M) =
      P * M * M * P + P * M * P * M + M * P * M * P + M * P * P * M := by
    noncomm_ring
  rw [hexp]
  simp only [Matrix.trace_add, Complex.add_re]
  have ht1 : Matrix.trace (P * M * M * P) = Matrix.trace (M * M) := by
    calc Matrix.trace (P * M * M * P)
        = Matrix.trace ((P * P) * (M * M)) := by
          rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
      _ = Matrix.trace (M * M) := by rw [hP2, Matrix.one_mul]
  have ht2 : Matrix.trace (M * P * P * M) = Matrix.trace (M * M) := by
    have : M * P * P * M = M * (P * P) * M := by simp [Matrix.mul_assoc]
    rw [this, hP2, Matrix.mul_one]
  have ht3 : Matrix.trace (P * M * P * M) = Matrix.trace (M * P * M * P) := by
    calc Matrix.trace (P * M * P * M)
        = Matrix.trace (M * (P * M * P)) := by
          rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
      _ = Matrix.trace (M * P * M * P) := by simp [Matrix.mul_assoc]
  rw [ht1, ht2, ht3]
  ring

/-- MSS-regulated four-point correlator `F_MSS(A, V) := Re Tr(ρ^{1/4} A ρ^{1/4} V ρ^{1/4} A ρ^{1/4} V)`. -/
def fMSS (ρQuarter A V : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (jBeta ρQuarter A * V * jBeta ρQuarter A * V)).re

/-- Zero-time Wightman two-point correlator `C_{β,V}^W(0) := Re Tr(ρ^{1/2} V ρ^{1/2} V)`. -/
def cWZero (ρHalf V : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (ρHalf * V * ρHalf * V)).re

/-- **Proposition 2.3(1)** (N-qubit MSS-OTOC and Thermal-Size Identity, Eq. 2.9). -/
theorem prop_2_3_qubit_identity {κIdx : Type*} [Fintype κIdx]
    (ρQuarter ρHalf A : Matrix ι ι ℂ) (σ : κIdx → Matrix ι ι ℂ)
    (hρQ : ρQuarterᴴ = ρQuarter) (hρH : ρHalfᴴ = ρHalf)
    (hSq : ρQuarter * ρQuarter = ρHalf)
    (hA : Aᴴ = A)
    (hNorm : wightmanNormSq ρHalf A = 1)
    (hTrρ : (Matrix.trace (ρHalf * ρHalf)).re = 1)
    (hσH : ∀ k, (σ k)ᴴ = σ k) (hσ2 : ∀ k, σ k * σ k = 1) :
    (1 / 8 : ℝ) * (∑ k : κIdx, hsNormSq (matComm (jBeta ρQuarter A) (σ k))) -
    (1 / 8 : ℝ) * (∑ k : κIdx, hsNormSq (matComm ρHalf (σ k))) =
    (1 / 4 : ℝ) * ∑ k : κIdx, (cWZero ρHalf (σ k) - fMSS ρQuarter A (σ k)) := by
  have hJM : (jBeta ρQuarter A)ᴴ = jBeta ρQuarter A := by
    unfold jBeta
    simp [Matrix.conjTranspose_mul, hρQ, hA, Matrix.mul_assoc]
  have hJTr : (Matrix.trace (jBeta ρQuarter A * jBeta ρQuarter A)).re = 1 := by
    have hiso := prop_2_2_jBeta_isometry ρQuarter ρHalf A A hρQ hSq
    unfold wightmanNormSq at hNorm
    rw [← hiso] at hNorm
    unfold hsInner at hNorm
    rwa [hJM] at hNorm
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : κIdx,
      hsNormSq (matComm (jBeta ρQuarter A) (σ k)) - hsNormSq (matComm ρHalf (σ k)) =
      2 * (cWZero ρHalf (σ k) - fMSS ρQuarter A (σ k)) := by
    intro k
    rw [hsNormSq_comm_hermitian_unitary (jBeta ρQuarter A) (σ k) hJM (hσH k) (hσ2 k)]
    rw [hsNormSq_comm_hermitian_unitary ρHalf (σ k) hρH (hσH k) (hσ2 k)]
    rw [hJTr, hTrρ]
    unfold cWZero fMSS
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

/-- **Proposition 2.3(2)** (N-Majorana MSS-OTOC and Thermal-Size Identity, Eq. 2.10). -/
theorem prop_2_3_majorana_identity {κIdx : Type*} [Fintype κIdx]
    (ρQuarter ρHalf A : Matrix ι ι ℂ) (V : κIdx → Matrix ι ι ℂ)
    (hρQ : ρQuarterᴴ = ρQuarter) (hρH : ρHalfᴴ = ρHalf)
    (hSq : ρQuarter * ρQuarter = ρHalf)
    (hA : Aᴴ = A)
    (hNorm : wightmanNormSq ρHalf A = 1)
    (hTrρ : (Matrix.trace (ρHalf * ρHalf)).re = 1)
    (hVH : ∀ k, (V k)ᴴ = V k) (hV2 : ∀ k, V k * V k = 1) :
    (1 / 4 : ℝ) * (∑ k : κIdx, hsNormSq (matAntiComm (jBeta ρQuarter A) (V k))) -
    (1 / 4 : ℝ) * (∑ k : κIdx, hsNormSq (matComm ρHalf (V k))) =
    (1 / 2 : ℝ) * ∑ k : κIdx, (cWZero ρHalf (V k) + fMSS ρQuarter A (V k)) := by
  have hJM : (jBeta ρQuarter A)ᴴ = jBeta ρQuarter A := by
    unfold jBeta
    simp [Matrix.conjTranspose_mul, hρQ, hA, Matrix.mul_assoc]
  have hJTr : (Matrix.trace (jBeta ρQuarter A * jBeta ρQuarter A)).re = 1 := by
    have hiso := prop_2_2_jBeta_isometry ρQuarter ρHalf A A hρQ hSq
    unfold wightmanNormSq at hNorm
    rw [← hiso] at hNorm
    unfold hsInner at hNorm
    rwa [hJM] at hNorm
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : κIdx,
      hsNormSq (matAntiComm (jBeta ρQuarter A) (V k)) - hsNormSq (matComm ρHalf (V k)) =
      2 * (cWZero ρHalf (V k) + fMSS ρQuarter A (V k)) := by
    intro k
    rw [hsNormSq_anticomm_hermitian_unitary (jBeta ρQuarter A) (V k) hJM (hVH k) (hV2 k)]
    rw [hsNormSq_comm_hermitian_unitary ρHalf (V k) hρH (hVH k) (hV2 k)]
    rw [hJTr, hTrρ]
    unfold cWZero fMSS
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

end OperatorAlgebra

section NestedCommutatorCluster

/-- **Lemma 2.1(1)** (Nested-Commutator Cluster Bound, Eq. 2.3):
Inductive bound on the causal-sequence norm sum `S(m) := ∑_{|Γ|=m} ‖T_Γ‖_∞`. -/
theorem lemma_2_1_causal_induction
    {r s : ℕ} {Jsite normO : ℝ} (S : ℕ → ℝ)
    (hr : 2 ≤ r) (hJ : 0 < Jsite)
    (h0 : S 0 ≤ normO)
    (hstep : ∀ m, S (m + 1) ≤ 2 * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * Jsite * S m) :
    ∀ m : ℕ, S m ≤ normO * (invLocalityScale r Jsite)⁻¹ ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
  intro m
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
      linarith
    have hcoeff_nonneg : 0 ≤ 2 * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * Jsite := by positivity
    have hrewrite : 2 * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * Jsite =
        (invLocalityScale r Jsite)⁻¹ * ((s : ℝ) / ((r : ℝ) - 1) + (m : ℝ)) := by
      unfold invLocalityScale
      field_simp
      ring
    calc S (m + 1)
        ≤ 2 * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * Jsite * S m := hstep m
      _ ≤ 2 * ((s : ℝ) + (m : ℝ) * ((r : ℝ) - 1)) * Jsite *
          (normO * (invLocalityScale r Jsite)⁻¹ ^ m *
            ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) :=
          mul_le_mul_of_nonneg_left ih hcoeff_nonneg
      _ = normO * (invLocalityScale r Jsite)⁻¹ ^ (m + 1) *
          ∏ j ∈ Finset.range (m + 1), ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) := by
          rw [hrewrite, Finset.prod_range_succ, pow_succ]
          ring

/-- Factorial comparison for single-site operators (`s = 1`, `r ≥ 2`):
`∏_{j=0}^{m-1} (1/(r-1) + j) ≤ m!`. -/
theorem prod_single_site_le_factorial {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, mul_comm]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hterm : (1 : ℝ) / ((r : ℝ) - 1) + (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      have hdiv : (1 : ℝ) / ((r : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ hr1 (by linarith)
      push_cast
      linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    exact mul_le_mul ih hterm (by positivity) (by positivity)

/-- Factorial comparison for `r`-local operators (`s ≤ r`, `r ≥ 2`):
`∏_{j=0}^{m-1} (s/(r-1) + j) ≤ (m + 1)!`. -/
theorem prod_r_local_le_factorial_succ {r s : ℕ} (hr : 2 ≤ r) (hs : s ≤ r) (m : ℕ) :
    ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ ((m + 1).factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, mul_comm]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hs_div : (s : ℝ) / ((r : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have hs' : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hterm : (s : ℝ) / ((r : ℝ) - 1) + (m : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    exact mul_le_mul ih hterm (by positivity) (by positivity)

/-- **Lemma 2.1(2)** (Single-site imaginary-time series bound, Eq. 2.4):
`∑_{m=0}^∞ ((|τ|/4)^m / m!) κ^{-m} ∏_{j=0}^{m-1} (1/(r-1) + j) ≤ (1 - |τ|/(4κ))⁻¹`. -/
theorem lemma_2_1_single_site_series {r : ℕ} {κ τ : ℝ}
    (hr : 2 ≤ r) (hκ : 0 < κ) (hτ : |τ| < 4 * κ) :
    (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
      ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ≤
    (1 - |τ| / (4 * κ))⁻¹ := by
  set q : ℝ := |τ| / (4 * κ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [div_lt_one (by positivity)]
    exact hτ
  have hterm : ∀ m : ℕ,
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤ q ^ m := by
    intro m
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hle := prod_single_site_le_factorial hr m
    calc ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
          ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
        ≤ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = q ^ m := by
          simp only [q]
          field_simp [hfac.ne']
          rw [← mul_pow, ← div_pow]
          ring
  have hgeom : Summable (fun m : ℕ ↦ q ^ m) := summable_geometric_of_lt_one hq0 hq1
  have hsumm : Summable (fun m : ℕ ↦
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun m ↦ ?_) hterm hgeom
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
      linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    positivity
  calc (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((1 : ℝ) / ((r : ℝ) - 1) + (j : ℝ)))
      ≤ ∑' m : ℕ, q ^ m := hsumm.tsum_le_tsum hterm hgeom
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- **Lemma 2.1(3)** (`r`-local imaginary-time series bound, Eq. 2.5):
`∑_{m=0}^∞ ((|τ|/4)^m / m!) κ^{-m} ∏_{j=0}^{m-1} (s/(r-1) + j) ≤ (1 - |τ|/(4κ))⁻²`. -/
theorem lemma_2_1_r_local_series {r s : ℕ} {κ τ : ℝ}
    (hr : 2 ≤ r) (hs : s ≤ r) (hκ : 0 < κ) (hτ : |τ| < 4 * κ) :
    (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
      ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) ≤
    (1 - |τ| / (4 * κ))⁻¹ ^ 2 := by
  set q : ℝ := |τ| / (4 * κ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [div_lt_one (by positivity)]
    exact hτ
  have hterm : ∀ m : ℕ,
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) * q ^ m := by
    intro m
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hle := prod_r_local_le_factorial_succ hr hs m
    calc ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
          ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))
        ≤ ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m * ((m + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((m + 1 : ℕ) : ℝ) * q ^ m := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          simp only [q]
          field_simp [hfac.ne']
          rw [← mul_pow, ← div_pow]
          ring
  have hhas : HasSum (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * q ^ m) ((1 - q)⁻¹ ^ 2) := by
    have h1 := hasSum_geometric_of_lt_one hq0 hq1
    have h2 := h1.mul_left ((1 - q)⁻¹)
    -- Use Cauchy product of geometric series with itself:
    have hc := hasSum_sum_range_mul_of_summable_norm
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using h1.summable)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using h1.summable)
    have hsum_eq : (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), q ^ k * q ^ (n - k)) =
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * q ^ n) := by
      ext n
      have hconst : ∀ k ∈ Finset.range (n + 1), q ^ k * q ^ (n - k) = q ^ n := by
        intro k hk
        rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum_eq, h1.tsum_eq, ← sq] at hc
    exact hc
  have hsumm : Summable (fun m : ℕ ↦
      ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun m ↦ ?_) hterm hhas.summable
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
      linarith
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ ↦ by positivity
    positivity
  calc (∑' m : ℕ, ((|τ| / 4) ^ m / (m.factorial : ℝ)) * κ⁻¹ ^ m *
        ∏ j ∈ Finset.range m, ((s : ℝ) / ((r : ℝ) - 1) + (j : ℝ)))
      ≤ ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * q ^ m := hsumm.tsum_le_tsum hterm hhas.summable
    _ = (1 - q)⁻¹ ^ 2 := hhas.tsum_eq

end NestedCommutatorCluster

end KrylovChaos
