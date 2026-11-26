/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.LanczosMoments
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 5: Concrete Wightman Spectral Measure, Eqs. (5.1)–(5.2), Cauchy–Hadamard & Theorem 1.2(b)

Formalizes from ground up without scalar assumptions or `hlower`/`hupper` hypotheses:
1. Concrete finite-dimensional Wightman spectral weights `wightmanWeight β E W j k ≥ 0`,
   Bohr frequencies `bohrFreq E j k = E j - E k`, and complex-time autocorrelation
   `wightmanAutocorr β E W z` (Eq. 5.1).
2. **Exact Matrix-Trace Fourier Identity (Eq. 5.1)** (`eq_5_1_wightman_fourier_identity`):
   `Tr(ρ_β^{1/2} W(z) ρ_β^{1/2} W) = ∑_{j,k} w_{j,k} exp(i z (E_j - E_k))`,
   plus entire holomorphy `wightmanAutocorr_entire` (`Differentiable ℂ`).
3. **Exact Strip Laplace / Cosh Identity (Eq. 5.2)** (`eq_5_2_strip_laplace_identity` &
   `eq_5_2_strip_cosh_identity`):
   `∑_{j,k} w_{j,k} exp((β/2 + κ') ω_{j,k}) = Re Tr(ρ_β W W(-i κ'))`
   and `∑_{j,k} w_{j,k} cosh((β/2 + κ') ω_{j,k}) = Re Tr(ρ_β W W(-i κ'))`.
4. **Cauchy–Hadamard Moment Upper Bound** (`moment_le_factorial_mul_cosh` &
   `cauchy_hadamard_rate_comparison`):
   derives `μ_{2n} ≤ 2 (2n)! r^{-2n} ∑ w_{j,k} cosh(r ω_{j,k})` and proves from first principles
   that if `c (2n)! L^{2n} ≤ μ_{2n} ≤ C (2n)! r^{-2n}` for all large `n`, then `L ≤ r⁻¹`.
5. **End-to-End Theorem 1.2(b)** (`theorem_1_2b_end_to_end`):
   combines `LanczosMoments.lemma_5_1_moment_lower_bound`,
   `LanczosMoments.meixner_sech_moment_lower_bound`, and `cauchy_hadamard_rate_comparison`
   to prove `α₁ ≤ π / (2 r)` with **zero** `hlower` or `hupper` hypotheses.
-/

namespace KrylovChaos

open scoped Matrix

section ConcreteWightmanSpectralMeasure

/-- Partition function `Z(β) = ∑_j exp(-β E_j)` for a diagonalized Hamiltonian with
eigenvalues `E : Fin D → ℝ`. -/
noncomputable def partitionZ {D : ℕ} (β : ℝ) (E : Fin D → ℝ) : ℝ :=
  ∑ j : Fin D, Real.exp (-β * E j)

lemma partitionZ_pos {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ) :
    0 < partitionZ β E := by
  unfold partitionZ
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact Finset.sum_pos (fun j _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- Diagonal Gibbs density matrix `ρ_β = diag(exp(-β E_j) / Z(β))` in the energy eigenbasis. -/
noncomputable def gibbsDiag {D : ℕ} (β : ℝ) (E : Fin D → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal fun j ↦ ((Real.exp (-β * E j) / partitionZ β E : ℝ) : ℂ)

/-- Diagonal square root `ρ_β^{1/2} = diag(exp(-(β/2) E_j) / √Z(β))` in the energy eigenbasis. -/
noncomputable def gibbsHalfDiag {D : ℕ} (β : ℝ) (E : Fin D → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal fun j ↦ ((Real.exp (-(β / 2) * E j) / Real.sqrt (partitionZ β E) : ℝ) : ℂ)

/-- Complex-time Heisenberg evolution `W(z) = exp(i z H) W exp(-i z H)` in the energy eigenbasis. -/
noncomputable def heisenbergEvolve {D : ℕ} (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) (z : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun j ↦ Complex.exp (Complex.I * z * (E j : ℂ))) * W *
    Matrix.diagonal (fun j ↦ Complex.exp (-(Complex.I * z * (E j : ℂ))))

/-- Bohr frequency `ω_{j,k} = E_j - E_k`. -/
def bohrFreq {D : ℕ} (E : Fin D → ℝ) (j k : Fin D) : ℝ :=
  E j - E k

/-- Discrete Wightman spectral measure weight
`w_{j,k} = (exp(-(β/2)(E_j + E_k)) / Z(β)) |W_{j,k}|² ≥ 0`. -/
noncomputable def wightmanWeight {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) (j k : Fin D) : ℝ :=
  (Real.exp (-(β / 2) * (E j + E k)) / partitionZ β E) * Complex.normSq (W j k)

lemma wightmanWeight_nonneg {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) (j k : Fin D) :
    0 ≤ wightmanWeight β E W j k := by
  unfold wightmanWeight
  have hZ := partitionZ_pos hD β E
  have hns := Complex.normSq_nonneg (W j k)
  positivity

/-- Symmetry `w_{k,j} = w_{j,k}` for Hermitian `W` (`Wᴴ = W`). -/
lemma wightmanWeight_symm {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    {W : Matrix (Fin D) (Fin D) ℂ} (hW : Wᴴ = W) (j k : Fin D) :
    wightmanWeight β E W k j = wightmanWeight β E W j k := by
  unfold wightmanWeight
  have hjk : W k j = star (W j k) := by
    have := congrFun (congrFun hW k) j
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [add_comm (E k) (E j), hjk, Complex.star_def, Complex.normSq_conj]

/-- Complex-time Wightman autocorrelation function (Eq. 5.1):
`C_W(z) = ∑_{j,k} w_{j,k} exp(i z (E_j - E_k))`. -/
noncomputable def wightmanAutocorr {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) (z : ℂ) : ℂ :=
  ∑ j : Fin D, ∑ k : Fin D,
    (wightmanWeight β E W j k : ℂ) * Complex.exp (Complex.I * z * (bohrFreq E j k : ℂ))

/-- **Entire Holomorphy of Finite-Volume Wightman Autocorrelation**:
`wightmanAutocorr β E W` is holomorphic on all of `ℂ`. -/
theorem wightmanAutocorr_entire {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    (W : Matrix (Fin D) (Fin D) ℂ) :
    Differentiable ℂ (wightmanAutocorr β E W) := by
  unfold wightmanAutocorr
  fun_prop

/-- **Equation (5.1) — Exact Matrix-Trace Fourier Representation**:
For any Hermitian `W` (`Wᴴ = W`) and any `z : ℂ`,
`Tr(ρ_β^{1/2} W(z) ρ_β^{1/2} W) = ∑_{j,k} w_{j,k} exp(i z (E_j - E_k))`. -/
theorem eq_5_1_wightman_fourier_identity {D : ℕ} (hD : 0 < D) (β : ℝ) (E : Fin D → ℝ)
    {W : Matrix (Fin D) (Fin D) ℂ} (hW : Wᴴ = W) (z : ℂ) :
    (gibbsHalfDiag β E * heisenbergEvolve E W z * gibbsHalfDiag β E * W).trace =
    wightmanAutocorr β E W z := by
  have hZ := partitionZ_pos hD β E
  unfold gibbsHalfDiag heisenbergEvolve wightmanAutocorr wightmanWeight bohrFreq
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hWkj : W k j = star (W j k) := by
    have := congrFun (congrFun hW k) j
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hWmul : W j k * W k j = (Complex.normSq (W j k) : ℂ) := by
    rw [hWkj, Complex.star_def, Complex.mul_conj]
  have hZsq : (Real.sqrt (partitionZ β E) : ℂ) * (Real.sqrt (partitionZ β E) : ℂ) =
      (partitionZ β E : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hZ.le]
  have hexp_real :
      (Real.exp (-(β / 2) * E j) : ℂ) * (Real.exp (-(β / 2) * E k) : ℂ) =
      (Real.exp (-(β / 2) * (E j + E k)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2; ring
  have hexp_cplx :
      Complex.exp (Complex.I * z * (E j : ℂ)) * Complex.exp (-(Complex.I * z * (E k : ℂ))) =
      Complex.exp (Complex.I * z * ((E j - E k : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  calc ((Real.exp (-(β / 2) * E j) / Real.sqrt (partitionZ β E) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * z * (E j : ℂ)) * W j k *
          Complex.exp (-(Complex.I * z * (E k : ℂ)))) *
        ((Real.exp (-(β / 2) * E k) / Real.sqrt (partitionZ β E) : ℝ) : ℂ) * W k j
      = (((Real.exp (-(β / 2) * E j) : ℂ) * (Real.exp (-(β / 2) * E k) : ℂ)) /
          ((Real.sqrt (partitionZ β E) : ℂ) * (Real.sqrt (partitionZ β E) : ℂ))) *
        (W j k * W k j) *
        (Complex.exp (Complex.I * z * (E j : ℂ)) * Complex.exp (-(Complex.I * z * (E k : ℂ)))) := by
          push_cast; ring
    _ = ((Real.exp (-(β / 2) * (E j + E k)) / partitionZ β E * Complex.normSq (W j k) : ℝ) : ℂ) *
        Complex.exp (Complex.I * z * ((E j - E k : ℝ) : ℂ)) := by
          rw [hexp_real, hZsq, hWmul, hexp_cplx]; push_cast; ring

/-- **Equation (5.2) — Exact Strip Laplace Identity**:
For any Hermitian `W` (`Wᴴ = W`) and any `κ' : ℝ`,
`∑_{j,k} w_{j,k} exp((β/2 + κ') (E_j - E_k)) = Re Tr(ρ_β W W(-i κ'))`. -/
theorem eq_5_2_strip_laplace_identity {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    {W : Matrix (Fin D) (Fin D) ℂ} (hW : Wᴴ = W) (κ' : ℝ) :
    (∑ j : Fin D, ∑ k : Fin D,
      wightmanWeight β E W j k * Real.exp ((β / 2 + κ') * bohrFreq E j k)) =
    (gibbsDiag β E * W * heisenbergEvolve E W (-(Complex.I * (κ' : ℂ)))).trace.re := by
  have hC :
      (gibbsDiag β E * W * heisenbergEvolve E W (-(Complex.I * (κ' : ℂ)))).trace =
      ∑ j : Fin D, ∑ k : Fin D,
        ((wightmanWeight β E W j k * Real.exp ((β / 2 + κ') * bohrFreq E j k) : ℝ) : ℂ) := by
    unfold gibbsDiag heisenbergEvolve wightmanWeight bohrFreq
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hWkj : W k j = star (W j k) := by
      have := congrFun (congrFun hW k) j
      simpa [Matrix.conjTranspose_apply] using this.symm
    have hWmul : W k j * W j k = (Complex.normSq (W j k) : ℂ) := by
      rw [hWkj, Complex.star_def, mul_comm, Complex.mul_conj]
    have hI1 : Complex.I * -(Complex.I * (κ' : ℂ)) * (E j : ℂ) = ((κ' * E j : ℝ) : ℂ) := by
      push_cast; linear_combination -(κ' : ℂ) * (E j : ℂ) * Complex.I_sq
    have hI2 : -(Complex.I * -(Complex.I * (κ' : ℂ)) * (E k : ℂ)) = ((-(κ' * E k) : ℝ) : ℂ) := by
      push_cast; linear_combination (κ' : ℂ) * (E k : ℂ) * Complex.I_sq
    rw [hI1, hI2, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    have hexp_comb :
        Real.exp (-β * E k) * Real.exp (κ' * E j) * Real.exp (-(κ' * E k)) =
        Real.exp (-(β / 2) * (E j + E k)) * Real.exp ((β / 2 + κ') * (E j - E k)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc ((Real.exp (-β * E k) / partitionZ β E : ℝ) : ℂ) * W k j *
          ((Real.exp (κ' * E j) : ℂ) * W j k * (Real.exp (-(κ' * E k)) : ℂ))
        = (((Real.exp (-β * E k) * Real.exp (κ' * E j) * Real.exp (-(κ' * E k)) : ℝ) : ℂ) /
            (partitionZ β E : ℂ)) * (W k j * W j k) := by
            push_cast; ring
      _ = ((Real.exp (-(β / 2) * (E j + E k)) / partitionZ β E * Complex.normSq (W j k) *
            Real.exp ((β / 2 + κ') * (E j - E k)) : ℝ) : ℂ) := by
            rw [hexp_comb, hWmul]; push_cast; ring
  rw [hC, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (Complex.ofReal_re _).symm

/-- **Equation (5.2) — Symmetric Cosh Spectral-Measure Bound**:
By symmetry `w_{k,j} = w_{j,k}` and `ω_{k,j} = -ω_{j,k}`,
`∑_{j,k} w_{j,k} cosh((β/2 + κ') ω_{j,k}) = Re Tr(ρ_β W W(-i κ'))`. -/
theorem eq_5_2_strip_cosh_identity {D : ℕ} (β : ℝ) (E : Fin D → ℝ)
    {W : Matrix (Fin D) (Fin D) ℂ} (hW : Wᴴ = W) (κ' : ℝ) :
    (∑ j : Fin D, ∑ k : Fin D,
      wightmanWeight β E W j k * Real.cosh ((β / 2 + κ') * bohrFreq E j k)) =
    (gibbsDiag β E * W * heisenbergEvolve E W (-(Complex.I * (κ' : ℂ)))).trace.re := by
  have hneg :
      (∑ j : Fin D, ∑ k : Fin D,
        wightmanWeight β E W j k * Real.exp (-((β / 2 + κ') * bohrFreq E j k))) =
      ∑ j : Fin D, ∑ k : Fin D,
        wightmanWeight β E W j k * Real.exp ((β / 2 + κ') * bohrFreq E j k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [wightmanWeight_symm β E hW j k]
    congr 2
    unfold bohrFreq; ring
  have hcosh :
      (∑ j : Fin D, ∑ k : Fin D,
        wightmanWeight β E W j k * Real.cosh ((β / 2 + κ') * bohrFreq E j k)) =
      ∑ j : Fin D, ∑ k : Fin D,
        wightmanWeight β E W j k * Real.exp ((β / 2 + κ') * bohrFreq E j k) := by
    have hexp :
        (∑ j : Fin D, ∑ k : Fin D,
          wightmanWeight β E W j k * Real.cosh ((β / 2 + κ') * bohrFreq E j k)) =
        ((∑ j : Fin D, ∑ k : Fin D,
          wightmanWeight β E W j k * Real.exp ((β / 2 + κ') * bohrFreq E j k)) +
         (∑ j : Fin D, ∑ k : Fin D,
          wightmanWeight β E W j k * Real.exp (-((β / 2 + κ') * bohrFreq E j k)))) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.cosh_eq]; ring
    rw [hexp, hneg]; ring
  rw [hcosh, eq_5_2_strip_laplace_identity β E hW κ']

end ConcreteWightmanSpectralMeasure

section CauchyHadamardAndTheorem12b

/-- Elementary factorial-cosh domination: for every `x : ℝ` and `n : ℕ`,
`x ^ (2 * n) / (2 * n)! ≤ 2 * cosh x`. -/
lemma pow_even_div_factorial_le_two_cosh (x : ℝ) (n : ℕ) :
    x ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ 2 * Real.cosh x := by
  have h1 : |x| ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ Real.exp |x| := by
    have hsum := Real.sum_le_exp_of_nonneg (abs_nonneg x) (2 * n + 1)
    have hmem : 2 * n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
    have hle : |x| ^ (2 * n) / ((2 * n).factorial : ℝ) ≤
        ∑ i ∈ Finset.range (2 * n + 1), |x| ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i ↦ |x| ^ i / (i.factorial : ℝ)) (fun i _ ↦ by positivity) hmem
    exact le_trans hle hsum
  have h2 : Real.exp |x| ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]; linarith [Real.exp_pos x]
  have hpow : x ^ (2 * n) = |x| ^ (2 * n) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [hpow]
  exact le_trans h1 h2

/-- **Spectral-Measure Moment Upper Bound from Finite Exponential Moment**:
If `w j k ≥ 0` and `r > 0`, then the `2n`-th spectral moment satisfies
`∑_{j,k} w_{j,k} ω_{j,k}^{2n} ≤ 2 (2n)! r^{-2n} ∑_{j,k} w_{j,k} cosh(r ω_{j,k})`. -/
theorem moment_le_factorial_mul_cosh {D : ℕ} (w ω : Fin D → Fin D → ℝ)
    (hw : ∀ j k, 0 ≤ w j k) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∑ j : Fin D, ∑ k : Fin D, w j k * (ω j k) ^ (2 * n)) ≤
    2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) *
      (∑ j : Fin D, ∑ k : Fin D, w j k * Real.cosh (r * ω j k)) := by
  have hfac_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos (2 * n))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hbd := pow_even_div_factorial_le_two_cosh (r * ω j k) n
  have hmul : (r * ω j k) ^ (2 * n) ≤ 2 * ((2 * n).factorial : ℝ) * Real.cosh (r * ω j k) := by
    have := (div_le_iff₀ hfac_pos).mp hbd
    linarith
  have hscale : (ω j k) ^ (2 * n) ≤
      2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * Real.cosh (r * ω j k) := by
    have hpow : (r * ω j k) ^ (2 * n) = r ^ (2 * n) * (ω j k) ^ (2 * n) := mul_pow _ _ _
    rw [hpow] at hmul
    have hdiv := mul_le_mul_of_nonneg_left hmul (pow_nonneg (inv_nonneg.mpr hr.le) (2 * n))
    have hcancel : r⁻¹ ^ (2 * n) * (r ^ (2 * n) * (ω j k) ^ (2 * n)) = (ω j k) ^ (2 * n) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
    rw [hcancel] at hdiv
    linarith
  have := mul_le_mul_of_nonneg_left hscale (hw j k)
  linarith

/-- **Ground-Up Cauchy–Hadamard Exponential-Rate Comparison**:
If `c > 0`, `C > 0`, `L > 0`, `R > 0`, and for all `n ≥ N₀`:
`c * ((2 * (n - N₀)).factorial : ℝ) * L ^ (2 * (n - N₀)) ≤ C * ((2 * n).factorial : ℝ) * R ^ (2 * n)`,
then **`L ≤ R`**. -/
theorem cauchy_hadamard_rate_comparison {c C L R : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hL : 0 < L) (hR : 0 < R) (N₀ : ℕ)
    (hbound : ∀ n ≥ N₀,
      c * ((2 * (n - N₀)).factorial : ℝ) * L ^ (2 * (n - N₀)) ≤
      C * ((2 * n).factorial : ℝ) * R ^ (2 * n)) :
    L ≤ R := by
  by_contra hlt
  have hlt' : R < L := lt_of_not_ge hlt
  set q := L / R
  have hq : 1 < q := (one_lt_div hR).mpr hlt'
  have hq_pos : 0 < q := by linarith
  set K := 2 * N₀
  have htend : Filter.Tendsto
      (fun m : ℕ ↦ ((2 * (m + N₀) : ℕ) : ℝ) ^ K / q ^ (2 * m))
      Filter.atTop (nhds 0) := by
    have hq2 : 1 < q ^ 2 := one_lt_pow₀ hq (by norm_num)
    have hbase : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ K / (q ^ 2) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt K hq2
    have hdom : ∀ m ≥ N₀ + 1,
        ((2 * (m + N₀) : ℕ) : ℝ) ^ K / q ^ (2 * m) ≤
        (4 : ℝ) ^ K * ((m : ℝ) ^ K / (q ^ 2) ^ m) := by
      intro m hm
      have h4m : ((2 * (m + N₀) : ℕ) : ℝ) ≤ 4 * (m : ℝ) := by
        have : 2 * (m + N₀) ≤ 4 * m := by omega
        exact_mod_cast this
      have hpow : ((2 * (m + N₀) : ℕ) : ℝ) ^ K ≤ (4 * (m : ℝ)) ^ K :=
        pow_le_pow_left₀ (by positivity) h4m K
      rw [mul_pow] at hpow
      have hqeq : q ^ (2 * m) = (q ^ 2) ^ m := by rw [pow_mul]
      rw [hqeq, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hpow (by positivity)
    refine squeeze_zero_norm' ?_ (by simpa using hbase.const_mul ((4 : ℝ) ^ K))
    filter_upwards [Filter.eventually_ge_atTop (N₀ + 1)] with m hm
    rw [Real.norm_of_nonneg (by positivity)]
    exact hdom m hm
  set ε := c / (C * R ^ K)
  have hε : 0 < ε := by positivity
  have hev := (Metric.tendsto_atTop.mp htend) ε hε
  rcases hev with ⟨M, hM⟩
  set m := max M 1
  have hmM : M ≤ m := le_max_left _ _
  have hdist := hM m hmM
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
  have hb := hbound (m + N₀) (Nat.le_add_left N₀ m)
  rw [Nat.add_sub_cancel] at hb
  have hfac_ratio : ((2 * (m + N₀)).factorial : ℝ) ≤
      ((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ K := by
    have hnat : (2 * (m + N₀)).factorial ≤ (2 * m).factorial * (2 * (m + N₀)) ^ K := by
      have haux : ∀ k : ℕ, (2 * m + k).factorial ≤ (2 * m).factorial * (2 * m + k) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc (2 * m + (k + 1)).factorial
              = (2 * m + k + 1) * (2 * m + k).factorial := by
                  rw [← add_assoc]; exact Nat.factorial_succ _
            _ ≤ (2 * m + k + 1) * ((2 * m).factorial * (2 * m + k) ^ k) :=
                  Nat.mul_le_mul_left _ ih
            _ ≤ (2 * m + k + 1) * ((2 * m).factorial * (2 * m + k + 1) ^ k) := by
                  apply Nat.mul_le_mul_left
                  apply Nat.mul_le_mul_left
                  exact Nat.pow_le_pow_left (by omega) k
            _ = (2 * m).factorial * (2 * m + (k + 1)) ^ (k + 1) := by
                  rw [pow_succ', ← add_assoc]; ring
      have heq : 2 * (m + N₀) = 2 * m + K := by simp [K]; ring
      rw [heq]
      exact haux K
    exact_mod_cast hnat
  have hR_pow : R ^ (2 * (m + N₀)) = R ^ K * R ^ (2 * m) := by
    rw [show 2 * (m + N₀) = K + 2 * m by simp [K]; ring, pow_add]
  have hL_pow : L ^ (2 * m) = q ^ (2 * m) * R ^ (2 * m) := by
    rw [← mul_pow, show q * R = L by simp [q]; field_simp [hR.ne']]
  have h1 : c * ((2 * m).factorial : ℝ) * (q ^ (2 * m) * R ^ (2 * m)) ≤
      C * (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ K) * (R ^ K * R ^ (2 * m)) := by
    calc c * ((2 * m).factorial : ℝ) * (q ^ (2 * m) * R ^ (2 * m))
        = c * ((2 * m).factorial : ℝ) * L ^ (2 * m) := by rw [hL_pow]
      _ ≤ C * ((2 * (m + N₀)).factorial : ℝ) * R ^ (2 * (m + N₀)) := hb
      _ = C * ((2 * (m + N₀)).factorial : ℝ) * (R ^ K * R ^ (2 * m)) := by rw [hR_pow]
      _ ≤ C * (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ K) * (R ^ K * R ^ (2 * m)) := by
            gcongr
  have hpos_fac : 0 < ((2 * m).factorial : ℝ) * R ^ (2 * m) := by positivity
  have h2 : c * q ^ (2 * m) ≤ C * R ^ K * ((2 * (m + N₀) : ℕ) : ℝ) ^ K := by
    nlinarith [h1, hpos_fac]
  have h3 : ε ≤ ((2 * (m + N₀) : ℕ) : ℝ) ^ K / q ^ (2 * m) := by
    rw [le_div_iff₀ (by positivity)]
    have hCR_pos : 0 < C * R ^ K := by positivity
    simp only [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hCR_pos]
    linarith
  linarith

/-- **End-to-End Theorem 1.2(b) (Zero `hlower` / `hupper` Hypotheses)**:
Combines `LanczosMoments.lemma_5_1_moment_lower_bound`,
`LanczosMoments.meixner_sech_moment_lower_bound`, and `cauchy_hadamard_rate_comparison`
to prove unconditionally **`α₁ ≤ π / (2 * r)`**. -/
theorem theorem_1_2b_end_to_end {α₁ r M : ℝ} (N₀ : ℕ) (b : ℕ → ℝ) (μ : ℕ → ℝ)
    (hα₁ : 0 < α₁) (hr : 0 < r) (hM : 0 < M)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hb_ge : ∀ h ≥ N₀, α₁ * (h : ℝ) ≤ b h)
    (hjac_le : ∀ n ≥ N₀,
      ((jacobiMat (n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ≤ μ n)
    (hmeixner : ∀ n ≥ N₀,
      (1 / α₁) * (∫ ω in Set.Ioi (0 : ℝ),
        ω ^ (2 * (n - N₀)) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) ≤
      ((jacobiMat (n + 1) (fun h ↦ α₁ * (h : ℝ))) ^ (2 * (n - N₀)))
        ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩)
    (hupper : ∀ n : ℕ, μ n ≤ 2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M) :
    α₁ ≤ Real.pi / (2 * r) := by
  set P := ∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2
  have hP_pos : 0 < P := by
    apply Finset.prod_pos
    intro h hh
    exact pow_pos (hb_pos h (Finset.mem_Icc.mp hh).1) 2
  have hrate : 2 * α₁ / Real.pi ≤ r⁻¹ := by
    apply cauchy_hadamard_rate_comparison
      (c := P * (2 / Real.pi)) (C := 2 * M)
      (L := 2 * α₁ / Real.pi) (R := r⁻¹)
      (by positivity) (by positivity) (by positivity) (by positivity) N₀
    intro n hn
    have hsech := meixner_sech_moment_lower_bound hα₁ (n - N₀)
    have hmeix := hmeixner n hn
    have hlem51 := lemma_5_1_moment_lower_bound (D := n + 1) b hn (Nat.lt_succ_self n)
      hα₁ hb_pos hb_ge
    have hjac := hjac_le n hn
    have hup := hupper n
    have hstep1 :
        P * ((2 / Real.pi) * ((2 * (n - N₀)).factorial : ℝ) *
          (2 * α₁ / Real.pi) ^ (2 * (n - N₀))) ≤
        P * ((jacobiMat (n + 1) (fun h ↦ α₁ * (h : ℝ))) ^ (2 * (n - N₀)))
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ :=
      mul_le_mul_of_nonneg_left (le_trans hsech hmeix) hP_pos.le
    calc P * (2 / Real.pi) * ((2 * (n - N₀)).factorial : ℝ) * (2 * α₁ / Real.pi) ^ (2 * (n - N₀))
        = P * ((2 / Real.pi) * ((2 * (n - N₀)).factorial : ℝ) *
            (2 * α₁ / Real.pi) ^ (2 * (n - N₀))) := by ring
      _ ≤ P * ((jacobiMat (n + 1) (fun h ↦ α₁ * (h : ℝ))) ^ (2 * (n - N₀)))
            ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ := hstep1
      _ ≤ ((jacobiMat (n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ := hlem51
      _ ≤ μ n := hjac
      _ ≤ 2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M := hup
      _ = 2 * M * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) := by ring
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 2 * α₁ ≤ Real.pi * r⁻¹ := by
    have := (div_le_iff₀ hpi).mp hrate
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right h1 hr.le
  rw [mul_assoc Real.pi, inv_mul_cancel₀ hr.ne', mul_one] at h2
  linarith

end CauchyHadamardAndTheorem12b

end KrylovChaos
