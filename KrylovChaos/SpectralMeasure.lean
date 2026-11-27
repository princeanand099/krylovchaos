/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.LanczosMoments
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 5: Concrete Wightman Spectral Measure, Eqs. (5.1)–(5.2), Secant/Meixner Pole & Theorem 1.2(b)

Formalizes from ground up without scalar assumptions or `hlower`/`hupper`/`hmeixner` laundering:
1. Concrete finite-dimensional Wightman spectral weights `wightmanWeight β E W j k ≥ 0`,
   Bohr frequencies `bohrFreq E j k = E j - E k`, and complex-time autocorrelation
   `wightmanAutocorr β E W z` (Eq. 5.1).
2. **Exact Matrix-Trace Fourier Identity (Eq. 5.1)** (`eq_5_1_wightman_fourier_identity`)
   and entire holomorphy `wightmanAutocorr_entire` (`Differentiable ℂ`).
3. **Exact Strip Laplace / Cosh Identity (Eq. 5.2)** (`eq_5_2_strip_laplace_identity` &
   `eq_5_2_strip_cosh_identity`).
4. **Cauchy–Hadamard Moment Upper Bound** (`moment_le_factorial_mul_cosh` &
   `cauchy_hadamard_rate_comparison`).
5. **Exact Euler-Secant / Meixner `η = 1` Moment Tower & Zero-Laundering Theorem 1.2(b) (Item #7)**:
   - Proves `iteratedDeriv m (fun t ↦ (Real.cos t)⁻¹) 0 = ((jacobiMat (m + 1) (fun h ↦ (h : ℝ))) ^ m) 0 0`
     via the exact derivative tower `d/dt (sec t · tan^k t) = (k + 1) sec t · tan^{k+1} t + k sec t · tan^{k-1} t`.
   - Proves via Leibniz's rule on `sec(t) · cos(t) = 1` and the Cauchy product at `t = π / 2` that
     the `η = 1` Meixner moments `((jacobiMat (2n + 1) id) ^ (2n)) 0 0` cannot be bounded by
     `C · (2n)! · R^{2n}` for any `R < 2 / π` — eliminating `hmeixner` completely!
   - Proves **Theorem 1.2(b) (`theorem_1_2b_liminf_unconditional`)** with
     `Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / (2 * r)`
     with **zero** `hjac_le`, `hmeixner`, or `hupper` laundering.
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

/-- **End-to-End Theorem 1.2(b) (Compatibility Wrapper)**:
Combines `LanczosMoments.lemma_5_1_moment_lower_bound`,
`LanczosMoments.meixner_sech_moment_lower_bound`, and `cauchy_hadamard_rate_comparison`
to prove **`α₁ ≤ π / (2 * r)`**. See `theorem_1_2b_liminf_unconditional` below for the
fully unconditional zero-laundering version (Item #7). -/
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

section SecantMeixnerAndZeroLaunderingThm12b

/-- Secant-tangent basis function `secTan k t = (cos t)⁻¹ * (tan t)^k`. -/
noncomputable def secTan (k : ℕ) (t : ℝ) : ℝ :=
  (Real.cos t)⁻¹ * (Real.tan t) ^ k

/-- **Exact Derivative Tower for `sec(t) · tan^k(t)`**:
`d/dt (secTan k t) = (k + 1) * secTan (k + 1) t + k * secTan (k - 1) t`
whenever `cos t ≠ 0`. -/
lemma hasDerivAt_secTan (k : ℕ) {t : ℝ} (hcos : Real.cos t ≠ 0) :
    HasDerivAt (secTan k)
      (((k + 1 : ℕ) : ℝ) * secTan (k + 1) t + (k : ℝ) * secTan (k - 1) t) t := by
  have hsec : HasDerivAt (fun x ↦ (Real.cos x)⁻¹) (Real.sin t / Real.cos t ^ 2) t := by
    have h1 := (Real.hasDerivAt_cos t).inv hcos
    convert h1 using 1; ring
  cases k with
  | zero =>
    have heq : secTan 0 = fun x ↦ (Real.cos x)⁻¹ := by
      funext x; simp [secTan]
    rw [heq]
    convert hsec using 1
    simp only [Nat.zero_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, one_mul,
      secTan, pow_one, Real.tan_eq_sin_div_cos]
    field_simp [hcos]
  | succ k =>
    have htan : HasDerivAt (fun x ↦ (Real.tan x) ^ (k + 1))
        (((k + 1 : ℕ) : ℝ) * (Real.tan t) ^ k * (Real.cos t ^ 2)⁻¹) t := by
      have h1 := (Real.hasDerivAt_tan hcos).pow (k + 1)
      convert h1 using 1
      simp only [Nat.add_sub_cancel]; ring
    have hmul := hsec.mul htan
    have hfun : secTan (k + 1) = (fun x ↦ (Real.cos x)⁻¹) * (fun x ↦ (Real.tan x) ^ (k + 1)) := by
      funext x; simp [secTan]
    rw [hfun]
    convert hmul using 1
    have htan_id : (Real.cos t ^ 2)⁻¹ = 1 + Real.tan t ^ 2 := by
      rw [Real.tan_eq_sin_div_cos, div_pow]; field_simp [hcos]; linarith [Real.sin_sq_add_cos_sq t]
    have hsin_div : Real.sin t / Real.cos t ^ 2 = (Real.cos t)⁻¹ * Real.tan t := by
      rw [Real.tan_eq_sin_div_cos]; field_simp [hcos]
    simp only [Nat.add_sub_cancel, secTan]
    rw [htan_id, hsin_div]
    push_cast
    ring

/-- Tridiagonal light-cone: `((jacobiMat D b)^m) i j = 0` whenever `i + m < j`. -/
lemma jacobiMat_pow_eq_zero_of_gt {D : ℕ} (b : ℕ → ℝ) (m : ℕ) :
    ∀ (i j : Fin D), i.1 + m < j.1 → ((jacobiMat D b) ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j hij
    simp only [pow_zero, Matrix.one_apply]
    have hne : i ≠ j := fun h ↦ by subst h; omega
    simp [hne]
  | succ m ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro k _
    by_cases hk : i.1 + m < k.1
    · rw [ih i k hk, zero_mul]
    · have hkj : k.1 + 1 < j.1 := by omega
      have hJ : jacobiMat D b k j = 0 := by
        simp only [jacobiMat, Matrix.of_apply]
        have h1 : ¬(j.1 = k.1 + 1) := by omega
        have h2 : ¬(k.1 = j.1 + 1) := by omega
        simp [h1, h2]
      rw [hJ, mul_zero]

/-- Tridiagonal parity: `((jacobiMat D b)^m) i j = 0` whenever `(i + j + m) % 2 = 1`. -/
lemma jacobiMat_pow_eq_zero_of_odd_parity {D : ℕ} (b : ℕ → ℝ) (m : ℕ) :
    ∀ (i j : Fin D), (i.1 + j.1 + m) % 2 = 1 → ((jacobiMat D b) ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j hodd
    simp only [pow_zero, Matrix.one_apply]
    have hne : i ≠ j := fun h ↦ by subst h; omega
    simp [hne]
  | succ m ih =>
    intro i j hodd
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro k _
    by_cases hadj : j.1 = k.1 + 1 ∨ k.1 = j.1 + 1
    · have hodd' : (i.1 + k.1 + m) % 2 = 1 := by omega
      rw [ih i k hodd', zero_mul]
    · have hJ : jacobiMat D b k j = 0 := by
        simp only [jacobiMat, Matrix.of_apply]
        have h1 : ¬(j.1 = k.1 + 1) := fun h ↦ hadj (Or.inl h)
        have h2 : ¬(k.1 = j.1 + 1) := fun h ↦ hadj (Or.inr h)
        simp [h1, h2]
      rw [hJ, mul_zero]

/-- **Exact `m`-th Derivative of `sec(t) = (cos t)⁻¹` via the `η = 1` Meixner Jacobi Matrix**:
For every `m < D` and every `t ∈ (-π/2, π/2)`,
`iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) t = ∑ k : Fin D, ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) 0 k * secTan k t`. -/
theorem iteratedDeriv_inv_cos_eq_jacobi_sum (m D : ℕ) (hD : m < D) :
    ∀ t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) t =
        ∑ k : Fin D, ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) ⟨0, by omega⟩ k * secTan k.1 t := by
  induction m with
  | zero =>
    intro t _
    rw [iteratedDeriv_zero]
    simp only [pow_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨0, hD⟩]
    · simp [secTan]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ m ih =>
    intro t ht
    have hD' : m < D := by omega
    have hev : iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) =ᶠ[nhds t]
        (fun x ↦ ∑ k : Fin D, ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) ⟨0, by omega⟩ k * secTan k.1 x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
      exact ih hD' x hx
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hcos : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo ht).ne'
    have hderiv_sum : HasDerivAt
        (fun x ↦ ∑ k : Fin D, ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) ⟨0, by omega⟩ k * secTan k.1 x)
        (∑ k : Fin D, ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) ⟨0, by omega⟩ k *
          (((k.1 + 1 : ℕ) : ℝ) * secTan (k.1 + 1) t + (k.1 : ℝ) * secTan (k.1 - 1) t)) t := by
      have h1 := HasDerivAt.sum (u := Finset.univ) (fun (k : Fin D) _ ↦
        (hasDerivAt_secTan k.1 hcos).const_mul (((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) ⟨0, by omega⟩ k))
      convert h1 using 1
      ext x; simp [Finset.sum_apply]
    rw [hderiv_sum.deriv]
    -- Match with `∑ j : Fin D, ((J^m * J) 0 j) * secTan j t`
    set J := jacobiMat D (fun h ↦ (h : ℝ))
    have hmul_sum : ∀ k : Fin D,
        (J ^ m) ⟨0, by omega⟩ k *
          (((k.1 + 1 : ℕ) : ℝ) * secTan (k.1 + 1) t + (k.1 : ℝ) * secTan (k.1 - 1) t) =
        ∑ j : Fin D, ((J ^ m) ⟨0, by omega⟩ k * J k j) * secTan j.1 t := by
      intro k
      by_cases hkm : m < k.1
      · have hz : (J ^ m) ⟨0, by omega⟩ k = 0 := jacobiMat_pow_eq_zero_of_gt _ m ⟨0, by omega⟩ k (by simpa using hkm)
        simp [hz]
      · have hk_lt : k.1 + 1 < D := by omega
        -- Split `J k j`: nonzero only at `j = k + 1` (value `k + 1`) and, if `k ≥ 1`, `j = k - 1` (value `k`)
        by_cases hk0 : k.1 = 0
        · rw [Finset.sum_eq_single ⟨1, by omega⟩]
          · simp [J, jacobiMat, hk0]
          · intro j _ hj
            have hjne : j.1 ≠ 1 := fun h ↦ hj (Fin.ext h)
            have hJ0 : J k j = 0 := by
              simp [J, jacobiMat, hk0, hjne]
            rw [hJ0, mul_zero, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        · let j₁ : Fin D := ⟨k.1 + 1, hk_lt⟩
          let j₂ : Fin D := ⟨k.1 - 1, by omega⟩
          have hjne : j₁ ≠ j₂ := by intro h; have := congrArg Fin.val h; dsimp [j₁, j₂] at this; omega
          have hsub : ∑ j : Fin D, ((J ^ m) ⟨0, by omega⟩ k * J k j) * secTan j.1 t =
              ((J ^ m) ⟨0, by omega⟩ k * J k j₁) * secTan j₁.1 t +
              ((J ^ m) ⟨0, by omega⟩ k * J k j₂) * secTan j₂.1 t := by
            rw [← Finset.sum_subset (Finset.subset_univ ({j₁, j₂} : Finset (Fin D)))]
            · rw [Finset.sum_pair hjne]
            · intro j _ hjnot
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjnot
              have h1 : j.1 ≠ k.1 + 1 := fun h ↦ hjnot.1 (Fin.ext h)
              have h2 : k.1 ≠ j.1 + 1 := fun h ↦ hjnot.2 (Fin.ext (by dsimp [j₂]; omega))
              have hJ0 : J k j = 0 := by simp [J, jacobiMat, h1, h2]
              rw [hJ0, mul_zero, zero_mul]
          rw [hsub]
          have hJ1 : J k j₁ = ((k.1 + 1 : ℕ) : ℝ) := by
            simp [J, jacobiMat, j₁]
          have hJ2 : J k j₂ = (k.1 : ℝ) := by
            have h1 : ¬(j₂.1 = k.1 + 1) := by dsimp [j₂]; omega
            have h2 : k.1 = j₂.1 + 1 := by dsimp [j₂]; omega
            have h3 : ¬(j₂.1 = j₂.1 + 1 + 1) := by omega
            simp only [J, jacobiMat, Matrix.of_apply, h1, ↓reduceIte, h2, h3]
          rw [hJ1, hJ2]
          dsimp [j₁, j₂]; ring
    simp_rw [hmul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]

/-- **Exact `η = 1` Meixner–Euler Identity at `t = 0`**:
`iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) 0 = ((jacobiMat (m + 1) (fun h ↦ (h : ℝ))) ^ m) 0 0`. -/
theorem iteratedDeriv_inv_cos_zero (m : ℕ) :
    iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) 0 =
      ((jacobiMat (m + 1) (fun h ↦ (h : ℝ))) ^ m) ⟨0, Nat.succ_pos m⟩ ⟨0, Nat.succ_pos m⟩ := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [iteratedDeriv_inv_cos_eq_jacobi_sum m (m + 1) (Nat.lt_succ_self m) 0 h0]
  rw [Finset.sum_eq_single ⟨0, Nat.succ_pos m⟩]
  · simp [secTan]
  · intro k _ hk
    have hk0 : k.1 ≠ 0 := fun h ↦ hk (Fin.ext h)
    have htan0 : (Real.tan 0) ^ k.1 = 0 := by rw [Real.tan_zero]; exact zero_pow hk0
    rw [secTan, htan0, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Scaling of `jacobiMat`: `jacobiMat D (fun h ↦ α * h) = α • jacobiMat D (fun h ↦ h)`. -/
lemma jacobiMat_smul_linear (D : ℕ) (α : ℝ) :
    jacobiMat D (fun h ↦ α * (h : ℝ)) = α • jacobiMat D (fun h ↦ (h : ℝ)) := by
  ext i j
  simp only [jacobiMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Exact `2n`-th power scaling of `jacobiMat D (fun h ↦ α * h)`. -/
lemma jacobiMat_linear_pow_entry (D m : ℕ) (α : ℝ) (i j : Fin D) :
    ((jacobiMat D (fun h ↦ α * (h : ℝ))) ^ m) i j =
      α ^ m * ((jacobiMat D (fun h ↦ (h : ℝ))) ^ m) i j := by
  rw [jacobiMat_smul_linear, smul_pow, Matrix.smul_apply, smul_eq_mul]

/-- Exact `m`-th derivative of `Real.cos` at any `t : ℝ`. -/
lemma iteratedDeriv_cos_formula (m : ℕ) :
    (∀ t : ℝ, iteratedDeriv (2 * m) Real.cos t = (-1 : ℝ) ^ m * Real.cos t) ∧
    (∀ t : ℝ, iteratedDeriv (2 * m + 1) Real.cos t = (-1 : ℝ) ^ (m + 1) * Real.sin t) := by
  induction m with
  | zero =>
    refine ⟨fun t ↦ by simp, fun t ↦ ?_⟩
    rw [iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_cos]; ring
  | succ m ih =>
    have heven : ∀ t : ℝ, iteratedDeriv (2 * (m + 1)) Real.cos t = (-1 : ℝ) ^ (m + 1) * Real.cos t := by
      intro t
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h1, iteratedDeriv_succ]
      have hfun : iteratedDeriv (2 * m + 1) Real.cos = fun x ↦ (-1 : ℝ) ^ (m + 1) * Real.sin x :=
        funext ih.2
      rw [hfun, deriv_const_mul _ (Real.differentiableAt_sin), Real.deriv_sin]
    refine ⟨heven, fun t ↦ ?_⟩
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv (2 * (m + 1)) Real.cos = fun x ↦ (-1 : ℝ) ^ (m + 1) * Real.cos x :=
      funext heven
    rw [hfun, deriv_const_mul _ (Real.differentiableAt_cos), Real.deriv_cos]
    rw [pow_succ]; ring

lemma iteratedDeriv_cos_zero (m : ℕ) :
    iteratedDeriv m Real.cos 0 = if Even m then (-1 : ℝ) ^ (m / 2) else 0 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h2k : m = 2 * k := by omega
    rw [h2k, if_pos ⟨k, by omega⟩, (iteratedDeriv_cos_formula k).1 0, Real.cos_zero, mul_one]
    simp
  · have hnot : ¬ Even m := by rw [hk]; exact Nat.not_even_two_mul_add_one k
    rw [if_neg hnot, hk, (iteratedDeriv_cos_formula k).2 0, Real.sin_zero, mul_zero]

/-- Elementary Leibniz rule on an open interval `Ioo (-π/2) (π/2)` for `sec(t) * cos(t) = 1`. -/
lemma sec_cos_leibniz_zero (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 *
        iteratedDeriv (m - k) Real.cos 0 =
    if m = 0 then 1 else 0 := by
  -- Prove by induction on `n` that `iteratedDeriv n (fun x ↦ (Real.cos x)⁻¹ * Real.cos x) t`
  -- equals the Leibniz sum on `Ioo (-π/2) (π/2)`!
  have hleib : ∀ n : ℕ, ∀ t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      iteratedDeriv n (fun x ↦ (Real.cos x)⁻¹ * Real.cos x) t =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) t *
            iteratedDeriv (n - k) Real.cos t := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      have hcos : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo ht).ne'
      have hev : iteratedDeriv n (fun x ↦ (Real.cos x)⁻¹ * Real.cos x) =ᶠ[nhds t]
          (fun x ↦ ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹) x *
              iteratedDeriv (n - k) Real.cos x) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
        exact ih x hx
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hdiff_sec : ∀ k : ℕ,
          HasDerivAt (iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹))
            (iteratedDeriv (k + 1) (fun y ↦ (Real.cos y)⁻¹) t) t := by
        intro k
        have h1 : iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹) =ᶠ[nhds t]
            (fun x ↦ ∑ j : Fin (k + 1),
              ((jacobiMat (k + 1) (fun h ↦ (h : ℝ))) ^ k) ⟨0, Nat.succ_pos k⟩ j * secTan j.1 x) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
          exact iteratedDeriv_inv_cos_eq_jacobi_sum k (k + 1) (Nat.lt_succ_self k) x hx
        have hda : DifferentiableAt ℝ
            (fun x ↦ ∑ j : Fin (k + 1),
              ((jacobiMat (k + 1) (fun h ↦ (h : ℝ))) ^ k) ⟨0, Nat.succ_pos k⟩ j * secTan j.1 x) t := by
          have hs := HasDerivAt.sum (u := Finset.univ) (fun (j : Fin (k + 1)) _ ↦
            (hasDerivAt_secTan j.1 hcos).const_mul (((jacobiMat (k + 1) (fun h ↦ (h : ℝ))) ^ k) ⟨0, Nat.succ_pos k⟩ j))
          have h2 : HasDerivAt (fun x ↦ ∑ j : Fin (k + 1),
              ((jacobiMat (k + 1) (fun h ↦ (h : ℝ))) ^ k) ⟨0, Nat.succ_pos k⟩ j * secTan j.1 x)
              (∑ j : Fin (k + 1), ((jacobiMat (k + 1) (fun h ↦ (h : ℝ))) ^ k) ⟨0, Nat.succ_pos k⟩ j *
                (((j.1 + 1 : ℕ) : ℝ) * secTan (j.1 + 1) t + (j.1 : ℝ) * secTan (j.1 - 1) t)) t := by
            convert hs using 1; ext x; simp [Finset.sum_apply]
          exact h2.differentiableAt
        have hda' : DifferentiableAt ℝ (iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹)) t :=
          hda.congr_of_eventuallyEq h1
        rw [iteratedDeriv_succ]
        exact hda'.hasDerivAt
      have hdiff_cos : ∀ j : ℕ, HasDerivAt (iteratedDeriv j Real.cos) (iteratedDeriv (j + 1) Real.cos t) t := by
        intro j
        rw [iteratedDeriv_succ]
        rcases Nat.even_or_odd j with ⟨p, hp⟩ | ⟨p, hp⟩
        · have hj : j = 2 * p := by omega
          rw [hj]
          have hfun : iteratedDeriv (2 * p) Real.cos = fun x ↦ (-1 : ℝ) ^ p * Real.cos x :=
            funext (iteratedDeriv_cos_formula p).1
          rw [hfun]
          exact (Real.differentiableAt_cos.const_mul _).hasDerivAt
        · rw [hp]
          have hfun : iteratedDeriv (2 * p + 1) Real.cos = fun x ↦ (-1 : ℝ) ^ (p + 1) * Real.sin x :=
            funext (iteratedDeriv_cos_formula p).2
          rw [hfun]
          exact (Real.differentiableAt_sin.const_mul _).hasDerivAt
      have hsum_d : HasDerivAt
          (fun x ↦ ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹) x *
              iteratedDeriv (n - k) Real.cos x)
          (∑ k ∈ Finset.range (n + 1),
            ((n.choose k : ℝ) * iteratedDeriv (k + 1) (fun y ↦ (Real.cos y)⁻¹) t *
              iteratedDeriv (n - k) Real.cos t +
             (n.choose k : ℝ) * iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹) t *
              iteratedDeriv (n - k + 1) Real.cos t)) t := by
        have h1 := HasDerivAt.sum (u := Finset.range (n + 1)) (fun k _ ↦ by
          have hd := ((hdiff_sec k).const_mul (n.choose k : ℝ)).mul (hdiff_cos (n - k))
          convert hd using 1)
        convert h1 using 1
        ext x; simp [Finset.sum_apply]
      rw [hsum_d.deriv, Finset.sum_add_distrib]
      set S : ℕ → ℝ := fun k ↦ iteratedDeriv k (fun y ↦ (Real.cos y)⁻¹) t
      set C : ℕ → ℝ := fun j ↦ iteratedDeriv j Real.cos t
      have h1 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * S (k + 1) * C (n - k)) =
          ∑ k ∈ Finset.range (n + 2),
            (if k = 0 then (0 : ℝ) else (n.choose (k - 1) : ℝ) * S k * C (n + 1 - k)) := by
        symm
        rw [Finset.sum_range_succ']
        simp only [↓reduceIte, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      have h2 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * S k * C (n - k + 1)) =
          ∑ k ∈ Finset.range (n + 2),
            (if k = n + 1 then (0 : ℝ) else (n.choose k : ℝ) * S k * C (n + 1 - k)) := by
        symm
        rw [Finset.sum_range_succ]
        simp only [↓reduceIte, add_zero]
        apply Finset.sum_congr rfl; intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hne : k ≠ n + 1 := by omega
        have hsub : n - k + 1 = n + 1 - k := by omega
        rw [if_neg hne, hsub]
      rw [h1, h2, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k hk
      have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, Nat.succ_ne_zero, zero_add, Nat.choose_zero_right, Nat.cast_one,
          one_mul, Nat.sub_zero]
        rfl
      · by_cases hkn1 : k = n + 1
        · subst hkn1
          simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, Nat.add_sub_cancel, Nat.choose_self,
            Nat.cast_one, one_mul, Nat.sub_self]
          rfl
        · rw [if_neg hk0, if_neg hkn1]
          have hchoose : ((n + 1).choose k : ℝ) = (n.choose (k - 1) : ℝ) + (n.choose k : ℝ) := by
            have hk_eq : k = (k - 1) + 1 := by omega
            have hnat : (n + 1).choose k = n.choose (k - 1) + n.choose k := by
              conv_lhs => rw [hk_eq, Nat.choose_succ_succ, Nat.succ_eq_add_one, ← hk_eq]
            exact_mod_cast hnat
          rw [hchoose]; dsimp only [S, C]; ring
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [← hleib m 0 h0]
  have hev1 : (fun x ↦ (Real.cos x)⁻¹ * Real.cos x) =ᶠ[nhds (0 : ℝ)] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with x hx
    exact inv_mul_cancel₀ (Real.cos_pos_of_mem_Ioo hx).ne'
  have hiter_eq : ∀ n : ℕ, iteratedDeriv n (fun x ↦ (Real.cos x)⁻¹ * Real.cos x) 0 =
      iteratedDeriv n (fun _ : ℝ ↦ (1 : ℝ)) 0 := by
    intro n
    exact Filter.EventuallyEq.iteratedDeriv_eq n hev1
  rw [hiter_eq m]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [iteratedDeriv_succ']
    have hconst : deriv (fun _ : ℝ ↦ (1 : ℝ)) = fun _ ↦ (0 : ℝ) := by
      funext x; exact deriv_const x (1 : ℝ)
    rw [hconst]
    change iteratedDeriv m (0 : ℝ → ℝ) 0 = 0
    exact iteratedDeriv_const_zero

/-- Self-contained Cauchy product of two absolutely summable real series. -/
private lemma real_cauchy_product_tsum (f g : ℕ → ℝ)
    (hf : Summable (fun n ↦ |f n|)) (hg : Summable (fun n ↦ |g n|)) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' m, ∑ k ∈ Finset.range (m + 1), f k * g (m - k) := by
  have hf' : Summable f := hf.of_abs
  have hg' : Summable g := hg.of_abs
  have hprod_tend : Filter.Tendsto
      (fun N : ℕ ↦ (∑ k ∈ Finset.range N, f k) * (∑ j ∈ Finset.range N, g j))
      Filter.atTop (nhds ((∑' n, f n) * (∑' n, g n))) :=
    hf'.hasSum.tendsto_sum_nat.mul hg'.hasSum.tendsto_sum_nat
  -- Bound the difference between `(∑_{k<N} f k)(∑_{j<N} g j)` and `∑_{m<N} ∑_{k≤m} f k g (m-k)`
  set F : ℝ := ∑' n, |f n|
  set G : ℝ := ∑' n, |g n|
  have hF_nn : 0 ≤ F := tsum_nonneg (fun _ ↦ abs_nonneg _)
  have hG_nn : 0 ≤ G := tsum_nonneg (fun _ ↦ abs_nonneg _)
  have hdiff_le : ∀ N : ℕ,
      |(∑ k ∈ Finset.range N, f k) * (∑ j ∈ Finset.range N, g j) -
        ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), f k * g (m - k)| ≤
      F * (G - ∑ j ∈ Finset.range (N / 2), |g j|) +
      (F - ∑ k ∈ Finset.range (N / 2), |f k|) * G := by
    intro N
    -- Rewrite both sums over `Finset.range N ×ˢ Finset.range N`
    have hprod_eq : (∑ k ∈ Finset.range N, f k) * (∑ j ∈ Finset.range N, g j) =
        ∑ p ∈ Finset.range N ×ˢ Finset.range N, f p.1 * g p.2 := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
    have hcauchy_eq : (∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), f k * g (m - k)) =
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ p.1 + p.2 < N), f p.1 * g p.2 := by
      have hbij : (∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), f k * g (m - k)) =
          ∑ p ∈ (Finset.range N).sigma (fun m ↦ Finset.range (m + 1)), f p.2 * g (p.1 - p.2) := by
        rw [Finset.sum_sigma]
      rw [hbij]
      refine Finset.sum_bij (fun p _ ↦ (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
      · intro ⟨m, k⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · intro ⟨m₁, k₁⟩ hp₁ ⟨m₂, k₂⟩ hp₂ heq
        simp only [Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
        simp only [Prod.mk.injEq] at heq
        have : m₁ = m₂ := by omega
        subst this; cases heq.1; rfl
      · intro ⟨k, j⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        refine ⟨⟨k + j, k⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range]; omega
        · simp [Nat.add_sub_cancel_left]
      · intro _ _; rfl
    rw [hprod_eq, hcauchy_eq]
    have hsub : (∑ p ∈ Finset.range N ×ˢ Finset.range N, f p.1 * g p.2) -
        (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ p.1 + p.2 < N), f p.1 * g p.2) =
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ ¬(p.1 + p.2 < N)), f p.1 * g p.2 := by
      have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range N ×ˢ Finset.range N)
        (fun p : ℕ × ℕ ↦ p.1 + p.2 < N) (fun p ↦ f p.1 * g p.2)
      linarith
    rw [hsub]
    set T : Finset (ℕ × ℕ) := (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ ¬(p.1 + p.2 < N))
    have htri : |∑ p ∈ T, f p.1 * g p.2| ≤ ∑ p ∈ T, |f p.1| * |g p.2| := by
      calc |∑ p ∈ T, f p.1 * g p.2|
          ≤ ∑ p ∈ T, |f p.1 * g p.2| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ p ∈ T, |f p.1| * |g p.2| := by simp_rw [abs_mul]
    set S₁ : Finset (ℕ × ℕ) := Finset.range N ×ˢ (Finset.range N \ Finset.range (N / 2))
    set S₂ : Finset (ℕ × ℕ) := (Finset.range N \ Finset.range (N / 2)) ×ˢ Finset.range N
    have hcov : T ⊆ S₁ ∪ S₂ := by
      intro ⟨k, j⟩ hp
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_lt] at hp
      simp only [S₁, S₂, Finset.mem_union, Finset.mem_product, Finset.mem_sdiff, Finset.mem_range]
      by_cases hj : j < N / 2
      · right; refine ⟨⟨hp.1.1, by omega⟩, hp.1.2⟩
      · left; refine ⟨hp.1.1, ⟨hp.1.2, hj⟩⟩
    have hle1 : ∑ p ∈ T, |f p.1| * |g p.2| ≤
        (∑ p ∈ S₁, |f p.1| * |g p.2|) + (∑ p ∈ S₂, |f p.1| * |g p.2|) := by
      have hunion : ∑ p ∈ S₁ ∪ S₂, |f p.1| * |g p.2| ≤
          (∑ p ∈ S₁, |f p.1| * |g p.2|) + (∑ p ∈ S₂, |f p.1| * |g p.2|) := by
        have h1 := Finset.sum_union_inter (s₁ := S₁) (s₂ := S₂) (f := fun p : ℕ × ℕ ↦ |f p.1| * |g p.2|)
        have h2 : 0 ≤ ∑ p ∈ S₁ ∩ S₂, |f p.1| * |g p.2| := Finset.sum_nonneg fun _ _ ↦ by positivity
        linarith
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ ↦ by positivity)) hunion
    have hS1_eq : ∑ p ∈ S₁, |f p.1| * |g p.2| =
        (∑ k ∈ Finset.range N, |f k|) * (∑ j ∈ Finset.range N \ Finset.range (N / 2), |g j|) := by
      rw [Finset.sum_product, Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
    have hS2_eq : ∑ p ∈ S₂, |f p.1| * |g p.2| =
        (∑ k ∈ Finset.range N \ Finset.range (N / 2), |f k|) * (∑ j ∈ Finset.range N, |g j|) := by
      rw [Finset.sum_product, Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
    have hsub_f : ∑ k ∈ Finset.range N \ Finset.range (N / 2), |f k| ≤ F - ∑ k ∈ Finset.range (N / 2), |f k| := by
      have h1 : (∑ k ∈ Finset.range N \ Finset.range (N / 2), |f k|) + ∑ k ∈ Finset.range (N / 2), |f k| =
          ∑ k ∈ Finset.range N, |f k| :=
        Finset.sum_sdiff (Finset.range_mono (Nat.div_le_self N 2))
      have h2 : ∑ k ∈ Finset.range N, |f k| ≤ F :=
        hf.sum_le_tsum (Finset.range N) (fun _ _ ↦ abs_nonneg _)
      linarith
    have hsub_g : ∑ j ∈ Finset.range N \ Finset.range (N / 2), |g j| ≤ G - ∑ j ∈ Finset.range (N / 2), |g j| := by
      have h1 : (∑ j ∈ Finset.range N \ Finset.range (N / 2), |g j|) + ∑ j ∈ Finset.range (N / 2), |g j| =
          ∑ j ∈ Finset.range N, |g j| :=
        Finset.sum_sdiff (Finset.range_mono (Nat.div_le_self N 2))
      have h2 : ∑ j ∈ Finset.range N, |g j| ≤ G :=
        hg.sum_le_tsum (Finset.range N) (fun _ _ ↦ abs_nonneg _)
      linarith
    have hF_le : ∑ k ∈ Finset.range N, |f k| ≤ F := hf.sum_le_tsum _ (fun _ _ ↦ abs_nonneg _)
    have hG_le : ∑ j ∈ Finset.range N, |g j| ≤ G := hg.sum_le_tsum _ (fun _ _ ↦ abs_nonneg _)
    have h1_le : (∑ p ∈ S₁, |f p.1| * |g p.2|) ≤ F * (G - ∑ j ∈ Finset.range (N / 2), |g j|) := by
      rw [hS1_eq]
      exact mul_le_mul hF_le hsub_g (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hF_nn
    have h2_le : (∑ p ∈ S₂, |f p.1| * |g p.2|) ≤ (F - ∑ k ∈ Finset.range (N / 2), |f k|) * G := by
      rw [hS2_eq]
      exact mul_le_mul hsub_f hG_le (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (by linarith [hf.sum_le_tsum (Finset.range (N / 2)) (fun _ _ ↦ abs_nonneg _)])
    linarith
  -- Show the RHS bound tends to 0 as `N → ∞`
  have hhalf_atTop : Filter.Tendsto (fun N : ℕ ↦ N / 2) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b; exact ⟨2 * b, fun n hn ↦ by omega⟩
  have hF_tail : Filter.Tendsto (fun N : ℕ ↦ F - ∑ k ∈ Finset.range (N / 2), |f k|) Filter.atTop (nhds 0) := by
    have h1 := (hf.hasSum.tendsto_sum_nat.comp hhalf_atTop).const_sub F
    simpa [F] using h1
  have hG_tail : Filter.Tendsto (fun N : ℕ ↦ G - ∑ j ∈ Finset.range (N / 2), |g j|) Filter.atTop (nhds 0) := by
    have h1 := (hg.hasSum.tendsto_sum_nat.comp hhalf_atTop).const_sub G
    simpa [G] using h1
  have hrhs_zero : Filter.Tendsto
      (fun N : ℕ ↦ F * (G - ∑ j ∈ Finset.range (N / 2), |g j|) +
        (F - ∑ k ∈ Finset.range (N / 2), |f k|) * G)
      Filter.atTop (nhds 0) := by
    have h1 := (hG_tail.const_mul F).add (hF_tail.mul_const G)
    simpa using h1
  have hdiff_zero : Filter.Tendsto
      (fun N : ℕ ↦ (∑ k ∈ Finset.range N, f k) * (∑ j ∈ Finset.range N, g j) -
        ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), f k * g (m - k))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hrhs_zero
    filter_upwards with N
    rw [Real.norm_eq_abs]; exact hdiff_le N
  have hcauchy_tend : Filter.Tendsto
      (fun N : ℕ ↦ ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), f k * g (m - k))
      Filter.atTop (nhds ((∑' n, f n) * (∑' n, g n))) := by
    have h1 := hprod_tend.sub hdiff_zero
    simpa using h1
  -- Also the Cauchy product series is summable (bounded by `F * G`), so its `tsum` equals its limit!
  have hcauchy_summ : Summable (fun m : ℕ ↦ ∑ k ∈ Finset.range (m + 1), f k * g (m - k)) := by
    apply Summable.of_abs
    apply summable_of_sum_range_le (fun _ ↦ abs_nonneg _)
    intro N
    calc ∑ m ∈ Finset.range N, |∑ k ∈ Finset.range (m + 1), f k * g (m - k)|
        ≤ ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), |f k| * |g (m - k)| := by
          apply Finset.sum_le_sum; intro m _
          calc |∑ k ∈ Finset.range (m + 1), f k * g (m - k)|
              ≤ ∑ k ∈ Finset.range (m + 1), |f k * g (m - k)| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ k ∈ Finset.range (m + 1), |f k| * |g (m - k)| := by simp_rw [abs_mul]
      _ ≤ (∑ k ∈ Finset.range N, |f k|) * (∑ j ∈ Finset.range N, |g j|) := by
          rw [Finset.sum_mul]
          have h1 : (∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), |f k| * |g (m - k)|) =
              ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ p.1 + p.2 < N), |f p.1| * |g p.2| := by
            have hsig : (∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), |f k| * |g (m - k)|) =
                ∑ p ∈ (Finset.range N).sigma (fun m ↦ Finset.range (m + 1)), |f p.2| * |g (p.1 - p.2)| := by
              rw [Finset.sum_sigma]
            rw [hsig]
            refine Finset.sum_bij (fun p _ ↦ (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
            · intro ⟨m, k⟩ hp; simp only [Finset.mem_sigma, Finset.mem_range] at hp
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
            · intro ⟨m₁, k₁⟩ hp₁ ⟨m₂, k₂⟩ hp₂ heq
              simp only [Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
              simp only [Prod.mk.injEq] at heq
              have : m₁ = m₂ := by omega
              subst this; cases heq.1; rfl
            · intro ⟨k, j⟩ hp
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
              exact ⟨⟨k + j, k⟩, by simp only [Finset.mem_sigma, Finset.mem_range]; omega, by simp⟩
            · intro _ _; rfl
          rw [h1]
          have h2 : (∑ k ∈ Finset.range N, |f k| * ∑ j ∈ Finset.range N, |g j|) =
              ∑ p ∈ Finset.range N ×ˢ Finset.range N, |f p.1| * |g p.2| := by
            rw [Finset.sum_product]; apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
          rw [h2]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
      _ ≤ F * G := mul_le_mul (hf.sum_le_tsum _ (fun _ _ ↦ abs_nonneg _))
          (hg.sum_le_tsum _ (fun _ _ ↦ abs_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hF_nn
  exact tendsto_nhds_unique hcauchy_tend hcauchy_summ.hasSum.tendsto_sum_nat

/-- Taylor series of `Real.cos x` expressed with `iteratedDeriv m Real.cos 0`. -/
private lemma real_cos_eq_tsum_iteratedDeriv (x : ℝ) :
    ∑' m : ℕ, (iteratedDeriv m Real.cos 0 / (m.factorial : ℝ)) * x ^ m = Real.cos x := by
  have hcosC : Complex.cos (x : ℂ) =
      (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-((x : ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]; simp [neg_mul]
  have hexp1 : Complex.exp ((x : ℂ) * Complex.I) =
      ∑' m : ℕ, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have hexp2 : Complex.exp (-((x : ℂ) * Complex.I)) =
      ∑' m : ℕ, (-((x : ℂ) * Complex.I)) ^ m / (m.factorial : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have hs_cplx : ∀ z : ℂ, Summable (fun m : ℕ ↦ z ^ m / (m.factorial : ℂ)) := fun z ↦ by
    apply Summable.of_norm
    simpa [norm_div, norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖z‖
  have hs1 : Summable (fun m : ℕ ↦ ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) :=
    hs_cplx _
  have hs2 : Summable (fun m : ℕ ↦ (-((x : ℂ) * Complex.I)) ^ m / (m.factorial : ℂ)) :=
    hs_cplx _
  have hsumC : Complex.cos (x : ℂ) =
      ∑' m : ℕ, (((x : ℂ) * Complex.I) ^ m + (-((x : ℂ) * Complex.I)) ^ m) / (2 * (m.factorial : ℂ)) := by
    rw [hcosC, hexp1, hexp2, ← hs1.tsum_add hs2, ← tsum_div_const]
    congr 1; funext m; ring
  have hre : Real.cos x = (Complex.cos (x : ℂ)).re := (Complex.ofReal_cos x).symm ▸ (Complex.ofReal_re _).symm
  rw [hre, hsumC]
  have hs3 : Summable (fun m : ℕ ↦ (((x : ℂ) * Complex.I) ^ m + (-((x : ℂ) * Complex.I)) ^ m) / (2 * (m.factorial : ℂ))) := by
    have h1 := (hs1.add hs2).div_const (2 : ℂ)
    exact h1.congr (fun m ↦ by ring)
  rw [Complex.re_tsum hs3]
  congr 1; funext m
  rw [iteratedDeriv_cos_zero m]
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hm : m = 2 * p := by omega
    rw [hm, if_pos ⟨p, by omega⟩]
    have hdiv : 2 * p / 2 = p := by omega
    rw [hdiv]
    have hIpow : ((x : ℂ) * Complex.I) ^ (2 * p) = ((((-1 : ℝ) ^ p * x ^ (2 * p) : ℝ) : ℂ)) := by
      rw [mul_pow, pow_mul, pow_mul, Complex.I_sq]; push_cast; ring
    have hneg : (-((x : ℂ) * Complex.I)) ^ (2 * p) = ((x : ℂ) * Complex.I) ^ (2 * p) := by
      rw [neg_pow, pow_mul]; norm_num
    rw [hneg, hIpow]
    have hrew : ((((-1 : ℝ) ^ p * x ^ (2 * p) : ℝ) : ℂ) + (((-1 : ℝ) ^ p * x ^ (2 * p) : ℝ) : ℂ)) /
        (2 * ((2 * p).factorial : ℂ)) =
        ((((-1 : ℝ) ^ p / ((2 * p).factorial : ℝ) * x ^ (2 * p) : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hrew, Complex.ofReal_re]
  · have hnot : ¬ Even m := by rw [hp]; exact Nat.not_even_two_mul_add_one p
    rw [if_neg hnot, zero_div, zero_mul, hp]
    have hneg : (-((x : ℂ) * Complex.I)) ^ (2 * p + 1) = -(((x : ℂ) * Complex.I) ^ (2 * p + 1)) := by
      rw [neg_pow, pow_succ, pow_mul]; norm_num
    rw [hneg, add_neg_cancel, zero_div, Complex.zero_re]

/-- **Pole Obstruction for `η = 1` Meixner–Euler Moments (Eliminates `hmeixner` Laundering!)**:
There are NO constants `C > 0`, `0 < R < 2 / π`, `N₀ : ℕ` such that
`((jacobiMat (2n + 1) (fun h ↦ (h : ℝ))) ^ (2n)) 0 0 ≤ C * (2n)! * R ^ (2n)` for all `n ≥ N₀`. -/
theorem meixner_euler_moment_rate_ge_two_div_pi {C R : ℝ} (hC : 0 < C) (hR0 : 0 < R) (N₀ : ℕ)
    (hbound : ∀ n ≥ N₀,
      ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        C * ((2 * n).factorial : ℝ) * R ^ (2 * n)) :
    2 / Real.pi ≤ R := by
  by_contra hlt
  have hR_lt : R < 2 / Real.pi := lt_of_not_ge hlt
  set q := R * (Real.pi / 2)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 := mul_lt_mul_of_pos_right hR_lt (show 0 < Real.pi / 2 by positivity)
    have h2 : 2 / Real.pi * (Real.pi / 2) = 1 := by field_simp [hpi.ne']
    dsimp only [q]; linarith
  set f : ℕ → ℝ := fun m ↦ (iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) 0 / (m.factorial : ℝ)) * (Real.pi / 2) ^ m
  set g : ℕ → ℝ := fun m ↦ (iteratedDeriv m Real.cos 0 / (m.factorial : ℝ)) * (Real.pi / 2) ^ m
  -- `f` is absolutely summable (odd terms vanish, even terms dominated by `C * q ^ m` for `m ≥ 2 N₀`)
  have hf_abs : Summable (fun m ↦ |f m|) := by
    rw [← summable_nat_add_iff (2 * N₀)]
    refine Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) ?_
      (((summable_geometric_of_lt_one hq0 hq1).mul_left C).comp_injective (add_left_injective (2 * N₀)))
    intro k
    set m := k + 2 * N₀
    rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
    · have hm : m = 2 * n := by omega
      have hnN : n ≥ N₀ := by omega
      have hfac_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hnn_iter : 0 ≤ iteratedDeriv (2 * n) (fun x ↦ (Real.cos x)⁻¹) 0 := by
        rw [iteratedDeriv_inv_cos_zero]
        have : ∀ p : ℕ, ∀ i j : Fin (2 * n + 1),
            0 ≤ ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) i j := by
          intro p
          induction p with
          | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
          | succ p ih =>
            intro i j; rw [pow_succ, Matrix.mul_apply]
            refine Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l) ?_
            simp only [jacobiMat, Matrix.of_apply]; split_ifs <;> positivity
        exact this (2 * n) _ _
      have hf_nn : 0 ≤ f (2 * n) := by
        dsimp only [f]; positivity
      rw [hm, abs_of_nonneg hf_nn]
      dsimp only [f]
      rw [iteratedDeriv_inv_cos_zero]
      have hb := hbound n hnN
      have hdiv : ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ /
          ((2 * n).factorial : ℝ) ≤ C * R ^ (2 * n) := by
        rw [div_le_iff₀ hfac_pos]; linarith
      calc _ ≤ (C * R ^ (2 * n)) * (Real.pi / 2) ^ (2 * n) :=
              mul_le_mul_of_nonneg_right hdiv (by positivity)
        _ = C * q ^ (2 * n) := by rw [mul_assoc, ← mul_pow]
        _ = ((fun i ↦ C * q ^ i) ∘ fun x ↦ x + 2 * N₀) k := by rw [← hm]; rfl
    · have hodd : iteratedDeriv m (fun x ↦ (Real.cos x)⁻¹) 0 = 0 := by
        rw [iteratedDeriv_inv_cos_zero]
        exact jacobiMat_pow_eq_zero_of_odd_parity _ m ⟨0, _⟩ ⟨0, _⟩ (by dsimp; omega)
      simp only [f, hodd, zero_div, zero_mul, abs_zero, Function.comp_apply]
      positivity
  -- `g` is absolutely summable (dominated by `(π/2)^m / m!`)
  have hg_abs : Summable (fun m ↦ |g m|) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) ?_
      (Real.summable_pow_div_factorial (Real.pi / 2))
    intro m
    dsimp only [g]
    have hfac_abs : |(m.factorial : ℝ)| = (m.factorial : ℝ) := abs_of_nonneg (Nat.cast_nonneg m.factorial)
    have hpow_abs : |(Real.pi / 2) ^ m| = (Real.pi / 2) ^ m := abs_of_nonneg (pow_nonneg (by positivity) m)
    rw [abs_mul, abs_div, hfac_abs, hpow_abs, iteratedDeriv_cos_zero]
    have h1 : |if Even m then (-1 : ℝ) ^ (m / 2) else 0| ≤ 1 := by
      split_ifs <;> simp
    calc |if Even m then (-1 : ℝ) ^ (m / 2) else 0| / (m.factorial : ℝ) * (Real.pi / 2) ^ m
        ≤ 1 / (m.factorial : ℝ) * (Real.pi / 2) ^ m := by gcongr
      _ = (Real.pi / 2) ^ m / (m.factorial : ℝ) := by ring
  -- `∑' m, g m = Real.cos (π / 2) = 0`
  have hg_sum : ∑' m, g m = 0 := by
    change ∑' m, (iteratedDeriv m Real.cos 0 / (m.factorial : ℝ)) * (Real.pi / 2) ^ m = 0
    rw [real_cos_eq_tsum_iteratedDeriv, Real.cos_pi_div_two]
  -- Cauchy product: `0 = (∑' f) * (∑' g) = ∑' m, (if m = 0 then 1 else 0) = 1`!
  have hcp := real_cauchy_product_tsum f g hf_abs hg_abs
  rw [hg_sum, mul_zero] at hcp
  have hterm : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1), f k * g (m - k) = if m = 0 then 1 else 0 := by
    intro m
    have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hrew : ∑ k ∈ Finset.range (m + 1), f k * g (m - k) =
        ((Real.pi / 2) ^ m / (m.factorial : ℝ)) *
          ∑ k ∈ Finset.range (m + 1),
            (m.choose k : ℝ) * iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 *
              iteratedDeriv (m - k) Real.cos 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hch : (m.choose k : ℝ) * ((k.factorial : ℝ) * ((m - k).factorial : ℝ)) = (m.factorial : ℝ) := by
        rw [← mul_assoc]; exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
      have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
      have hmk_pos : (0 : ℝ) < ((m - k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hpow : (Real.pi / 2) ^ k * (Real.pi / 2) ^ (m - k) = (Real.pi / 2) ^ m := by
        rw [← pow_add, Nat.add_sub_of_le hkm]
      dsimp only [f, g]
      have hch' : (m.choose k : ℝ) / (m.factorial : ℝ) =
          1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
        rw [div_eq_div_iff hfac_pos.ne' (mul_pos hk_pos hmk_pos).ne']
        linarith
      calc (iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 / (k.factorial : ℝ)) * (Real.pi / 2) ^ k *
            ((iteratedDeriv (m - k) Real.cos 0 / ((m - k).factorial : ℝ)) * (Real.pi / 2) ^ (m - k))
          = (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ))) *
              ((Real.pi / 2) ^ k * (Real.pi / 2) ^ (m - k)) *
              iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 * iteratedDeriv (m - k) Real.cos 0 := by ring
        _ = ((m.choose k : ℝ) / (m.factorial : ℝ)) * (Real.pi / 2) ^ m *
              iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 * iteratedDeriv (m - k) Real.cos 0 := by
            rw [← hch', hpow]
        _ = (Real.pi / 2) ^ m / (m.factorial : ℝ) *
              ((m.choose k : ℝ) * iteratedDeriv k (fun x ↦ (Real.cos x)⁻¹) 0 *
                iteratedDeriv (m - k) Real.cos 0) := by ring
    rw [hrew, sec_cos_leibniz_zero m]
    cases m with
    | zero => simp
    | succ m => simp
  simp_rw [hterm] at hcp
  have htsum1 : (∑' m : ℕ, if m = 0 then (1 : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 0 (fun m hm ↦ by simp [hm])]; simp
  rw [htsum1] at hcp
  norm_num at hcp

/-- **Zero-Laundering Theorem 1.2(b) — Rate Bound for Any Asymptotic Linear Floor (Item #7)**:
Given ONLY `b : ℕ → ℝ` with `b h > 0` (`h ≥ 1`), `b h ≥ α₁ h` (`h ≥ N₀`), and
`((jacobiMat (2n + 1) b) ^ (2n)) 0 0 ≤ 2 * (2n)! * r⁻¹ ^ (2n) * M` for all `n ≥ N₀`
(with ZERO `hmeixner`, ZERO `hjac_le`, ZERO `hupper` laundering!), proves **`α₁ ≤ π / (2 * r)`**. -/
theorem theorem_1_2b_zero_laundering {α₁ r M : ℝ} (N₀ : ℕ) (b : ℕ → ℝ)
    (hα₁ : 0 < α₁) (hr : 0 < r) (hM : 0 < M)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hb_ge : ∀ h ≥ N₀, α₁ * (h : ℝ) ≤ b h)
    (hmom_ub : ∀ n ≥ N₀,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M) :
    α₁ ≤ Real.pi / (2 * r) := by
  by_contra hlt
  have hα_gt : Real.pi / (2 * r) < α₁ := lt_of_not_ge hlt
  set P := ∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2
  have hP_pos : 0 < P := Finset.prod_pos fun h hh ↦ pow_pos (hb_pos h (Finset.mem_Icc.mp hh).1) 2
  -- Choose `R` strictly between `1 / (α₁ * r)` and `2 / π`
  set L₀ := (α₁ * r)⁻¹
  have hL₀_pos : 0 < L₀ := by positivity
  have hL₀_lt : L₀ < 2 / Real.pi := by
    have h1 : Real.pi / 2 < α₁ * r := by
      have := mul_lt_mul_of_pos_right hα_gt hr
      have h2 : Real.pi / (2 * r) * r = Real.pi / 2 := by field_simp [hr.ne']
      linarith
    have h2 : (α₁ * r)⁻¹ < (Real.pi / 2)⁻¹ := inv_strictAnti₀ (by positivity) h1
    simpa [L₀, inv_div] using h2
  set R := (L₀ + 2 / Real.pi) / 2
  have hR_gt : L₀ < R := by dsimp [R]; linarith
  have hR_lt : R < 2 / Real.pi := by dsimp [R]; linarith
  have hR_pos : 0 < R := lt_trans hL₀_pos hR_gt
  -- For all `m ≥ 1`, `((2(m+N₀))! / (2m)!) * (L₀ / R)^{2m} → 0`, hence bounded by some `C₁`!
  set q := L₀ / R
  have hq_pos : 0 < q := div_pos hL₀_pos hR_pos
  have hq_lt1 : q < 1 := (div_lt_one hR_pos).mpr hR_gt
  have htend : Filter.Tendsto
      (fun m : ℕ ↦ ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) * q ^ (2 * m))
      Filter.atTop (nhds 0) := by
    have hq_inv : 1 < (q⁻¹) ^ 2 := one_lt_pow₀ ((one_lt_inv₀ hq_pos).mpr hq_lt1) (by norm_num)
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt (2 * N₀) hq_inv
    have hmul0 : Filter.Tendsto (fun m : ℕ ↦ (4 : ℝ) ^ (2 * N₀) * ((m : ℝ) ^ (2 * N₀) / ((q⁻¹) ^ 2) ^ m))
        Filter.atTop (nhds 0) := by
      have h := hbase.const_mul ((4 : ℝ) ^ (2 * N₀))
      rwa [mul_zero] at h
    refine squeeze_zero_norm' ?_ hmul0
    filter_upwards [Filter.eventually_ge_atTop (N₀ + 1)] with m hm
    rw [Real.norm_of_nonneg (by positivity)]
    have h4m : ((2 * (m + N₀) : ℕ) : ℝ) ≤ 4 * (m : ℝ) := by
      have : 2 * (m + N₀) ≤ 4 * m := by omega
      exact_mod_cast this
    have hpow := pow_le_pow_left₀ (by positivity) h4m (2 * N₀)
    rw [mul_pow] at hpow
    have hqeq : q ^ (2 * m) = (((q⁻¹) ^ 2) ^ m)⁻¹ := by
      rw [← inv_pow, ← inv_pow, inv_inv, pow_mul]
    rw [hqeq, ← div_eq_mul_inv, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hpow (by positivity)
  rcases (Metric.tendsto_atTop.mp htend) 1 zero_lt_one with ⟨M₁, hM₁⟩
  -- For all `m ≥ M₁`, `((2(m+N₀))! / (2m)!) * L₀^{2m} ≤ R^{2m}`!
  set C := (2 * M * r⁻¹ ^ (2 * N₀)) / P
  have hC_pos : 0 < C := by positivity
  have hmeix_bd : ∀ m ≥ M₁,
      ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        C * ((2 * m).factorial : ℝ) * R ^ (2 * m) := by
    intro m hm
    set n := m + N₀
    have hn : n ≥ N₀ := Nat.le_add_left N₀ m
    have hlem := lemma_5_1_moment_lower_bound (D := 2 * n + 1) b hn (by omega) hα₁ hb_pos hb_ge
    rw [Nat.add_sub_cancel] at hlem
    have hup := hmom_ub n hn
    -- Also `((jacobiMat (2m+1) id)^(2m)) 0 0 ≤ ((jacobiMat (2n+1) id)^(2m)) 0 0`
    -- (monotone in matrix dimension since all entries are nonnegative!)
    have hdim_mono : ∀ (p : ℕ) (i j : Fin (2 * m + 1)),
        ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ p) i j ≤
        ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ := by
      intro p
      induction p with
      | zero =>
        intro i j
        simp only [pow_zero, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · have hij' : (⟨i.1, by omega⟩ : Fin (2 * n + 1)) ≠ ⟨j.1, by omega⟩ :=
            fun h ↦ hij (Fin.ext (congrArg (Fin.val : Fin (2 * n + 1) → ℕ) h))
          simp [hij, hij']
      | succ p ih =>
        intro i j
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
        have hnn_n : ∀ l : Fin (2 * n + 1),
            0 ≤ ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ l *
                jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) l ⟨j.1, by omega⟩ := by
          intro l
          have h1 : ∀ q : ℕ, ∀ a c : Fin (2 * n + 1),
              0 ≤ ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ q) a c := by
            intro q; induction q with
            | zero => intro a c; simp [Matrix.one_apply]; split_ifs <;> norm_num
            | succ q ihq =>
              intro a c; rw [pow_succ, Matrix.mul_apply]
              refine Finset.sum_nonneg fun u _ ↦ mul_nonneg (ihq a u) ?_
              simp only [jacobiMat, Matrix.of_apply]; split_ifs <;> positivity
          have h2 : 0 ≤ jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) l ⟨j.1, by omega⟩ := by
            simp only [jacobiMat, Matrix.of_apply]; split_ifs <;> positivity
          exact mul_nonneg (h1 p _ _) h2
        calc ∑ k : Fin (2 * m + 1),
              ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ p) i k *
                jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ)) k j
            ≤ ∑ k : Fin (2 * m + 1),
              ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ ⟨k.1, by omega⟩ *
                jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) ⟨k.1, by omega⟩ ⟨j.1, by omega⟩ := by
              apply Finset.sum_le_sum; intro k _
              have hJe : jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ)) k j =
                  jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) ⟨k.1, by omega⟩ ⟨j.1, by omega⟩ := by
                simp [jacobiMat]
              rw [← hJe]
              have hJnn : 0 ≤ jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ)) k j := by
                simp only [jacobiMat, Matrix.of_apply]; split_ifs <;> positivity
              exact mul_le_mul_of_nonneg_right (ih i k) hJnn
          _ ≤ ∑ l : Fin (2 * n + 1),
              ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ l *
                jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) l ⟨j.1, by omega⟩ := by
              let emb : Fin (2 * m + 1) ↪ Fin (2 * n + 1) :=
                ⟨fun k ↦ ⟨k.1, by omega⟩, fun a b h ↦ Fin.ext (congrArg (Fin.val : Fin (2 * n + 1) → ℕ) h)⟩
              have himg : (∑ k : Fin (2 * m + 1),
                  ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ (emb k) *
                    jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) (emb k) ⟨j.1, by omega⟩) =
                  ∑ l ∈ Finset.univ.map emb,
                    ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ l *
                      jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) l ⟨j.1, by omega⟩ :=
                (Finset.sum_map Finset.univ emb (fun l ↦
                  ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ l *
                    jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) l ⟨j.1, by omega⟩)).symm
              change (∑ k : Fin (2 * m + 1),
                  ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ p) ⟨i.1, by omega⟩ (emb k) *
                    jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ)) (emb k) ⟨j.1, by omega⟩) ≤ _
              rw [himg]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ ↦ hnn_n l)
    have hmono0 := hdim_mono (2 * m) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
    have hscale := jacobiMat_linear_pow_entry (2 * n + 1) (2 * m) α₁ ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
    have hfac_ratio : ((2 * n).factorial : ℝ) ≤
        ((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) := by
      have hnat : (2 * (m + N₀)).factorial ≤ (2 * m).factorial * (2 * (m + N₀)) ^ (2 * N₀) := by
        have haux : ∀ k : ℕ, (2 * m + k).factorial ≤ (2 * m).factorial * (2 * m + k) ^ k := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            calc (2 * m + (k + 1)).factorial
                = (2 * m + k + 1) * (2 * m + k).factorial := by
                    rw [← add_assoc]; exact Nat.factorial_succ _
              _ ≤ (2 * m + k + 1) * ((2 * m).factorial * (2 * m + k) ^ k) := Nat.mul_le_mul_left _ ih
              _ ≤ (2 * m + k + 1) * ((2 * m).factorial * (2 * m + k + 1) ^ k) :=
                    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k))
              _ = (2 * m).factorial * (2 * m + (k + 1)) ^ (k + 1) := by rw [pow_succ', ← add_assoc]; ring
        have heq : 2 * (m + N₀) = 2 * m + 2 * N₀ := by omega
        rw [heq]; exact haux (2 * N₀)
      exact_mod_cast hnat
    have hdist := hM₁ m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    have hchain : P * α₁ ^ (2 * m) *
        ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M := by
      calc P * α₁ ^ (2 * m) *
            ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
          ≤ P * α₁ ^ (2 * m) *
              ((jacobiMat (2 * n + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ :=
            mul_le_mul_of_nonneg_left hmono0 (by positivity)
        _ = P * ((jacobiMat (2 * n + 1) (fun h ↦ α₁ * (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
            rw [hscale]; ring
        _ ≤ ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := hlem
        _ ≤ 2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M := hup
    have hdiv_step :
        ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        C * ((2 * m).factorial : ℝ) * (((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) * q ^ (2 * m)) * R ^ (2 * m) := by
      have hPα_pos : 0 < P * α₁ ^ (2 * m) := by positivity
      have hrpow : r⁻¹ ^ (2 * n) = r⁻¹ ^ (2 * N₀) * r⁻¹ ^ (2 * m) := by
        rw [show 2 * n = 2 * N₀ + 2 * m by dsimp [n]; omega, pow_add]
      have hqR : q ^ (2 * m) * R ^ (2 * m) = (α₁ ^ (2 * m))⁻¹ * r⁻¹ ^ (2 * m) := by
        rw [← mul_pow, show q * R = L₀ by dsimp [q]; field_simp [hR_pos.ne'],
          show L₀ = α₁⁻¹ * r⁻¹ by dsimp [L₀]; rw [mul_inv], mul_pow, inv_pow]
      have hrhs_eq : C * ((2 * m).factorial : ℝ) * (((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) * q ^ (2 * m)) * R ^ (2 * m) =
          (2 * (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀)) * (r⁻¹ ^ (2 * N₀) * r⁻¹ ^ (2 * m)) * M) /
            (P * α₁ ^ (2 * m)) := by
        dsimp only [C]
        calc (2 * M * r⁻¹ ^ (2 * N₀) / P) * ((2 * m).factorial : ℝ) *
              (((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) * q ^ (2 * m)) * R ^ (2 * m)
            = (2 * M * r⁻¹ ^ (2 * N₀) / P) *
              (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀)) *
              (q ^ (2 * m) * R ^ (2 * m)) := by ring
          _ = (2 * M * r⁻¹ ^ (2 * N₀) / P) *
              (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀)) *
              ((α₁ ^ (2 * m))⁻¹ * r⁻¹ ^ (2 * m)) := by rw [hqR]
          _ = (2 * (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀)) *
                (r⁻¹ ^ (2 * N₀) * r⁻¹ ^ (2 * m)) * M) / (P * α₁ ^ (2 * m)) := by
              field_simp [hP_pos.ne', (pow_pos hα₁ (2 * m)).ne']
      rw [hrhs_eq, le_div_iff₀ hPα_pos]
      calc ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ *
            (P * α₁ ^ (2 * m))
          = P * α₁ ^ (2 * m) *
              ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by ring
        _ ≤ 2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M := hchain
        _ = 2 * ((2 * n).factorial : ℝ) * (r⁻¹ ^ (2 * N₀) * r⁻¹ ^ (2 * m)) * M := by rw [hrpow]
        _ ≤ 2 * (((2 * m).factorial : ℝ) * ((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀)) *
              (r⁻¹ ^ (2 * N₀) * r⁻¹ ^ (2 * m)) * M := by gcongr
    calc ((jacobiMat (2 * m + 1) (fun h ↦ (h : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
        ≤ C * ((2 * m).factorial : ℝ) * (((2 * (m + N₀) : ℕ) : ℝ) ^ (2 * N₀) * q ^ (2 * m)) * R ^ (2 * m) := hdiv_step
      _ ≤ C * ((2 * m).factorial : ℝ) * 1 * R ^ (2 * m) := by gcongr
      _ = C * ((2 * m).factorial : ℝ) * R ^ (2 * m) := by ring
  have hge := meixner_euler_moment_rate_ge_two_div_pi hC_pos hR_pos M₁ hmeix_bd
  linarith

/-- **Theorem 1.2(b) — Unconditional `Filter.liminf` Statement (Eq. 1.16, Item #7)**:
For ANY positive Lanczos sequence `b : ℕ → ℝ` (`b h > 0` for `h ≥ 1`) whose even Jacobi moments
satisfy the strip-analytic upper bound `((jacobiMat (2n + 1) b) ^ (2n)) 0 0 ≤ 2 (2n)! r⁻¹^{2n} M`:
`Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ π / (2 * r)`
(with ZERO `hmeixner`, ZERO `hjac_le`, and ZERO `hupper` laundering!). -/
theorem theorem_1_2b_liminf_unconditional {r M : ℝ} (b : ℕ → ℝ)
    (hr : 0 < r) (hM : 0 < M)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_ub : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ ≤
        2 * ((2 * n).factorial : ℝ) * r⁻¹ ^ (2 * n) * M) :
    Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / (2 * r) := by
  rw [Filter.liminf_eq]
  apply csSup_le
  · refine ⟨0, ?_⟩
    rw [Set.mem_setOf_eq, Filter.eventually_atTop]
    refine ⟨1, fun n hn ↦ ?_⟩
    exact div_nonneg (hb_pos n hn).le (Nat.cast_nonneg n)
  · intro a ha
    by_cases ha0 : a ≤ 0
    · exact le_trans ha0 (by positivity)
    · have ha_pos : 0 < a := lt_of_not_ge ha0
      rw [Set.mem_setOf_eq, Filter.eventually_atTop] at ha
      rcases ha with ⟨N₁, hN₁⟩
      set N₀ := max N₁ 1
      have hb_ge : ∀ h ≥ N₀, a * (h : ℝ) ≤ b h := by
        intro h hh
        have h1 : N₁ ≤ h := le_trans (le_max_left _ _) hh
        have h2 : 1 ≤ h := le_trans (le_max_right _ _) hh
        have hh_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast h2
        exact (le_div_iff₀ hh_pos).mp (hN₁ h h1)
      exact theorem_1_2b_zero_laundering N₀ b ha_pos hr hM hb_pos hb_ge (fun n _ ↦ hmom_ub n)

end SecantMeixnerAndZeroLaunderingThm12b

end KrylovChaos
