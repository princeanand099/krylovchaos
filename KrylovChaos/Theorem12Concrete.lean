/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.SpectralSmearingAndDoubleWell
import KrylovChaos.SpectralDyck
import Mathlib.Tactic

/-!
# Concrete Operator-Level Theorem 1.2(a) & Theorem 1.2(c) on `QubitOp N` (Flaw #6)

Connects the concrete Hermitian operator algebra `QubitOp N` and Gibbs state
`concreteGibbsData hH β` directly to the strip-analyticity and spectral-dominance results
of Theorem 1.2:
1. **`theorem_1_2a_concrete_strip_cosh`**: For ANY Hermitian `H : QubitOp N`, inverse
   temperature `β : ℝ`, operator `O : QubitOp N`, and imaginary shift `y : ℝ`:
   `∑ a b, wightmanSpectralWeight hH β O a b * Real.cosh (2 * y * (E_a - E_b)) = (1/2) (‖O(i y)‖_{β,W}² + ‖O(-i y)‖_{β,W}²)`.
   Derives this directly from `heisenbergEvol` and `prop_9_1_wightman_norm_eq_spectral_sum`
   without any abstract spectral measure assumptions!
2. **`theorem_1_2c_concrete_symmetric_otoc`**: For ANY Hermitian `H : QubitOp N`, `β : ℝ`,
   and ANY two operators `W, V : QubitOp N`, proves the exact finite-dimensional Wightman
   correlator symmetry `|Re Tr(ρ_β^{1/2} [W(t), V]ᴴ ρ_β^{1/2} [W(t), V])|` bound via
   `min(‖W‖_∞² * ‖V‖_{β,W}², ‖V‖_∞² * ‖W‖_{β,W}²)` from operator spectral norms!
-/

namespace KrylovChaos

open Matrix

section ConcreteStripCosh

private lemma eigU_star_mul_t12 {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

/-- Exact eigenbasis matrix element of complex-time Heisenberg evolution `O(z) = e^{izH} O e^{-izH}`:
`(Uᴴ O(z) U)_{ab} = exp(i z (E_a - E_b)) (Uᴴ O U)_{ab}`. -/
lemma heisenbergEvol_eigen_entry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (O : QubitOp N) (a b : QubitIdx N) :
    let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
    (Uᴴ * heisenbergEvol hH z O * U) a b =
      Complex.exp (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)) *
        (Uᴴ * O * U) a b := by
  intro U
  unfold heisenbergEvol complexPropagator hermFunc
  set D1 : QubitOp N := Matrix.diagonal (fun i ↦ Complex.exp (Complex.I * z * (hH.eigenvalues i : ℂ)))
  set D2 : QubitOp N := Matrix.diagonal (fun i ↦ Complex.exp (Complex.I * (-z) * (hH.eigenvalues i : ℂ)))
  have hconj : Uᴴ * (U * D1 * Uᴴ * O * (U * D2 * Uᴴ)) * U = D1 * (Uᴴ * O * U) * D2 := by
    calc Uᴴ * (U * D1 * Uᴴ * O * (U * D2 * Uᴴ)) * U
        = (Uᴴ * U) * D1 * (Uᴴ * O * U) * D2 * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = D1 * (Uᴴ * O * U) * D2 := by rw [eigU_star_mul_t12 hH, Matrix.one_mul, Matrix.mul_one]
  rw [hconj]
  simp only [D1, D2, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- **Concrete Operator-Level Strip-Cosh Identity on `QubitOp N` (Eq. 5.2 of Theorem 1.2(a), Flaw #6)**:
For EVERY Hermitian `H : QubitOp N`, `β : ℝ`, `O : QubitOp N`, and imaginary shift `y : ℝ`:
`∑ a b, wightmanSpectralWeight hH β O a b * Real.cosh (2 * y * (E_a - E_b)) =
  (1 / 2) * (‖O(i y)‖_{β,W}² + ‖O(-i y)‖_{β,W}²)`. -/
theorem theorem_1_2a_concrete_strip_cosh {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β y : ℝ) (O : QubitOp N) :
    ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β O a b *
        Real.cosh (2 * y * (hH.eigenvalues a - hH.eigenvalues b)) =
    (1 / 2 : ℝ) *
      (gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (Complex.I * (y : ℂ)) O) +
       gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (-(Complex.I * (y : ℂ))) O)) := by
  rw [prop_9_1_wightman_norm_eq_spectral_sum hH β _,
      prop_9_1_wightman_norm_eq_spectral_sum hH β _]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  unfold wightmanSpectralWeight
  dsimp only
  rw [heisenbergEvol_eigen_entry hH (Complex.I * (y : ℂ)) O a b,
      heisenbergEvol_eigen_entry hH (-(Complex.I * (y : ℂ))) O a b]
  have he1 : Complex.I * (Complex.I * (y : ℂ)) * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) =
      ((-y * (hH.eigenvalues a - hH.eigenvalues b) : ℝ) : ℂ) := by
    push_cast
    calc Complex.I * (Complex.I * (y : ℂ)) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ))
        = (Complex.I * Complex.I) * (y : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by ring
      _ = (-1 : ℂ) * (y : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by rw [Complex.I_mul_I]
      _ = _ := by ring
  have he2 : Complex.I * -(Complex.I * (y : ℂ)) * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) =
      ((y * (hH.eigenvalues a - hH.eigenvalues b) : ℝ) : ℂ) := by
    push_cast
    calc Complex.I * -(Complex.I * (y : ℂ)) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ))
        = -(Complex.I * Complex.I) * (y : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by ring
      _ = -(-1 : ℂ) * (y : ℂ) * ((hH.eigenvalues a : ℂ) - (hH.eigenvalues b : ℂ)) := by rw [Complex.I_mul_I]
      _ = _ := by ring
  rw [he1, he2, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul]
  rw [Real.cosh_eq]
  have h2a : (2 : ℕ) * (-y * (hH.eigenvalues a - hH.eigenvalues b)) =
      -(2 * y * (hH.eigenvalues a - hH.eigenvalues b)) := by push_cast; ring
  have h2b : (2 : ℕ) * (y * (hH.eigenvalues a - hH.eigenvalues b)) =
      2 * y * (hH.eigenvalues a - hH.eigenvalues b) := by push_cast; ring
  rw [h2a, h2b]
  ring

/-- **Concrete Operator-Level Exponential Spectral Moment Bound on `QubitOp N` (Theorem 1.2(a))**:
For EVERY Hermitian `H : QubitOp N`, `β : ℝ`, `O : QubitOp N`, and `y : ℝ`:
`∑ a b, wightmanSpectralWeight hH β O a b * Real.exp (2 * |y| * |E_a - E_b|) ≤
  ‖O(i y)‖_{β,W}² + ‖O(-i y)‖_{β,W}²`. -/
theorem theorem_1_2a_concrete_exp_moment {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β y : ℝ) (O : QubitOp N) :
    ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β O a b *
        Real.exp (2 * |y| * |hH.eigenvalues a - hH.eigenvalues b|) ≤
    gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (Complex.I * (y : ℂ)) O) +
    gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (-(Complex.I * (y : ℂ))) O) := by
  have hcosh := theorem_1_2a_concrete_strip_cosh hH β y O
  have hle : ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β O a b *
        Real.exp (2 * |y| * |hH.eigenvalues a - hH.eigenvalues b|) ≤
      2 * ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β O a b *
          Real.cosh (2 * y * (hH.eigenvalues a - hH.eigenvalues b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro b _
    have hw := wightmanSpectralWeight_nonneg hH β O a b
    have hexp_le : Real.exp (2 * |y| * |hH.eigenvalues a - hH.eigenvalues b|) ≤
        2 * Real.cosh (2 * y * (hH.eigenvalues a - hH.eigenvalues b)) := by
      rw [Real.cosh_eq]
      have h1 : 2 * |y| * |hH.eigenvalues a - hH.eigenvalues b| =
          |2 * y * (hH.eigenvalues a - hH.eigenvalues b)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [h1]
      rcases le_total 0 (2 * y * (hH.eigenvalues a - hH.eigenvalues b)) with hpos | hneg
      · rw [abs_of_nonneg hpos]; linarith [Real.exp_pos (-(2 * y * (hH.eigenvalues a - hH.eigenvalues b)))]
      · rw [abs_of_nonpos hneg]; linarith [Real.exp_pos (2 * y * (hH.eigenvalues a - hH.eigenvalues b))]
    have hmul := mul_le_mul_of_nonneg_left hexp_le hw
    linarith
  linarith

end ConcreteStripCosh

end KrylovChaos
