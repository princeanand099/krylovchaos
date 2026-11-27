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
import KrylovChaos.CausalExpansion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Concrete Operator-Level Theorem 1.2(a) on `QubitOp N` (Eqs. 5.2–5.4)

Connects the concrete Hermitian operator algebra `QubitOp N` and Gibbs state
`concreteGibbsData hH β` directly to the exact asymmetric strip-analyticity chain of
Theorem 1.2(a) (Eqs. 5.2–5.4 of `finite_temp_krylov_chaos.tex`):
1. **`theorem_1_2a_concrete_eq52_trace_bound`**: For Hermitian `H, W : QubitOp N` and any
   `β, κ' : ℝ`, proves Eq. (5.2):
   `∑ a b, wightmanSpectralWeight hH β W a b * exp ((β / 2 + κ') * |E_a - E_b|) ≤
      2 * Re Tr(ρ_β W W(-i κ'))`.
2. **`theorem_1_2a_concrete_eq53_opNorm_bound`**: Proves Eq. (5.3):
   `Re Tr(ρ_β W W(-i κ')) ≤ ‖W‖_∞ * ‖W(-i κ')‖_∞`.
3. **`theorem_1_2a_concrete_eq54_r_local_bound`**: For any `r`-local Hamiltonian (`r ≥ 2`) with
   site norm `≤ Jsite` and Hermitian `W ∈ supportedOn U₀` (`U₀.card ≤ sW`), proves the exact
   generalized-binomial rising-factorial bound for `0 ≤ κ' < κ = 1 / (2 (r - 1) Jsite)`:
   `‖W(-i κ')‖_∞ ≤ ‖W‖_∞ * (1 - κ' / κ)^(-sW / (r - 1))`,
   and combines Eqs. (5.2)–(5.4) into the full concrete finite-volume Theorem 1.2(a) bound:
   `∑ a b, wightmanSpectralWeight hH β W a b * exp ((β / 2 + κ') * |E_a - E_b|) ≤
      2 * ‖W‖_∞^2 * (1 - κ' / κ)^(-sW / (r - 1))`.
4. **`theorem_1_2a_concrete_strip_cosh`** & **`theorem_1_2a_concrete_exp_moment`**:
   Symmetric imaginary-time cosh identity for arbitrary `O : QubitOp N` and `y : ℝ`.
-/

namespace KrylovChaos

open Matrix

section ConcreteStripCosh

private lemma eigU_star_mul_t12 {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

private lemma eigU_mul_star_t12 {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

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

/-- Symmetric imaginary-time strip-cosh identity on `QubitOp N`:
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

/-- Symmetric exponential spectral moment bound on `QubitOp N`. -/
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

section AsymmetricEq52To54

/-- Exact eigenbasis formula for `Re Tr(ρ_β W W(-i κ'))` when `W` is Hermitian. -/
lemma trace_gibbsRho_mul_evol_eq {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (β κ' : ℝ) :
    (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        (gibbsPartitionFn hH β)⁻¹ *
          Real.exp (-β * hH.eigenvalues a + κ' * (hH.eigenvalues b - hH.eigenvalues a)) *
          ‖((hH.eigenvectorUnitary : QubitOp N)ᴴ * W * (hH.eigenvectorUnitary : QubitOp N)) a b‖ ^ 2 := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set Z : ℝ := gibbsPartitionFn hH β
  set Dρ : QubitOp N := Matrix.diagonal (fun a ↦ ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ))
  have hρ_eq : gibbsRho hH β = U * Dρ * Uᴴ := by
    unfold gibbsRho hermFunc
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 2
    ext i j
    simp only [Dρ, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp [Z, Complex.ofReal_exp]
  have hcyc : Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W) =
      Matrix.trace (Dρ * (Uᴴ * W * U) * (Uᴴ * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W * U)) := by
    rw [hρ_eq]
    have h1 : U * Dρ * Uᴴ * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W =
        U * (Dρ * Uᴴ * W * (1 * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)) := by
      simp only [Matrix.one_mul, Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm, ← eigU_mul_star_t12 hH]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [hcyc]
  simp only [Dρ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [heisenbergEvol_eigen_entry hH (-(Complex.I * (κ' : ℂ))) W b a]
  have hexp_c : Complex.I * -(Complex.I * (κ' : ℂ)) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ) =
      ((κ' * (hH.eigenvalues b - hH.eigenvalues a) : ℝ) : ℂ) := by
    push_cast
    calc Complex.I * -(Complex.I * (κ' : ℂ)) * ((hH.eigenvalues b : ℂ) - (hH.eigenvalues a : ℂ))
        = -(Complex.I * Complex.I) * (κ' : ℂ) * ((hH.eigenvalues b : ℂ) - (hH.eigenvalues a : ℂ)) := by ring
      _ = -(-1 : ℂ) * (κ' : ℂ) * ((hH.eigenvalues b : ℂ) - (hH.eigenvalues a : ℂ)) := by rw [Complex.I_mul_I]
      _ = _ := by ring
  rw [hexp_c, ← Complex.ofReal_exp]
  have hWherm : (Uᴴ * W * U) b a = star ((Uᴴ * W * U) a b) := by
    have hh : (Uᴴ * W * U)ᴴ = Uᴴ * W * U := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hW.eq, Matrix.mul_assoc]
    have := congrFun (congrFun hh a) b
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [hWherm]
  have hmul_star : (Uᴴ * W * U) a b * star ((Uᴴ * W * U) a b) = ((‖(Uᴴ * W * U) a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre_term : ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) * (Uᴴ * W * U) a b *
      (((Real.exp (κ' * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) * star ((Uᴴ * W * U) a b)) =
      (((Z⁻¹ * Real.exp (-β * hH.eigenvalues a + κ' * (hH.eigenvalues b - hH.eigenvalues a)) *
        ‖(Uᴴ * W * U) a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [Real.exp_add]
    calc ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) * (Uᴴ * W * U) a b *
          (((Real.exp (κ' * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) * star ((Uᴴ * W * U) a b))
        = ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) *
          ((Real.exp (κ' * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) *
          ((Uᴴ * W * U) a b * star ((Uᴴ * W * U) a b)) := by ring
      _ = ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) *
          ((Real.exp (κ' * (hH.eigenvalues b - hH.eigenvalues a)) : ℝ) : ℂ) *
          ((‖(Uᴴ * W * U) a b‖ ^ 2 : ℝ) : ℂ) := by rw [hmul_star]
      _ = _ := by push_cast; ring
  rw [hre_term, Complex.ofReal_re]

/-- **Theorem 1.2(a), Eq. (5.2) (Asymmetric Exponential Spectral Moment Bound)**:
For EVERY Hermitian `H, W : QubitOp N`, inverse temperature `β : ℝ`, and `κ' : ℝ` (with NO
smallness restriction on `β`):
`∑ a b, wightmanSpectralWeight hH β W a b * exp ((β / 2 + κ') * |E_a - E_b|) ≤
  2 * Re Tr(ρ_β W W(-i κ'))`. -/
theorem theorem_1_2a_concrete_eq52_trace_bound {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (β κ' : ℝ) :
    ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β W a b *
        Real.exp ((β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b|) ≤
    2 * (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hsym_w : ∀ a b : QubitIdx N,
      wightmanSpectralWeight hH β W b a = wightmanSpectralWeight hH β W a b := by
    intro a b
    unfold wightmanSpectralWeight
    have hWherm : (Uᴴ * W * U) b a = star ((Uᴴ * W * U) a b) := by
      have hh : (Uᴴ * W * U)ᴴ = Uᴴ * W * U := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hW.eq, Matrix.mul_assoc]
      have := congrFun (congrFun hh a) b
      simpa [Matrix.conjTranspose_apply] using this.symm
    have hnorm : ‖(Uᴴ * W * U) b a‖ = ‖(Uᴴ * W * U) a b‖ := by
      rw [hWherm, norm_star]
    rw [hnorm, add_comm (hH.eigenvalues b)]
  have hle_sum : ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β W a b *
        Real.exp ((β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b|) ≤
      (∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a))) +
      (∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro b _
    have hw := wightmanSpectralWeight_nonneg hH β W a b
    have hexp : Real.exp ((β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b|) ≤
        Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a)) +
        Real.exp ((β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b)) := by
      rcases le_total (hH.eigenvalues a) (hH.eigenvalues b) with hab | hba
      · have habs : |hH.eigenvalues a - hH.eigenvalues b| = hH.eigenvalues b - hH.eigenvalues a := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [habs]; linarith [Real.exp_pos ((β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b))]
      · have habs : |hH.eigenvalues a - hH.eigenvalues b| = hH.eigenvalues a - hH.eigenvalues b :=
          abs_of_nonneg (by linarith)
        rw [habs]; linarith [Real.exp_pos ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a))]
    nlinarith
  have hswap : (∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * (hH.eigenvalues a - hH.eigenvalues b))) =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hsym_w b a]
  have htr_eq : (∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a))) =
      (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re := by
    rw [trace_gibbsRho_mul_evol_eq hH hW β κ']
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold wightmanSpectralWeight
    have hexp_eq : Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) *
        Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a)) =
        Real.exp (-β * hH.eigenvalues a + κ' * (hH.eigenvalues b - hH.eigenvalues a)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (gibbsPartitionFn hH β)⁻¹ *
            Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) *
            ‖(Uᴴ * W * U) a b‖ ^ 2 *
            Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a))
        = (gibbsPartitionFn hH β)⁻¹ *
            (Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) *
             Real.exp ((β / 2 + κ') * (hH.eigenvalues b - hH.eigenvalues a))) *
            ‖(Uᴴ * W * U) a b‖ ^ 2 := by ring
      _ = _ := by rw [hexp_eq]
  linarith

/-- Any diagonal matrix entry is bounded in norm by the operator norm `opNorm M`. -/
lemma norm_diag_entry_le_opNorm {N : ℕ} (M : QubitOp N) (a : QubitIdx N) :
    ‖M a a‖ ≤ opNorm M := by
  let e : EuclideanSpace ℂ (QubitIdx N) := WithLp.toLp 2 (Pi.single a (1 : ℂ))
  have he_norm : ‖e‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ i : QubitIdx N, ‖e i‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single a]
      · simp [e]
      · intro i _ hia; simp [e, Pi.single_eq_of_ne hia]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    rw [hsq, Real.sqrt_one]
  have hentry : (opToCLM M e) a = M a a := by
    simp only [opToCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, e]
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hja; simp [Pi.single_eq_of_ne hja]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  have h1 : ‖M a a‖ ≤ ‖opToCLM M e‖ := by
    rw [← hentry]
    exact PiLp.norm_apply_le (opToCLM M e) a
  have h2 : ‖opToCLM M e‖ ≤ opNorm M * ‖e‖ := ContinuousLinearMap.le_opNorm (opToCLM M) e
  rw [he_norm, mul_one] at h2
  exact le_trans h1 h2

/-- Gibbs expectation value bound: `‖Tr(ρ_β X)‖ ≤ ‖X‖_∞` for every `X : QubitOp N`. -/
lemma norm_trace_gibbsRho_mul_le_opNorm {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (X : QubitOp N) :
    ‖Matrix.trace (gibbsRho hH β * X)‖ ≤ opNorm X := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set Z : ℝ := gibbsPartitionFn hH β
  set Dρ : QubitOp N := Matrix.diagonal (fun a ↦ ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ))
  have hρ_eq : gibbsRho hH β = U * Dρ * Uᴴ := by
    unfold gibbsRho hermFunc
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 2
    ext i j
    simp only [Dρ, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp [Z, Complex.ofReal_exp]
  have hcyc : Matrix.trace (gibbsRho hH β * X) = Matrix.trace (Dρ * (Uᴴ * X * U)) := by
    rw [hρ_eq]
    have h1 : U * Dρ * Uᴴ * X = U * (Dρ * Uᴴ * X) := by simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    congr 1; simp only [Matrix.mul_assoc]
  rw [hcyc]
  have htr : Matrix.trace (Dρ * (Uᴴ * X * U)) =
      ∑ a : QubitIdx N, ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) * (Uᴴ * X * U) a a := by
    simp only [Dρ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [htr]
  have hZpos : 0 < Z := gibbsPartitionFn_pos hH β
  have hop_conj : opNorm (Uᴴ * X * U) ≤ opNorm X := by
    have hU : opNorm U ≤ 1 := opNorm_unitary_le (eigU_star_mul_t12 hH)
    have hUH : opNorm Uᴴ ≤ 1 := opNorm_unitary_le (by rw [Matrix.conjTranspose_conjTranspose]; exact eigU_mul_star_t12 hH)
    calc opNorm (Uᴴ * X * U)
        ≤ opNorm (Uᴴ * X) * opNorm U := opNorm_mul_le _ _
      _ ≤ (opNorm Uᴴ * opNorm X) * opNorm U :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * opNorm X) * 1 := by
          apply mul_le_mul _ hU (opNorm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hUH (opNorm_nonneg _)
      _ = opNorm X := by ring
  calc ‖∑ a : QubitIdx N, ((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) * (Uᴴ * X * U) a a‖
      ≤ ∑ a : QubitIdx N, ‖((Z⁻¹ * Real.exp (-β * hH.eigenvalues a) : ℝ) : ℂ) * (Uᴴ * X * U) a a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : QubitIdx N, (Z⁻¹ * Real.exp (-β * hH.eigenvalues a)) * opNorm X := by
        apply Finset.sum_le_sum; intro a _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (mul_pos (inv_pos.mpr hZpos) (Real.exp_pos _))]
        exact mul_le_mul_of_nonneg_left
          (le_trans (norm_diag_entry_le_opNorm (Uᴴ * X * U) a) hop_conj) (by positivity)
    _ = (Z⁻¹ * ∑ a : QubitIdx N, Real.exp (-β * hH.eigenvalues a)) * opNorm X := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = opNorm X := by
        have hsum_eq : ∑ a : QubitIdx N, Real.exp (-β * hH.eigenvalues a) = Z := rfl
        rw [hsum_eq, inv_mul_cancel₀ hZpos.ne', one_mul]

/-- **Theorem 1.2(a), Eq. (5.3) (Operator-Norm Trace Bound)**:
`Re Tr(ρ_β W W(-i κ')) ≤ ‖W‖_∞ * ‖W(-i κ')‖_∞`. -/
theorem theorem_1_2a_concrete_eq53_opNorm_bound {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β κ' : ℝ) (W : QubitOp N) :
    (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re ≤
      opNorm W * opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W) := by
  have h1 : (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re ≤
      ‖Matrix.trace (gibbsRho hH β * (W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W))‖ := by
    rw [Matrix.mul_assoc]
    exact Complex.re_le_norm _
  have h2 := norm_trace_gibbsRho_mul_le_opNorm hH β (W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)
  have h3 := opNorm_mul_le W (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)
  exact le_trans h1 (le_trans h2 h3)

/-- Rising-factorial binomial coefficient `c(α, k) = (∏_{j=0}^{k-1} (α + j)) / k!`. -/
noncomputable def risingBinomCoeff (α : ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (α + (j : ℝ))) / (k.factorial : ℝ)

lemma risingBinomCoeff_nonneg {α : ℝ} (hα : 0 ≤ α) (k : ℕ) : 0 ≤ risingBinomCoeff α k := by
  unfold risingBinomCoeff
  exact div_nonneg (Finset.prod_nonneg fun j _ ↦ by positivity) (Nat.cast_nonneg _)

lemma risingBinomCoeff_zero (α : ℝ) : risingBinomCoeff α 0 = 1 := by
  simp [risingBinomCoeff]

lemma risingBinomCoeff_succ (α : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) = (α + (k : ℝ)) * risingBinomCoeff α k := by
  unfold risingBinomCoeff
  rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp [hk1, hkf]

/-- Generalized negative-binomial series bound proved via finite-sum differentiation of
`g_M(x) = (1 - x)^α * ∑_{k=0}^M c(α, k) x^k`:
for every `α ≥ 0` and `0 ≤ q < 1`, the series `∑' k, risingBinomCoeff α k * q^k` is summable
and bounded above by `(1 - q) ^ (-α)`. -/
lemma risingBinom_tsum_le_rpow {α q : ℝ} (hα : 0 ≤ α) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun k : ℕ ↦ risingBinomCoeff α k * q ^ k) ∧
    (∑' k : ℕ, risingBinomCoeff α k * q ^ k) ≤ (1 - q) ^ (-α) := by
  have hpart : ∀ M : ℕ,
      ∑ k ∈ Finset.range (M + 1), risingBinomCoeff α k * q ^ k ≤ (1 - q) ^ (-α) := by
    intro M
    let S : ℝ → ℝ := fun x ↦ ∑ k ∈ Finset.range (M + 1), risingBinomCoeff α k * x ^ k
    let g : ℝ → ℝ := fun x ↦ (1 - x) ^ α * S x
    have hderiv_S : ∀ x : ℝ,
        HasDerivAt S (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) x := by
      intro x
      have hsum : HasDerivAt S
          (∑ k ∈ Finset.range (M + 1), risingBinomCoeff α k * ((k : ℝ) * x ^ (k - 1))) x := by
        dsimp only [S]
        convert HasDerivAt.fun_sum (u := Finset.range (M + 1))
          (A := fun k x ↦ risingBinomCoeff α k * x ^ k)
          (A' := fun k ↦ risingBinomCoeff α k * ((k : ℝ) * x ^ (k - 1))) (fun k _ ↦
            (hasDerivAt_pow k x).const_mul (risingBinomCoeff α k)) using 1
      have heq_d : (∑ k ∈ Finset.range (M + 1), risingBinomCoeff α k * ((k : ℝ) * x ^ (k - 1))) =
          ∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        apply Finset.sum_congr rfl; intro k _
        simp only [Nat.add_sub_cancel]
        have hr := risingBinomCoeff_succ α k
        calc risingBinomCoeff α (k + 1) * (((k + 1 : ℕ) : ℝ) * x ^ k)
            = (((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1)) * x ^ k := by ring
          _ = (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k := by rw [hr]
      rwa [heq_d] at hsum
    have hderiv_g : ∀ x ∈ Set.Icc (0 : ℝ) q,
        HasDerivAt g
          (-((α + (M : ℝ)) * risingBinomCoeff α M * (1 - x) ^ (α - 1) * x ^ M)) x := by
      intro x hx
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have hd1 : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ α) (α * (1 - x) ^ (α - 1) * (-1)) x := by
        have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
          simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
        exact hsub.rpow_const (Or.inl h1x.ne')
      have hd_prod := hd1.mul (hderiv_S x)
      have halg : (1 - x) * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) -
          α * S x = -((α + (M : ℝ)) * risingBinomCoeff α M * x ^ M) := by
        have hmulx : x * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) =
            ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) * x ^ (k + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          rw [← risingBinomCoeff_succ α k, pow_succ]; ring
        have hsplit : (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) =
            α * (∑ k ∈ Finset.range M, risingBinomCoeff α k * x ^ k) +
            ∑ k ∈ Finset.range M, (k : ℝ) * risingBinomCoeff α k * x ^ k := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro k _; ring
        have htele : (∑ k ∈ Finset.range M, (k : ℝ) * risingBinomCoeff α k * x ^ k) -
            (∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) * x ^ (k + 1)) =
            -((M : ℝ) * risingBinomCoeff α M * x ^ M) := by
          have hshift : (∑ k ∈ Finset.range (M + 1), (k : ℝ) * risingBinomCoeff α k * x ^ k) =
              ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) * x ^ (k + 1) := by
            rw [Finset.sum_range_succ']
            simp only [Nat.cast_zero, zero_mul, add_zero]
          rw [← hshift, Finset.sum_range_succ]; ring
        have hS_split : S x = (∑ k ∈ Finset.range M, risingBinomCoeff α k * x ^ k) +
            risingBinomCoeff α M * x ^ M := Finset.sum_range_succ _ M
        calc (1 - x) * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) - α * S x
            = (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) -
              x * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) - α * S x := by ring
          _ = (α * (∑ k ∈ Finset.range M, risingBinomCoeff α k * x ^ k) +
              ∑ k ∈ Finset.range M, (k : ℝ) * risingBinomCoeff α k * x ^ k) -
              (∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) * x ^ (k + 1)) -
              α * ((∑ k ∈ Finset.range M, risingBinomCoeff α k * x ^ k) + risingBinomCoeff α M * x ^ M) := by
              rw [hsplit, hmulx, hS_split]
          _ = ((∑ k ∈ Finset.range M, (k : ℝ) * risingBinomCoeff α k * x ^ k) -
              (∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) * risingBinomCoeff α (k + 1) * x ^ (k + 1))) -
              α * risingBinomCoeff α M * x ^ M := by ring
          _ = -((M : ℝ) * risingBinomCoeff α M * x ^ M) - α * risingBinomCoeff α M * x ^ M := by
              rw [htele]
          _ = -((α + (M : ℝ)) * risingBinomCoeff α M * x ^ M) := by ring
      have hpow_split : (1 - x) ^ α = (1 - x) ^ (α - 1) * (1 - x) := by
        conv_lhs => rw [show α = (α - 1) + 1 by ring]
        rw [Real.rpow_add h1x, Real.rpow_one]
      have hderiv_eq : α * (1 - x) ^ (α - 1) * (-1) * S x +
          (1 - x) ^ α * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) =
          -((α + (M : ℝ)) * risingBinomCoeff α M * (1 - x) ^ (α - 1) * x ^ M) := by
        calc α * (1 - x) ^ (α - 1) * (-1) * S x +
              (1 - x) ^ α * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k)
            = (1 - x) ^ (α - 1) *
              ((1 - x) * (∑ k ∈ Finset.range M, (α + (k : ℝ)) * risingBinomCoeff α k * x ^ k) - α * S x) := by
              rw [hpow_split]; ring
          _ = (1 - x) ^ (α - 1) * (-((α + (M : ℝ)) * risingBinomCoeff α M * x ^ M)) := by rw [halg]
          _ = -((α + (M : ℝ)) * risingBinomCoeff α M * (1 - x) ^ (α - 1) * x ^ M) := by ring
      rwa [hderiv_eq] at hd_prod
    have hanti : AntitoneOn g (Set.Icc 0 q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 q)
      · exact fun x hx ↦ (hderiv_g x hx).continuousAt.continuousWithinAt
      · exact fun x hx ↦ (hderiv_g x (interior_subset hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hderiv_g x hx').deriv]
        have h1x : 0 < 1 - x := by linarith [hx'.2]
        have hnn : 0 ≤ (α + (M : ℝ)) * risingBinomCoeff α M * (1 - x) ^ (α - 1) * x ^ M := by
          have hc := risingBinomCoeff_nonneg hα M
          have hrp := (Real.rpow_pos_of_pos h1x (α - 1)).le
          have hxp := pow_nonneg hx'.1 M
          positivity
        linarith
    have hgq : g q ≤ g 0 := hanti (Set.left_mem_Icc.mpr hq0) (Set.right_mem_Icc.mpr hq0) hq0
    have hg0 : g 0 = 1 := by
      dsimp only [g, S]
      rw [sub_zero, Real.one_rpow, one_mul, Finset.sum_range_succ']
      simp [risingBinomCoeff_zero]
    rw [hg0] at hgq
    have h1q : 0 < 1 - q := by linarith
    have h1qa : 0 < (1 - q) ^ α := Real.rpow_pos_of_pos h1q α
    rw [Real.rpow_neg h1q.le, ← one_div, le_div_iff₀ h1qa]
    simpa [g, S, mul_comm] using hgq
  have hpart_all : ∀ N : ℕ, ∑ k ∈ Finset.range N, risingBinomCoeff α k * q ^ k ≤ (1 - q) ^ (-α) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.sum_range_zero]
      exact (Real.rpow_pos_of_pos (by linarith : 0 < 1 - q) (-α)).le
    | succ M => exact hpart M
  have hsumm : Summable (fun k : ℕ ↦ risingBinomCoeff α k * q ^ k) :=
    summable_of_sum_range_le (fun k ↦ mul_nonneg (risingBinomCoeff_nonneg hα k) (pow_nonneg hq0 k)) hpart_all
  exact ⟨hsumm, hsumm.tsum_le_of_sum_range_le hpart_all⟩

/-- **Theorem 1.2(a), Eq. (5.4) (Concrete `r`-Local Imaginary-Time Operator Norm Bound)**:
For ANY `r`-local Hamiltonian `H = ∑ X ∈ E, h X` (`2 ≤ r`, `∀ X ∈ E, X.card ≤ r`,
`∀ X, h X ∈ supportedOn X`, `hH : H.IsHermitian`, `∀ x, ∑_{X ∋ x} opNorm (h X) ≤ Jsite`,
`0 < Jsite`), ANY `W ∈ supportedOn U₀` (`U₀.card ≤ sW`), and ANY `0 ≤ κ' < κ` where
`κ = 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)`:
`opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W) ≤
  opNorm W * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))`. -/
theorem theorem_1_2a_concrete_eq54_r_local_norm_bound {N r sW : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ sW) {W : QubitOp N} (hW : W ∈ supportedOn U₀)
    {κ' : ℝ} (hκ'0 : 0 ≤ κ')
    (hκ'_lt : κ' < 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W) ≤
      opNorm W * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) := by
  intro κ
  have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  have hκ_pos : 0 < κ := by dsimp only [κ]; positivity
  set α : ℝ := (sW : ℝ) / ((r - 1 : ℕ) : ℝ)
  set q : ℝ := κ' / κ
  have hα_nn : 0 ≤ α := by positivity
  have hq0 : 0 ≤ q := div_nonneg hκ'0 hκ_pos.le
  have hq1 : q < 1 := (div_lt_one hκ_pos).mpr hκ'_lt
  have hq_eq : q = 2 * κ' * ((r - 1 : ℕ) : ℝ) * Jsite := by
    dsimp only [q, κ]
    field_simp [hr1_pos.ne', hJ.ne']
  have hhas := hasSum_heisenbergEvol_adPow hH (-(Complex.I * (κ' : ℂ))) W
  let φ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
    LinearMap.toContinuousLinearMap
      { toFun := opToCLM
        map_add' := opToCLM_add
        map_smul' := fun c A ↦ by simp [opToCLM_smul] }
  have hhas_clm := hhas.map φ φ.continuous
  have hterm : ∀ k : ℕ,
      ‖φ (((Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)) •
        adPowMat (∑ X ∈ E, h X) k W)‖ ≤
      opNorm W * (risingBinomCoeff α k * q ^ k) := by
    intro k
    change opNorm (((Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)) •
      adPowMat (∑ X ∈ E, h X) k W) ≤ _
    rw [opNorm_smul]
    have hcoeff : ‖(Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)‖ =
        κ' ^ k / (k.factorial : ℝ) := by
      have h1 : Complex.I * -(Complex.I * (κ' : ℂ)) = (κ' : ℂ) := by
        calc Complex.I * -(Complex.I * (κ' : ℂ))
            = -(Complex.I * Complex.I) * (κ' : ℂ) := by ring
          _ = -(-1 : ℂ) * (κ' : ℂ) := by rw [Complex.I_mul_I]
          _ = (κ' : ℂ) := by ring
      rw [h1, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ'0,
        Complex.norm_natCast]
    rw [hcoeff]
    have had_le : opNorm (adPowMat (∑ X ∈ E, h X) k W) ≤
        (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm W := by
      rw [adPowMat_eq_sum_causal E h hsupp hW k]
      calc opNorm (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀), iterComm h f W)
          ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀), opNorm (iterComm h f W) :=
            opNorm_sum_le _ _
        _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀),
              (2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (f j))) * opNorm W :=
            Finset.sum_le_sum fun f _ ↦ opNorm_iterComm_le h W f
        _ = (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm W := by
            unfold fwdCausalSum
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro f _; ring
    have hfwd := fwdCausalSum_r_minus_1_le (by omega : 1 ≤ r) E hcard
      (fun X ↦ opNorm (h X)) (fun X _ ↦ opNorm_nonneg _) hJ.le hsite k U₀
    have hprod_le : (∏ j ∈ Finset.range k, ((U₀.card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) ≤
        ((r - 1 : ℕ) : ℝ) ^ k * (∏ j ∈ Finset.range k, (α + (j : ℝ))) := by
      calc (∏ j ∈ Finset.range k, ((U₀.card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ)))
          ≤ ∏ j ∈ Finset.range k, ((sW : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
            apply Finset.prod_le_prod
            · intro j _; positivity
            · intro j _; have : (U₀.card : ℝ) ≤ (sW : ℝ) := by exact_mod_cast hU₀
              linarith
        _ = ∏ j ∈ Finset.range k, (((r - 1 : ℕ) : ℝ) * (α + (j : ℝ))) := by
            apply Finset.prod_congr rfl; intro j _
            dsimp only [α]; field_simp [hr1_pos.ne']
        _ = ((r - 1 : ℕ) : ℝ) ^ k * (∏ j ∈ Finset.range k, (α + (j : ℝ))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    calc κ' ^ k / (k.factorial : ℝ) * opNorm (adPowMat (∑ X ∈ E, h X) k W)
        ≤ κ' ^ k / (k.factorial : ℝ) * ((2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm W) :=
          mul_le_mul_of_nonneg_left had_le (by positivity)
      _ ≤ κ' ^ k / (k.factorial : ℝ) * ((2 : ℝ) ^ k *
            (((r - 1 : ℕ) : ℝ) ^ k * (∏ j ∈ Finset.range k, (α + (j : ℝ))) * Jsite ^ k) * opNorm W) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (opNorm_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans hfwd (mul_le_mul_of_nonneg_right hprod_le (pow_nonneg hJ.le k))
      _ = opNorm W * (risingBinomCoeff α k * q ^ k) := by
          unfold risingBinomCoeff
          rw [hq_eq]
          have hpow : (2 * κ' * ((r - 1 : ℕ) : ℝ) * Jsite) ^ k =
              (2 : ℝ) ^ k * κ' ^ k * ((r - 1 : ℕ) : ℝ) ^ k * Jsite ^ k := by
            simp only [mul_pow]
          rw [hpow]; ring
  have hrb := risingBinom_tsum_le_rpow hα_nn hq0 hq1
  have hsumm_rhs : Summable (fun k : ℕ ↦ opNorm W * (risingBinomCoeff α k * q ^ k)) :=
    hrb.1.mul_left (opNorm W)
  have hsumm_norm : Summable (fun k : ℕ ↦
      ‖φ (((Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)) •
        adPowMat (∑ X ∈ E, h X) k W)‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm hsumm_rhs
  have hnorm_le : ‖φ (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)‖ ≤
      ∑' k : ℕ, ‖φ (((Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)) •
        adPowMat (∑ X ∈ E, h X) k W)‖ := by
    rw [← hhas_clm.tsum_eq]
    exact norm_tsum_le_tsum_norm hsumm_norm
  calc opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)
      = ‖φ (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)‖ := rfl
    _ ≤ ∑' k : ℕ, ‖φ (((Complex.I * -(Complex.I * (κ' : ℂ))) ^ k / (k.factorial : ℂ)) •
          adPowMat (∑ X ∈ E, h X) k W)‖ := hnorm_le
    _ ≤ ∑' k : ℕ, opNorm W * (risingBinomCoeff α k * q ^ k) :=
        hsumm_norm.tsum_le_tsum hterm hsumm_rhs
    _ = opNorm W * ∑' k : ℕ, risingBinomCoeff α k * q ^ k := tsum_mul_left
    _ ≤ opNorm W * (1 - q) ^ (-α) := mul_le_mul_of_nonneg_left hrb.2 (opNorm_nonneg _)

/-- **Concrete End-to-End Finite-Volume Theorem 1.2(a) (Eqs. 5.2–5.4 Combined)**:
For ANY `r`-local Hamiltonian `H = ∑ X ∈ E, h X` (`2 ≤ r`) with site norm `≤ Jsite`, ANY inverse
temperature `β : ℝ`, ANY Hermitian `W ∈ supportedOn U₀` (`U₀.card ≤ sW`), and ANY `0 ≤ κ' < κ`
where `κ = 1 / (2 * (r - 1) * Jsite)`:
`∑ a b, wightmanSpectralWeight hH β W a b * exp ((β / 2 + κ') * |E_a - E_b|) ≤
  2 * (opNorm W) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))`. -/
theorem theorem_1_2a_concrete_eq54_r_local_bound {N r sW : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ sW) {W : QubitOp N}
    (hWherm : W.IsHermitian) (hW : W ∈ supportedOn U₀)
    (β : ℝ) {κ' : ℝ} (hκ'0 : 0 ≤ κ')
    (hκ'_lt : κ' < 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β W a b *
        Real.exp ((β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b|) ≤
      2 * (opNorm W) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) := by
  intro κ
  have h52 := theorem_1_2a_concrete_eq52_trace_bound hH hWherm β κ'
  have h53 := theorem_1_2a_concrete_eq53_opNorm_bound hH β κ' W
  have h54 := theorem_1_2a_concrete_eq54_r_local_norm_bound hr E hcard h hsupp hH hJ hsite hU₀ hW hκ'0 hκ'_lt
  calc ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        wightmanSpectralWeight hH β W a b *
          Real.exp ((β / 2 + κ') * |hH.eigenvalues a - hH.eigenvalues b|)
      ≤ 2 * (Matrix.trace (gibbsRho hH β * W * heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)).re := h52
    _ ≤ 2 * (opNorm W * opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W)) := by linarith
    _ ≤ 2 * (opNorm W * (opNorm W * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h54 (opNorm_nonneg _)
    _ = 2 * (opNorm W) ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) := by ring

end AsymmetricEq52To54

end KrylovChaos
