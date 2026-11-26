/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Gaussian Time-Smearing (Prop. 9.1(1)), Double-Well Schur Complement & Barrier Tunneling (Prop. 9.1(3), Lemma B.1)

Resolves Flaw #10 concretely on `QubitOp N` and block/barrier matrices:
1. **Proposition 9.1(1) (`gaussianSmear`, `prop_9_1_part1_spectral_density`,
   `prop_9_1_part1_subgaussian_moments`)**:
   Constructs the Gaussian time-smeared operator `O_σ` in the eigenbasis of `H : QubitOp N`,
   proves the exact Wightman norm = spectral weight sum identity, the exact Gaussian spectral
   weight law `w_σ(a,b) = exp(-σ² (E_a - E_b)²) w_0(a,b)` (Eq. 9.2), and the sub-Gaussian
   `2n`-th moment bound `μ_{2n}(O_σ) ≤ (n / (e σ²))^n μ_0(O)`.
2. **Proposition 9.1(3) & Lemma B.1 (`doubleWellBlock`, `doubleWell_even_odd_eigenpairs`,
   `schur_complement_eigen_eq`, `barrierHoppingMatrix`, `lemma_B_1_barrier_neumann_tunneling`)**:
   Proves exact `ℤ₂` even/odd eigenpair splitting and exact Schur-complement eigenvalue reduction
   for concrete block matrices, plus the exact nearest-neighbor barrier-crossing obstruction
   `(T^k)_{0, L} = 0` for `k < L` and exponential Neumann-series tunneling suppression
   `|R_{0, L}| ≤ (1 / E_B) * (2 |t_hop| / E_B)^L / (1 - 2 |t_hop| / E_B)`.
-/

namespace KrylovChaos

open Matrix

section GaussianTimeSmearing

/-- Concrete Gaussian time-smeared operator `O_σ` in the spectral basis of `H : QubitOp N`:
`(Uᴴ O_σ U)_{ab} = exp(-σ² (E_a - E_b)² / 2) (Uᴴ O U)_{ab}`. -/
noncomputable def gaussianSmear {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (σ : ℝ) (O : QubitOp N) : QubitOp N :=
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  let B : QubitOp N := Uᴴ * O * U
  U * Matrix.of (fun a b : QubitIdx N ↦
    ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) : ℝ) : ℂ) * B a b) * Uᴴ

private lemma eigU_mul_star {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

private lemma eigU_star_mul {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

lemma gaussianSmear_zero {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (O : QubitOp N) :
    gaussianSmear hH 0 O = O := by
  unfold gaussianSmear
  dsimp only
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hmat : Matrix.of (fun a b : QubitIdx N ↦
      ((Real.exp (-((0 : ℝ) ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) : ℝ) : ℂ) *
        (Uᴴ * O * U) a b) = Uᴴ * O * U := by
    ext a b; simp
  rw [hmat]
  calc U * (Uᴴ * O * U) * Uᴴ = (U * Uᴴ) * O * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = O := by rw [eigU_mul_star hH, Matrix.one_mul, Matrix.mul_one]

/-- Exact Wightman spectral weight at transition `(a, b)` for Hermitian `H : QubitOp N`
and inverse temperature `β : ℝ`:
`w_{ab}(O) = Z(β)⁻¹ exp(-β (E_a + E_b) / 2) ‖(Uᴴ O U)_{ab}‖²`. -/
noncomputable def wightmanSpectralWeight {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (a b : QubitIdx N) : ℝ :=
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  (gibbsPartitionFn hH β)⁻¹ *
    Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) *
    ‖(Uᴴ * O * U) a b‖ ^ 2

lemma wightmanSpectralWeight_nonneg {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (a b : QubitIdx N) :
    0 ≤ wightmanSpectralWeight hH β O a b := by
  unfold wightmanSpectralWeight
  have hZ := gibbsPartitionFn_pos hH β
  positivity

/-- **Exact Wightman Norm = Spectral Weight Sum Identity on `QubitOp N`**:
`gibbsWightmanNormSq (concreteGibbsData hH β) O = ∑ a, ∑ b, wightmanSpectralWeight hH β O a b`. -/
private lemma trace_conj_diag_pair {N : ℕ} (U D O : QubitOp N) :
    (U * D * Uᴴ * Oᴴ * (U * D * Uᴴ) * O).trace =
      (D * (Uᴴ * O * U)ᴴ * D * (Uᴴ * O * U)).trace := by
  have hBh : (Uᴴ * O * U)ᴴ = Uᴴ * Oᴴ * U := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hBh]
  calc (U * D * Uᴴ * Oᴴ * (U * D * Uᴴ) * O).trace
      = (U * (D * (Uᴴ * Oᴴ * U) * D * (Uᴴ * O))).trace := by simp only [Matrix.mul_assoc]
    _ = ((D * (Uᴴ * Oᴴ * U) * D * (Uᴴ * O)) * U).trace := Matrix.trace_mul_comm _ _
    _ = (D * (Uᴴ * Oᴴ * U) * D * (Uᴴ * O * U)).trace := by simp only [Matrix.mul_assoc]

theorem prop_9_1_wightman_norm_eq_spectral_sum {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) :
    gibbsWightmanNormSq (concreteGibbsData hH β) O =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N, wightmanSpectralWeight hH β O a b := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set B : QubitOp N := Uᴴ * O * U
  set D : QubitOp N := Matrix.diagonal (fun i ↦ (Real.exp (-(β / 2) * hH.eigenvalues i) : ℂ))
  have hZ := gibbsPartitionFn_pos hH β
  have htr : (gibbsRhoHalf hH β * Oᴴ * gibbsRhoHalf hH β * O).trace =
      ((gibbsPartitionFn hH β)⁻¹ : ℂ) * (D * Bᴴ * D * B).trace := by
    have hrh : gibbsRhoHalf hH β = ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) • (U * D * Uᴴ) := rfl
    rw [hrh]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hsc : ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) *
        ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) = ((gibbsPartitionFn hH β)⁻¹ : ℂ) := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hZ.le]
    rw [← mul_assoc, hsc, trace_conj_diag_pair U D O]
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner concreteGibbsData
  dsimp only
  rw [htr, Complex.re_ofReal_mul]
  have hDB : (D * Bᴴ * D * B).trace =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        ((Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) : ℝ) : ℂ) *
          ((‖B a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [D, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have hexp : (Real.exp (-(β / 2) * hH.eigenvalues b) : ℂ) *
        (Real.exp (-(β / 2) * hH.eigenvalues a) : ℂ) =
        (Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    have hnorm : star (B a b) * B a b = ((‖B a b‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    calc (Real.exp (-(β / 2) * hH.eigenvalues b) : ℂ) * star (B a b) *
          (Real.exp (-(β / 2) * hH.eigenvalues a) : ℂ) * B a b
        = ((Real.exp (-(β / 2) * hH.eigenvalues b) : ℂ) *
            (Real.exp (-(β / 2) * hH.eigenvalues a) : ℂ)) * (star (B a b) * B a b) := by ring
      _ = _ := by rw [hexp, hnorm]
  rw [hDB, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  unfold wightmanSpectralWeight
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **Proposition 9.1(1) — Exact Gaussian Spectral Density Law (Eq. 9.2)**:
`wightmanSpectralWeight hH β (gaussianSmear hH σ O) a b = exp(-σ² (E_a - E_b)²) * wightmanSpectralWeight hH β O a b`. -/
theorem prop_9_1_part1_spectral_density {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β σ : ℝ) (O : QubitOp N) (a b : QubitIdx N) :
    wightmanSpectralWeight hH β (gaussianSmear hH σ O) a b =
      Real.exp (-(σ ^ 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) *
        wightmanSpectralWeight hH β O a b := by
  unfold wightmanSpectralWeight gaussianSmear
  dsimp only
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set M : QubitOp N := Matrix.of (fun p q : QubitIdx N ↦
    ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues p - hH.eigenvalues q) ^ 2) : ℝ) : ℂ) *
      (Uᴴ * O * U) p q)
  have hconj : Uᴴ * (U * M * Uᴴ) * U = M := by
    calc Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [eigU_star_mul hH, Matrix.one_mul, Matrix.mul_one]
  rw [hconj]
  simp only [M, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  have hexp : (2 : ℕ) * (-(σ ^ 2 / 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2) =
      -(σ ^ 2) * (hH.eigenvalues a - hH.eigenvalues b) ^ 2 := by push_cast; ring
  rw [hexp]; ring

private lemma rpow_mul_exp_neg_le (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x) ≤ ((n : ℝ) / Real.exp 1) ^ n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : x / (n : ℝ) ≤ Real.exp (x / (n : ℝ) - 1) := by
    have := Real.add_one_le_exp (x / (n : ℝ) - 1)
    linarith
  have hpow : (x / (n : ℝ)) ^ n ≤ (Real.exp (x / (n : ℝ) - 1)) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  rw [← Real.exp_nat_mul] at hpow
  have hexp_eq : (n : ℝ) * (x / (n : ℝ) - 1) = x - (n : ℝ) := by field_simp [hn_pos.ne']
  rw [hexp_eq, Real.exp_sub, div_pow] at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-x)).le
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add] at hmul
  have hcancel : x + -x = 0 := by ring
  rw [hcancel, Real.exp_zero, div_le_div_iff₀ (pow_pos hn_pos n) (Real.exp_pos _)] at hmul
  have he : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [he] at hmul
  rw [div_pow, le_div_iff₀ (pow_pos (Real.exp_pos 1) n)]
  linarith

/-- **Proposition 9.1(1) — Sub-Gaussian Spectral Moment Bound**:
For all `σ > 0` and `n ≥ 1`, the `2n`-th spectral moment of `gaussianSmear hH σ O` satisfies:
`∑ a b, w_σ(a,b) * (E_a - E_b)^{2n} ≤ (n / (e σ²))^n * ∑ a b, w_0(a,b)`. -/
theorem prop_9_1_part1_subgaussian_moments {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) {σ : ℝ} (hσ : 0 < σ) (O : QubitOp N) {n : ℕ} (hn : 1 ≤ n) :
    ∑ a : QubitIdx N, ∑ b : QubitIdx N,
      wightmanSpectralWeight hH β (gaussianSmear hH σ O) a b *
        (hH.eigenvalues a - hH.eigenvalues b) ^ (2 * n) ≤
    ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n *
      ∑ a : QubitIdx N, ∑ b : QubitIdx N, wightmanSpectralWeight hH β O a b := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro b _
  rw [prop_9_1_part1_spectral_density]
  set ω : ℝ := hH.eigenvalues a - hH.eigenvalues b
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hx : 0 ≤ σ ^ 2 * ω ^ 2 := by positivity
  have hpeak := rpow_mul_exp_neg_le n hn hx
  have hrew : (σ ^ 2 * ω ^ 2) ^ n = (σ ^ 2) ^ n * ω ^ (2 * n) := by
    rw [mul_pow, pow_mul]
  rw [hrew] at hpeak
  have hdiv : ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2)) ≤ ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n := by
    have h1 : (σ ^ 2) ^ n * (ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2))) ≤
        ((n : ℝ) / Real.exp 1) ^ n := by
      have : (σ ^ 2) ^ n * (ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2))) =
          (σ ^ 2) ^ n * ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2)) := by ring
      linarith
    have h2 : ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n =
        ((n : ℝ) / Real.exp 1) ^ n / (σ ^ 2) ^ n := by
      rw [div_pow, div_pow, mul_pow, div_div]
    rw [h2, le_div_iff₀ (pow_pos hσ2 n)]
    linarith
  have hw_nn := wightmanSpectralWeight_nonneg hH β O a b
  have heq : -(σ ^ 2) * ω ^ 2 = -(σ ^ 2 * ω ^ 2) := by ring
  rw [heq]
  calc Real.exp (-(σ ^ 2 * ω ^ 2)) * wightmanSpectralWeight hH β O a b * ω ^ (2 * n)
      = wightmanSpectralWeight hH β O a b * (ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2))) := by ring
    _ ≤ wightmanSpectralWeight hH β O a b * ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n :=
        mul_le_mul_of_nonneg_left hdiv hw_nn
    _ = ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n * wightmanSpectralWeight hH β O a b := by ring

end GaussianTimeSmearing

section DoubleWellAndSchurComplement

/-- Concrete `ℤ₂`-symmetric double-well block Hamiltonian `[[H_L, V], [V, H_L]]`. -/
def doubleWellBlock {n : ℕ} (H_L V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks H_L V V H_L

/-- **Exact `ℤ₂` Parity Splitting for Concrete Double-Well Hamiltonians (Prop. 9.1(3))**:
If `(H_L + V) *ᵥ u = E₊ • u` and `(H_L - V) *ᵥ u = E₋ • u`, then the symmetric and
antisymmetric states `Sum.elim u u` and `Sum.elim u (-u)` are exact eigenvectors of
`doubleWellBlock H_L V` with eigenvalues `E₊` and `E₋`. -/
theorem doubleWell_even_odd_eigenpairs {n : ℕ} (H_L V : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) (E_plus E_minus : ℝ)
    (hplus : (H_L + V) *ᵥ u = E_plus • u)
    (hminus : (H_L - V) *ᵥ u = E_minus • u) :
    doubleWellBlock H_L V *ᵥ Sum.elim u u = E_plus • Sum.elim u u ∧
    doubleWellBlock H_L V *ᵥ Sum.elim u (-u) = E_minus • Sum.elim u (-u) := by
  unfold doubleWellBlock
  constructor
  · rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : H_L *ᵥ u + V *ᵥ u = E_plus • u := by rw [← Matrix.add_mulVec]; exact hplus
    rw [h1]
    ext x; cases x <;> simp
  · rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : H_L *ᵥ u + V *ᵥ (-u) = E_minus • u := by
      rw [Matrix.mulVec_neg, ← sub_eq_add_neg, ← Matrix.sub_mulVec]; exact hminus
    have h2 : V *ᵥ u + H_L *ᵥ (-u) = -(E_minus • u) := by
      rw [Matrix.mulVec_neg, ← sub_eq_add_neg, ← neg_sub (H_L *ᵥ u), ← Matrix.sub_mulVec, hminus]
    rw [h1, h2]
    ext x; cases x <;> simp

/-- **Exact Schur Complement Eigenvalue Reduction on Concrete Block Matrices (Prop. 9.1(3))**:
If `Matrix.fromBlocks A B C D *ᵥ Sum.elim u v = E • Sum.elim u v` and `(D - E • 1) * Dinv = 1`
(with `Dinv * (D - E • 1) = 1`), then `(A - B * Dinv * C) *ᵥ u = E • u`. -/
theorem schur_complement_eigen_eq {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin m) ℝ) (D Dinv : Matrix (Fin k) (Fin k) ℝ)
    (E : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ)
    (heig : Matrix.fromBlocks A B C D *ᵥ Sum.elim u v = E • Sum.elim u v)
    (hinv : Dinv * (D - E • 1) = 1) :
    (A - B * Dinv * C) *ᵥ u = E • u := by
  rw [Matrix.fromBlocks_mulVec] at heig
  have htop : A *ᵥ u + B *ᵥ v = E • u := by
    ext i; simpa using congrFun heig (Sum.inl i)
  have hbot : C *ᵥ u + D *ᵥ v = E • v := by
    ext j; simpa using congrFun heig (Sum.inr j)
  have hDv : (D - E • 1) *ᵥ v = -(C *ᵥ u) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext j
    have hj := congrFun hbot j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hv : v = -(Dinv *ᵥ (C *ᵥ u)) := by
    calc v = (1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (Dinv * (D - E • 1)) *ᵥ v := by rw [hinv]
      _ = Dinv *ᵥ ((D - E • 1) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = Dinv *ᵥ (-(C *ᵥ u)) := by rw [hDv]
      _ = -(Dinv *ᵥ (C *ᵥ u)) := Matrix.mulVec_neg _ _
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hv, Matrix.mulVec_neg] at htop
  ext i
  have hi := congrFun htop i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Concrete `(L + 1) × (L + 1)` nearest-neighbor barrier hopping matrix `T`:
`T_{i, j} = t_hop` if `|i - j| = 1`, else `0`. -/
def barrierHoppingMatrix (L : ℕ) (t_hop : ℝ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  Matrix.of (fun i j ↦ if i.val + 1 = j.val ∨ j.val + 1 = i.val then t_hop else 0)

/-- Exact finite-speed propagation across the barrier:
`(T^k)_{i, j} = 0` whenever `k < |i - j|` (in particular `j.val - i.val > k`). -/
theorem barrierHoppingMatrix_pow_zero_of_lt (L : ℕ) (t_hop : ℝ) :
    ∀ k : ℕ, ∀ i j : Fin (L + 1), i.val + k < j.val →
      (barrierHoppingMatrix L t_hop ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    simp only [pow_zero, Matrix.one_apply]
    rw [if_neg]; intro h; subst h; omega
  | succ k ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro m _
    by_cases hm : m.val + 1 = j.val ∨ j.val + 1 = m.val
    · have him : i.val + k < m.val := by omega
      rw [ih i m him, zero_mul]
    · simp [barrierHoppingMatrix, hm]

/-- Concrete `ℓ¹` row-sum bound for powers of the barrier hopping matrix:
`∑ j, |(T^k)_{i, j}| ≤ (2 * |t_hop|)^k`. -/
theorem barrierHoppingMatrix_pow_row_sum_le (L : ℕ) (t_hop : ℝ) :
    ∀ k : ℕ, ∀ i : Fin (L + 1),
      ∑ j : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ k) i j| ≤ (2 * |t_hop|) ^ k := by
  intro k
  induction k with
  | zero =>
    intro i
    simp only [pow_zero, Matrix.one_apply]
    have h1 : ∀ j : Fin (L + 1), |(if i = j then (1 : ℝ) else 0)| = if i = j then 1 else 0 := by
      intro j; split_ifs <;> simp
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact le_rfl
  | succ k ih =>
    intro i
    have hrow1 : ∀ m : Fin (L + 1),
        ∑ j : Fin (L + 1), |barrierHoppingMatrix L t_hop m j| ≤ 2 * |t_hop| := by
      intro m
      have hcard : (Finset.univ.filter (fun j : Fin (L + 1) ↦
          m.val + 1 = j.val ∨ j.val + 1 = m.val)).card ≤ 2 := by
        have hsub : Finset.univ.filter (fun j : Fin (L + 1) ↦
            m.val + 1 = j.val ∨ j.val + 1 = m.val) ⊆
            (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val = m.val + 1)) ∪
            (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val + 1 = m.val)) := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
          omega
        have hc1 : (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val = m.val + 1)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)
        have hc2 : (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val + 1 = m.val)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)
        calc (Finset.univ.filter _).card
            ≤ ((Finset.univ.filter _) ∪ (Finset.univ.filter _)).card := Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter _).card + (Finset.univ.filter _).card := Finset.card_union_le _ _
          _ ≤ 1 + 1 := add_le_add hc1 hc2
      have hsum : ∑ j : Fin (L + 1), |barrierHoppingMatrix L t_hop m j| =
          ((Finset.univ.filter (fun j : Fin (L + 1) ↦
            m.val + 1 = j.val ∨ j.val + 1 = m.val)).card : ℝ) * |t_hop| := by
        unfold barrierHoppingMatrix
        have hite : ∀ j : Fin (L + 1),
            |(if m.val + 1 = j.val ∨ j.val + 1 = m.val then t_hop else 0)| =
            if m.val + 1 = j.val ∨ j.val + 1 = m.val then |t_hop| else 0 := by
          intro j; split_ifs <;> simp
        simp_rw [Matrix.of_apply, hite, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (abs_nonneg _)
    calc ∑ j : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ (k + 1)) i j|
        = ∑ j : Fin (L + 1), |∑ m : Fin (L + 1),
            (barrierHoppingMatrix L t_hop ^ k) i m * barrierHoppingMatrix L t_hop m j| := by
          apply Finset.sum_congr rfl; intro j _; rw [pow_succ, Matrix.mul_apply]
      _ ≤ ∑ j : Fin (L + 1), ∑ m : Fin (L + 1),
            |(barrierHoppingMatrix L t_hop ^ k) i m| * |barrierHoppingMatrix L t_hop m j| := by
          apply Finset.sum_le_sum; intro j _
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          apply Finset.sum_le_sum; intro m _; rw [abs_mul]
      _ = ∑ m : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ k) i m| *
            (∑ j : Fin (L + 1), |barrierHoppingMatrix L t_hop m j|) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _; rw [← Finset.mul_sum]
      _ ≤ ∑ m : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ k) i m| * (2 * |t_hop|) := by
          apply Finset.sum_le_sum; intro m _
          exact mul_le_mul_of_nonneg_left (hrow1 m) (abs_nonneg _)
      _ = (∑ m : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ k) i m|) * (2 * |t_hop|) := by
          rw [← Finset.sum_mul]
      _ ≤ (2 * |t_hop|) ^ k * (2 * |t_hop|) :=
          mul_le_mul_of_nonneg_right (ih i) (by positivity)
      _ = (2 * |t_hop|) ^ (k + 1) := by rw [pow_succ]

/-- **Lemma B.1 (Concrete Exponential Barrier Tunneling Bound via Neumann Series, Flaw #10)**:
For barrier height `E_B > 2 * |t_hop|` and width `L`, every partial sum `M` of the Neumann
series for `(E_B I - T)⁻¹_{0, L}` obeys the exact exponential tunneling suppression:
`|∑_{k=0}^{M-1} E_B^{-(k+1)} (T^k)_{0, L}| ≤ (1 / E_B) * (2 |t_hop| / E_B)^L / (1 - 2 |t_hop| / E_B)`. -/
theorem lemma_B_1_barrier_neumann_tunneling (L : ℕ) {E_B t_hop : ℝ}
    (hE : 2 * |t_hop| < E_B) (M : ℕ) :
    |∑ k ∈ Finset.range M,
        (E_B⁻¹) ^ (k + 1) * (barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩| ≤
      (1 / E_B) * ((2 * |t_hop| / E_B) ^ L / (1 - 2 * |t_hop| / E_B)) := by
  have hE_pos : 0 < E_B := lt_of_le_of_lt (by positivity) hE
  set q : ℝ := 2 * |t_hop| / E_B
  have hq_nn : 0 ≤ q := div_nonneg (by positivity) hE_pos.le
  have hq_lt : q < 1 := (div_lt_one hE_pos).mpr hE
  have hterm : ∀ k : ℕ,
      |(E_B⁻¹) ^ (k + 1) * (barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩| ≤
      if L ≤ k then (1 / E_B) * q ^ k else 0 := by
    intro k
    by_cases hLk : L ≤ k
    · rw [if_pos hLk, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hE_pos.le) _)]
      have hle_sum : |(barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩| ≤
          ∑ j : Fin (L + 1), |(barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ j| :=
        Finset.single_le_sum (f := fun j ↦ |(barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ j|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)
      have hrow := barrierHoppingMatrix_pow_row_sum_le L t_hop k ⟨0, Nat.zero_lt_succ L⟩
      have hpow_eq : (E_B⁻¹) ^ (k + 1) * (2 * |t_hop|) ^ k = (1 / E_B) * q ^ k := by
        simp only [q, div_pow, pow_succ, one_div, inv_pow]; ring
      calc (E_B⁻¹) ^ (k + 1) * |(barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩|
          ≤ (E_B⁻¹) ^ (k + 1) * (2 * |t_hop|) ^ k :=
            mul_le_mul_of_nonneg_left (le_trans hle_sum hrow) (pow_nonneg (inv_nonneg.mpr hE_pos.le) _)
        _ = (1 / E_B) * q ^ k := hpow_eq
    · rw [if_neg hLk]
      have hzero := barrierHoppingMatrix_pow_zero_of_lt L t_hop k
        ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩ (by dsimp; omega)
      rw [hzero, mul_zero, abs_zero]
  calc |∑ k ∈ Finset.range M,
          (E_B⁻¹) ^ (k + 1) * (barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩|
      ≤ ∑ k ∈ Finset.range M,
          |(E_B⁻¹) ^ (k + 1) * (barrierHoppingMatrix L t_hop ^ k) ⟨0, Nat.zero_lt_succ L⟩ ⟨L, Nat.lt_succ_self L⟩| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M, if L ≤ k then (1 / E_B) * q ^ k else 0 :=
        Finset.sum_le_sum fun k _ ↦ hterm k
    _ ≤ (1 / E_B) * (q ^ L / (1 - q)) := by
        by_cases hML : M ≤ L
        · have h0 : ∑ k ∈ Finset.range M, (if L ≤ k then (1 / E_B) * q ^ k else (0 : ℝ)) = 0 := by
            apply Finset.sum_eq_zero; intro k hk
            rw [if_neg]; have := Finset.mem_range.mp hk; omega
          rw [h0]
          exact mul_nonneg (div_nonneg zero_le_one hE_pos.le)
            (div_nonneg (pow_nonneg hq_nn L) (by linarith))
        · have hsplit : ∑ k ∈ Finset.range M, (if L ≤ k then (1 / E_B) * q ^ k else (0 : ℝ)) =
              (1 / E_B) * q ^ L * ∑ j ∈ Finset.range (M - L), q ^ j := by
            rw [Finset.mul_sum, ← Finset.sum_filter]
            refine Finset.sum_bij (fun k _ ↦ k - L) ?_ ?_ ?_ ?_
            · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
            · intro k₁ hk₁ k₂ hk₂ heq
              simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂; omega
            · intro j hj; refine ⟨j + L, ?_, by omega⟩
              simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
            · intro k hk
              simp only [Finset.mem_filter, Finset.mem_range] at hk
              rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hk.2]
          rw [hsplit, geom_sum_eq hq_lt.ne]
          have h1 : (q ^ (M - L) - 1) / (q - 1) ≤ 1 / (1 - q) := by
            have hneg : 0 < 1 - q := by linarith
            rw [show (q ^ (M - L) - 1) / (q - 1) = (1 - q ^ (M - L)) / (1 - q) by
              field_simp [hneg.ne', (show q - 1 ≠ 0 by linarith)]; ring]
            exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hq_nn (M - L)]) hneg.le
          have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg (div_nonneg zero_le_one hE_pos.le) (pow_nonneg hq_nn L))
          linarith [show (1 / E_B) * q ^ L * (1 / (1 - q)) = (1 / E_B) * (q ^ L / (1 - q)) by ring]

end DoubleWellAndSchurComplement

end KrylovChaos
