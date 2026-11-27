/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.WightmanIsometry
import KrylovChaos.ManyBodySetup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Concrete Gibbs State Construction, Wightman Lanczos Recursion, and Superoperators

Resolves Core Infrastructure (Flaw #1) directly on `QubitOp N`:
1. **Spectral Functional Calculus & Concrete Gibbs State**: Constructs `ρ_β = exp(-β H) / Tr(exp(-β H))`,
   `ρ_β^{1/2}`, `ρ_β^{1/4}`, `ρ_β^{-1/4}` from any Hermitian `H : QubitOp N` (and in particular
   any `ham : LocalHamiltonian N r`) via Mathlib's `Matrix.IsHermitian.spectral_theorem`, proving
   Hermiticity, root identities, unit trace, `[H, ρ_β^{1/4}] = 0`, and instantiating `GibbsData N`.
2. **Complex-Time Heisenberg Evolution**: Constructs `A(z) = exp(i z H) A exp(-i z H)` for `z : ℂ`,
   proving group law, real-time unitarity, and the Heisenberg ODE `d/dt A(t) = i [H, A(t)]`.
3. **Concrete Wightman Lanczos Recursion (Eq. 2.6) & Krylov Complexity**: Defines `{𝒪_n^{(β)}, b_{n,T}^{(W)}}`
   and `K_β^W(t)` concretely on `QubitOp N`.
4. **Concrete Superoperators & OTOCs**: Defines `Π_s^{(β)}`, `𝒬^{(β)} = ∑_{s=0}^{N-1} (1 - Π_s^{(β)})`
   (Eq. 1.6), `P_{x,0}^{(β)}`, `𝒬̃^{(β)} = ∑_x (1 - P_{x,0}^{(β)})` (Eq. 1.7), shifted commutator
   sum `I(A)` (Eq. 1.10), and static supremum `Λ_β^{MSS}(s)` (Eq. 1.11).
-/

namespace KrylovChaos

open Matrix

/-- Computational basis index type `Fin N → Fin 2` for `N`-qubit Hilbert space `(ℂ²)^{⊗ N}`. -/
abbrev QubitIdx (N : ℕ) := Fin N → Fin 2

section SpectralGibbs

/-- Spectral functional calculus `f(H) = U diag(f(λ_i)) Uᴴ` for a Hermitian operator `H : QubitOp N`. -/
noncomputable def hermFunc {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f : ℝ → ℂ) : QubitOp N :=
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  U * Matrix.diagonal (fun i ↦ f (hH.eigenvalues i)) * Uᴴ

private lemma eigenvectorUnitary_mul_star {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

private lemma eigenvectorUnitary_star_mul {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

lemma hermFunc_one {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    hermFunc hH (fun _ ↦ 1) = 1 := by
  unfold hermFunc
  simp only [Matrix.diagonal_one, Matrix.mul_one]
  exact eigenvectorUnitary_mul_star hH

lemma hermFunc_id {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    hermFunc hH (fun x ↦ (x : ℂ)) = H := by
  unfold hermFunc
  have hspec := hH.spectral_theorem
  simpa [Function.comp_def, RCLike.ofReal_real_eq_id, Matrix.star_eq_conjTranspose] using hspec.symm

lemma hermFunc_mul {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f g : ℝ → ℂ) :
    hermFunc hH f * hermFunc hH g = hermFunc hH (fun x ↦ f x * g x) := by
  unfold hermFunc
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hUU : Uᴴ * U = 1 := eigenvectorUnitary_star_mul hH
  calc U * Matrix.diagonal (fun i ↦ f (hH.eigenvalues i)) * Uᴴ *
        (U * Matrix.diagonal (fun i ↦ g (hH.eigenvalues i)) * Uᴴ)
      = U * Matrix.diagonal (fun i ↦ f (hH.eigenvalues i)) * (Uᴴ * U) *
          Matrix.diagonal (fun i ↦ g (hH.eigenvalues i)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i ↦ f (hH.eigenvalues i)) *
          Matrix.diagonal (fun i ↦ g (hH.eigenvalues i))) * Uᴴ := by
        rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i ↦ f (hH.eigenvalues i) * g (hH.eigenvalues i)) * Uᴴ := by
        rw [Matrix.diagonal_mul_diagonal]

lemma hermFunc_comm {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f g : ℝ → ℂ) :
    hermFunc hH f * hermFunc hH g = hermFunc hH g * hermFunc hH f := by
  rw [hermFunc_mul, hermFunc_mul]
  congr 1; funext x; ring

lemma hermFunc_conjTranspose {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f : ℝ → ℂ) :
    (hermFunc hH f)ᴴ = hermFunc hH (fun x ↦ star (f x)) := by
  unfold hermFunc
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  rfl

lemma hermFunc_herm_of_real {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (hermFunc hH (fun x ↦ (f x : ℂ)))ᴴ = hermFunc hH (fun x ↦ (f x : ℂ)) := by
  rw [hermFunc_conjTranspose]
  congr 1; funext x; simp

lemma hermFunc_trace {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f : ℝ → ℂ) :
    (hermFunc hH f).trace = ∑ i : QubitIdx N, f (hH.eigenvalues i) := by
  unfold hermFunc
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  rw [Matrix.trace_mul_cycle, eigenvectorUnitary_star_mul hH, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- Partition function `Z(β) = Tr(exp(-β H)) = ∑_i exp(-β E_i)` for Hermitian `H : QubitOp N`. -/
noncomputable def gibbsPartitionFn {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  ∑ i : QubitIdx N, Real.exp (-β * hH.eigenvalues i)

lemma gibbsPartitionFn_pos {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    0 < gibbsPartitionFn hH β := by
  unfold gibbsPartitionFn
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- Concrete Gibbs density matrix `ρ_β = exp(-β H) / Z(β)` on `QubitOp N`. -/
noncomputable def gibbsRho {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) : QubitOp N :=
  ((gibbsPartitionFn hH β)⁻¹ : ℂ) • hermFunc hH (fun E ↦ (Real.exp (-β * E) : ℂ))

/-- Concrete `ρ_β^{1/2} = exp(-(β/2) H) / √Z(β)` on `QubitOp N`. -/
noncomputable def gibbsRhoHalf {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) : QubitOp N :=
  ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) •
    hermFunc hH (fun E ↦ (Real.exp (-(β / 2) * E) : ℂ))

/-- Concrete `ρ_β^{1/4} = exp(-(β/4) H) / Z(β)^{1/4}` on `QubitOp N`. -/
noncomputable def gibbsRhoQuarter {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) : QubitOp N :=
  (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) •
    hermFunc hH (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ))

/-- Concrete `ρ_β^{-1/4} = Z(β)^{1/4} exp((β/4) H)` on `QubitOp N`. -/
noncomputable def gibbsRhoQuarterInv {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    QubitOp N :=
  (((gibbsPartitionFn hH β) ^ (1 / 4 : ℝ) : ℝ) : ℂ) •
    hermFunc hH (fun E ↦ (Real.exp ((β / 4) * E) : ℂ))

/-- Concrete instantiation of `GibbsData N` from ANY Hermitian operator `H : QubitOp N`
and inverse temperature `β : ℝ`. -/
noncomputable def concreteGibbsData {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    GibbsData N where
  ρβ := gibbsRho hH β
  ρHalf := gibbsRhoHalf hH β
  ρQuarter := gibbsRhoQuarter hH β
  ρQuarterInv := gibbsRhoQuarterInv hH β
  ρβ_herm := by
    unfold gibbsRho
    rw [Matrix.conjTranspose_smul, hermFunc_herm_of_real]
    simp [Complex.star_def]
  ρHalf_herm := by
    unfold gibbsRhoHalf
    rw [Matrix.conjTranspose_smul, hermFunc_herm_of_real]
    simp [Complex.star_def]
  ρQuarter_herm := by
    unfold gibbsRhoQuarter
    rw [Matrix.conjTranspose_smul, hermFunc_herm_of_real]
    simp [Complex.star_def]
  ρQuarterInv_herm := by
    unfold gibbsRhoQuarterInv
    rw [Matrix.conjTranspose_smul, hermFunc_herm_of_real]
    simp [Complex.star_def]
  sq_quarter := by
    unfold gibbsRhoQuarter gibbsRhoHalf
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hermFunc_mul]
    have hZ := gibbsPartitionFn_pos hH β
    have hsc : (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) =
        ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hZ, Real.sqrt_eq_rpow,
        ← Complex.ofReal_inv, ← Real.rpow_neg hZ.le]
      congr 1; congr 1; norm_num
    rw [hsc]
    congr 1; congr 1; funext E
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2; ring
  sq_half := by
    unfold gibbsRhoHalf gibbsRho
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hermFunc_mul]
    have hZ := gibbsPartitionFn_pos hH β
    have hsc : ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) *
        ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℂ) = ((gibbsPartitionFn hH β)⁻¹ : ℂ) := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hZ.le]
    rw [hsc]
    congr 1; congr 1; funext E
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2; ring
  inv_left := by
    unfold gibbsRhoQuarterInv gibbsRhoQuarter
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hermFunc_mul]
    have hZ := gibbsPartitionFn_pos hH β
    have hsc : (((gibbsPartitionFn hH β) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hZ]
      norm_num
    rw [hsc, one_smul]
    have hfn : (fun E ↦ (Real.exp ((β / 4) * E) : ℂ) * (Real.exp (-(β / 4) * E) : ℂ)) =
        fun _ ↦ 1 := by
      funext E; rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    rw [hfn, hermFunc_one]
  inv_right := by
    unfold gibbsRhoQuarter gibbsRhoQuarterInv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hermFunc_mul]
    have hZ := gibbsPartitionFn_pos hH β
    have hsc : (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (((gibbsPartitionFn hH β) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hZ]
      norm_num
    rw [hsc, one_smul]
    have hfn : (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ) * (Real.exp ((β / 4) * E) : ℂ)) =
        fun _ ↦ 1 := by
      funext E; rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    rw [hfn, hermFunc_one]
  trace_one := by
    unfold gibbsRho
    rw [Matrix.trace_smul, smul_eq_mul, hermFunc_trace]
    have hZ := gibbsPartitionFn_pos hH β
    have hsum : (∑ i : QubitIdx N, (Real.exp (-β * hH.eigenvalues i) : ℂ)) =
        (gibbsPartitionFn hH β : ℂ) := by
      unfold gibbsPartitionFn; push_cast; rfl
    rw [hsum, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hZ.ne')]

/-- **Commutation `[H, ρ_β^{1/4}] = 0`**: Proved directly from the concrete spectral construction. -/
theorem concreteGibbsData_comm_H {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    H * (concreteGibbsData hH β).ρQuarter = (concreteGibbsData hH β).ρQuarter * H := by
  change H * gibbsRhoQuarter hH β = gibbsRhoQuarter hH β * H
  unfold gibbsRhoQuarter
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have h1 : H * hermFunc hH (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ)) =
      hermFunc hH (fun x ↦ (x : ℂ)) * hermFunc hH (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ)) :=
    congrArg (· * _) (hermFunc_id hH).symm
  have h2 : hermFunc hH (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ)) * H =
      hermFunc hH (fun E ↦ (Real.exp (-(β / 4) * E) : ℂ)) * hermFunc hH (fun x ↦ (x : ℂ)) :=
    congrArg (_ * ·) (hermFunc_id hH).symm
  rw [h1, h2]
  exact hermFunc_comm hH _ _

/-- Concrete Gibbs state directly from an `r`-local Hamiltonian `ham : LocalHamiltonian N r`. -/
noncomputable def localHamiltonianGibbs {N r : ℕ} (ham : LocalHamiltonian N r) (β : ℝ) :
    GibbsData N :=
  concreteGibbsData ham.totalOp_herm β

/-- Concrete commutation `[H, ρ_β^{1/4}] = 0` for any `LocalHamiltonian N r`. -/
theorem localHamiltonianGibbs_comm {N r : ℕ} (ham : LocalHamiltonian N r) (β : ℝ) :
    ham.totalOp * (localHamiltonianGibbs ham β).ρQuarter =
      (localHamiltonianGibbs ham β).ρQuarter * ham.totalOp :=
  concreteGibbsData_comm_H ham.totalOp_herm β

end SpectralGibbs

section ComplexHeisenberg

/-- Complex-time propagator `U(z) = exp(i z H)` on `QubitOp N`. -/
noncomputable def complexPropagator {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z : ℂ) :
    QubitOp N :=
  hermFunc hH (fun E ↦ Complex.exp (Complex.I * z * (E : ℂ)))

lemma complexPropagator_zero {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    complexPropagator hH 0 = 1 := by
  unfold complexPropagator
  simp only [mul_zero, zero_mul, Complex.exp_zero]
  exact hermFunc_one hH

lemma complexPropagator_add {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z₁ z₂ : ℂ) :
    complexPropagator hH z₁ * complexPropagator hH z₂ = complexPropagator hH (z₁ + z₂) := by
  unfold complexPropagator
  rw [hermFunc_mul]
  congr 1; funext E
  rw [← Complex.exp_add]
  congr 1; ring

/-- Complex-time Heisenberg evolution `A(z) = exp(i z H) A exp(-i z H)` (Eq. 2.1). -/
noncomputable def heisenbergEvol {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (A : QubitOp N) : QubitOp N :=
  complexPropagator hH z * A * complexPropagator hH (-z)

lemma heisenbergEvol_zero {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (A : QubitOp N) :
    heisenbergEvol hH 0 A = A := by
  unfold heisenbergEvol
  rw [neg_zero, complexPropagator_zero, Matrix.one_mul, Matrix.mul_one]

lemma heisenbergEvol_add {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z₁ z₂ : ℂ) (A : QubitOp N) :
    heisenbergEvol hH z₁ (heisenbergEvol hH z₂ A) = heisenbergEvol hH (z₁ + z₂) A := by
  unfold heisenbergEvol
  calc complexPropagator hH z₁ * (complexPropagator hH z₂ * A * complexPropagator hH (-z₂)) *
          complexPropagator hH (-z₁)
      = (complexPropagator hH z₁ * complexPropagator hH z₂) * A *
          (complexPropagator hH (-z₂) * complexPropagator hH (-z₁)) := by
        simp only [Matrix.mul_assoc]
    _ = complexPropagator hH (z₁ + z₂) * A * complexPropagator hH (-(z₁ + z₂)) := by
        rw [complexPropagator_add, complexPropagator_add]
        congr 2; ring

/-- Real-time propagator is unitary: `U(t)ᴴ = U(-t)`. -/
lemma complexPropagator_real_conjTranspose {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (t : ℝ) :
    (complexPropagator hH (t : ℂ))ᴴ = complexPropagator hH (-(t : ℂ)) := by
  unfold complexPropagator
  rw [hermFunc_conjTranspose]
  congr 1; funext E
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

/-- Entrywise Heisenberg ODE: for every matrix entry `(i, j)`,
`d/dt (A(t))_{ij} = (i [H, A(t)])_{ij}`. -/
theorem heisenbergEvol_entry_hasDerivAt {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (A : QubitOp N) (t : ℝ) (i j : QubitIdx N) :
    HasDerivAt (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) A i j)
      ((Complex.I • matComm H (heisenbergEvol hH (t : ℂ) A)) i j) t := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set B : QubitOp N := Uᴴ * A * U
  have hformula : ∀ s : ℝ, heisenbergEvol hH (s : ℂ) A i j =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        U i b * B b a * Uᴴ a j *
          Complex.exp (Complex.I * (s : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)) := by
    intro s
    unfold heisenbergEvol complexPropagator hermFunc
    have hrew : (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ) *
        A * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ) =
        U * (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues a : ℂ))) *
          B * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues b : ℂ)))) * Uᴴ := by
      simp only [B, Matrix.mul_assoc]
    rw [hrew]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    have hexp : Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues b : ℂ)) *
        Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues a : ℂ)) =
        Complex.exp (Complex.I * (s : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination U i b * B b a * Uᴴ a j * hexp
  have hderiv_sum : HasDerivAt (fun s : ℝ ↦
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        U i b * B b a * Uᴴ a j *
          Complex.exp (Complex.I * (s : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)))
      (∑ a : QubitIdx N, ∑ b : QubitIdx N,
        U i b * B b a * Uᴴ a j *
          (Complex.exp (Complex.I * (t : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)) *
            (Complex.I * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)))) t := by
    apply HasDerivAt.fun_sum; intro a _
    apply HasDerivAt.fun_sum; intro b _
    have hlin : HasDerivAt (fun s : ℝ ↦
        Complex.I * (s : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ))
        (Complex.I * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)) t := by
      have h1 : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := h1.const_mul Complex.I
      have h3 := h2.mul_const ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)
      simpa using h3
    exact (hlin.cexp).const_mul (U i b * B b a * Uᴴ a j)
  have hrhs : (Complex.I • matComm H (heisenbergEvol hH (t : ℂ) A)) i j =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        U i b * B b a * Uᴴ a j *
          (Complex.exp (Complex.I * (t : ℂ) * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ)) *
            (Complex.I * ((hH.eigenvalues b - hH.eigenvalues a : ℝ) : ℂ))) := by
    set At := heisenbergEvol hH (t : ℂ) A
    have hH_left : H * At = hermFunc hH (fun E ↦ (E : ℂ)) * At :=
      congrArg (· * At) (hermFunc_id hH).symm
    have hH_right : At * H = At * hermFunc hH (fun E ↦ (E : ℂ)) :=
      congrArg (At * ·) (hermFunc_id hH).symm
    have hcomm_mat : matComm H At =
        U * (Matrix.diagonal (fun a ↦ (hH.eigenvalues a : ℂ)) *
          (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
            B * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ)))) -
          (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
            B * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ)))) *
          Matrix.diagonal (fun b ↦ (hH.eigenvalues b : ℂ))) * Uᴴ := by
      unfold matComm
      rw [hH_left, hH_right]
      simp only [At, heisenbergEvol, complexPropagator, hermFunc]
      have hUU : Uᴴ * U = 1 := eigenvectorUnitary_star_mul hH
      have h1 : (U * Matrix.diagonal (fun a ↦ (hH.eigenvalues a : ℂ)) * Uᴴ) *
          (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
            A * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)) =
          U * (Matrix.diagonal (fun a ↦ (hH.eigenvalues a : ℂ)) *
            (Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
              B * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))))) * Uᴴ := by
        have hstep : U * Matrix.diagonal (fun a ↦ (hH.eigenvalues a : ℂ)) * Uᴴ *
            (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
              A * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)) =
            U * Matrix.diagonal (fun a ↦ (hH.eigenvalues a : ℂ)) * (Uᴴ * U) *
              Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
              (Uᴴ * A * U) * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
        rw [hstep, hUU, Matrix.mul_one]
        simp only [B, Matrix.mul_assoc]
      have h2 : (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
            A * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)) *
          (U * Matrix.diagonal (fun b ↦ (hH.eigenvalues b : ℂ)) * Uᴴ) =
          U * ((Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
              B * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ)))) *
            Matrix.diagonal (fun b ↦ (hH.eigenvalues b : ℂ))) * Uᴴ := by
        have hstep : (U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) * Uᴴ *
              A * (U * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) * Uᴴ)) *
            (U * Matrix.diagonal (fun b ↦ (hH.eigenvalues b : ℂ)) * Uᴴ) =
            U * Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues a : ℂ))) *
              (Uᴴ * A * U) * Matrix.diagonal (fun b ↦ Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues b : ℂ))) *
              (Uᴴ * U) * Matrix.diagonal (fun b ↦ (hH.eigenvalues b : ℂ)) * Uᴴ := by
          simp only [Matrix.mul_assoc]
        rw [hstep, hUU, Matrix.mul_one]
        simp only [B, Matrix.mul_assoc]
      rw [h1, h2, Matrix.mul_sub, Matrix.sub_mul]
    rw [Matrix.smul_apply, smul_eq_mul, hcomm_mat]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    have hexp : Complex.exp (Complex.I * (t : ℂ) * (hH.eigenvalues b : ℂ)) *
        Complex.exp (Complex.I * (-(t : ℂ)) * (hH.eigenvalues a : ℂ)) =
        Complex.exp (Complex.I * (t : ℂ) * ((hH.eigenvalues b : ℂ) - (hH.eigenvalues a : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    linear_combination Complex.I * U i b * B b a * Uᴴ a j *
      ((hH.eigenvalues b : ℂ) - (hH.eigenvalues a : ℂ)) * hexp
  rw [hrhs]
  exact hderiv_sum.congr_of_eventuallyEq (Filter.Eventually.of_forall hformula)

end ComplexHeisenberg

section ConcreteLanczos

/-- Concrete Wightman Lanczos recursion state `(O_n, O_{n-1}, b_n)` on `QubitOp N` (Eq. 2.6). -/
noncomputable def lanczosState {N : ℕ} (G : GibbsData N) (H O : QubitOp N) :
    ℕ → QubitOp N × QubitOp N × ℝ
  | 0 =>
    let nrm := Real.sqrt (gibbsWightmanNormSq G O)
    (if nrm = 0 then 0 else ((nrm⁻¹ : ℝ) : ℂ) • O, 0, 0)
  | n + 1 =>
    let (On, Oprev, bn) := lanczosState G H O n
    let Anext := matComm H On - (bn : ℂ) • Oprev
    let bnext := Real.sqrt (gibbsWightmanNormSq G Anext)
    (if bnext = 0 then 0 else ((bnext⁻¹ : ℝ) : ℂ) • Anext, On, bnext)

/-- Concrete `n`-th Wightman Krylov basis operator `𝒪_n^{(β)}` (Eq. 2.6). -/
noncomputable def lanczosOp {N : ℕ} (G : GibbsData N) (H O : QubitOp N) (n : ℕ) : QubitOp N :=
  (lanczosState G H O n).1

/-- Concrete `n`-th Wightman Lanczos coefficient `b_{n,T}^{(W)}` (Eq. 2.6). -/
noncomputable def lanczosCoeff {N : ℕ} (G : GibbsData N) (H O : QubitOp N) (n : ℕ) : ℝ :=
  (lanczosState G H O n).2.2

lemma lanczosCoeff_zero {N : ℕ} (G : GibbsData N) (H O : QubitOp N) :
    lanczosCoeff G H O 0 = 0 := rfl

lemma lanczosCoeff_nonneg {N : ℕ} (G : GibbsData N) (H O : QubitOp N) (n : ℕ) :
    0 ≤ lanczosCoeff G H O n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Real.sqrt_nonneg _

lemma lanczosState_prev {N : ℕ} (G : GibbsData N) (H O : QubitOp N) (n : ℕ) :
    (lanczosState G H O (n + 1)).2.1 = lanczosOp G H O n := rfl

/-- Exact three-term Lanczos recursion Eq. (2.6):
`[H, 𝒪_n] = b_{n+1} 𝒪_{n+1} + b_n 𝒪_{n-1}` whenever `b_{n+1} > 0`. -/
theorem lanczos_three_term {N : ℕ} (G : GibbsData N) (H O : QubitOp N) (n : ℕ)
    (hb : lanczosCoeff G H O (n + 1) ≠ 0) :
    matComm H (lanczosOp G H O n) =
      (lanczosCoeff G H O (n + 1) : ℂ) • lanczosOp G H O (n + 1) +
      (lanczosCoeff G H O n : ℂ) • (lanczosState G H O n).2.1 := by
  have hbC : (lanczosCoeff G H O (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hdef : lanczosOp G H O (n + 1) =
      ((lanczosCoeff G H O (n + 1))⁻¹ : ℂ) •
        (matComm H (lanczosOp G H O n) -
          (lanczosCoeff G H O n : ℂ) • (lanczosState G H O n).2.1) := by
    have hb' : Real.sqrt (gibbsWightmanNormSq G
        (matComm H (lanczosState G H O n).1 -
          ((lanczosState G H O n).2.2 : ℂ) • (lanczosState G H O n).2.1)) ≠ 0 := hb
    unfold lanczosOp lanczosCoeff
    simp only [lanczosState]
    rw [if_neg hb']
    simp [Complex.ofReal_inv]
  rw [hdef, smul_smul, mul_inv_cancel₀ hbC, one_smul, sub_add_cancel]

/-- Concrete Krylov wavefunction `φ_n^{(β)}(t) = (-i)^n (𝒪_n^{(β)} | 𝒪(t))_β^W`,
matching `𝒪(t) = ∑_n i^n φ_n^{(β)}(t) 𝒪_n^{(β)}` (Eq. 2.7, `tex:364`). -/
noncomputable def concreteKrylovWavefn {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (n : ℕ) (t : ℝ) : ℂ :=
  let G := concreteGibbsData hH β
  (-Complex.I) ^ n * gibbsWightmanInner G (lanczosOp G H O n) (heisenbergEvol hH (t : ℂ) O)

/-- Concrete Krylov complexity `K_β^W(t) = ∑_{n < 4^N} n |φ_n^{(β)}(t)|²`. -/
noncomputable def concreteKrylovComplexity {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (4 ^ N), (n : ℝ) * ‖concreteKrylovWavefn hH β O n t‖ ^ 2

end ConcreteLanczos

section ConcreteSuperoperators

/-- Linear equivalence identifying `QubitOp N` with `EuclideanSpace ℂ (QubitIdx N × QubitIdx N)`
equipped with the Hilbert–Schmidt inner product. -/
noncomputable def qubitOpToHS (N : ℕ) :
    QubitOp N ≃ₗ[ℂ] EuclideanSpace ℂ (QubitIdx N × QubitIdx N) where
  toFun A := WithLp.toLp 2 (fun p : QubitIdx N × QubitIdx N ↦ A p.1 p.2)
  invFun v := Matrix.of (fun i j ↦ (WithLp.ofLp v) (i, j))
  map_add' A B := by ext p; rfl
  map_smul' c A := by ext p; rfl
  left_inv A := by ext i j; rfl
  right_inv v := by ext p; rfl

lemma qubitOpToHS_inner {N : ℕ} (A B : QubitOp N) :
    @inner ℂ _ _ (qubitOpToHS N A) (qubitOpToHS N B) = hsInner A B := by
  rw [PiLp.inner_apply]
  unfold hsInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.inner_apply, qubitOpToHS, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  simp [Complex.star_def, mul_comm]

/-- Orthogonal projection onto a subspace `S : Submodule ℂ (QubitOp N)` in the Wightman inner
product `(· | ·)_β^W`, constructed via the unitary isometry `𝒥_β : QubitOp N → QubitOp N`. -/
noncomputable def wightmanSubspaceProj {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) : QubitOp N →ₗ[ℂ] QubitOp N :=
  let jLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun A ↦ jBeta G.ρQuarter A
      map_add' := fun A B ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let jInvLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun A ↦ jBeta G.ρQuarterInv A
      map_add' := fun A B ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let K : Submodule ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) :=
    S.map ((qubitOpToHS N).toLinearMap.comp jLin)
  letI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  jInvLin.comp ((qubitOpToHS N).symm.toLinearMap.comp
    ((K.starProjection.toLinearMap).comp ((qubitOpToHS N).toLinearMap.comp jLin)))

/-- Concrete Wightman filtration projector `Π_s^{(β)}` onto `𝒱_s = filtrationSubmodule N s`. -/
noncomputable def wightmanFiltrationProj {N : ℕ} (G : GibbsData N) (s : ℕ) :
    QubitOp N →ₗ[ℂ] QubitOp N :=
  wightmanSubspaceProj G (filtrationSubmodule N s)

/-- Concrete Wightman filtration superoperator `𝒬^{(β)} = ∑_{s=0}^{N-1} (1 - Π_s^{(β)})` (Eq. 1.6). -/
noncomputable def wightmanQ {N : ℕ} (G : GibbsData N) : QubitOp N →ₗ[ℂ] QubitOp N :=
  ∑ s ∈ Finset.range N, (LinearMap.id - wightmanFiltrationProj G s)

/-- Subspace of `N`-qubit operators acting trivially on site `x` (range of `ℰ_x`). -/
def singleSiteTrivialSubmodule (N : ℕ) (x : Fin N) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ { P : QubitOp N | ∃ a : Fin N → Fin 4, a x = 0 ∧ P = pauliString a }

/-- Concrete single-site Wightman projector `P_{x,0}^{(β)}` onto operators trivial on site `x`. -/
noncomputable def singleSiteWightmanProj {N : ℕ} (G : GibbsData N) (x : Fin N) :
    QubitOp N →ₗ[ℂ] QubitOp N :=
  wightmanSubspaceProj G (singleSiteTrivialSubmodule N x)

/-- Concrete quantum Glauber generator `𝒬̃^{(β)} = ∑_{x=1}^N (1 - P_{x,0}^{(β)})` (Eq. 1.7). -/
noncomputable def quantumGlauberGen {N : ℕ} (G : GibbsData N) : QubitOp N →ₗ[ℂ] QubitOp N :=
  ∑ x : Fin N, (LinearMap.id - singleSiteWightmanProj G x)

/-- Concrete imaginary-time shifted commutator sum (Eq. 1.10):
`I(A) = (1/8) ∑_{x=1}^N ∑_{α=1}^3 ‖[A, σ_x^α(-i β / 4)]‖_{β,W}²`. -/
noncomputable def otocI {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ)
    (A : QubitOp N) : ℝ :=
  let G := concreteGibbsData hH β
  (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
    gibbsWightmanNormSq G (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
      (pauliSite x α.succ)))

/-- Concrete static thermal-size supremum `Λ_β^{MSS}(s)` (Eq. 1.11):
`sup { S_β(A) | A ∈ 𝒱_s, ‖A‖_{β,W}² = 1 }`. -/
noncomputable def lambdaMSS {N : ℕ} (G : GibbsData N) (s : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ A ∈ filtrationSubmodule N s,
    gibbsWightmanNormSq G A = 1 ∧ r = mssThermalSize G A }

/-- Key Hilbert-space identity: `(A | (1 - Π_S) A)_β^W = ‖(1 - Π_S) A‖_{β,W}² ≥ 0`. -/
theorem wightmanSubspaceProj_complement_nonneg {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) :
    0 ≤ (gibbsWightmanInner G A (A - wightmanSubspaceProj G S A)).re := by
  have hj_inv : ∀ X : QubitOp N, jBeta G.ρQuarter (jBeta G.ρQuarterInv X) = X := by
    intro X
    unfold jBeta
    calc G.ρQuarter * (G.ρQuarterInv * X * G.ρQuarterInv) * G.ρQuarter
        = (G.ρQuarter * G.ρQuarterInv) * X * (G.ρQuarterInv * G.ρQuarter) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [G.inv_right, G.inv_left, Matrix.one_mul, Matrix.mul_one]
  have hJ_sub : jBeta G.ρQuarter (A - wightmanSubspaceProj G S A) =
      jBeta G.ρQuarter A - jBeta G.ρQuarter (wightmanSubspaceProj G S A) := by
    unfold jBeta; simp [Matrix.mul_sub, Matrix.sub_mul]
  let jLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun X ↦ jBeta G.ρQuarter X
      map_add' := fun X Y ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let K : Submodule ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) :=
    S.map ((qubitOpToHS N).toLinearMap.comp jLin)
  letI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  set v : EuclideanSpace ℂ (QubitIdx N × QubitIdx N) := qubitOpToHS N (jBeta G.ρQuarter A)
  have hv_proj : qubitOpToHS N (jBeta G.ρQuarter (wightmanSubspaceProj G S A)) =
      K.starProjection v := by
    unfold wightmanSubspaceProj
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [hj_inv, (qubitOpToHS N).apply_symm_apply]
    rfl
  have hinner : gibbsWightmanInner G A (A - wightmanSubspaceProj G S A) =
      @inner ℂ _ _ v (v - K.starProjection v) := by
    unfold gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf A _ G.ρQuarter_herm G.sq_quarter]
    change hsInner (jBeta G.ρQuarter A) (jBeta G.ρQuarter (A - wightmanSubspaceProj G S A)) = _
    rw [← qubitOpToHS_inner, hJ_sub, map_sub, hv_proj]
  rw [hinner]
  have horth : @inner ℂ _ _ (K.starProjection v) (v - K.starProjection v) = 0 := by
    have hmem : K.starProjection v ∈ K := K.starProjection_apply_mem v
    have hsub : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact (Submodule.mem_orthogonal K _).mp hsub _ hmem
  have hsplit : @inner ℂ _ _ v (v - K.starProjection v) =
      @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) := by
    calc @inner ℂ _ _ v (v - K.starProjection v)
        = @inner ℂ _ _ ((v - K.starProjection v) + K.starProjection v) (v - K.starProjection v) := by
          rw [sub_add_cancel]
      _ = @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) +
          @inner ℂ _ _ (K.starProjection v) (v - K.starProjection v) := inner_add_left _ _ _
      _ = @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) := by
          rw [horth, add_zero]
  rw [hsplit]
  exact inner_self_nonneg (𝕜 := ℂ) (x := v - K.starProjection v)

/-- Positivity of `𝒬^{(β)}`: `Re (A | 𝒬^{(β)} A)_β^W ≥ 0` for all `A : QubitOp N`. -/
theorem wightmanQ_nonneg {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    0 ≤ (gibbsWightmanInner G A (wightmanQ G A)).re := by
  unfold wightmanQ
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G A (∑ s ∈ Finset.range N, (A - wightmanFiltrationProj G s A)) =
      ∑ s ∈ Finset.range N, gibbsWightmanInner G A (A - wightmanFiltrationProj G s A) := by
    unfold gibbsWightmanInner wightmanInner
    rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  exact Finset.sum_nonneg fun s _ ↦ wightmanSubspaceProj_complement_nonneg G _ A

/-- Positivity of `𝒬̃^{(β)}`: `Re (A | 𝒬̃^{(β)} A)_β^W ≥ 0` for all `A : QubitOp N`. -/
theorem quantumGlauberGen_nonneg {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    0 ≤ (gibbsWightmanInner G A (quantumGlauberGen G A)).re := by
  unfold quantumGlauberGen
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G A (∑ x : Fin N, (A - singleSiteWightmanProj G x A)) =
      ∑ x : Fin N, gibbsWightmanInner G A (A - singleSiteWightmanProj G x A) := by
    unfold gibbsWightmanInner wightmanInner
    rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  exact Finset.sum_nonneg fun x _ ↦ wightmanSubspaceProj_complement_nonneg G _ A

end ConcreteSuperoperators

end KrylovChaos
