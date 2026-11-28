/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Locked Challenge Definitions for `KrylovChaos`

Self-contained transparent definitions (using only Lean core and Mathlib)
referenced by the locked headline theorem signatures in `Challenge.lean`.
-/

namespace ChallengeDefs

open Matrix MeasureTheory

/-- Inverse locality scale `κ := (2 (r - 1) J_site)⁻¹`. -/
noncomputable def invLocalityScale (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (2 * ((r : ℝ) - 1) * Jsite)

/-- High-temperature weak-coupling threshold `β_wc := (4 · 6^r · e^2 · r · J_site)⁻¹`. -/
noncomputable def betaWC (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (4 * (6 : ℝ) ^ r * Real.exp 2 * (r : ℝ) * Jsite)

/-- High-temperature weak-coupling threshold `β_wc = (4 e² r 6^r J_site)⁻¹`. -/
noncomputable def highTempBetaWC (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite)

/-- Characteristic curve auxiliary `u(t) = tanh(θ₀/4) e^{-2αt}`. -/
noncomputable def charU (α θ₀ t : ℝ) : ℝ :=
  Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)

/-- Characteristic curve `θ(t) = 2 ln((1 + u(t))/(1 - u(t)))`. -/
noncomputable def charTheta (α θ₀ t : ℝ) : ℝ :=
  2 * Real.log ((1 + charU α θ₀ t) / (1 - charU α θ₀ t))

/-- Finite-chain Krylov complexity `K_{Nmax}(t) := ∑_{n=0}^{Nmax} n φ_n(t)²`. -/
noncomputable def finiteKrylovComplexity (Nmax : ℕ) (φ : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * (φ n t) ^ 2

/-- Hilbert–Schmidt squared norm `‖A‖_HS² := Re Tr(A† A)`. -/
def hsNormSq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (Aᴴ * A)).re

/-- Single-site parameter `σ(m) = √(1 - m²)`. -/
noncomputable def prodSigma (m : ℝ) : ℝ := Real.sqrt (1 - m ^ 2)

/-- Single-site parameter `q(m) = √((1 + m)/2) - √((1 - m)/2)`. -/
noncomputable def prodQ (m : ℝ) : ℝ :=
  Real.sqrt ((1 + m) / 2) - Real.sqrt ((1 - m) / 2)

/-- Single-site `4 × 4` thermal-size matrix `M_x` in the Pauli basis `{I, X, Y, Z}`. -/
noncomputable def singleSiteM (m : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0
  | 1, 1 => 1 - (prodQ m) ^ 2 / 2
  | 2, 2 => 1 - (prodQ m) ^ 2 / 2
  | 3, 3 => prodSigma m
  | 0, 3 => m / 2
  | 3, 0 => m / 2
  | _, _ => 0

/-- Hamming weight `|a|` of a Pauli string `a : Fin N → Fin 4`. -/
def stringWeight {N : ℕ} (a : Fin N → Fin 4) : ℕ :=
  (Finset.univ.filter (fun x : Fin N ↦ a x ≠ 0)).card

/-- Discrete Hubbard–Stratonovich coupling `φ(u) := (1/2) ln(e^{2u} + √(e^{4u} - 1))`. -/
noncomputable def hsPhi (u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1))

/-- Pairwise compatibility of a finite polymer subset `I`. -/
abbrev isCompatPolymer {Γ : Type*} (incompat : Γ → Γ → Prop) (I : Finset Γ) : Prop :=
  ∀ γ₁ ∈ I, ∀ γ₂ ∈ I, γ₁ ≠ γ₂ → ¬ incompat γ₁ γ₂

/-- Finite-volume polymer partition function `Z(Λ) = ∑_{I ⊆ Λ, compat} ∏_{γ ∈ I} w(γ)`. -/
noncomputable def polymerZ {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (w : Γ → ℂ) (Λ : Finset Γ) : ℂ :=
  ∑ I ∈ Λ.powerset.filter (fun I ↦ isCompatPolymer incompat I), ∏ γ ∈ I, w γ

/-- Kotecký–Preiss effective activity `r(γ) = ‖w γ‖ e^{a γ}`. -/
noncomputable def kpActivity {Γ : Type*} (w : Γ → ℂ) (a : Γ → ℝ) (γ : Γ) : ℝ :=
  ‖w γ‖ * Real.exp (a γ)

/-- Symmetric `D × D` tridiagonal double-well matrix `ℒ(E_B)` from Section 9 / Appendix B. -/
def doubleWellTridiag (D : ℕ) (E_B : ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦
    if i = j then (if i.val = 0 ∨ i.val = D - 1 then 0 else E_B)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1
    else 0

lemma doubleWellTridiag_isHermitian (D : ℕ) (E_B : ℝ) :
    (doubleWellTridiag D E_B).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, doubleWellTridiag, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte, or_comm]

/-- Spatial reflection (parity) matrix `P_{ij} = δ_{i + j, D - 1}` on `ℝ^D`. -/
def parityMat (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦ if i.val + j.val + 1 = D then 1 else 0

/-- Concrete `D × D` real symmetric tridiagonal Jacobi matrix. -/
def jacobiMat (D : ℕ) (b : ℕ → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦
    if j.1 = i.1 + 1 then b (i.1 + 1)
    else if i.1 = j.1 + 1 then b (j.1 + 1)
    else 0

/-- Maximal holomorphic strip half-width `r_W` of the Fourier–Stieltjes transform of `μ`. -/
noncomputable def holoStripHalfWidth (μ : Measure ℝ) : EReal :=
  sSup { r : EReal | ∃ R : ℝ, r = (R : EReal) ∧ 0 < R ∧
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | |z.im| < R} ∧
      ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ }

/-- Extended-real quotient `π / r` for `r : EReal`. -/
noncomputable def piDivEReal (r : EReal) : EReal :=
  if r = ⊤ then (0 : EReal) else if r = ⊥ then ⊤ else ((Real.pi / r.toReal : ℝ) : EReal)

/-- Classical spin configuration `z ∈ {-1, +1}^N` encoded as `Fin N → Bool`. -/
abbrev SpinConfig (N : ℕ) := Fin N → Bool

/-- Spin value `±1` for `b : Bool`. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- Flip spin at coordinate `i`. -/
def flipSpin {N : ℕ} (z : SpinConfig N) (i : Fin N) : SpinConfig N :=
  Function.update z i (!(z i))

/-- Undirected edge `{i, j}` with `i < j`. -/
abbrev IsingEdge (N : ℕ) := { p : Fin N × Fin N // p.1 < p.2 }

/-- Classical Ising Hamiltonian `H(σ) = -∑_{i < j} J_{ij} σ_i σ_j - ∑_i h_i σ_i`. -/
def isingHamiltonianStrict {N : ℕ} (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (σ : SpinConfig N) : ℝ :=
  -(∑ e : IsingEdge N, J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) -
  ∑ i : Fin N, hfield i * spinVal (σ i)

/-- Classical Ising Gibbs measure `μ_{β,J,h}(σ) = exp(-β H(σ)) / Z`. -/
noncomputable def isingGibbsMeasure {N : ℕ} (β : ℝ) (J : Fin N → Fin N → ℝ)
    (hfield : Fin N → ℝ) (σ : SpinConfig N) : ℝ :=
  Real.exp (-β * isingHamiltonianStrict J hfield σ) /
    ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ)

/-- Single-site conditional expectation `E_μ[f | σ_{-i}]`. -/
noncomputable def condExpSite {N : ℕ} (μ : SpinConfig N → ℝ) (i : Fin N)
    (f : SpinConfig N → ℝ) (z : SpinConfig N) : ℝ :=
  (μ z * f z + μ (flipSpin z i) * f (flipSpin z i)) / (μ z + μ (flipSpin z i))

/-- Classical Glauber Dirichlet form `ℰ_μ(f) = ∑_i ∑_z μ(z) (f(z) - E_μ[f | z_{-i}])²`. -/
noncomputable def glauberDirichlet {N : ℕ} (μ : SpinConfig N → ℝ) (f : SpinConfig N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ z : SpinConfig N, μ z * (f z - condExpSite μ i f z) ^ 2

/-- Subspace of multilinear spin functions of degree `≤ k`. -/
def classicalDegreeSubspace (N k : ℕ) : Submodule ℝ (SpinConfig N → ℝ) :=
  Submodule.span ℝ { g : SpinConfig N → ℝ |
    ∃ S : Finset (Fin N), S.card ≤ k ∧ g = fun z ↦ ∏ i ∈ S, spinVal (z i) }

/-- Squared `L²(μ)` distance from `f` to `classicalDegreeSubspace N k`. -/
noncomputable def distSqDegree {N : ℕ} (μ : SpinConfig N → ℝ) (k : ℕ)
    (f : SpinConfig N → ℝ) : ℝ :=
  sInf { r : ℝ | ∃ g ∈ classicalDegreeSubspace N k,
    r = ∑ z : SpinConfig N, μ z * (f z - g z) ^ 2 }

/-- Classical degree-filtration Dirichlet form `Q_μ(f) = ∑_{k=0}^{N-1} d_{L²(μ)}(f, V_k)²`. -/
noncomputable def degreeFiltrationQ {N : ℕ} (μ : SpinConfig N → ℝ) (f : SpinConfig N → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, distSqDegree μ k f

/-- Computational basis index type `Fin N → Fin 2` for `N`-qubit Hilbert space `(ℂ²)^{⊗ N}`. -/
abbrev QubitIdx (N : ℕ) := Fin N → Fin 2

/-- The concrete `2^N × 2^N` operator algebra on `N` qubits `(ℂ²)^{⊗ N}`. -/
abbrev QubitOp (N : ℕ) := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ

/-- Single-qubit Pauli matrices indexed by `Fin 4`: `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`. -/
def pauliMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- Kronecker tensor product `⊗_{x : Fin N} M_x` acting on `(ℂ²)^{⊗ N}`. -/
def kronOp {N : ℕ} (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) : QubitOp N :=
  Matrix.of fun i j ↦ ∏ x : Fin N, M x (i x) (j x)

/-- Concrete `N`-qubit Pauli string `P_a = ⊗_{x=1}^N σ_{a_x}`. -/
def pauliString {N : ℕ} (a : Fin N → Fin 4) : QubitOp N :=
  kronOp (fun x ↦ pauliMat (a x))

/-- Single-site Pauli operator `σ_x^α` acting on site `x` and as identity elsewhere. -/
def pauliSite {N : ℕ} (x : Fin N) (α : Fin 4) : QubitOp N :=
  pauliString (Function.update (fun _ ↦ (0 : Fin 4)) x α)

/-- Normalized single-site trace-averaging superoperator `ℰ_x(A) = (1/4) ∑_{α=0}^3 σ_x^α A σ_x^α`. -/
noncomputable def partialTraceSite {N : ℕ} (x : Fin N) (A : QubitOp N) : QubitOp N :=
  (1 / 4 : ℂ) • ∑ α : Fin 4, pauliSite x α * A * pauliSite x α

/-- Single-site operator-size superoperator `𝒮_x(A) = A - ℰ_x(A)`. -/
noncomputable def siteSizeOp {N : ℕ} (x : Fin N) (A : QubitOp N) : QubitOp N :=
  A - partialTraceSite x A

/-- Concrete ascending locality filtration `𝒱_s ⊆ QubitOp N` spanned by Pauli strings of weight `≤ s`. -/
def filtrationSubmodule (N s : ℕ) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ {P : QubitOp N | ∃ a : Fin N → Fin 4, stringWeight a ≤ s ∧ P = pauliString a}

/-- Subspace of `QubitOp N` spanned by Pauli strings supported inside `U`. -/
def supportedOn {N : ℕ} (U : Finset (Fin N)) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ { P : QubitOp N | ∃ a : Fin N → Fin 4, (∀ x ∉ U, a x = 0) ∧ P = pauliString a }

/-- Subspace of `N`-qubit operators acting trivially on site `x`. -/
def singleSiteTrivialSubmodule (N : ℕ) (x : Fin N) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ { P : QubitOp N | ∃ a : Fin N → Fin 4, a x = 0 ∧ P = pauliString a }

/-- View `A : QubitOp N` as a continuous linear operator on `EuclideanSpace ℂ (QubitIdx N)`. -/
noncomputable def opToCLM {N : ℕ} (A : QubitOp N) :
    EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N) :=
  LinearMap.toContinuousLinearMap
    ((EuclideanSpace.equiv (QubitIdx N) ℂ).symm.toLinearMap.comp
      (A.toLin'.comp (EuclideanSpace.equiv (QubitIdx N) ℂ).toLinearMap))

/-- Spectral / operator norm `‖A‖_op` on `QubitOp N`. -/
noncomputable def opNorm {N : ℕ} (A : QubitOp N) : ℝ := ‖opToCLM A‖

/-- Matrix commutator `[A, B] = A B - B A`. -/
def matComm {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * B - B * A

/-- Finite-dimensional Wightman inner product `(A | B)_β^W = Tr(ρ^{1/2} A† ρ^{1/2} B)`. -/
def wightmanInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρHalf A B : Matrix ι ι ℂ) : ℂ :=
  (ρHalf * Aᴴ * ρHalf * B).trace

/-- Wightman-to-Hilbert–Schmidt isometry `𝒥_β(A) = ρ^{1/4} A ρ^{1/4}`. -/
def jBeta {ι : Type*} [Fintype ι] [DecidableEq ι] (ρQuarter A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ρQuarter * A * ρQuarter

/-- Spectral functional calculus `f(H) = U diag(f(λ_i)) Uᴴ` for Hermitian `H : QubitOp N`. -/
noncomputable def hermFunc {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (f : ℝ → ℂ) : QubitOp N :=
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  U * Matrix.diagonal (fun i ↦ f (hH.eigenvalues i)) * Uᴴ

/-- Partition function `Z(β) = ∑_i exp(-β E_i)` for Hermitian `H : QubitOp N`. -/
noncomputable def gibbsPartitionFn {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  ∑ i : QubitIdx N, Real.exp (-β * hH.eigenvalues i)

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

/-- Complex-time propagator `U(z) = exp(i z H)` on `QubitOp N`. -/
noncomputable def complexPropagator {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z : ℂ) :
    QubitOp N :=
  hermFunc hH (fun E ↦ Complex.exp (Complex.I * z * (E : ℂ)))

/-- Complex-time Heisenberg evolution `A(z) = exp(i z H) A exp(-i z H)`. -/
noncomputable def heisenbergEvol {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (A : QubitOp N) : QubitOp N :=
  complexPropagator hH z * A * complexPropagator hH (-z)

/-- Wightman spectral weight `w_{ab} = Z(β)⁻¹ exp(-(β/2)(E_a + E_b)) |O_{ab}|²`. -/
noncomputable def wightmanSpectralWeight {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (a b : QubitIdx N) : ℝ :=
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  (gibbsPartitionFn hH β)⁻¹ *
    Real.exp (-(β / 2) * (hH.eigenvalues a + hH.eigenvalues b)) *
    ‖(Uᴴ * O * U) a b‖ ^ 2

/-- Concrete Wightman spectral measure on `ℝ` built from `wightmanSpectralWeight`. -/
noncomputable def concreteWightmanSpectralMeasure {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (W : QubitOp N) : Measure ℝ :=
  ∑ a : QubitIdx N, ∑ b : QubitIdx N,
    ENNReal.ofReal (wightmanSpectralWeight hH β W a b) •
      Measure.dirac (hH.eigenvalues a - hH.eigenvalues b)

/-- Concrete Wightman inner product `(A | B)_β^W` for `H, β`. -/
noncomputable def concreteGibbsWightmanInner {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A B : QubitOp N) : ℂ :=
  wightmanInner (gibbsRhoHalf hH β) A B

/-- Concrete Wightman squared norm `‖A‖_{β,W}²` for `H, β`. -/
noncomputable def concreteGibbsWightmanNormSq {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  (concreteGibbsWightmanInner hH β A A).re

/-- Concrete summed Wightman squared commutator `C_W(A) = (1/8) ∑_{x,α} ‖[A, σ_x^α]‖_{β,W}²`. -/
noncomputable def concreteOtocCW {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
    concreteGibbsWightmanNormSq hH β (matComm A (pauliSite x α.succ))

/-- Concrete complex-time OTOC `F_{β,N}(z) = Tr((ρ_β^{1/4} W(z) ρ_β^{1/4} V)²)`. -/
noncomputable def concreteOTOC {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (z : ℂ) : ℂ :=
  let A := jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH z W) * V
  Matrix.trace (A * A)

/-- Concrete shifted Wightman squared norm `‖W(t + i τ)‖_{β,W}²`. -/
noncomputable def concreteWightmanNormAtShift {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W : QubitOp N) (τ t : ℝ) : ℝ :=
  concreteGibbsWightmanNormSq hH β (heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W)

/-- Concrete time-ordered thermal correlator `T_{τ,N}(t)` from Eq. (1.17). -/
noncomputable def concreteTimeOrderedT {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (t τ : ℝ) : ℝ :=
  (gibbsRhoQuarter hH β *
    heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
    gibbsRhoHalf hH β *
    heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W *
    gibbsRhoQuarter hH β * (V * V)).trace.re

/-- Linear equivalence identifying `QubitOp N` with `EuclideanSpace ℂ (QubitIdx N × QubitIdx N)`. -/
noncomputable def qubitOpToHS (N : ℕ) :
    QubitOp N ≃ₗ[ℂ] EuclideanSpace ℂ (QubitIdx N × QubitIdx N) where
  toFun A := WithLp.toLp 2 (fun p : QubitIdx N × QubitIdx N ↦ A p.1 p.2)
  invFun v := Matrix.of (fun i j ↦ (WithLp.ofLp v) (i, j))
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl
  left_inv _ := by ext i j; rfl
  right_inv _ := by ext p; rfl

/-- Concrete Wightman orthogonal projector onto `S : Submodule ℂ (QubitOp N)`. -/
noncomputable def concreteWightmanSubspaceProj {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (S : Submodule ℂ (QubitOp N)) : QubitOp N →ₗ[ℂ] QubitOp N :=
  let jLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun A ↦ jBeta (gibbsRhoQuarter hH β) A
      map_add' := fun A B ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let jInvLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun A ↦ jBeta (gibbsRhoQuarterInv hH β) A
      map_add' := fun A B ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let K : Submodule ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) :=
    S.map ((qubitOpToHS N).toLinearMap.comp jLin)
  letI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  jInvLin.comp ((qubitOpToHS N).symm.toLinearMap.comp
    ((K.starProjection.toLinearMap).comp ((qubitOpToHS N).toLinearMap.comp jLin)))

/-- Concrete Wightman filtration superoperator `𝒬^{(β)} = ∑_{s=0}^{N-1} (1 - Π_s^{(β)})` (Eq. 1.6). -/
noncomputable def concreteWightmanQ {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) : QubitOp N →ₗ[ℂ] QubitOp N :=
  ∑ s ∈ Finset.range N, (LinearMap.id - concreteWightmanSubspaceProj hH β (filtrationSubmodule N s))

/-- Concrete quantum Glauber generator `𝒬̃^{(β)} = ∑_{x=1}^N (1 - P_{x,0}^{(β)})` (Eq. 1.7). -/
noncomputable def concreteQuantumGlauberGen {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) : QubitOp N →ₗ[ℂ] QubitOp N :=
  ∑ x : Fin N, (LinearMap.id - concreteWightmanSubspaceProj hH β (singleSiteTrivialSubmodule N x))

/-- All-temperature 1D Araki constant `M_{1D}(β, r, J)`. -/
noncomputable def araki1DM (β : ℝ) (r : ℕ) (J : ℝ) : ℝ :=
  Real.exp ((r : ℝ) * J * |β| * (1 + Real.exp ((r : ℝ) * J * |β|)))

end ChallengeDefs
