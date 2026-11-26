/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Locked Challenge Definitions for `KrylovChaos`

Self-contained transparent definitions (using only Lean core and Mathlib)
referenced by the locked headline theorem signatures in `Challenge.lean`.
-/

namespace ChallengeDefs

open Matrix

/-- Inverse locality scale `κ := (2 (r - 1) J_site)⁻¹`. -/
noncomputable def invLocalityScale (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (2 * ((r : ℝ) - 1) * Jsite)

/-- High-temperature weak-coupling threshold `β_wc := (4 · 6^r · e^2 · r · J_site)⁻¹`. -/
noncomputable def betaWC (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (4 * (6 : ℝ) ^ r * Real.exp 2 * (r : ℝ) * Jsite)

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

end ChallengeDefs
