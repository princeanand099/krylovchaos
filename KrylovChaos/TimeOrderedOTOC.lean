/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.SpectralDyck
import KrylovChaos.Milestone2AnalyticFoundations
import KrylovChaos.Milestone2SpectralAndVitali
import Mathlib.Tactic

/-!
# Concrete Time-Ordered Correlator and Three-Way OTOC Dominance (Theorem 1.2(c), Eq. 1.17)

Defines the concrete time-ordered thermal correlator
`T_{τ,N}(t) = Re Tr(ρ_β^{1/4} W(t - iτ) ρ_β^{1/2} W(t + iτ) ρ_β^{1/4} V²)`
and proves the exact three-way OTOC bound Eq. (1.17) of Theorem 1.2(c):
`|F_{W,V}(t + iτ)| ≤ min(‖V‖_∞² C_W(2iτ), ‖W‖_∞² C_V(-2iτ), T_{τ,N}(t))`.
-/

namespace KrylovChaos

open Matrix

/-- Concrete time-ordered thermal correlator `T_{τ,N}(t)` from Eq. (1.17):
`Re Tr(ρ_β^{1/4} W(t - iτ) ρ_β^{1/2} W(t + iτ) ρ_β^{1/4} V²)`. -/
noncomputable def concreteTimeOrderedT {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (t τ : ℝ) : ℝ :=
  (gibbsRhoQuarter hH β *
    heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
    gibbsRhoHalf hH β *
    heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W *
    gibbsRhoQuarter hH β * (V * V)).trace.re

/-- Conjugate transpose of the complex-time propagator:
`(complexPropagator hH z)ᴴ = complexPropagator hH (-starRingEnd ℂ z)`. -/
lemma complexPropagator_conjTranspose {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z : ℂ) :
    (complexPropagator hH z)ᴴ = complexPropagator hH (-(starRingEnd ℂ z)) := by
  unfold complexPropagator hermFunc
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 1; congr 1
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    congr 1; ring
  · simp [hij, Ne.symm hij]

/-- Conjugate transpose of complex-time Heisenberg evolution of a Hermitian operator:
`(heisenbergEvol hH z W)ᴴ = heisenbergEvol hH (starRingEnd ℂ z) W`. -/
lemma heisenbergEvol_conjTranspose_of_herm {N : ℕ} {H W : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (z : ℂ) :
    (heisenbergEvol hH z W)ᴴ = heisenbergEvol hH (starRingEnd ℂ z) W := by
  unfold heisenbergEvol
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    complexPropagator_conjTranspose, complexPropagator_conjTranspose, hW.eq]
  simp only [map_neg, neg_neg, Matrix.mul_assoc]

/-- Direct Hilbert–Schmidt dominance `‖F_{W,V}(t + iτ)‖ ≤ T_{τ,N}(t)` for Hermitian `W, V`. -/
theorem concreteOTOC_norm_le_timeOrderedT {N : ℕ} {H W V : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hV : V.IsHermitian) (β t τ : ℝ) :
    ‖concreteOTOC hH β W V ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
      concreteTimeOrderedT hH β W V t τ := by
  set z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
  set G := concreteGibbsData hH β
  set B : QubitOp N := jBeta G.ρQuarter (heisenbergEvol hH z W)
  have hz_conj : starRingEnd ℂ z = (t : ℂ) - Complex.I * (τ : ℂ) := by
    dsimp only [z]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hB_adj : Bᴴ = jBeta G.ρQuarter (heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W) := by
    unfold B jBeta
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, G.ρQuarter_herm,
      heisenbergEvol_conjTranspose_of_herm hH hW z, hz_conj, Matrix.mul_assoc]
  have hBB : Bᴴ * B =
      gibbsRhoQuarter hH β *
        heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
        gibbsRhoHalf hH β *
        heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W *
        gibbsRhoQuarter hH β := by
    rw [hB_adj]
    unfold B jBeta
    have hq : G.ρQuarter * G.ρQuarter = gibbsRhoHalf hH β := G.sq_quarter
    change (gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W * gibbsRhoQuarter hH β) *
      (gibbsRhoQuarter hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β) = _
    calc (gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W * gibbsRhoQuarter hH β) *
          (gibbsRhoQuarter hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β)
        = gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
          (gibbsRhoQuarter hH β * gibbsRhoQuarter hH β) *
          heisenbergEvol hH z W * gibbsRhoQuarter hH β := by simp only [Matrix.mul_assoc]
      _ = gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
          gibbsRhoHalf hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β := by rw [hq]
  have hotoc_eq : concreteOTOC hH β W V z = Matrix.trace ((B * V) * (B * V)) := rfl
  have hT_eq : concreteTimeOrderedT hH β W V t τ = hsNormSq (B * V) := by
    unfold concreteTimeOrderedT hsNormSq hsInner
    rw [← hBB]
    congr 1
    rw [Matrix.conjTranspose_mul, hV.eq]
    calc (Bᴴ * B * (V * V)).trace
        = ((Bᴴ * B * V) * V).trace := by simp only [Matrix.mul_assoc]
      _ = (V * (Bᴴ * B * V)).trace := Matrix.trace_mul_comm _ _
      _ = (V * Bᴴ * (B * V)).trace := by simp only [Matrix.mul_assoc]
  rw [hotoc_eq, hT_eq]
  exact trace_sq_norm_le_hsNormSq (B * V)

/-- **Theorem 1.2(c) — Exact Three-Way OTOC Dominance (Eq. 1.17)**:
For any Hermitian `H, W, V : QubitOp N` and any `β, t, τ : ℝ`:
`‖F_{W,V}(t + iτ)‖ ≤ min(‖V‖_∞² C_W(2iτ), ‖W‖_∞² C_V(-2iτ), T_{τ,N}(t))`. -/
theorem theorem_1_2c_concrete_eq_1_17 {N : ℕ} {H W V : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hV : V.IsHermitian) (β t τ : ℝ) :
    let z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
    ‖concreteOTOC hH β W V z‖ ≤
      min ((opNorm V) ^ 2 * concreteWightmanNormAtShift hH β W τ 0)
        (min ((opNorm W) ^ 2 * concreteWightmanNormAtShift hH β V (-τ) 0)
          (concreteTimeOrderedT hH β W V t τ)) := by
  intro z
  have h12 := concreteOTOC_three_way_eq_1_17 hH hW hV β t τ
  have h3 := concreteOTOC_norm_le_timeOrderedT hH hW hV β t τ
  exact le_min h12.1 (le_min h12.2.1 h3)

end KrylovChaos
