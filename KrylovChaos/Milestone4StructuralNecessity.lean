/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.SpectralMeasure
import KrylovChaos.BimodalExact
import KrylovChaos.SpectralSmearingAndDoubleWell
import KrylovChaos.StructuralNecessity
import KrylovChaos.ConcreteEndToEndWiring
import Mathlib.Tactic

/-!
# Milestone 4 Structural Necessity Bridges: Proposition 9.1(1)–(3) & Appendix B (Items #21–#23)
-/

namespace KrylovChaos

open Matrix Filter

section Item21GaussianSmearingEntireAndLiminf

theorem prop_9_1_part1_entire_autocorr {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β σ : ℝ) (O : QubitOp N) :
    Differentiable ℂ (fun z : ℂ ↦ wightmanAutocorr hH β (gaussianSmear hH σ O) z) := by
  have heq : (fun z : ℂ ↦ wightmanAutocorr hH β (gaussianSmear hH σ O) z) =
      fun z : ℂ ↦ ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        (spectralWeight hH β (gaussianSmear hH σ O) i j : ℂ) *
          Complex.exp (Complex.I * z * ((hH.eigenvalues i - hH.eigenvalues j : ℝ) : ℂ)) :=
    funext fun z ↦ eq_5_1_wightman_fourier_identity hH β (gaussianSmear hH σ O) z
  rw [heq]
  refine Differentiable.fun_sum fun i _ ↦ Differentiable.fun_sum fun j _ ↦ ?_
  refine Differentiable.const_mul ?_ _
  exact Complex.differentiable_exp.comp
    ((differentiable_id.const_mul Complex.I).mul_const _)

theorem prop_9_1_part1_liminf_eq_zero (b : ℕ → ℝ) (hb_nn : ∀ n, 0 ≤ b n)
    (hstrip : ∀ r : ℝ, 0 < r →
      Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / (2 * r)) :
    Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop = 0 := by
  set L := Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop
  have hL_le : L ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := hstrip (Real.pi / L) (div_pos Real.pi_pos hpos)
    have hrhs : Real.pi / (2 * (Real.pi / L)) = L / 2 := by
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have hLne : L ≠ 0 := hpos.ne'
      field_simp [hpi, hLne]
    rw [hrhs] at h1
    linarith
  have hL_ge : 0 ≤ L := by
    have hnn : ∀ᶠ n : ℕ in Filter.atTop, (0 : ℝ) ≤ b n / (n : ℝ) :=
      Eventually.of_forall fun n ↦ div_nonneg (hb_nn n) (Nat.cast_nonneg n)
    exact Filter.le_liminf_of_le (by exact ⟨0, fun a ha ↦ by
      rcases ha.exists with ⟨n, hn⟩
      exact le_trans (div_nonneg (hb_nn n) (Nat.cast_nonneg n)) hn⟩) hnn
  exact le_antisymm hL_le hL_ge

end Item21GaussianSmearingEntireAndLiminf

section Item22BimodalLocalObservable

lemma pauliSite_mem_filtration_one {N : ℕ} (x : Fin N) (α : Fin 3) :
    pauliSite x α.succ ∈ filtrationSubmodule N 1 := by
  unfold pauliSite filtrationSubmodule
  apply Submodule.subset_span
  refine ⟨Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ, ?_, rfl⟩
  unfold stringWeight
  have hsub : Finset.univ.filter (fun y : Fin N ↦ Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y ≠ 0) ⊆ {x} := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hy ⊢
    by_contra hne
    exact hy (by simp [Function.update_of_ne hne])
  calc (Finset.univ.filter (fun y : Fin N ↦ Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y ≠ 0)).card
      ≤ ({x} : Finset (Fin N)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton x

theorem prop_9_1_part2_bimodal_theta_N {N : ℕ} (hN : 2 ≤ N) (x : Fin N) :
    pauliSite x 3 ∈ filtrationSubmodule N 1 ∧
    hsInner (bimodalJADiag N) (totalSizeOp (bimodalJADiag N)) -
      hsInner (bimodalRhoHalfDiag N) (totalSizeOp (bimodalRhoHalfDiag N)) =
      (((N : ℝ) - 1 : ℝ) : ℂ) := by
  refine ⟨pauliSite_mem_filtration_one x 2, ?_⟩
  have h := prop_9_1_bimodal_operator_exact_size (N := N) (by omega)
  exact h

end Item22BimodalLocalObservable

section Item23TwoLevelTunnelingAndEq93

theorem twoLevel_tunneling_complexity {Δ : ℝ} (hΔ : 0 < Δ) :
    let φ₀ : ℝ → ℝ := fun t ↦ Real.cos (Δ * t / 2)
    let φ₁ : ℝ → ℝ := fun t ↦ Real.sin (Δ * t / 2)
    let K : ℝ → ℝ := fun t ↦ 0 * (φ₀ t) ^ 2 + 1 * (φ₁ t) ^ 2
    (∀ t, (φ₀ t) ^ 2 + (φ₁ t) ^ 2 = 1) ∧
    (∀ t, K t = (Real.sin (Δ * t / 2)) ^ 2) ∧
    K (Real.pi / Δ) = 1 ∧
    (φ₁ (Real.pi / Δ)) ^ 2 = 1 := by
  intro φ₀ φ₁ K
  have hnorm : ∀ t, (φ₀ t) ^ 2 + (φ₁ t) ^ 2 = 1 := fun t ↦ Real.cos_sq_add_sin_sq _
  have hK : ∀ t, K t = (Real.sin (Δ * t / 2)) ^ 2 := fun t ↦ by dsimp only [K, φ₁]; ring
  have harg : Δ * (Real.pi / Δ) / 2 = Real.pi / 2 := by field_simp [hΔ.ne']
  have hsin : Real.sin (Δ * (Real.pi / Δ) / 2) = 1 := by rw [harg, Real.sin_pi_div_two]
  refine ⟨hnorm, hK, ?_, ?_⟩
  · rw [hK, hsin, one_pow]
  · dsimp only [φ₁]; rw [hsin, one_pow]

theorem prop_9_1_part3_tunneling_time_lower_bound {D : ℕ} {Δ C E_B : ℝ}
    (hΔ : 0 < Δ) (hC : 0 < C) (hEB : 0 < E_B)
    (hsplit : Δ ≤ C * (2 / E_B) ^ D) :
    (Real.pi / C) * (E_B / 2) ^ D ≤ Real.pi / Δ := by
  have hpos : 0 < C * (2 / E_B) ^ D := by positivity
  have h1 : Real.pi / (C * (2 / E_B) ^ D) ≤ Real.pi / Δ :=
    div_le_div_of_nonneg_left Real.pi_pos.le hΔ hsplit
  have heq : Real.pi / (C * (2 / E_B) ^ D) = (Real.pi / C) * (E_B / 2) ^ D := by
    rw [div_pow, div_pow]
    have h2 : (2 : ℝ) ^ D ≠ 0 := pow_ne_zero D (by norm_num)
    have hE : E_B ^ D ≠ 0 := pow_ne_zero D hEB.ne'
    field_simp [hC.ne', h2, hE]
  rwa [heq] at h1

end Item23TwoLevelTunnelingAndEq93

end KrylovChaos
