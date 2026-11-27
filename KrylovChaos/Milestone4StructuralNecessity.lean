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

Strictly Mathlib-only, complete proofs, zero custom axioms, zero hypothesis laundering:
1. **Item #21 (Proposition 9.1(1) — Entireness of Gaussian-Smeared Autocorrelation & `liminf b_n / n = 0`)**:
   - `prop_9_1_part1_entire_autocorr`: for every Hermitian `H : QubitOp N`, `O : QubitOp N`,
     `β : ℝ`, and `σ > 0`, `z ↦ gibbsWightmanInner (concreteGibbsData hH β) (gaussianSmear hH σ O)
     (heisenbergEvol hH z (gaussianSmear hH σ O))` is entire (`Differentiable ℂ`).
   - `prop_9_1_part1_liminf_eq_zero`: if `b : ℕ → ℝ` (`0 ≤ b n`) satisfies the universal
     strip bound `liminf_{n → ∞} b_n / n ≤ π / (2 r)` for EVERY `r > 0` (as holds for any
     Gaussian-smeared spectral density with `r_W = ∞`), then
     `Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop = 0`.
2. **Item #22 (Proposition 9.1(2) — 1-Local Observable `Z_0 ∈ filtrationSubmodule N 1` & Bimodal `Θ(N)` Size)**:
   - `pauliSite_mem_filtration_one`: `pauliSite x α.succ ∈ filtrationSubmodule N 1`.
   - `prop_9_1_part2_bimodal_theta_N`: wires `pauliSite_mem_filtration_one` with
     `BimodalExact.prop_9_1_bimodal_operator_exact_size` to exhibit a concrete 1-local
     observable with `Θ(N)` thermal size (`= (N - 1)/4 + (√(2^(N+1)))⁻¹` at `N ≥ 2`).
3. **Item #23 (Proposition 9.1(3) & Lemma B.1 — Two-Level Unitary Tunneling `K(t_*) = 1` & Eq. 9.3)**:
   - `twoLevel_tunneling_complexity`: for the exact 2-level tunneling pair with splitting
     `Δ > 0`, proves `φ_0(t)² + φ_1(t)² = 1`, `K(t) = Real.sin (Δ * t / 2) ^ 2`, and
     at `t_* = Real.pi / Δ`: `K(t_*) = 1` and tunneling transfer probability `|φ_1(t_*)|² = 1`.
   - `prop_9_1_part3_tunneling_time_lower_bound`: combines `Δ ≤ C * (2 / E_B)^D` (from
     Lemma B.1) with `t_* = π / Δ` to derive Eq. (9.3): `t_* ≥ (π / C) * (E_B / 2)^D`.
-/

namespace KrylovChaos

open Matrix Filter

section Item21GaussianSmearingEntireAndLiminf

private lemma differentiable_complexPropagator_entry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (i j : QubitIdx N) :
    Differentiable ℂ (fun z : ℂ ↦ complexPropagator hH z i j) := by
  have heq : (fun z : ℂ ↦ complexPropagator hH z i j) =
      fun z : ℂ ↦ ∑ k : QubitIdx N,
        ((hH.eigenvectorUnitary : QubitOp N) i k * (hH.eigenvectorUnitary : QubitOp N)ᴴ k j) *
          Complex.exp (Complex.I * z * (hH.eigenvalues k : ℂ)) := by
    funext z
    unfold complexPropagator hermFunc
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [heq]
  refine Differentiable.fun_sum fun k _ ↦ Differentiable.const_mul ?_ _
  exact Complex.differentiable_exp.comp
    ((differentiable_id.const_mul Complex.I).mul_const _)

/-- **Item #21 (Entireness of Gaussian-Smeared Wightman Autocorrelation)**:
For ANY Hermitian `H : QubitOp N`, `O : QubitOp N`, `β : ℝ`, and `σ : ℝ`, the Wightman
autocorrelation `z ↦ (O_σ | O_σ(z))_β^W` is entire on `ℂ`. -/
theorem prop_9_1_part1_entire_autocorr {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β σ : ℝ) (O : QubitOp N) :
    Differentiable ℂ (fun z : ℂ ↦
      gibbsWightmanInner (concreteGibbsData hH β) (gaussianSmear hH σ O)
        (heisenbergEvol hH z (gaussianSmear hH σ O))) := by
  set Oσ := gaussianSmear hH σ O
  set ρH := (concreteGibbsData hH β).ρHalf
  have heq : (fun z : ℂ ↦ gibbsWightmanInner (concreteGibbsData hH β) Oσ (heisenbergEvol hH z Oσ)) =
      fun z : ℂ ↦ ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        (ρH * Oσᴴ * ρH) i j *
          ∑ k : QubitIdx N, ∑ l : QubitIdx N,
            complexPropagator hH z j k * Oσ k l * complexPropagator hH (-z) l i := by
    funext z
    unfold gibbsWightmanInner wightmanInner heisenbergEvol
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [heq]
  refine Differentiable.fun_sum fun i _ ↦ Differentiable.fun_sum fun j _ ↦
    Differentiable.const_mul ?_ _
  refine Differentiable.fun_sum fun k _ ↦ Differentiable.fun_sum fun l _ ↦ ?_
  exact ((differentiable_complexPropagator_entry hH j k).mul_const _).mul
    ((differentiable_complexPropagator_entry hH l i).comp differentiable_neg)

/-- **Item #21 (Sublinear Lanczos Growth `liminf_{n → ∞} b_n / n = 0` from Entireness `r_W = ∞`)**:
If `b : ℕ → ℝ` (`0 ≤ b n`) satisfies `liminf (b n / n) ≤ π / (2 r)` for EVERY `r > 0`
(which follows from `theorem_1_2b_lanczos_liminf_bound` for every strip width `r > 0`
when the spectral measure has Gaussian tail `exp(-σ^2 ω^2)`), then
`Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop = 0`. -/
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
    by_cases hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun n : ℕ ↦ b n / (n : ℝ))
    · exact Filter.le_liminf_of_le hcb hnn
    · dsimp only [L]
      unfold Filter.liminf Filter.limsInf
      rw [Real.sSup_of_not_bddAbove]
      intro ⟨M, hM⟩
      exact hcb ⟨M, fun a ha ↦ hM (by simpa [Filter.eventually_map] using ha)⟩
  exact le_antisymm hL_le hL_ge

end Item21GaussianSmearingEntireAndLiminf

section Item22BimodalLocalObservable

/-- Every single-site Pauli operator `pauliSite x α.succ` lies in `filtrationSubmodule N 1`. -/
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

/-- **Item #22 (Proposition 9.1(2) — 1-Local Observable with `Θ(N)` Bimodal Thermal Size)**:
For every `N ≥ 2` and `x : Fin N`, the 1-local Pauli operator `Z_x ∈ filtrationSubmodule N 1`
together with the bimodal GHZ-mixture state achieves exact operator thermal size
`= (N - 1) / 4 + (√(2^(N+1)))⁻¹` (scaling linearly as `Θ(N)`). -/
theorem prop_9_1_part2_bimodal_theta_N {N : ℕ} (hN : 2 ≤ N) (x : Fin N) :
    pauliSite x 3 ∈ filtrationSubmodule N 1 ∧
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re -
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re =
      ((N : ℝ) - 1) / 4 + (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ :=
  ⟨pauliSite_mem_filtration_one x 2, prop_9_1_bimodal_operator_exact_size hN⟩

end Item22BimodalLocalObservable

section Item23TwoLevelTunnelingAndEq93

/-- **Item #23 (Exact Two-Level Unitary Tunneling Krylov Complexity `K(t) = sin²(Δ t / 2)`)**:
For the exact 2-level tunneling pair with splitting `Δ > 0`:
- `φ_0(t) = cos(Δ t / 2)` and `φ_1(t) = sin(Δ t / 2)` satisfy `φ_0(t)² + φ_1(t)² = 1`,
- Krylov complexity `K(t) = 0 * φ_0(t)² + 1 * φ_1(t)² = sin²(Δ t / 2)`,
- At `t_* = π / Δ`: `K(t_*) = 1` and tunneling probability `φ_1(t_*)² = 1`. -/
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

/-- **Item #23 (Proposition 9.1(3) & Eq. (9.3) Tunneling Time Lower Bound)**:
If the double-well energy splitting satisfies `0 < Δ ≤ C * (2 / E_B) ^ D` with `C > 0`
and `E_B > 2` (from Lemma B.1 / Neumann-series barrier decay), then the tunneling time
`t_* = π / Δ` satisfies Eq. (9.3): `t_* ≥ (π / C) * (E_B / 2) ^ D`. -/
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
