/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.ClassicalIsing
import KrylovChaos.DepolarizedFrame
import KrylovChaos.Filtration
import KrylovChaos.GlauberDecoupling
import KrylovChaos.KrylovTail
import KrylovChaos.PolymerTrees
import KrylovChaos.ProductState
import KrylovChaos.SpectralDyck
import KrylovChaos.StructuralNecessity
import KrylovChaos.WightmanIsometry
import KrylovChaos.HighTempSharpBounds
import KrylovChaos.Section9EndToEnd
import KrylovChaos.MainTheoremPackaging

/-!
# Non-Vacuity Witnesses and Concrete Small-Case Sanity Checks

Verifies that the hypotheses of the main theorems are non-vacuously satisfiable
and confirms concrete evaluations at small system sizes (`N = 2`, `N = 4`, `D = 4`, `r = 2`).
-/

namespace KrylovChaos

open Matrix

/-- Concrete parameter check at `r = 2`, `J_site = 1`: `κ = 1/2` and `0 < β_wc < 2 κ`. -/
theorem sanity_invLocalityScale_r2 :
    invLocalityScale 2 1 = 1 / 2 ∧
    0 < betaWC 2 1 ∧
    betaWC 2 1 < 2 * invLocalityScale 2 1 := by
  refine ⟨?_, betaWC_pos (by omega) (by norm_num), betaWC_lt_two_kappa (by omega) (by norm_num)⟩
  unfold invLocalityScale
  norm_num

/-- Non-vacuity witness for **Theorem 1.1(a)** on the `Nmax = 0` static chain (`b ≡ 0`, `φ_0 ≡ 1`). -/
theorem sanity_theorem_1_1a_static_zero :
    finiteKrylovComplexity 0 (fun n _ ↦ if n = 0 then (1 : ℝ) else 0) 0 ≤
      (Real.exp ((1 / 2 + (0 : ℝ) / 1) * 1) / (4 * Real.exp 1 * Real.tanh (1 / 4))) *
        Real.exp (2 * 1 * 0) := by
  exact theorem_1_1a_finite_complexity
    (Nmax := 0) (α := 1) (γ := 0) (θ₀ := 1)
    (b := fun _ ↦ 0) (φ := fun n _ ↦ if n = 0 then (1 : ℝ) else 0)
    (by norm_num) le_rfl (by norm_num) rfl rfl
    (fun _ _ _ ↦ le_rfl)
    (fun n _ _ ↦ by positivity)
    (fun n hn t ↦ by
      have hn0 : n = 0 := by omega
      subst hn0
      simpa using hasDerivAt_const t (1 : ℝ))
    (fun _ _ ↦ rfl)
    0 le_rfl

/-- Concrete check of **Lemma 7.1** on `s = 0` (`P̃_0` Hermitian, trace `1`). -/
theorem sanity_lemma_7_1_frame :
    (depolP 0)ᴴ = depolP 0 ∧ Matrix.trace (depolP 0) = 1 :=
  ⟨lemma_7_1_herm_trace_avg.1 0, lemma_7_1_herm_trace_avg.2.1 0⟩

/-- Concrete instantiation of **Theorem 1.3(b)** at `r = 2`, `J_site = 1`, `β = β_wc(2, 1)`. -/
theorem sanity_theorem_1_3b_r2 :
    (3 / 2 : ℝ) * (1 - betaWC 2 1 / (4 * invLocalityScale 2 1))⁻¹ ^ 2 * 9 < 54 ∧
    2 * betaWC 2 1 * (3 : ℝ) ^ (2 - 1) * Real.exp 1 * (2 : ℝ) * 1 ≤ 1 / 2 ∧
    (3 / 8 : ℝ) * (24 : ℝ) ^ 2 = 216 :=
  theorem_1_3b_constants (r := 2) (β := betaWC 2 1) (Jsite := 1)
    (by omega) (by norm_num) (betaWC_pos (by omega) (by norm_num)).le le_rfl

/-- Concrete spin check of **Lemma 8.2** at `u = 1, s = 1, z₁ = 1, z₂ = -1`. -/
theorem sanity_lemma_8_2_ising :
    Real.exp ((1 : ℝ) * (1 * 1 * (-1))) =
    Real.exp (-1) * (1 / 2 : ℝ) *
      (Real.exp (hsPhi 1 * (1 + 1 * (-1))) + Real.exp (-(hsPhi 1 * (1 + 1 * (-1))))) :=
  lemma_8_2_hubbard_stratonovich_identity (u := 1) (s := 1) (z₁ := 1) (z₂ := -1)
    (by norm_num) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)

/-- Concrete evaluation of **Proposition 9.1** bimodal exact background size at `N = 2`. -/
theorem sanity_prop_9_1_bimodal_N2 :
    let z1Contrib := (2 : ℝ) ^ (2 : ℕ) * (1 / 8 : ℝ) *
      ((2 : ℝ) ^ (-((2 - 1 : ℕ) : ℝ) / 2) - (2 : ℝ) ^ (-((2 - 1 : ℕ) : ℝ))) ^ 2
    let nonemptyContrib := (2 : ℝ) ^ (-((2 + 1 : ℕ) : ℝ)) *
      ∑ k ∈ Finset.Icc 1 (2 - 1), (Nat.choose (2 - 1) k : ℝ) * (2 * (k : ℝ) + 1)
    let bgSize := z1Contrib + nonemptyContrib
    bgSize = ((2 : ℝ) + 1) / 4 - (2 : ℝ) ^ (-((2 + 1 : ℕ) : ℝ) / 2) ∧
    (2 : ℝ) / 2 - bgSize = ((2 : ℝ) - 1) / 4 + (2 : ℝ) ^ (-((2 + 1 : ℕ) : ℝ) / 2) :=
  prop_9_1_bimodal_exact_size (N := 2) (by omega)

/-- Concrete evaluation of **Lemma B.1** at `d = 1`, `E_B = 4`. -/
theorem sanity_lemma_B_1_d1_EB4 :
    Real.sqrt 2 * (∑' m : ℕ, (2 : ℝ) ^ (1 - 1 + m) / (4 : ℝ) ^ (1 - 1 + m + 1)) =
    (Real.sqrt 2 / (4 - 2)) * (2 / (4 : ℝ)) ^ (1 - 1) :=
  lemma_B_1_neumann_tail_sum (d := 1) (EB := 4) (by omega) (by norm_num)

/-- Concrete linear upper bound on the discrete Hubbard–Stratonovich parameter at `β = 1, J = 1`. -/
theorem sanity_isingHSParam_linear :
    isingHSParam 1 1 ≤ (1 : ℝ) * |(1 : ℝ)| + (1 / 2 : ℝ) * Real.log 2 :=
  isingHSParam_le_linear (by norm_num) 1

/-- Concrete `N = 2` non-vacuity witness for the Eq. (9.1) qubit-1-conditioned bimodal state
and 1-local witness `A = √2 |1⟩⟨1|_0`. -/
theorem sanity_eq91_bimodal_N2 :
    gibbsWightmanNormSq
        (eq91BimodalGibbs 2 ⟨0, by omega⟩ (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1))
        (eq91WitnessOp ⟨0, by omega⟩) = 1 ∧
    ((2 - 1 : ℝ) / 4) * (1 - (1 / 32 : ℝ) - 2 * Real.sqrt (2 * (1 / 32 : ℝ) / (2 : ℝ) ^ 2)) ≤
      lambdaMSS
        (eq91BimodalGibbs 2 ⟨0, by omega⟩ (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)) 1 :=
  ⟨eq91WitnessOp_wightmanNormSq ⟨0, by omega⟩ (by norm_num) (by norm_num),
   eq91Bimodal_lambdaMSS_lower (by omega) ⟨0, by omega⟩ (by norm_num) (by norm_num)⟩

/-- Concrete `D = 4, E_B = 4` non-vacuity witness for the 2D double-well Lanczos basis `{|K₀⟩, |K₁⟩}`. -/
theorem sanity_doubleWell_lanczos_D4_EB4 :
    vecInner (doubleWellK0 (D := 4) (by omega) (E_B := 4) (by norm_num))
      (doubleWellK0 (D := 4) (by omega) (E_B := 4) (by norm_num)) = 1 ∧
    vecInner (doubleWellK1 (D := 4) (by omega) (E_B := 4) (by norm_num))
      (doubleWellK1 (D := 4) (by omega) (E_B := 4) (by norm_num)) = 1 ∧
    vecInner (doubleWellK0 (D := 4) (by omega) (E_B := 4) (by norm_num))
      (doubleWellK1 (D := 4) (by omega) (E_B := 4) (by norm_num)) = 0 :=
  doubleWell_lanczos_orthonormal (D := 4) (by omega) (E_B := 4) (by norm_num)

/-- Concrete `D = 4, E_B = 4` non-vacuity witness for Courant–Fischer bulk eigenvalue localization. -/
theorem sanity_lemma_B_1_bulk_D4_EB4 :
    let hL := doubleWellTridiag_isHermitian 4 4
    (∀ k : Fin 4, hL.eigenvalues k ≤ 4 + 2) ∧
    (Finset.univ.filter (fun k : Fin 4 ↦ hL.eigenvalues k < 4 - 2)).card ≤ 2 ∧
    4 - 2 ≤ (Finset.univ.filter (fun k : Fin 4 ↦ 4 - 2 ≤ hL.eigenvalues k ∧
      hL.eigenvalues k ≤ 4 + 2)).card :=
  lemma_B_1_bulk_eigenvalues_in_band (D := 4) (by omega) (E_B := 4) (by norm_num)

/-- Concrete `N = 2, r = 2` non-vacuity witness for the sharp Proposition 6.2 high-temperature bound. -/
theorem sanity_prop_6_2_sharp_N2 :
    let E : Finset (Finset (Fin 2)) := ∅
    let h : Finset (Fin 2) → QubitOp 2 := fun _ ↦ 0
    let hH : (∑ X ∈ E, h X).IsHermitian := by simp [E, h]
    let κ : ℝ := 1 / (2 * ((2 - 1 : ℕ) : ℝ) * 1)
    let G := concreteGibbsData hH 1
    otocCW G (1 : QubitOp 2) ≤ (3 / 2 : ℝ) * (1 - 1 / (4 * κ))⁻¹ ^ 2 *
      (gibbsWightmanInner G (1 : QubitOp 2) (quantumGlauberGen G (1 : QubitOp 2))).re :=
  prop_6_2_sharp_r_local_high_temp (N := 2) (r := 2) (by omega) ∅
    (by simp) (fun _ ↦ 0) (fun _ ↦ Submodule.zero_mem _) (by simp)
    (Jsite := 1) (β := 1) (by norm_num)
    (fun _ ↦ by simp) (by norm_num) (by norm_num) (1 : QubitOp 2)

/-- Concrete `N = 4, Δ = 2 < N - 1` non-vacuity witness for the 1D nearest-neighbor Ising chain,
confirming active-edge degree `Δ = 2 < 3` in `prop_8_3_ising_explicit_eq_8_4_cosh`. -/
theorem sanity_ising_1d_chain_N4_Delta2 (f : SpinConfig 4 → ℝ) :
    let J : Fin 4 → Fin 4 → ℝ := fun i j ↦ if i.val + 1 = j.val then 1 else 0
    glauberDirichlet (isingGibbsMeasure 1 J (fun _ ↦ 0)) f ≤
      (Real.cosh (1 * 2 + ((2 : ℕ) : ℝ) / 2 * Real.log 2)) ^ 2 *
        degreeFiltrationQ (isingGibbsMeasure 1 J (fun _ ↦ 0)) f := by
  intro J
  have hsum_edge : ∀ g : Fin 4 × Fin 4 → ℝ,
      (∑ e : IsingEdge 4, g e.1) =
        ∑ a : Fin 4, ∑ b : Fin 4, if a < b then g (a, b) else 0 := by
    intro g
    rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
    refine Finset.sum_bij (fun e _ ↦ e.1) ?_ ?_ ?_ ?_
    · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
    · intro e₁ _ e₂ _ h; exact Subtype.ext h
    · intro p hp; exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  refine prop_8_3_ising_explicit_eq_8_4_cosh (N := 4) (Δ := 2) (β := 1) (H_max := 2)
    (by norm_num) (by norm_num) J (fun _ ↦ 0) ?_ ?_ f
  · intro i
    rw [hsum_edge (fun p ↦ if J p.1 p.2 ≠ 0 then
      ((if p.1 = i then (1 : ℝ) else 0) + (if p.2 = i then (1 : ℝ) else 0)) else 0)]
    fin_cases i <;> (simp [Fin.sum_univ_four, J]; try norm_num)
  · intro i
    rw [abs_zero, zero_add]
    rw [hsum_edge (fun p ↦ (if p.1 = i then |J p.1 p.2| else 0) + (if p.2 = i then |J p.1 p.2| else 0))]
    fin_cases i <;> (simp [Fin.sum_univ_four, J]; try norm_num)

end KrylovChaos
