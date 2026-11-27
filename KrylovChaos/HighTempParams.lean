/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.Lemma72Concrete
import KrylovChaos.ShiftedCommutatorAndThm13c
import KrylovChaos.Milestone3Sections678
import Mathlib.Tactic

/-!
# High-Temperature Threshold `β_wc` and Unconditional Statements of Lemma 7.2 and Theorem 1.3(a)–(b)

Defines the explicit high-temperature inverse-temperature threshold
`highTempBetaWC r J = (4 e² r 6^r J)⁻¹`
and proves that `0 ≤ β ≤ highTempBetaWC r J` automatically discharges all Kotecký–Preiss
and causal-series hypotheses, exposing clean top-level statements of Lemma 7.2, Theorem 1.3(a),
and Theorem 1.3(b) parameterized solely by `(r, J, β)` and the local interaction bound.
-/

namespace KrylovChaos

open Matrix

/-- Explicit high-temperature threshold `β_wc(r, J) = (4 e² r 6^r J)⁻¹`. -/
noncomputable def highTempBetaWC (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite)

lemma highTempBetaWC_pos {r : ℕ} (hr : 2 ≤ r) {Jsite : ℝ} (hJ : 0 < Jsite) :
    0 < highTempBetaWC r Jsite := by
  unfold highTempBetaWC
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  positivity

/-- Elementary exponential upper bound: for `0 ≤ u ≤ 1`, `exp u - 1 ≤ e * u`. -/
lemma exp_sub_one_le_e_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ Real.exp 1 * u := by
  have h1 : Real.exp (-u) ≥ 1 - u := by linarith [Real.add_one_le_exp (-u)]
  have h2 : 1 - Real.exp (-u) ≤ u := by linarith
  have h3 : Real.exp u - 1 = Real.exp u * (1 - Real.exp (-u)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [h3]
  calc Real.exp u * (1 - Real.exp (-u))
      ≤ Real.exp u * u := mul_le_mul_of_nonneg_left h2 (Real.exp_pos u).le
    _ ≤ Real.exp 1 * u := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu1) hu0

/-- Parameter bridge: `0 ≤ β ≤ highTempBetaWC r Jsite` discharges the Kotecký–Preiss
site bound, convergence inequality, causal-series threshold `hq`, `betaWC_concrete`,
and `β ≤ (8 e² r Jsite)⁻¹` simultaneously with `c = (2 r)⁻¹` and `η₀ = (2 e r)⁻¹`. -/
theorem highTempBetaWC_discharges_params {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite) :
    let c : ℝ := 1 / (2 * (r : ℝ))
    let η₀ : ℝ := 1 / (2 * Real.exp 1 * (r : ℝ))
    0 < c ∧
    (∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀) ∧
    η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c ∧
    (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * Jsite ≤ 1 / 2 ∧
    β ≤ betaWC_concrete r Jsite ∧
    β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) := by
  intro c η₀
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have he1_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have he2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h6r_ge36 : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h6r_pos : (0 : ℝ) < (6 : ℝ) ^ r := by positivity
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  have hkp : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c := by
    dsimp only [c, η₀]
    have h2cr : 2 * (1 / (2 * (r : ℝ))) * (r : ℝ) = 1 := by field_simp [hrpos.ne']
    rw [h2cr]
    have heq : 1 / (2 * Real.exp 1 * (r : ℝ)) * Real.exp 1 = 1 / (2 * (r : ℝ)) := by
      field_simp [he1_pos.ne', hrpos.ne']
    linarith
  have hβ_le_8e2 : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) := by
    refine le_trans hβ ?_
    unfold highTempBetaWC
    apply one_div_le_one_div_of_le (by positivity)
    have h2_le : (2 : ℝ) ≤ (6 : ℝ) ^ r := by linarith
    nlinarith [Real.exp_pos 2, mul_pos hrpos hJ]
  have hβ_le_wc : β ≤ betaWC_concrete r Jsite := by
    refine le_trans hβ_le_8e2 ?_
    unfold betaWC_concrete
    have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
    have hr1_le : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : r - 1 ≤ r)
    have he2_ge1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hβJ_le1 : (β / 2) * Jsite ≤ 1 := by
    have h1 : (β / 2) * Jsite ≤ (1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) / 2) * Jsite := by
      nlinarith
    have h2 : (1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) / 2) * Jsite = 1 / (16 * Real.exp 2 * (r : ℝ)) := by
      field_simp [hJ.ne', (Real.exp_pos 2).ne', hrpos.ne']; ring
    have he2_ge1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have h3 : 1 / (16 * Real.exp 2 * (r : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hsite_kp : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀ := by
    intro x
    have hterm : ∀ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤
          (6 : ℝ) ^ r * Real.exp 1 * (β / 2) * opNorm (h X) := by
      intro X hX
      have hXE : X ∈ E := (Finset.mem_filter.mp hX).1
      have hle_J : opNorm (h X) ≤ Jsite := le_trans
        (Finset.single_le_sum (fun Y _ ↦ opNorm_nonneg (h Y)) hX) (hsite x)
      have hu0 : 0 ≤ (β / 2) * opNorm (h X) := mul_nonneg (by linarith) (opNorm_nonneg _)
      have hu1 : (β / 2) * opNorm (h X) ≤ 1 := by nlinarith
      have hexp := exp_sub_one_le_e_mul hu0 hu1
      have h6_le : (6 : ℝ) ^ X.card ≤ (6 : ℝ) ^ r :=
        pow_le_pow_right₀ (by norm_num) (hcard X hXE)
      calc (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1)
          ≤ (6 : ℝ) ^ X.card * (Real.exp 1 * ((β / 2) * opNorm (h X))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ (6 : ℝ) ^ r * (Real.exp 1 * ((β / 2) * opNorm (h X))) :=
            mul_le_mul_of_nonneg_right h6_le (by positivity)
        _ = (6 : ℝ) ^ r * Real.exp 1 * (β / 2) * opNorm (h X) := by ring
    calc ∑ X ∈ E.filter (fun X ↦ x ∈ X),
          (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1)
        ≤ ∑ X ∈ E.filter (fun X ↦ x ∈ X),
          (6 : ℝ) ^ r * Real.exp 1 * (β / 2) * opNorm (h X) := Finset.sum_le_sum hterm
      _ = (6 : ℝ) ^ r * Real.exp 1 * (β / 2) *
          ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) := (Finset.mul_sum _ _ _).symm
      _ ≤ (6 : ℝ) ^ r * Real.exp 1 * (β / 2) * Jsite :=
          mul_le_mul_of_nonneg_left (hsite x) (by positivity)
      _ ≤ (6 : ℝ) ^ r * Real.exp 1 * (highTempBetaWC r Jsite / 2) * Jsite := by
          have : 0 ≤ (6 : ℝ) ^ r * Real.exp 1 := by positivity
          nlinarith
      _ = 1 / (8 * Real.exp 1 * (r : ℝ)) := by
          unfold highTempBetaWC; rw [he2_eq]
          field_simp [h6r_pos.ne', he1_pos.ne', hrpos.ne', hJ.ne']; ring
      _ ≤ η₀ := by
          dsimp only [η₀]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
  have hq : (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * Jsite ≤ 1 / 2 := by
    have hsqrt3_le6 : Real.sqrt 3 ≤ 6 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hpow_le : (Real.sqrt 3) ^ (r - 1) ≤ (6 : ℝ) ^ r := by
      calc (Real.sqrt 3) ^ (r - 1)
          ≤ (6 : ℝ) ^ (r - 1) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt3_le6 _
        _ ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)
    have he2_ge1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    calc (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * Jsite
        ≤ (highTempBetaWC r Jsite / 2) * (6 : ℝ) ^ r * (r : ℝ) * Jsite := by
          have h1 : (β / 2) * (Real.sqrt 3) ^ (r - 1) ≤ (highTempBetaWC r Jsite / 2) * (6 : ℝ) ^ r :=
            mul_le_mul (by linarith) hpow_le (pow_nonneg (Real.sqrt_nonneg _) _) (by linarith [highTempBetaWC_pos hr hJ])
          nlinarith [mul_pos hrpos hJ]
      _ = 1 / (8 * Real.exp 2) := by
          unfold highTempBetaWC
          field_simp [h6r_pos.ne', (Real.exp_pos 2).ne', hrpos.ne', hJ.ne']; ring
      _ ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num)
          linarith
  exact ⟨hc_pos, hsite_kp, hkp, hq, hβ_le_wc, hβ_le_8e2⟩

/-- **Lemma 7.2 (Unconditional High-Temperature Positive Dual Frame)**:
Parameterized solely by `2 ≤ r`, `0 < Jsite`, local site norm bound, and `0 ≤ β ≤ highTempBetaWC r Jsite`. -/
theorem lemma_7_2_high_temp {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite) :
    ∃ π : (Fin N → Fin 6) → ℝ, (∀ s, 0 < π s) ∧
      gibbsRhoHalf hH β = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s := by
  rcases highTempBetaWC_discharges_params hr E hcard h hJ hsite hβ0 hβ with
    ⟨hc, hsite_kp, hkp, _, _, _⟩
  exact lemma_7_2_concrete_positive_frame E hne hcard h hsupp hH hβ0 hc hsite_kp hkp

/-- **Theorem 1.3(a) (Unconditional High-Temperature Reverse Poincaré Inequality)**:
Parameterized solely by `2 ≤ r`, `0 < Jsite`, local site norm bound, and `0 ≤ β ≤ highTempBetaWC r Jsite`. -/
theorem theorem_1_3a_high_temp {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      9 * (gibbsWightmanInner G A (wightmanQ G A)).re := by
  rcases highTempBetaWC_discharges_params hr E hcard h hJ hsite hβ0 hβ with
    ⟨hc, hsite_kp, hkp, _, _, _⟩
  exact theorem_1_3a_unconditional E hne hcard h hsupp hH hβ0 hc hsite_kp hkp A

/-- **Theorem 1.3(b) (Unconditional High-Temperature OTOC–Krylov Bound, Eq. 1.22)**:
Proves both `otocCW ≤ 54 * ((r - 1) K_β^W(t) + s₀)` and `otocI ≤ 216 * ((r - 1) K_β^W(t) + s₀)`
parameterized solely by `2 ≤ r`, `0 < Jsite`, local site norm bound, and `0 ≤ β ≤ highTempBetaWC r Jsite`. -/
theorem theorem_1_3b_high_temp {N r s₀ : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    {O : QubitOp N} (hO : O.IsHermitian)
    (hHf : (∑ X ∈ E, h X) ∈ filtrationSubmodule N r)
    (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (t : ℝ) :
    let G := concreteGibbsData hH β
    otocCW G (heisenbergEvol hH (t : ℂ) O) ≤
      54 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) ∧
    otocI hH β (heisenbergEvol hH (t : ℂ) O) ≤
      216 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) := by
  rcases highTempBetaWC_discharges_params hr E hcard h hJ hsite hβ0 hβ with
    ⟨hc, hsite_kp, hkp, hq, hβ_wc, _⟩
  exact theorem_1_3b_concrete_exact_54_216 hr E hne hcard h hsupp hH hβ0 hc hJ
    hsite_kp hkp hsite hβ_wc hq hO hHf hOf hOnorm t

end KrylovChaos
