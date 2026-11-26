/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.HighTempConditioning
import KrylovChaos.OperatorGlauberAndLanczosFiltration
import KrylovChaos.KrylovTail
import KrylovChaos.Filtration
import Mathlib.Tactic

/-!
# Concrete Operator-Level Prop. 4.1, Lemma 4.2, Theorem 1.1(b) & Exact Infinite-Chain Constant (Flaws #5 & #12)

1. **Flaw #12 (`theorem_1_1a_infinite_exact_constant`)**:
   Specializes the infinite-chain MGF/complexity bound at `θ₀ = 4` to derive the explicit
   closed-form prefactor `C_{1,α,γ} = exp(2 + 4 γ / α) / (4 e tanh 1)` directly from
   `theorem_1_1a_infinite_tail_and_complexity`.
2. **Flaw #5 (Concrete Operator-Level Prop. 4.1, Lemma 4.2 & Theorem 1.1(b) on `QubitOp N`)**:
   - `prop_4_1_concrete_operator`: for EVERY `G : GibbsData N` and EVERY `A ∈ filtrationSubmodule N s`,
     `Re (A | 𝒬^{(β)} A)_β^W ≤ (s : ℝ) * gibbsWightmanNormSq G A`.
   - `wightmanQ_le_N_normSq`: for EVERY `G : GibbsData N` and EVERY `A : QubitOp N`,
     `Re (A | 𝒬^{(β)} A)_β^W ≤ (N : ℝ) * gibbsWightmanNormSq G A`.
   - `wightmanQ_add_bound`: exact operator-level quadratic split bound on `QubitOp N`:
     `Re ((A + R) | 𝒬^{(β)} (A + R))_β^W ≤ Q(A) + 2 √(Q(A)) √(Q(R)) + Q(R)`.
   - `lemma_4_2_concrete_operator`: combines `lanczosTrunc_mem_filtration`, `prop_4_1_concrete_operator`,
     `wightmanQ_le_N_normSq`, and `wightmanQ_add_bound` directly on `heisenbergEvol hH t O = A_M(t) + R_M(t)`
     with zero scalar-wrapper hypotheses!
-/

namespace KrylovChaos

open Matrix

section Flaw12ExactConstant

/-- **Flaw #12 (Explicit Infinite-Chain Prefactor for Theorem 1.1(a), Eq. 1.13)**:
Specializing `theorem_1_1a_infinite_tail_and_complexity` at `θ₀ = 4` yields the explicit
closed-form complexity bound `∑' n, n (φ n t)² ≤ (exp(2 + 4 γ / α) / (4 e tanh 1)) * exp(2 α t)`
and exponential tail bound `∑' m, (φ (n + m) t)² ≤ exp(2 + 4 γ / α) * exp(-4 tanh 1 * n * exp(-2 α t))`. -/
theorem theorem_1_1a_infinite_exact_constant {α γ : ℝ}
    (φ : ℕ → ℝ → ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t)
    (hfatou : ∀ M : ℕ, ∑ m ∈ Finset.range M,
      Real.exp (charTheta α 4 t * (m : ℝ)) * (φ m t) ^ 2 ≤
      Real.exp (2 + 4 * γ / α)) :
    (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
      Real.exp (2 + 4 * γ / α) *
        Real.exp (-4 * Real.tanh 1 * (n : ℝ) * Real.exp (-2 * α * t))) ∧
    (∑' n : ℕ, (n : ℝ) * (φ n t) ^ 2 ≤
      (Real.exp (2 + 4 * γ / α) / (4 * Real.exp 1 * Real.tanh 1)) *
        Real.exp (2 * α * t)) := by
  have h1 : (1 / 2 + γ / α) * (4 : ℝ) = 2 + 4 * γ / α := by ring
  have h4 : (4 : ℝ) / 4 = 1 := by norm_num
  have hmain := theorem_1_1a_infinite_tail_and_complexity φ hα hγ (by norm_num : (0 : ℝ) < 4) t ht
    (fun M ↦ by rw [h1]; exact hfatou M)
  rw [h1, h4] at hmain
  exact hmain

end Flaw12ExactConstant

section ConcreteOperatorFiltrationAndTruncation

lemma wightmanDistSq_nonneg {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) :
    0 ≤ wightmanDistSq G S A := by
  unfold wightmanDistSq
  apply Real.sInf_nonneg
  rintro r ⟨B, _, rfl⟩
  unfold gibbsWightmanNormSq gibbsWightmanInner
  rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
  exact hsNormSq_nonneg _

lemma wightmanDistSq_eq_zero_of_mem {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) {A : QubitOp N} (hA : A ∈ S) :
    wightmanDistSq G S A = 0 := by
  apply le_antisymm _ (wightmanDistSq_nonneg G S A)
  unfold wightmanDistSq
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨B, _, rfl⟩
    unfold gibbsWightmanNormSq gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
    exact hsNormSq_nonneg _
  · refine ⟨A, hA, ?_⟩
    simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]

lemma wightmanDistSq_le_normSq {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) :
    wightmanDistSq G S A ≤ gibbsWightmanNormSq G A := by
  unfold wightmanDistSq
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨B, _, rfl⟩
    unfold gibbsWightmanNormSq gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
    exact hsNormSq_nonneg _
  · exact ⟨0, Submodule.zero_mem S, by simp⟩

lemma wightmanQ_eq_sum_distSq {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    (gibbsWightmanInner G A (wightmanQ G A)).re =
      ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A := by
  unfold wightmanQ
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  unfold gibbsWightmanInner wightmanInner
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro k _
  exact wightmanSubspaceProj_eq_distSq G (filtrationSubmodule N k) A

/-- **Concrete Operator-Level Proposition 4.1 on `QubitOp N` (Flaw #5)**:
For EVERY `G : GibbsData N` and EVERY `A ∈ filtrationSubmodule N s`,
`Re (A | 𝒬^{(β)} A)_β^W ≤ (s : ℝ) * ‖A‖_{β,W}²`. -/
theorem prop_4_1_concrete_operator {N s : ℕ} (G : GibbsData N) {A : QubitOp N}
    (hA : A ∈ filtrationSubmodule N s) :
    (gibbsWightmanInner G A (wightmanQ G A)).re ≤ (s : ℝ) * gibbsWightmanNormSq G A := by
  rw [wightmanQ_eq_sum_distSq]
  have hterm : ∀ k ∈ Finset.range N,
      wightmanDistSq G (filtrationSubmodule N k) A ≤
        if k < s then gibbsWightmanNormSq G A else 0 := by
    intro k _
    by_cases hks : k < s
    · rw [if_pos hks]; exact wightmanDistSq_le_normSq G _ A
    · rw [if_neg hks]
      have hmem : A ∈ filtrationSubmodule N k :=
        filtrationSubmodule_mono N (by omega) hA
      rw [wightmanDistSq_eq_zero_of_mem G _ hmem]
  have hnorm_nn : 0 ≤ gibbsWightmanNormSq G A := by
    unfold gibbsWightmanNormSq gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
    exact hsNormSq_nonneg _
  calc ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A
      ≤ ∑ k ∈ Finset.range N, if k < s then gibbsWightmanNormSq G A else 0 :=
        Finset.sum_le_sum hterm
    _ = (((Finset.range N).filter (fun k ↦ k < s)).card : ℝ) * gibbsWightmanNormSq G A := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s : ℝ) * gibbsWightmanNormSq G A := by
        apply mul_le_mul_of_nonneg_right _ hnorm_nn
        have hsub : (Finset.range N).filter (fun k ↦ k < s) ⊆ Finset.range s := by
          intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2
        have hcard : ((Finset.range N).filter (fun k ↦ k < s)).card ≤ s := by
          calc ((Finset.range N).filter (fun k ↦ k < s)).card
              ≤ (Finset.range s).card := Finset.card_le_card hsub
            _ = s := Finset.card_range s
        exact_mod_cast hcard

/-- **Global Operator Norm Bound `𝒬^{(β)} ≤ N · 1` on `QubitOp N`**:
For EVERY `G : GibbsData N` and EVERY `A : QubitOp N`:
`Re (A | 𝒬^{(β)} A)_β^W ≤ (N : ℝ) * ‖A‖_{β,W}²`. -/
theorem wightmanQ_le_N_normSq {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    (gibbsWightmanInner G A (wightmanQ G A)).re ≤ (N : ℝ) * gibbsWightmanNormSq G A := by
  rw [wightmanQ_eq_sum_distSq]
  calc ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A
      ≤ ∑ _k ∈ Finset.range N, gibbsWightmanNormSq G A :=
        Finset.sum_le_sum fun k _ ↦ wightmanDistSq_le_normSq G _ A
    _ = (N : ℝ) * gibbsWightmanNormSq G A := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Exact triangle inequality for `√(wightmanDistSq G S (A + R))` on `QubitOp N`. -/
private lemma sqrt_wightmanDistSq_add_le {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A R : QubitOp N) :
    Real.sqrt (wightmanDistSq G S (A + R)) ≤
      Real.sqrt (wightmanDistSq G S A) + Real.sqrt (wightmanDistSq G S R) := by
  have hnorm_add : ∀ X Y : QubitOp N,
      Real.sqrt (gibbsWightmanNormSq G (X + Y)) ≤
        Real.sqrt (gibbsWightmanNormSq G X) + Real.sqrt (gibbsWightmanNormSq G Y) := by
    intro X Y
    have hnorm_eq : ∀ Z : QubitOp N,
        Real.sqrt (gibbsWightmanNormSq G Z) = ‖qubitOpToHS N (jBeta G.ρQuarter Z)‖ := by
      intro Z
      unfold gibbsWightmanNormSq gibbsWightmanInner
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
      have h1 : (hsInner (jBeta G.ρQuarter Z) (jBeta G.ρQuarter Z)).re =
          ‖qubitOpToHS N (jBeta G.ρQuarter Z)‖ ^ 2 := by
        rw [← qubitOpToHS_inner, inner_self_eq_norm_sq_to_K]
        change ((‖qubitOpToHS N (jBeta G.ρQuarter Z)‖ : ℂ) ^ 2).re = _
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      change Real.sqrt (hsInner (jBeta G.ρQuarter Z) (jBeta G.ρQuarter Z)).re = _
      rw [h1, Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm_eq, hnorm_eq, hnorm_eq]
    have hj_add : jBeta G.ρQuarter (X + Y) = jBeta G.ρQuarter X + jBeta G.ρQuarter Y := by
      unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
    rw [hj_add, map_add]
    exact norm_add_le _ _
  have hpair : ∀ B₁ ∈ S, ∀ B₂ ∈ S,
      Real.sqrt (wightmanDistSq G S (A + R)) ≤
        Real.sqrt (gibbsWightmanNormSq G (A - B₁)) + Real.sqrt (gibbsWightmanNormSq G (R - B₂)) := by
    intro B₁ hB₁ B₂ hB₂
    have hle : wightmanDistSq G S (A + R) ≤ gibbsWightmanNormSq G ((A + R) - (B₁ + B₂)) := by
      unfold wightmanDistSq
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨B, _, rfl⟩
        unfold gibbsWightmanNormSq gibbsWightmanInner
        rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
        exact hsNormSq_nonneg _
      · exact ⟨B₁ + B₂, Submodule.add_mem S hB₁ hB₂, rfl⟩
    have hrew : (A + R) - (B₁ + B₂) = (A - B₁) + (R - B₂) := by abel
    rw [hrew] at hle
    exact le_trans (Real.sqrt_le_sqrt hle) (hnorm_add (A - B₁) (R - B₂))
  have hstep1 : ∀ B₂ ∈ S,
      Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (gibbsWightmanNormSq G (R - B₂)) ≤
        Real.sqrt (wightmanDistSq G S A) := by
    intro B₂ hB₂
    by_cases hneg : Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (gibbsWightmanNormSq G (R - B₂)) ≤ 0
    · exact le_trans hneg (Real.sqrt_nonneg _)
    · push Not at hneg
      have hsq : (Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (gibbsWightmanNormSq G (R - B₂))) ^ 2 ≤
          wightmanDistSq G S A := by
        unfold wightmanDistSq
        apply le_csInf
        · exact ⟨_, 0, Submodule.zero_mem S, rfl⟩
        · rintro r ⟨B₁, hB₁, rfl⟩
          have h1 : Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (gibbsWightmanNormSq G (R - B₂)) ≤
              Real.sqrt (gibbsWightmanNormSq G (A - B₁)) := by linarith [hpair B₁ hB₁ B₂ hB₂]
          have hnn : 0 ≤ gibbsWightmanNormSq G (A - B₁) := by
            unfold gibbsWightmanNormSq gibbsWightmanInner
            rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
            exact hsNormSq_nonneg _
          calc (Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (gibbsWightmanNormSq G (R - B₂))) ^ 2
              ≤ (Real.sqrt (gibbsWightmanNormSq G (A - B₁))) ^ 2 := pow_le_pow_left₀ hneg.le h1 2
            _ = gibbsWightmanNormSq G (A - B₁) := Real.sq_sqrt hnn
      exact (Real.le_sqrt hneg.le (wightmanDistSq_nonneg G S A)).mpr hsq
  by_cases hneg2 : Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (wightmanDistSq G S A) ≤ 0
  · linarith [Real.sqrt_nonneg (wightmanDistSq G S R)]
  · push Not at hneg2
    have hsq2 : (Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (wightmanDistSq G S A)) ^ 2 ≤
        wightmanDistSq G S R := by
      unfold wightmanDistSq
      apply le_csInf
      · exact ⟨_, 0, Submodule.zero_mem S, rfl⟩
      · rintro r ⟨B₂, hB₂, rfl⟩
        have h1 : Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (wightmanDistSq G S A) ≤
            Real.sqrt (gibbsWightmanNormSq G (R - B₂)) := by linarith [hstep1 B₂ hB₂]
        have hnn : 0 ≤ gibbsWightmanNormSq G (R - B₂) := by
          unfold gibbsWightmanNormSq gibbsWightmanInner
          rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
          exact hsNormSq_nonneg _
        calc (Real.sqrt (wightmanDistSq G S (A + R)) - Real.sqrt (wightmanDistSq G S A)) ^ 2
            ≤ (Real.sqrt (gibbsWightmanNormSq G (R - B₂))) ^ 2 := pow_le_pow_left₀ hneg2.le h1 2
          _ = gibbsWightmanNormSq G (R - B₂) := Real.sq_sqrt hnn
    have hfin := (Real.le_sqrt hneg2.le (wightmanDistSq_nonneg G S R)).mpr hsq2
    linarith

/-- **Exact Operator-Level Quadratic Split Bound for `𝒬^{(β)}` on `QubitOp N`**:
For EVERY `G : GibbsData N` and EVERY `A, R : QubitOp N`:
`Re ((A + R) | 𝒬^{(β)} (A + R))_β^W ≤ Q(A) + 2 √(Q(A)) √(Q(R)) + Q(R)`. -/
theorem wightmanQ_add_bound {N : ℕ} (G : GibbsData N) (A R : QubitOp N) :
    (gibbsWightmanInner G (A + R) (wightmanQ G (A + R))).re ≤
      (gibbsWightmanInner G A (wightmanQ G A)).re +
      2 * Real.sqrt (gibbsWightmanInner G A (wightmanQ G A)).re *
          Real.sqrt (gibbsWightmanInner G R (wightmanQ G R)).re +
      (gibbsWightmanInner G R (wightmanQ G R)).re := by
  rw [wightmanQ_eq_sum_distSq, wightmanQ_eq_sum_distSq, wightmanQ_eq_sum_distSq]
  have hterm : ∀ k ∈ Finset.range N,
      wightmanDistSq G (filtrationSubmodule N k) (A + R) ≤
        wightmanDistSq G (filtrationSubmodule N k) A +
        2 * (Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
             Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R)) +
        wightmanDistSq G (filtrationSubmodule N k) R := by
    intro k _
    have htri := sqrt_wightmanDistSq_add_le G (filtrationSubmodule N k) A R
    have hnnAR := wightmanDistSq_nonneg G (filtrationSubmodule N k) (A + R)
    have hnnA := wightmanDistSq_nonneg G (filtrationSubmodule N k) A
    have hnnR := wightmanDistSq_nonneg G (filtrationSubmodule N k) R
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) htri 2
    rw [Real.sq_sqrt hnnAR] at hsq
    have hexp : (Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) +
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R)) ^ 2 =
        wightmanDistSq G (filtrationSubmodule N k) A +
        2 * (Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
             Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R)) +
        wightmanDistSq G (filtrationSubmodule N k) R := by
      ring_nf; rw [Real.sq_sqrt hnnA, Real.sq_sqrt hnnR]
    linarith
  have hcs : ∑ k ∈ Finset.range N,
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R) ≤
      Real.sqrt (∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A) *
      Real.sqrt (∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) R) := by
    have hsq_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun k ↦ Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A))
      (fun k ↦ Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R))
    have hA_sq : ∑ k ∈ Finset.range N,
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) ^ 2 =
        ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A :=
      Finset.sum_congr rfl fun k _ ↦ Real.sq_sqrt (wightmanDistSq_nonneg G _ A)
    have hR_sq : ∑ k ∈ Finset.range N,
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R) ^ 2 =
        ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) R :=
      Finset.sum_congr rfl fun k _ ↦ Real.sq_sqrt (wightmanDistSq_nonneg G _ R)
    rw [hA_sq, hR_sq] at hsq_cs
    have hnn_sumA : 0 ≤ ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A :=
      Finset.sum_nonneg fun k _ ↦ wightmanDistSq_nonneg G _ A
    have hnn_sumR : 0 ≤ ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) R :=
      Finset.sum_nonneg fun k _ ↦ wightmanDistSq_nonneg G _ R
    have hnn_lhs : 0 ≤ ∑ k ∈ Finset.range N,
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
        Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R) :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_mul hnn_sumA]
    exact (Real.le_sqrt hnn_lhs (mul_nonneg hnn_sumA hnn_sumR)).mpr hsq_cs
  calc ∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) (A + R)
      ≤ ∑ k ∈ Finset.range N,
          (wightmanDistSq G (filtrationSubmodule N k) A +
           2 * (Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
                Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R)) +
           wightmanDistSq G (filtrationSubmodule N k) R) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) A) +
        2 * (∑ k ∈ Finset.range N,
              Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) A) *
              Real.sqrt (wightmanDistSq G (filtrationSubmodule N k) R)) +
        (∑ k ∈ Finset.range N, wightmanDistSq G (filtrationSubmodule N k) R) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

/-- **Concrete Operator-Level Lemma 4.2 (Lanczos Truncation Filtration Bound on `QubitOp N`, Flaw #5)**:
For ANY Hermitian `H ∈ filtrationSubmodule N r` (`1 ≤ r`), `O ∈ filtrationSubmodule N s₀`,
`β : ℝ`, `t : ℝ`, and `M ≥ 1`, letting `G := concreteGibbsData hH β`,
`A_M := lanczosTrunc hH β O M t`, and `R_M := heisenbergEvol hH t O - A_M`,
the Wightman filtration expectation satisfies:
`Re (O(t) | 𝒬^{(β)} O(t))_β^W ≤ s_M * ‖A_M‖_{β,W}² + 2 * √(s_M * ‖A_M‖_{β,W}²) * √(N * ‖R_M‖_{β,W}²) + N * ‖R_M‖_{β,W}²`
where `s_M = s₀ + (M - 1) * (r - 1)`. Zero scalar-wrapper hypotheses! -/
theorem lemma_4_2_concrete_operator {N r s₀ M : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp N} (hH : H.IsHermitian) (β t : ℝ)
    (hHf : H ∈ filtrationSubmodule N r) (hOf : O ∈ filtrationSubmodule N s₀) :
    let G := concreteGibbsData hH β
    let A_M := lanczosTrunc hH β O M t
    let R_M := heisenbergEvol hH t O - A_M
    let s_M : ℕ := s₀ + (M - 1) * (r - 1)
    (gibbsWightmanInner G (heisenbergEvol hH t O) (wightmanQ G (heisenbergEvol hH t O))).re ≤
      (s_M : ℝ) * gibbsWightmanNormSq G A_M +
      2 * Real.sqrt ((s_M : ℝ) * gibbsWightmanNormSq G A_M) *
          Real.sqrt ((N : ℝ) * gibbsWightmanNormSq G R_M) +
      (N : ℝ) * gibbsWightmanNormSq G R_M := by
  intro G A_M R_M s_M
  have hsplit : heisenbergEvol hH t O = A_M + R_M := by simp [R_M]
  have hmem : A_M ∈ filtrationSubmodule N s_M :=
    lanczosTrunc_mem_filtration hr hM hH β t hHf hOf
  have hQA : (gibbsWightmanInner G A_M (wightmanQ G A_M)).re ≤
      (s_M : ℝ) * gibbsWightmanNormSq G A_M :=
    prop_4_1_concrete_operator G hmem
  have hQR : (gibbsWightmanInner G R_M (wightmanQ G R_M)).re ≤
      (N : ℝ) * gibbsWightmanNormSq G R_M :=
    wightmanQ_le_N_normSq G R_M
  have hsqrtA : Real.sqrt (gibbsWightmanInner G A_M (wightmanQ G A_M)).re ≤
      Real.sqrt ((s_M : ℝ) * gibbsWightmanNormSq G A_M) := Real.sqrt_le_sqrt hQA
  have hsqrtR : Real.sqrt (gibbsWightmanInner G R_M (wightmanQ G R_M)).re ≤
      Real.sqrt ((N : ℝ) * gibbsWightmanNormSq G R_M) := Real.sqrt_le_sqrt hQR
  have hprod : Real.sqrt (gibbsWightmanInner G A_M (wightmanQ G A_M)).re *
        Real.sqrt (gibbsWightmanInner G R_M (wightmanQ G R_M)).re ≤
      Real.sqrt ((s_M : ℝ) * gibbsWightmanNormSq G A_M) *
        Real.sqrt ((N : ℝ) * gibbsWightmanNormSq G R_M) :=
    mul_le_mul hsqrtA hsqrtR (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hadd := wightmanQ_add_bound G A_M R_M
  rw [← hsplit] at hadd
  linarith

end ConcreteOperatorFiltrationAndTruncation

end KrylovChaos
