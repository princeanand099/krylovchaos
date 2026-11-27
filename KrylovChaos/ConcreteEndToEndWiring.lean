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
import KrylovChaos.WightmanProjectors
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Concrete Operator-Level Prop. 4.1, Lemma 4.2, Concrete Lanczos ODE & Exact Infinite-Chain Constant

1. **Flaw #12 (`theorem_1_1a_infinite_exact_constant`)**:
   Specializes the infinite-chain MGF/complexity bound at `θ₀ = 4` to derive the explicit
   closed-form prefactor `C_{1,α,γ} = exp(2 + 4 γ / α) / (4 e tanh 1)` directly from
   `theorem_1_1a_infinite_tail_and_complexity`.
2. **Concrete Operator-Level Lanczos Orthonormality, Parity, Completeness & ODE (Item #2)**:
   - `lanczosOp_parity`: `(𝒪_n^{(β)})ᴴ = (-1)^n 𝒪_n^{(β)}` for all `n`.
   - `lanczosOp_orthonormal_all`: `(𝒪_m^{(β)} | 𝒪_n^{(β)})_β^W = δ_{mn}` for all nonzero `𝒪_n^{(β)}`.
   - `concreteKrylovWavefn_im_eq_zero`, `concreteKrylovWavefn_zero`, `concreteKrylovWavefn_sum_sq_eq_one`,
     and `concreteKrylovWavefn_hasDerivAt` (exact Eq. 2.7 ODE `∂_t φ_n = b_n φ_{n-1} - b_{n+1} φ_{n+1}`).
3. **Genuine Concrete Proposition 4.1(2) on `QubitOp N` (Item #3, Eq. 4.2)**:
   - `prop_4_1_part2_concrete_operator`: `Re (𝒪(t) | 𝒬^{(β)} 𝒪(t))_β^W ≤ (r - 1) K_β^W(t) + s₀`.
4. **Genuine Concrete Lemma 4.2 on `mssThermalSize` & `lambdaMSS` (Item #4, Eq. 4.3)**:
   - `mssThermalSize_one`, `lambdaMSS_nonneg`, `mssThermalSize_le_lambdaMSS_of_mem`, and
     `lemma_4_2_mss_thermal_size_concrete`:
     `mssThermalSize G 𝒪(t) ≤ lambdaMSS G s_M + 2 N ε_M + N ε_M²` with zero laundered hypotheses.
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
    (by simpa [h1] using hfatou)
  simpa [h1, h4] using hmain

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

/-- Static filtration bound on `QubitOp N`:
for EVERY `G : GibbsData N` and EVERY `A ∈ filtrationSubmodule N s`,
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
        filtrationSubmodule_mono (by omega) hA
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
        simp
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
    · push_neg at hneg
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
  · push_neg at hneg2
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
      ring_nf; rw [Real.sq_sqrt hnnA, Real.sq_sqrt hnnR]; ring
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

/-- Lanczos truncation bound for `𝒬^{(β)}` on `QubitOp N`. -/
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

section ConcreteLanczosPropertiesAndODE

private lemma gibbsRhoHalf_comm_H {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    H * (concreteGibbsData hH β).ρHalf = (concreteGibbsData hH β).ρHalf * H := by
  have hq := concreteGibbsData_comm_H hH β
  rw [← (concreteGibbsData hH β).sq_quarter]
  calc H * ((concreteGibbsData hH β).ρQuarter * (concreteGibbsData hH β).ρQuarter)
      = (H * (concreteGibbsData hH β).ρQuarter) * (concreteGibbsData hH β).ρQuarter := by
        simp only [Matrix.mul_assoc]
    _ = ((concreteGibbsData hH β).ρQuarter * H) * (concreteGibbsData hH β).ρQuarter := by rw [hq]
    _ = (concreteGibbsData hH β).ρQuarter * (H * (concreteGibbsData hH β).ρQuarter) := by
        simp only [Matrix.mul_assoc]
    _ = (concreteGibbsData hH β).ρQuarter * ((concreteGibbsData hH β).ρQuarter * H) := by rw [hq]
    _ = ((concreteGibbsData hH β).ρQuarter * (concreteGibbsData hH β).ρQuarter) * H := by
        simp only [Matrix.mul_assoc]

lemma gibbsWightmanInner_conj_symm {N : ℕ} (G : GibbsData N) (A B : QubitOp N) :
    star (gibbsWightmanInner G A B) = gibbsWightmanInner G B A := by
  unfold gibbsWightmanInner wightmanInner
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, G.ρHalf_herm]
  calc Matrix.trace (Bᴴ * G.ρHalf * A * G.ρHalf)
      = Matrix.trace (G.ρHalf * (Bᴴ * G.ρHalf * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (G.ρHalf * Bᴴ * G.ρHalf * A) := by simp only [Matrix.mul_assoc]

/-- Self-adjointness of the Liouvillian `ad_H = [H, ·]` in the Wightman inner product. -/
theorem gibbsWightmanInner_matComm_selfAdjoint {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A B : QubitOp N) :
    gibbsWightmanInner (concreteGibbsData hH β) (matComm H A) B =
      gibbsWightmanInner (concreteGibbsData hH β) A (matComm H B) := by
  set G := concreteGibbsData hH β
  have hcomm := gibbsRhoHalf_comm_H hH β
  unfold gibbsWightmanInner wightmanInner matComm
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  have h1 : Matrix.trace (G.ρHalf * (Aᴴ * H) * G.ρHalf * B) =
      Matrix.trace (G.ρHalf * Aᴴ * G.ρHalf * (H * B)) := by
    calc Matrix.trace (G.ρHalf * (Aᴴ * H) * G.ρHalf * B)
        = Matrix.trace (G.ρHalf * Aᴴ * (H * G.ρHalf) * B) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (G.ρHalf * Aᴴ * (G.ρHalf * H) * B) := by rw [hcomm]
      _ = Matrix.trace (G.ρHalf * Aᴴ * G.ρHalf * (H * B)) := by simp only [Matrix.mul_assoc]
  have h2 : Matrix.trace (G.ρHalf * (H * Aᴴ) * G.ρHalf * B) =
      Matrix.trace (G.ρHalf * Aᴴ * G.ρHalf * (B * H)) := by
    calc Matrix.trace (G.ρHalf * (H * Aᴴ) * G.ρHalf * B)
        = Matrix.trace ((G.ρHalf * H) * (Aᴴ * G.ρHalf * B)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((H * G.ρHalf) * (Aᴴ * G.ρHalf * B)) := by rw [← hcomm]
      _ = Matrix.trace (H * (G.ρHalf * Aᴴ * G.ρHalf * B)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G.ρHalf * Aᴴ * G.ρHalf * B) * H) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G.ρHalf * Aᴴ * G.ρHalf * (B * H)) := by simp only [Matrix.mul_assoc]
  rw [h1, h2]

/-- Parity symmetry of the Wightman inner product: if `Aᴴ = ε • A` and `Bᴴ = B`, then
`star (A | B)_β^W = ε * (A | B)_β^W`. -/
lemma gibbsWightmanInner_parity_symm {N : ℕ} (G : GibbsData N) {A B : QubitOp N} {ε : ℂ}
    (hA : Aᴴ = ε • A) (hB : Bᴴ = B) (hε2 : ε * ε = 1) :
    star (gibbsWightmanInner G A B) = ε * gibbsWightmanInner G A B := by
  rw [gibbsWightmanInner_conj_symm]
  unfold gibbsWightmanInner wightmanInner
  rw [hB, hA]
  calc Matrix.trace (G.ρHalf * B * G.ρHalf * A)
      = Matrix.trace ((G.ρHalf * B) * (G.ρHalf * A)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((G.ρHalf * A) * (G.ρHalf * B)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (G.ρHalf * A * G.ρHalf * B) := by simp only [Matrix.mul_assoc]
    _ = (ε * ε) * Matrix.trace (G.ρHalf * A * G.ρHalf * B) := by rw [hε2, one_mul]
    _ = ε * Matrix.trace (G.ρHalf * (ε • A) * G.ρHalf * B) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring

/-- Zero diagonal of `ad_H = [H, ·]` on any definite-parity operator `Aᴴ = ε • A`. -/
theorem gibbsWightmanInner_matComm_diag_zero_of_parity {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) {A : QubitOp N} {ε : ℂ} (hA : Aᴴ = ε • A) :
    gibbsWightmanInner (concreteGibbsData hH β) A (matComm H A) = 0 := by
  set G := concreteGibbsData hH β
  have hcomm := gibbsRhoHalf_comm_H hH β
  unfold gibbsWightmanInner wightmanInner matComm
  rw [Matrix.mul_sub, Matrix.trace_sub, hA]
  have heq : Matrix.trace (G.ρHalf * (ε • A) * G.ρHalf * (H * A)) =
      Matrix.trace (G.ρHalf * (ε • A) * G.ρHalf * (A * H)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    calc Matrix.trace (G.ρHalf * A * G.ρHalf * (H * A))
        = Matrix.trace ((G.ρHalf * A) * ((G.ρHalf * H) * A)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G.ρHalf * A) * ((H * G.ρHalf) * A)) := by rw [← hcomm]
      _ = Matrix.trace ((G.ρHalf * A * H) * (G.ρHalf * A)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G.ρHalf * A) * (G.ρHalf * A * H)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G.ρHalf * A * G.ρHalf * (A * H)) := by simp only [Matrix.mul_assoc]
  rw [heq, sub_self]

/-- Zero Wightman norm squared implies the operator is zero. -/
lemma eq_zero_of_gibbsWightmanNormSq_eq_zero {N : ℕ} (G : GibbsData N) {A : QubitOp N}
    (h0 : gibbsWightmanNormSq G A = 0) : A = 0 := by
  have hhs : hsNormSq (jBeta G.ρQuarter A) = 0 := by
    unfold gibbsWightmanNormSq gibbsWightmanInner at h0
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at h0
    exact h0
  have hv0 : ‖qubitOpToHS N (jBeta G.ρQuarter A)‖ = 0 := by
    have h1 : ‖qubitOpToHS N (jBeta G.ρQuarter A)‖ ^ 2 = hsNormSq (jBeta G.ρQuarter A) := by
      unfold hsNormSq; rw [← qubitOpToHS_inner, inner_self_eq_norm_sq_to_K]
      simp [RCLike.re_to_complex]
    rw [hhs] at h1
    exact sq_eq_zero_iff.mp h1
  have hj0 : jBeta G.ρQuarter A = 0 := (qubitOpToHS N).map_eq_zero_iff.mp (norm_eq_zero.mp hv0)
  have hinv : jBeta G.ρQuarterInv (jBeta G.ρQuarter A) = A := by
    unfold jBeta
    calc G.ρQuarterInv * (G.ρQuarter * A * G.ρQuarter) * G.ρQuarterInv
        = (G.ρQuarterInv * G.ρQuarter) * A * (G.ρQuarter * G.ρQuarterInv) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [G.inv_left, G.inv_right, Matrix.one_mul, Matrix.mul_one]
  rw [← hinv, hj0]; unfold jBeta; simp

lemma gibbsWightmanNormSq_nonneg {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    0 ≤ gibbsWightmanNormSq G A := by
  unfold gibbsWightmanNormSq gibbsWightmanInner
  rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
  exact hsNormSq_nonneg _

lemma lanczos_stays_zero {N : ℕ} (G : GibbsData N) (H O : QubitOp N) :
    ∀ k : ℕ, lanczosOp G H O k = 0 → lanczosCoeff G H O k = 0 →
      ∀ j : ℕ, lanczosOp G H O (k + j) = 0 ∧ lanczosCoeff G H O (k + j) = 0 := by
  intro k hOk hbk j
  induction j with
  | zero => exact ⟨hOk, hbk⟩
  | succ j ih =>
    rcases ih with ⟨hO, hb⟩
    have hAnext : matComm H (lanczosOp G H O (k + j)) -
        ((lanczosCoeff G H O (k + j) : ℝ) : ℂ) • (lanczosState G H O (k + j)).2.1 = 0 := by
      rw [hO, hb]; unfold matComm; simp
    have hbnext : lanczosCoeff G H O (k + j + 1) = 0 := by
      change Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosOp G H O (k + j)) -
        ((lanczosCoeff G H O (k + j) : ℝ) : ℂ) • (lanczosState G H O (k + j)).2.1)) = 0
      rw [hAnext]
      simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
    have hOnext : lanczosOp G H O (k + j + 1) = 0 := by
      unfold lanczosOp
      simp only [lanczosState]
      have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O (k + j)).1 -
          ((lanczosState G H O (k + j)).2.2 : ℂ) • (lanczosState G H O (k + j)).2.1)) = 0 := hbnext
      rw [if_pos hb']
    exact ⟨hOnext, hbnext⟩

lemma lanczosOp_eq_zero_of_coeff_zero {N : ℕ} (G : GibbsData N) (H O : QubitOp N)
    {n : ℕ} (hb : lanczosCoeff G H O (n + 1) = 0) :
    lanczosOp G H O (n + 1) = 0 := by
  unfold lanczosOp
  simp only [lanczosState]
  have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O n).1 -
      ((lanczosState G H O n).2.2 : ℂ) • (lanczosState G H O n).2.1)) = 0 := hb
  rw [if_pos hb']

/-- **Exact Parity of Concrete Lanczos Basis Operators**:
`(𝒪_n^{(β)})ᴴ = (-1)^n 𝒪_n^{(β)}` for every `n : ℕ` (completing Prop. 2.2 zero-diagonal). -/
theorem lanczosOp_parity {N : ℕ} (G : GibbsData N) {H O : QubitOp N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) :
    ∀ n : ℕ, (lanczosOp G H O n)ᴴ = ((-1 : ℂ) ^ n) • lanczosOp G H O n ∧
      (n = 0 ∨ ((lanczosState G H O n).2.1)ᴴ = ((-1 : ℂ) ^ (n - 1)) • (lanczosState G H O n).2.1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inl rfl⟩
    simp only [pow_zero, one_smul, lanczosOp, lanczosState]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_smul, hO.eq]; simp [Complex.star_def]
  | succ n ih =>
    rcases ih with ⟨hOn, hOprev⟩
    have hAnext_par : (matComm H (lanczosOp G H O n) -
        ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1)ᴴ =
        ((-1 : ℂ) ^ (n + 1)) • (matComm H (lanczosOp G H O n) -
          ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1) := by
      have hcomm_par : (matComm H (lanczosOp G H O n))ᴴ =
          ((-1 : ℂ) ^ (n + 1)) • matComm H (lanczosOp G H O n) := by
        unfold matComm
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hH.eq, hOn, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, pow_succ, mul_comm,
          ← smul_smul]
        congr 1; simp [neg_sub]
      have hprev_par : (((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1)ᴴ =
          ((-1 : ℂ) ^ (n + 1)) • (((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1) := by
        rcases hOprev with rfl | hp
        · simp [lanczosCoeff_zero]
        · by_cases hn0 : n = 0
          · subst hn0; simp [lanczosCoeff_zero]
          · rw [Matrix.conjTranspose_smul, hp, Complex.star_def, Complex.conj_ofReal, smul_comm]
            congr 1
            have h2 : n + 1 = (n - 1) + 2 := by omega
            rw [h2, pow_add]; norm_num
      rw [Matrix.conjTranspose_sub, hcomm_par, hprev_par, smul_sub]
    refine ⟨?_, Or.inr (by simpa [lanczosState_prev] using hOn)⟩
    unfold lanczosOp
    simp only [lanczosState]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      change (((lanczosCoeff G H O (n + 1))⁻¹ : ℝ) : ℂ) •
        (matComm H (lanczosOp G H O n) -
          ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1)ᴴ = _
      rw [hAnext_par, smul_comm]

/-- **Concrete Wightman Lanczos Orthonormality**:
For ANY Hermitian `H, O : QubitOp N`, `G := concreteGibbsData hH β`, and ALL `m, n : ℕ`:
`(𝒪_m^{(β)} | 𝒪_n^{(β)})_β^W = 1` if `m = n ∧ 𝒪_n^{(β)} ≠ 0`, and `0` otherwise. -/
theorem lanczosOp_orthonormal {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β : ℝ) :
    let G := concreteGibbsData hH β
    ∀ n m : ℕ, m ≤ n →
      gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O n) =
        if m = n ∧ lanczosOp G H O n ≠ 0 then 1 else 0 := by
  intro G n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hmn
    cases n with
    | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      simp only [true_and]
      by_cases h0 : lanczosOp G H O 0 = 0
      · rw [if_neg (not_not.mpr h0), h0]; simp [gibbsWightmanInner, wightmanInner]
      · rw [if_pos h0]
        have hnrm_ne : Real.sqrt (gibbsWightmanNormSq G O) ≠ 0 := by
          intro hzr
          apply h0
          unfold lanczosOp; simp only [lanczosState, if_pos hzr]
        have hO0 : lanczosOp G H O 0 = ((Real.sqrt (gibbsWightmanNormSq G O)⁻¹ : ℝ) : ℂ) • O := by
          unfold lanczosOp; simp only [lanczosState, if_neg hnrm_ne]
        rw [hO0]
        unfold gibbsWightmanInner wightmanInner
        simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
          smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
        have him : (gibbsWightmanInner G O O).im = 0 := by
          have hconj := gibbsWightmanInner_conj_symm G O O
          rw [Complex.star_def] at hconj
          have h1 := congrArg Complex.im hconj
          simp only [Complex.conj_im] at h1; linarith
        have hre : (G.ρHalf * Oᴴ * G.ρHalf * O).trace = (gibbsWightmanNormSq G O : ℂ) :=
          Complex.ext rfl (by simp [him])
        change ((Real.sqrt (gibbsWightmanNormSq G O)⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (gibbsWightmanNormSq G O)⁻¹ : ℝ) : ℂ) * (G.ρHalf * Oᴴ * G.ρHalf * O).trace) = 1
        rw [hre]
        have hsq : Real.sqrt (gibbsWightmanNormSq G O) ^ 2 = gibbsWightmanNormSq G O :=
          Real.sq_sqrt (gibbsWightmanNormSq_nonneg G O)
        have hneC : (Real.sqrt (gibbsWightmanNormSq G O) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnrm_ne
        rw [← hsq]; push_cast; field_simp [hneC]
    | succ n =>
      by_cases hbn1 : lanczosCoeff G H O (n + 1) = 0
      · have hOn1 : lanczosOp G H O (n + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbn1
        rw [hOn1, if_neg (by simp)]
        simp [gibbsWightmanInner, wightmanInner]
      · have hOn1_def : lanczosOp G H O (n + 1) =
            ((lanczosCoeff G H O (n + 1))⁻¹ : ℂ) •
              (matComm H (lanczosOp G H O n) -
                ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1) := by
          have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O n).1 -
              ((lanczosState G H O n).2.2 : ℂ) • (lanczosState G H O n).2.1)) ≠ 0 := hbn1
          unfold lanczosOp lanczosCoeff; simp only [lanczosState, if_neg hb', Complex.ofReal_inv]
        set Anext := matComm H (lanczosOp G H O n) -
          ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1
        have hAnext_norm : gibbsWightmanNormSq G Anext = (lanczosCoeff G H O (n + 1)) ^ 2 :=
          (Real.sq_sqrt (gibbsWightmanNormSq_nonneg G Anext)).symm
        have hOn1_ne : lanczosOp G H O (n + 1) ≠ 0 := by
          intro h0
          have hA0 : Anext = 0 := by
            have := congrArg (((lanczosCoeff G H O (n + 1) : ℝ) : ℂ) • ·) h0
            rw [hOn1_def, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hbn1), one_smul,
              smul_zero] at this
            exact this
          have hnorm0 : gibbsWightmanNormSq G Anext = 0 := by
            rw [hA0]; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
          rw [hnorm0] at hAnext_norm
          exact hbn1 (sq_eq_zero_iff.mp hAnext_norm.symm)
        by_cases hmeq : m = n + 1
        · subst hmeq
          rw [if_pos ⟨rfl, hOn1_ne⟩, hOn1_def]
          unfold gibbsWightmanInner wightmanInner
          simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
            smul_eq_mul, Complex.star_def, Complex.conj_ofReal, map_inv₀]
          have him : (gibbsWightmanInner G Anext Anext).im = 0 := by
            have hconj := gibbsWightmanInner_conj_symm G Anext Anext
            rw [Complex.star_def] at hconj
            have h1 := congrArg Complex.im hconj
            simp only [Complex.conj_im] at h1; linarith
          have hre : (G.ρHalf * Anextᴴ * G.ρHalf * Anext).trace = (gibbsWightmanNormSq G Anext : ℂ) :=
            Complex.ext rfl (by simp [him])
          change ((lanczosCoeff G H O (n + 1) : ℂ)⁻¹) *
            (((lanczosCoeff G H O (n + 1) : ℂ)⁻¹) * (G.ρHalf * Anextᴴ * G.ρHalf * Anext).trace) = 1
          rw [hre, hAnext_norm]
          have hneC : (lanczosCoeff G H O (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbn1
          push_cast; field_simp [hneC]
        · rw [if_neg (by intro h; exact hmeq h.1)]
          rw [hOn1_def]
          have hpull : gibbsWightmanInner G (lanczosOp G H O m) (((lanczosCoeff G H O (n + 1))⁻¹ : ℂ) • Anext) =
              ((lanczosCoeff G H O (n + 1))⁻¹ : ℂ) * gibbsWightmanInner G (lanczosOp G H O m) Anext := by
            unfold gibbsWightmanInner wightmanInner
            simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
          rw [hpull]
          suffices h0 : gibbsWightmanInner G (lanczosOp G H O m) Anext = 0 by rw [h0, mul_zero]
          have hsplit : gibbsWightmanInner G (lanczosOp G H O m) Anext =
              gibbsWightmanInner G (lanczosOp G H O m) (matComm H (lanczosOp G H O n)) -
              ((lanczosCoeff G H O n : ℝ) : ℂ) *
                gibbsWightmanInner G (lanczosOp G H O m) (lanczosState G H O n).2.1 := by
            unfold Anext gibbsWightmanInner wightmanInner
            simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
          rw [hsplit]
          by_cases hmn_eq : m = n
          · subst hmn_eq
            have hdiag := gibbsWightmanInner_matComm_diag_zero_of_parity hH β (lanczosOp_parity G hH hO n).1
            rw [hdiag, zero_sub]
            cases n with
            | zero => simp [lanczosCoeff_zero]
            | succ k =>
              rw [lanczosState_prev]
              have horth := ih (k + 1) (by omega) k (by omega)
              have hsym := gibbsWightmanInner_conj_symm G (lanczosOp G H O k) (lanczosOp G H O (k + 1))
              rw [horth, if_neg (by omega), star_zero] at hsym
              rw [← hsym, mul_zero, neg_zero]
          · cases n with
            | zero => omega
            | succ k =>
              rw [lanczosState_prev]
              by_cases hmk : m = k
              · subst hmk
                rw [← gibbsWightmanInner_matComm_selfAdjoint hH β]
                by_cases hbk1 : lanczosCoeff G H O (k + 1) = 0
                · have hOk1 : lanczosOp G H O (k + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk1
                  rw [hOk1, hbk1]; simp [gibbsWightmanInner, wightmanInner]
                · rw [lanczos_three_term G H O k hbk1]
                  have hlin_l : gibbsWightmanInner G
                      ((lanczosCoeff G H O (k + 1) : ℂ) • lanczosOp G H O (k + 1) +
                        (lanczosCoeff G H O k : ℂ) • (lanczosState G H O k).2.1)
                      (lanczosOp G H O (k + 1)) =
                      (lanczosCoeff G H O (k + 1) : ℂ) *
                        gibbsWightmanInner G (lanczosOp G H O (k + 1)) (lanczosOp G H O (k + 1)) +
                      (lanczosCoeff G H O k : ℂ) *
                        gibbsWightmanInner G (lanczosState G H O k).2.1 (lanczosOp G H O (k + 1)) := by
                    unfold gibbsWightmanInner wightmanInner
                    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
                      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
                      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.star_def,
                      Complex.conj_ofReal]
                  rw [hlin_l]
                  have hprev0 : (lanczosCoeff G H O k : ℂ) *
                      gibbsWightmanInner G (lanczosState G H O k).2.1 (lanczosOp G H O (k + 1)) = 0 := by
                    cases k with
                    | zero => simp [lanczosCoeff_zero]
                    | succ j =>
                      rw [lanczosState_prev, ih (j + 2) (by omega) j (by omega), if_neg (by omega), mul_zero]
                  rw [hprev0, add_zero]
                  have hOk1_ne : lanczosOp G H O (k + 1) ≠ 0 := by
                    intro h0
                    have hnorm1 : gibbsWightmanNormSq G (matComm H (lanczosOp G H O k) -
                        ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1) =
                        (lanczosCoeff G H O (k + 1)) ^ 2 :=
                      (Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)).symm
                    have hdef : lanczosOp G H O (k + 1) =
                        ((lanczosCoeff G H O (k + 1))⁻¹ : ℂ) •
                          (matComm H (lanczosOp G H O k) -
                            ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1) := by
                      have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O k).1 -
                          ((lanczosState G H O k).2.2 : ℂ) • (lanczosState G H O k).2.1)) ≠ 0 := hbk1
                      unfold lanczosOp lanczosCoeff; simp only [lanczosState, if_neg hb', Complex.ofReal_inv]
                    have hA0 : matComm H (lanczosOp G H O k) -
                        ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1 = 0 := by
                      have := congrArg (((lanczosCoeff G H O (k + 1) : ℝ) : ℂ) • ·) h0
                      rw [hdef, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hbk1),
                        one_smul, smul_zero] at this
                      exact this
                    rw [hA0] at hnorm1
                    simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner] at hnorm1
                    exact hbk1 hnorm1
                  have hOk_ne : lanczosOp G H O k ≠ 0 := by
                    intro h0
                    cases k with
                    | zero =>
                      have hAn : matComm H (lanczosOp G H O 0) -
                          ((lanczosCoeff G H O 0 : ℝ) : ℂ) • (lanczosState G H O 0).2.1 = 0 := by
                        rw [h0, lanczosCoeff_zero]; unfold matComm; simp
                      have : lanczosCoeff G H O 1 = 0 := by
                        change Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosOp G H O 0) -
                          ((lanczosCoeff G H O 0 : ℝ) : ℂ) • (lanczosState G H O 0).2.1)) = 0
                        rw [hAn]; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
                      exact hbk1 this
                    | succ j =>
                      have hbj : lanczosCoeff G H O (j + 1) = 0 := by
                        by_contra hne
                        have hnorm1 : gibbsWightmanNormSq G (matComm H (lanczosOp G H O j) -
                            ((lanczosCoeff G H O j : ℝ) : ℂ) • (lanczosState G H O j).2.1) =
                            (lanczosCoeff G H O (j + 1)) ^ 2 :=
                          (Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)).symm
                        have hdef : lanczosOp G H O (j + 1) =
                            ((lanczosCoeff G H O (j + 1))⁻¹ : ℂ) •
                              (matComm H (lanczosOp G H O j) -
                                ((lanczosCoeff G H O j : ℝ) : ℂ) • (lanczosState G H O j).2.1) := by
                          have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O j).1 -
                              ((lanczosState G H O j).2.2 : ℂ) • (lanczosState G H O j).2.1)) ≠ 0 := hne
                          unfold lanczosOp lanczosCoeff; simp only [lanczosState, if_neg hb', Complex.ofReal_inv]
                        have hA0 : matComm H (lanczosOp G H O j) -
                            ((lanczosCoeff G H O j : ℝ) : ℂ) • (lanczosState G H O j).2.1 = 0 := by
                          have := congrArg (((lanczosCoeff G H O (j + 1) : ℝ) : ℂ) • ·) h0
                          rw [hdef, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hne),
                            one_smul, smul_zero] at this
                          exact this
                        rw [hA0] at hnorm1
                        simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner] at hnorm1
                        exact hne hnorm1
                      exact hbk1 (lanczos_stays_zero G H O (j + 1) h0 hbj 1).2
                  rw [ih (k + 1) (by omega) (k + 1) le_rfl, if_pos ⟨rfl, hOk1_ne⟩,
                    ih k (by omega) k le_rfl, if_pos ⟨rfl, hOk_ne⟩, mul_one, mul_one, sub_self]
              · have h2nd : gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O k) = 0 := by
                  rw [ih k (by omega) m (by omega), if_neg (by omega)]
                rw [h2nd, mul_zero, sub_zero, ← gibbsWightmanInner_matComm_selfAdjoint hH β]
                by_cases hbm1 : lanczosCoeff G H O (m + 1) = 0
                · have hOm1 : lanczosOp G H O (m + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbm1
                  have hOk1 : lanczosOp G H O (k + 1) = 0 := by
                    have h := (lanczos_stays_zero G H O (m + 1) hOm1 hbm1 (k - m)).1
                    rwa [show m + 1 + (k - m) = k + 1 by omega] at h
                  rw [hOk1]; simp [gibbsWightmanInner, wightmanInner]
                · rw [lanczos_three_term G H O m hbm1]
                  have hlin_l : gibbsWightmanInner G
                      ((lanczosCoeff G H O (m + 1) : ℂ) • lanczosOp G H O (m + 1) +
                        (lanczosCoeff G H O m : ℂ) • (lanczosState G H O m).2.1)
                      (lanczosOp G H O (k + 1)) =
                      (lanczosCoeff G H O (m + 1) : ℂ) *
                        gibbsWightmanInner G (lanczosOp G H O (m + 1)) (lanczosOp G H O (k + 1)) +
                      (lanczosCoeff G H O m : ℂ) *
                        gibbsWightmanInner G (lanczosState G H O m).2.1 (lanczosOp G H O (k + 1)) := by
                    unfold gibbsWightmanInner wightmanInner
                    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
                      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
                      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.star_def,
                      Complex.conj_ofReal]
                  rw [hlin_l, ih (k + 1) (by omega) (m + 1) (by omega), if_neg (by omega), mul_zero, zero_add]
                  cases m with
                  | zero => simp [lanczosCoeff_zero]
                  | succ j =>
                    rw [lanczosState_prev, ih (k + 1) (by omega) j (by omega), if_neg (by omega), mul_zero]

theorem lanczosOp_orthonormal_all {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β : ℝ) (m n : ℕ) :
    gibbsWightmanInner (concreteGibbsData hH β)
      (lanczosOp (concreteGibbsData hH β) H O m) (lanczosOp (concreteGibbsData hH β) H O n) =
      if m = n ∧ lanczosOp (concreteGibbsData hH β) H O n ≠ 0 then 1 else 0 := by
  rcases le_total m n with hmn | hnm
  · exact lanczosOp_orthonormal hH hO β n m hmn
  · have h := lanczosOp_orthonormal hH hO β m n hnm
    have hsym := gibbsWightmanInner_conj_symm (concreteGibbsData hH β)
      (lanczosOp (concreteGibbsData hH β) H O n) (lanczosOp (concreteGibbsData hH β) H O m)
    rw [← hsym, h]
    by_cases hmeq : m = n
    · subst hmeq; split_ifs <;> simp
    · have hne : n ≠ m := Ne.symm hmeq
      rw [if_neg (by tauto), if_neg (by tauto), star_zero]

lemma heisenbergEvol_real_herm {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (t : ℝ) :
    (heisenbergEvol hH (t : ℂ) O)ᴴ = heisenbergEvol hH (t : ℂ) O := by
  unfold heisenbergEvol
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hO.eq,
    complexPropagator_real_conjTranspose hH t]
  have hneg : (complexPropagator hH (-(t : ℂ)))ᴴ = complexPropagator hH (t : ℂ) := by
    have := complexPropagator_real_conjTranspose hH (-t)
    simpa using this
  rw [hneg, Matrix.mul_assoc]

/-- Real-time Heisenberg evolution preserves the Wightman norm squared:
`‖𝒪(t)‖_{β,W}² = ‖𝒪‖_{β,W}²`. -/
theorem heisenbergEvol_real_wightmanNormSq {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β t : ℝ) (O : QubitOp N) :
    gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (t : ℂ) O) =
      gibbsWightmanNormSq (concreteGibbsData hH β) O := by
  set G := concreteGibbsData hH β
  have hU_comm : ∀ z : ℂ, complexPropagator hH z * G.ρHalf = G.ρHalf * complexPropagator hH z := by
    intro z
    change complexPropagator hH z * gibbsRhoHalf hH β = gibbsRhoHalf hH β * complexPropagator hH z
    unfold complexPropagator gibbsRhoHalf
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1; exact hermFunc_comm hH _ _
  have hU_unit1 : complexPropagator hH (-(t : ℂ)) * complexPropagator hH (t : ℂ) = 1 := by
    rw [complexPropagator_add, neg_add_cancel, complexPropagator_zero]
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner heisenbergEvol
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, complexPropagator_real_conjTranspose hH t]
  have hneg : (complexPropagator hH (-(t : ℂ)))ᴴ = complexPropagator hH (t : ℂ) := by
    have := complexPropagator_real_conjTranspose hH (-t); simpa using this
  rw [hneg]
  calc Matrix.trace (G.ρHalf * (complexPropagator hH (t : ℂ) * Oᴴ * complexPropagator hH (-(t : ℂ))) *
          G.ρHalf * (complexPropagator hH (t : ℂ) * O * complexPropagator hH (-(t : ℂ))))
      = Matrix.trace ((G.ρHalf * complexPropagator hH (t : ℂ)) * Oᴴ *
          (complexPropagator hH (-(t : ℂ)) * G.ρHalf) * complexPropagator hH (t : ℂ) * O *
          complexPropagator hH (-(t : ℂ))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((complexPropagator hH (t : ℂ) * G.ρHalf) * Oᴴ *
          (G.ρHalf * complexPropagator hH (-(t : ℂ))) * complexPropagator hH (t : ℂ) * O *
          complexPropagator hH (-(t : ℂ))) := by rw [← hU_comm, hU_comm]
    _ = Matrix.trace (complexPropagator hH (t : ℂ) *
          (G.ρHalf * Oᴴ * G.ρHalf * (complexPropagator hH (-(t : ℂ)) * complexPropagator hH (t : ℂ)) *
            O * complexPropagator hH (-(t : ℂ)))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (complexPropagator hH (t : ℂ) *
          (G.ρHalf * Oᴴ * G.ρHalf * O * complexPropagator hH (-(t : ℂ)))) := by
        rw [hU_unit1, Matrix.mul_one]
    _ = Matrix.trace ((G.ρHalf * Oᴴ * G.ρHalf * O * complexPropagator hH (-(t : ℂ))) *
          complexPropagator hH (t : ℂ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (G.ρHalf * Oᴴ * G.ρHalf * O *
          (complexPropagator hH (-(t : ℂ)) * complexPropagator hH (t : ℂ))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (G.ρHalf * Oᴴ * G.ρHalf * O) := by rw [hU_unit1, Matrix.mul_one]

/-- **Item #2 (Real-Valuedness of Concrete Krylov Wavefunction)**:
For Hermitian `H, O : QubitOp N`, `φ_n^{(β)}(t) = (-i)^n (𝒪_n^{(β)} | 𝒪(t))_β^W` is real-valued! -/
theorem concreteKrylovWavefn_im_eq_zero {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β : ℝ) (n : ℕ) (t : ℝ) :
    (concreteKrylovWavefn hH β O n t).im = 0 := by
  set G := concreteGibbsData hH β
  have hstar : star (concreteKrylovWavefn hH β O n t) = concreteKrylovWavefn hH β O n t := by
    unfold concreteKrylovWavefn
    rw [star_mul', star_pow, Complex.star_def, map_neg, Complex.conj_I, neg_neg]
    have hpar := (lanczosOp_parity G hH hO n).1
    have hOt := heisenbergEvol_real_herm hH hO t
    have hε2 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rw [← mul_pow]; norm_num
    have hsym := gibbsWightmanInner_parity_symm G hpar hOt hε2
    rw [Complex.star_def] at hsym
    rw [hsym]
    have hpow : (-Complex.I) ^ n = Complex.I ^ n * (-1 : ℂ) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [hpow]; ring
  have h1 := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at h1
  linarith

/-- **Item #2 (Initial Condition `φ_n^{(β)}(0) = δ_{n, 0}`)**:
For Hermitian `H, O : QubitOp N` normalized with `‖O‖_{β,W}² = 1`:
`concreteKrylovWavefn hH β O n 0 = if n = 0 then 1 else 0`. -/
theorem concreteKrylovWavefn_zero {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β : ℝ) (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (n : ℕ) :
    concreteKrylovWavefn hH β O n 0 = if n = 0 then 1 else 0 := by
  set G := concreteGibbsData hH β
  have hO0_eq : lanczosOp G H O 0 = O := by
    unfold lanczosOp
    simp only [lanczosState, hOnorm, Real.sqrt_one, one_ne_zero, ↓reduceIte, inv_one,
      Complex.ofReal_one, one_smul]
  have hO0_ne : lanczosOp G H O 0 ≠ 0 := by
    intro h0; rw [hO0_eq] at h0
    rw [h0] at hOnorm; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner] at hOnorm
  unfold concreteKrylovWavefn
  simp only [Complex.ofReal_zero, heisenbergEvol_zero]
  rw [← hO0_eq, lanczosOp_orthonormal_all hH hO β n 0]
  by_cases hn0 : n = 0
  · subst hn0; simp [hO0_ne]
  · simp [hn0]

/-- **Item #2 (Concrete Krylov ODE, Eq. 2.7)**:
For Hermitian `H, O : QubitOp N`, `φ_n(t) = concreteKrylovWavefn hH β O n t` solves the exact
discrete Schrödinger / Lanczos ODE:
`d/dt φ_n(t) = b_n φ_{n-1}(t) - b_{n+1} φ_{n+1}(t)`. -/
theorem concreteKrylovWavefn_hasDerivAt {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β : ℝ) (n : ℕ) (t : ℝ) :
    let G := concreteGibbsData hH β
    HasDerivAt (fun s : ℝ ↦ concreteKrylovWavefn hH β O n s)
      ((lanczosCoeff G H O n : ℂ) * (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) t) -
       (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) t) t := by
  intro G
  set M : QubitOp N := G.ρHalf * (lanczosOp G H O n)ᴴ * G.ρHalf
  have hinner_eq : ∀ s : ℝ, concreteKrylovWavefn hH β O n s =
      (-Complex.I) ^ n * ∑ i : QubitIdx N, ∑ j : QubitIdx N, M i j * heisenbergEvol hH (s : ℂ) O j i := by
    intro s
    unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
    congr 1
    simp only [M, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hd : HasDerivAt (fun s : ℝ ↦
      (-Complex.I) ^ n * ∑ i : QubitIdx N, ∑ j : QubitIdx N, M i j * heisenbergEvol hH (s : ℂ) O j i)
      ((-Complex.I) ^ n * ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        M i j * (Complex.I • matComm H (heisenbergEvol hH (t : ℂ) O)) j i) t := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum; intro i _
    apply HasDerivAt.fun_sum; intro j _
    exact (heisenbergEvol_entry_hasDerivAt hH O t j i).const_mul (M i j)
  have hrhs_eq : (-Complex.I) ^ n * ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        M i j * (Complex.I • matComm H (heisenbergEvol hH (t : ℂ) O)) j i =
      (lanczosCoeff G H O n : ℂ) * (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) t) -
      (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) t := by
    have htr : (∑ i : QubitIdx N, ∑ j : QubitIdx N,
        M i j * (Complex.I • matComm H (heisenbergEvol hH (t : ℂ) O)) j i) =
        Complex.I * gibbsWightmanInner G (lanczosOp G H O n) (matComm H (heisenbergEvol hH (t : ℂ) O)) := by
      unfold gibbsWightmanInner wightmanInner
      have h1 : Matrix.trace (M * (Complex.I • matComm H (heisenbergEvol hH (t : ℂ) O))) =
          Complex.I * Matrix.trace (M * matComm H (heisenbergEvol hH (t : ℂ) O)) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [← h1]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [htr, ← gibbsWightmanInner_matComm_selfAdjoint hH β]
    have h3term : matComm H (lanczosOp G H O n) =
        (lanczosCoeff G H O (n + 1) : ℂ) • lanczosOp G H O (n + 1) +
        (lanczosCoeff G H O n : ℂ) • (lanczosState G H O n).2.1 := by
      by_cases hb : lanczosCoeff G H O (n + 1) = 0
      · have hnorm0 : gibbsWightmanNormSq G (matComm H (lanczosOp G H O n) -
            ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1) = 0 := by
          have hsq : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosOp G H O n) -
              ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1)) = 0 := hb
          have := congrArg (· ^ 2) hsq
          rwa [Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _), zero_pow (by norm_num)] at this
        have hsub0 := eq_zero_of_gibbsWightmanNormSq_eq_zero G hnorm0
        rw [hb, Complex.ofReal_zero, zero_smul, zero_add]
        exact sub_eq_zero.mp hsub0
      · exact lanczos_three_term G H O n hb
    rw [h3term]
    have hlin : gibbsWightmanInner G
        ((lanczosCoeff G H O (n + 1) : ℂ) • lanczosOp G H O (n + 1) +
         (lanczosCoeff G H O n : ℂ) • (lanczosState G H O n).2.1) (heisenbergEvol hH (t : ℂ) O) =
        (lanczosCoeff G H O (n + 1) : ℂ) *
          gibbsWightmanInner G (lanczosOp G H O (n + 1)) (heisenbergEvol hH (t : ℂ) O) +
        (lanczosCoeff G H O n : ℂ) *
          gibbsWightmanInner G (lanczosState G H O n).2.1 (heisenbergEvol hH (t : ℂ) O) := by
      unfold gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [hlin]
    cases n with
    | zero =>
      simp only [lanczosCoeff_zero, Complex.ofReal_zero, zero_mul, add_zero, ↓reduceIte, zero_sub,
        pow_zero, one_mul, pow_one, concreteKrylovWavefn]
      ring
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, lanczosState_prev,
        concreteKrylovWavefn]
      have hphase_prev : (-Complex.I) ^ (k + 1) * Complex.I = (-Complex.I) ^ k := by
        rw [pow_succ, mul_assoc]
        have hI : (-Complex.I) * Complex.I = 1 := by
          calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
            _ = -(-1 : ℂ) := by rw [Complex.I_mul_I]
            _ = 1 := by ring
        rw [hI, mul_one]
      calc (-Complex.I) ^ (k + 1) * (Complex.I *
              ((lanczosCoeff G H O (k + 2) : ℂ) *
                gibbsWightmanInner G (lanczosOp G H O (k + 2)) (heisenbergEvol hH (t : ℂ) O) +
               (lanczosCoeff G H O (k + 1) : ℂ) *
                gibbsWightmanInner G (lanczosOp G H O k) (heisenbergEvol hH (t : ℂ) O)))
          = ((-Complex.I) ^ (k + 1) * Complex.I) * (lanczosCoeff G H O (k + 1) : ℂ) *
              gibbsWightmanInner G (lanczosOp G H O k) (heisenbergEvol hH (t : ℂ) O) +
            ((-Complex.I) ^ (k + 1) * Complex.I) * (lanczosCoeff G H O (k + 2) : ℂ) *
              gibbsWightmanInner G (lanczosOp G H O (k + 2)) (heisenbergEvol hH (t : ℂ) O) := by ring
        _ = (lanczosCoeff G H O (k + 1) : ℂ) * ((-Complex.I) ^ k *
              gibbsWightmanInner G (lanczosOp G H O k) (heisenbergEvol hH (t : ℂ) O)) -
            (lanczosCoeff G H O (k + 2) : ℂ) * ((-Complex.I) ^ (k + 2) *
              gibbsWightmanInner G (lanczosOp G H O (k + 2)) (heisenbergEvol hH (t : ℂ) O)) := by
            conv_lhs => rw [hphase_prev]; rhs; rw [show (-Complex.I) ^ k = -((-Complex.I) ^ (k + 2)) by
              rw [pow_add]; have h2 : (-Complex.I) ^ 2 = -1 := by
                rw [sq]; calc (-Complex.I) * (-Complex.I) = Complex.I * Complex.I := by ring
                  _ = -1 := Complex.I_mul_I
              rw [h2]; ring]
            ring
  rw [← hrhs_eq]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hinner_eq)

/-- Every finite-dimensional Krylov chain on `QubitOp N` terminates at some index `k < 4^N`. -/
lemma lanczos_terminates {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (β : ℝ) :
    ∃ k < 4 ^ N, lanczosCoeff (concreteGibbsData hH β) H O (k + 1) = 0 := by
  set G := concreteGibbsData hH β
  by_contra hall
  push Not at hall
  have hO0_ne : lanczosOp G H O 0 ≠ 0 := by
    intro h0
    have h1 := (lanczos_stays_zero G H O 0 h0 (lanczosCoeff_zero G H O) 1).2
    exact hall 0 (by positivity) h1
  have hOn_ne : ∀ n : Fin (4 ^ N + 1), lanczosOp G H O n.val ≠ 0 := by
    intro ⟨n, hn⟩
    cases n with
    | zero => exact hO0_ne
    | succ k =>
      intro h0
      have hbk1 := hall k (by omega)
      have hdef : lanczosOp G H O (k + 1) =
          ((lanczosCoeff G H O (k + 1))⁻¹ : ℂ) •
            (matComm H (lanczosOp G H O k) -
              ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1) := by
        have hb' : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosState G H O k).1 -
            ((lanczosState G H O k).2.2 : ℂ) • (lanczosState G H O k).2.1)) ≠ 0 := hbk1
        unfold lanczosOp lanczosCoeff; simp only [lanczosState, if_neg hb', Complex.ofReal_inv]
      have hA0 : matComm H (lanczosOp G H O k) -
          ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1 = 0 := by
        have := congrArg (((lanczosCoeff G H O (k + 1) : ℝ) : ℂ) • ·) h0
        rw [hdef, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hbk1),
          one_smul, smul_zero] at this
        exact this
      have hnorm0 : gibbsWightmanNormSq G (matComm H (lanczosOp G H O k) -
          ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1) = 0 := by
        rw [hA0]; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
      have hsq : (lanczosCoeff G H O (k + 1)) ^ 2 = 0 := by
        have := (Real.sq_sqrt (gibbsWightmanNormSq_nonneg G (matComm H (lanczosOp G H O k) -
          ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1))).symm
        change gibbsWightmanNormSq G _ = (lanczosCoeff G H O (k + 1)) ^ 2 at this
        linarith
      exact hbk1 (sq_eq_zero_iff.mp hsq)
  let v : Fin (4 ^ N + 1) → EuclideanSpace ℂ (QubitIdx N × QubitIdx N) :=
    fun n ↦ qubitOpToHS N (jBeta G.ρQuarter (lanczosOp G H O n.val))
  have hortho : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change @inner ℂ _ _ (qubitOpToHS N (jBeta G.ρQuarter (lanczosOp G H O i.val)))
      (qubitOpToHS N (jBeta G.ρQuarter (lanczosOp G H O j.val))) = if i = j then 1 else 0
    rw [qubitOpToHS_inner]
    have h1 := prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf
      (lanczosOp G H O i.val) (lanczosOp G H O j.val) G.ρQuarter_herm G.sq_quarter
    change gibbsWightmanInner G (lanczosOp G H O i.val) (lanczosOp G H O j.val) = _ at h1
    rw [← h1, lanczosOp_orthonormal_all hH hO β i.val j.val]
    by_cases hij : i = j
    · subst hij; simp [hOn_ne i]
    · have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      simp [hij, hne]
  have hli := hortho.linearIndependent
  have hcard := hli.fintype_card_le_finrank
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) = 4 ^ N := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, ← mul_pow]; norm_num
  rw [Fintype.card_fin, hdim] at hcard
  omega

/-- **Concrete Krylov Subspace Completeness**:
For Hermitian `H, O : QubitOp N` with `‖O‖_{β,W}² = 1` and ANY real time `t : ℝ`,
`heisenbergEvol hH (t : ℂ) O = lanczosTrunc hH β O (4 ^ N) t`. -/
theorem heisenbergEvol_eq_lanczosTrunc_full {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β t : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    heisenbergEvol hH (t : ℂ) O = lanczosTrunc hH β O (4 ^ N) t := by
  set G := concreteGibbsData hH β
  have hphase : ∀ n : ℕ, Complex.I ^ n * (-Complex.I) ^ n = 1 := by
    intro n; rw [← mul_pow]
    have hI : Complex.I * (-Complex.I) = 1 := by
      calc Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by ring
        _ = -(-1 : ℂ) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    rw [hI, one_pow]
  have htrunc_eq : ∀ s : ℝ, lanczosTrunc hH β O (4 ^ N) s =
      ∑ n ∈ Finset.range (4 ^ N),
        (gibbsWightmanInner G (lanczosOp G H O n) (heisenbergEvol hH (s : ℂ) O)) •
          lanczosOp G H O n := by
    intro s
    unfold lanczosTrunc concreteKrylovWavefn
    apply Finset.sum_congr rfl; intro n _
    rw [← mul_assoc, hphase n, one_mul]
  set R : ℝ → QubitOp N := fun s ↦ heisenbergEvol hH (s : ℂ) O - lanczosTrunc hH β O (4 ^ N) s
  have hR_zero : R 0 = 0 := by
    have hO0_eq : lanczosOp G H O 0 = O := by
      unfold lanczosOp
      simp only [lanczosState, hOnorm, Real.sqrt_one, one_ne_zero, ↓reduceIte, inv_one,
        Complex.ofReal_one, one_smul]
    have hO0_ne : lanczosOp G H O 0 ≠ 0 := by
      intro h0; rw [hO0_eq] at h0; rw [h0] at hOnorm
      simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner] at hOnorm
    dsimp only [R]
    rw [htrunc_eq 0, Complex.ofReal_zero, heisenbergEvol_zero]
    rw [Finset.sum_eq_single 0]
    · rw [← hO0_eq, lanczosOp_orthonormal_all hH hO β 0 0, if_pos ⟨rfl, hO0_ne⟩, one_smul, sub_self]
    · intro n _ hn0
      rw [← hO0_eq, lanczosOp_orthonormal_all hH hO β n 0, if_neg (by tauto), zero_smul]
    · intro h0; exact absurd (Finset.mem_range.mpr (by positivity)) h0
  have hterm_4N : lanczosCoeff G H O (4 ^ N) = 0 := by
    rcases lanczos_terminates hH hO β with ⟨k, hk, hbk⟩
    have hOk1 : lanczosOp G H O (k + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk
    have h := (lanczos_stays_zero G H O (k + 1) hOk1 hbk (4 ^ N - (k + 1))).2
    rwa [show k + 1 + (4 ^ N - (k + 1)) = 4 ^ N by omega] at h
  have hR_deriv : ∀ (s : ℝ) (i j : QubitIdx N),
      HasDerivAt (fun u : ℝ ↦ R u i j) ((Complex.I • matComm H (R s)) i j) s := by
    intro s i j
    have hdO := heisenbergEvol_entry_hasDerivAt hH O s i j
    have hdT : HasDerivAt (fun u : ℝ ↦ (lanczosTrunc hH β O (4 ^ N) u) i j)
        ((Complex.I • matComm H (lanczosTrunc hH β O (4 ^ N) s)) i j) s := by
      have hentry : ∀ u : ℝ, (lanczosTrunc hH β O (4 ^ N) u) i j =
          ∑ n ∈ Finset.range (4 ^ N),
            (Complex.I ^ n * concreteKrylovWavefn hH β O n u) * (lanczosOp G H O n) i j := by
        intro u; unfold lanczosTrunc; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      have hdsum : HasDerivAt (fun u : ℝ ↦
          ∑ n ∈ Finset.range (4 ^ N),
            (Complex.I ^ n * concreteKrylovWavefn hH β O n u) * (lanczosOp G H O n) i j)
          (∑ n ∈ Finset.range (4 ^ N),
            (Complex.I ^ n *
              ((lanczosCoeff G H O n : ℂ) * (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) s) -
               (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) s)) *
              (lanczosOp G H O n) i j) s := by
        apply HasDerivAt.fun_sum; intro n _
        exact ((concreteKrylovWavefn_hasDerivAt hH hO β n s).const_mul (Complex.I ^ n)).mul_const _
      have hrhs : (∑ n ∈ Finset.range (4 ^ N),
            (Complex.I ^ n *
              ((lanczosCoeff G H O n : ℂ) * (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) s) -
               (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) s)) *
              (lanczosOp G H O n) i j) =
          (Complex.I • matComm H (lanczosTrunc hH β O (4 ^ N) s)) i j := by
        have hcomm_sum : matComm H (lanczosTrunc hH β O (4 ^ N) s) =
            ∑ n ∈ Finset.range (4 ^ N),
              (Complex.I ^ n * concreteKrylovWavefn hH β O n s) •
                ((lanczosCoeff G H O (n + 1) : ℂ) • lanczosOp G H O (n + 1) +
                 (lanczosCoeff G H O n : ℂ) • (lanczosState G H O n).2.1) := by
          unfold lanczosTrunc matComm
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
            ← Finset.sum_sub_distrib, ← smul_sub]
          apply Finset.sum_congr rfl; intro n _
          congr 1
          by_cases hb : lanczosCoeff G H O (n + 1) = 0
          · have hnorm0 : gibbsWightmanNormSq G (matComm H (lanczosOp G H O n) -
                ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1) = 0 := by
              have hsq : Real.sqrt (gibbsWightmanNormSq G (matComm H (lanczosOp G H O n) -
                  ((lanczosCoeff G H O n : ℝ) : ℂ) • (lanczosState G H O n).2.1)) = 0 := hb
              have := congrArg (· ^ 2) hsq
              rwa [Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _), zero_pow (by norm_num)] at this
            have hsub0 := eq_zero_of_gibbsWightmanNormSq_eq_zero G hnorm0
            rw [hb, Complex.ofReal_zero, zero_smul, zero_add]
            exact sub_eq_zero.mp hsub0
          · exact lanczos_three_term G H O n hb
        rw [hcomm_sum]
        simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.add_apply, smul_eq_mul, Finset.mul_sum]
        have hS1 : (∑ n ∈ Finset.range (4 ^ N),
              Complex.I ^ n * ((lanczosCoeff G H O n : ℂ) *
                (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) s)) * (lanczosOp G H O n) i j) =
            ∑ n ∈ Finset.range (4 ^ N),
              Complex.I * (Complex.I ^ n * concreteKrylovWavefn hH β O n s *
                ((lanczosCoeff G H O (n + 1) : ℂ) * (lanczosOp G H O (n + 1)) i j)) := by
          have h4pos : 0 < 4 ^ N := by positivity
          have hsub1 : (4 ^ N) = (4 ^ N - 1) + 1 := by omega
          conv_lhs => rw [hsub1, Finset.sum_range_succ']
          conv_rhs => rw [hsub1, Finset.sum_range_succ]
          simp only [↓reduceIte, mul_zero, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
          rw [show (4 ^ N - 1) + 1 = 4 ^ N by omega, hterm_4N, Complex.ofReal_zero, zero_mul,
            mul_zero, mul_zero, add_zero]
          apply Finset.sum_congr rfl; intro k _
          rw [pow_succ]; ring
        have hS2 : (∑ n ∈ Finset.range (4 ^ N),
              -(Complex.I ^ n * ((lanczosCoeff G H O (n + 1) : ℂ) *
                concreteKrylovWavefn hH β O (n + 1) s) * (lanczosOp G H O n) i j)) =
            ∑ n ∈ Finset.range (4 ^ N),
              Complex.I * (Complex.I ^ n * concreteKrylovWavefn hH β O n s *
                ((lanczosCoeff G H O n : ℂ) * ((lanczosState G H O n).2.1) i j)) := by
          have h4pos : 0 < 4 ^ N := by positivity
          have hsub1 : (4 ^ N) = (4 ^ N - 1) + 1 := by omega
          conv_lhs => rw [hsub1, Finset.sum_range_succ]
          conv_rhs => rw [hsub1, Finset.sum_range_succ']
          rw [show (4 ^ N - 1) + 1 = 4 ^ N by omega, hterm_4N, Complex.ofReal_zero, zero_mul,
            mul_zero, zero_mul, neg_zero, add_zero, lanczosCoeff_zero, Complex.ofReal_zero,
            zero_mul, mul_zero, mul_zero, add_zero]
          apply Finset.sum_congr rfl; intro k _
          rw [lanczosState_prev, pow_succ]
          have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination -((Complex.I ^ k * concreteKrylovWavefn hH β O (k + 1) s *
            (lanczosCoeff G H O (k + 1) : ℂ) * (lanczosOp G H O k) i j) * hI2)
        have hL : (∑ n ∈ Finset.range (4 ^ N),
              (Complex.I ^ n *
                ((lanczosCoeff G H O n : ℂ) * (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) s) -
                 (lanczosCoeff G H O (n + 1) : ℂ) * concreteKrylovWavefn hH β O (n + 1) s)) *
                (lanczosOp G H O n) i j) =
            (∑ n ∈ Finset.range (4 ^ N),
              Complex.I ^ n * ((lanczosCoeff G H O n : ℂ) *
                (if n = 0 then 0 else concreteKrylovWavefn hH β O (n - 1) s)) * (lanczosOp G H O n) i j) +
            (∑ n ∈ Finset.range (4 ^ N),
              -(Complex.I ^ n * ((lanczosCoeff G H O (n + 1) : ℂ) *
                concreteKrylovWavefn hH β O (n + 1) s) * (lanczosOp G H O n) i j)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro n _; ring
        rw [hL, hS1, hS2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro n _; ring
      rw [← hrhs]
      exact hdsum.congr_of_eventuallyEq (Filter.Eventually.of_forall hentry)
    have hsub := hdO.sub hdT
    have hcomm_sub : (Complex.I • matComm H (heisenbergEvol hH (s : ℂ) O)) i j -
        (Complex.I • matComm H (lanczosTrunc hH β O (4 ^ N) s)) i j =
        (Complex.I • matComm H (R s)) i j := by
      unfold R matComm
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [hcomm_sub] at hsub
  let f : ℝ → ℝ := fun s ↦ gibbsWightmanNormSq G (R s)
  have hf_deriv : ∀ s : ℝ, HasDerivAt f 0 s := by
    intro s
    have hf_eq : ∀ u : ℝ, f u =
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
          G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i).re := by
      intro u
      unfold f gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      congr 1
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      calc ∑ l : QubitIdx N, ∑ k : QubitIdx N, ∑ j : QubitIdx N,
            G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i
          = ∑ l : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N,
              G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i :=
            Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
        _ = ∑ j : QubitIdx N, ∑ l : QubitIdx N, ∑ k : QubitIdx N,
              G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i := Finset.sum_comm
        _ = ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
              G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i :=
            Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    have hd_cplx : HasDerivAt (fun u : ℝ ↦
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
          G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i)
        (gibbsWightmanInner G (Complex.I • matComm H (R s)) (R s) +
         gibbsWightmanInner G (R s) (Complex.I • matComm H (R s))) s := by
      have hd_raw : HasDerivAt (fun u : ℝ ↦
          ∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
            G.ρHalf i j * star (R u k j) * G.ρHalf k l * R u l i)
          (∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
            (G.ρHalf i j * star ((Complex.I • matComm H (R s)) k j) * G.ρHalf k l * R s l i +
             G.ρHalf i j * star (R s k j) * G.ρHalf k l * (Complex.I • matComm H (R s)) l i)) s := by
        apply HasDerivAt.fun_sum; intro i _
        apply HasDerivAt.fun_sum; intro j _
        apply HasDerivAt.fun_sum; intro k _
        apply HasDerivAt.fun_sum; intro l _
        have hd1 : HasDerivAt (fun u : ℝ ↦ star (R u k j))
            (star ((Complex.I • matComm H (R s)) k j)) s := by
          simpa only [Complex.star_def] using
            Complex.conjCLE.hasFDerivAt.comp_hasDerivAt s (hR_deriv s k j)
        have hd2 := hR_deriv s l i
        have hmul := ((hd1.const_mul (G.ρHalf i j)).mul_const (G.ρHalf k l)).mul hd2
        simpa [mul_assoc] using hmul
      have hsum_eq : (∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
            (G.ρHalf i j * star ((Complex.I • matComm H (R s)) k j) * G.ρHalf k l * R s l i +
             G.ρHalf i j * star (R s k j) * G.ρHalf k l * (Complex.I • matComm H (R s)) l i)) =
          gibbsWightmanInner G (Complex.I • matComm H (R s)) (R s) +
          gibbsWightmanInner G (R s) (Complex.I • matComm H (R s)) := by
        have htr_form : ∀ X Y : QubitOp N,
            gibbsWightmanInner G X Y =
            ∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
              G.ρHalf i j * star (X k j) * G.ρHalf k l * Y l i := by
          intro X Y
          unfold gibbsWightmanInner wightmanInner
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          calc ∑ l : QubitIdx N, ∑ k : QubitIdx N, ∑ j : QubitIdx N,
                G.ρHalf i j * star (X k j) * G.ρHalf k l * Y l i
              = ∑ l : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N,
                  G.ρHalf i j * star (X k j) * G.ρHalf k l * Y l i :=
                Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
            _ = ∑ j : QubitIdx N, ∑ l : QubitIdx N, ∑ k : QubitIdx N,
                  G.ρHalf i j * star (X k j) * G.ρHalf k l * Y l i := Finset.sum_comm
            _ = ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N,
                  G.ρHalf i j * star (X k j) * G.ρHalf k l * Y l i :=
                Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
        rw [htr_form, htr_form]
        simp only [Finset.sum_add_distrib]
      rwa [hsum_eq] at hd_raw
    have hre_zero : (gibbsWightmanInner G (Complex.I • matComm H (R s)) (R s) +
        gibbsWightmanInner G (R s) (Complex.I • matComm H (R s))).re = 0 := by
      have h1 : gibbsWightmanInner G (Complex.I • matComm H (R s)) (R s) =
          (-Complex.I) * gibbsWightmanInner G (matComm H (R s)) (R s) := by
        unfold gibbsWightmanInner wightmanInner
        simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
          smul_eq_mul, Complex.star_def, Complex.conj_I]
      have h2 : gibbsWightmanInner G (R s) (Complex.I • matComm H (R s)) =
          Complex.I * gibbsWightmanInner G (R s) (matComm H (R s)) := by
        unfold gibbsWightmanInner wightmanInner
        simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [h1, h2, gibbsWightmanInner_matComm_selfAdjoint hH β]
      have hcancel : (-Complex.I) * gibbsWightmanInner G (R s) (matComm H (R s)) +
          Complex.I * gibbsWightmanInner G (R s) (matComm H (R s)) = 0 := by ring
      rw [hcancel, Complex.zero_re]
    have hd_re := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd_cplx
    rw [show Complex.reCLM (gibbsWightmanInner G (Complex.I • matComm H (R s)) (R s) +
        gibbsWightmanInner G (R s) (Complex.I • matComm H (R s))) = 0 from hre_zero] at hd_re
    exact hd_re.congr_of_eventuallyEq (Filter.Eventually.of_forall hf_eq)
  have hf_const : f t = f 0 :=
    is_const_of_deriv_eq_zero (fun s ↦ (hf_deriv s).differentiableAt)
      (fun s ↦ (hf_deriv s).deriv) t 0
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [hR_zero]; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
  rw [hf0] at hf_const
  exact sub_eq_zero.mp (eq_zero_of_gibbsWightmanNormSq_eq_zero G hf_const)

lemma lanczosTrunc_wightmanNormSq_eq {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β t : ℝ) (M : ℕ) :
    gibbsWightmanNormSq (concreteGibbsData hH β) (lanczosTrunc hH β O M t) =
      ∑ n ∈ Finset.range M, ‖concreteKrylovWavefn hH β O n t‖ ^ 2 := by
  set G := concreteGibbsData hH β
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner lanczosTrunc
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro m hm
  have hre_pull : (∑ n ∈ Finset.range M,
      ((Complex.I ^ n * concreteKrylovWavefn hH β O n t) *
        (star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
          (G.ρHalf * (lanczosOp G H O m)ᴴ * G.ρHalf * lanczosOp G H O n).trace)).re) =
      (∑ n ∈ Finset.range M,
        star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
        (Complex.I ^ n * concreteKrylovWavefn hH β O n t *
          gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O n))).re := by
    rw [← Complex.re_sum]; congr 1; apply Finset.sum_congr rfl; intro n _
    unfold gibbsWightmanInner wightmanInner; ring
  rw [hre_pull, Finset.sum_eq_single m]
  · rw [lanczosOp_orthonormal_all hH hO β m m]
    by_cases hOm : lanczosOp G H O m = 0
    · rw [if_neg (by simp [hOm]), mul_zero, mul_zero, Complex.zero_re]
      have hφ0 : concreteKrylovWavefn hH β O m t = 0 := by
        unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
        rw [hOm]; simp
      rw [hφ0, norm_zero, zero_pow (by norm_num)]
    · rw [if_pos ⟨rfl, hOm⟩, mul_one, Complex.star_def, Complex.conj_mul',
        ← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_I,
        one_pow, one_mul]
  · intro n _ hnm
    rw [lanczosOp_orthonormal_all hH hO β m n, if_neg (by intro h; exact hnm h.1.symm),
      mul_zero, mul_zero]
  · intro hm'; exact absurd hm hm'

/-- **Item #2 (Normalization `∑_{n < 4^N} ‖φ_n^{(β)}(t)‖² = 1`)**:
Directly from `heisenbergEvol_eq_lanczosTrunc_full` and `lanczosTrunc_wightmanNormSq_eq`. -/
theorem concreteKrylovWavefn_sum_sq_eq_one {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β t : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    ∑ n ∈ Finset.range (4 ^ N), ‖concreteKrylovWavefn hH β O n t‖ ^ 2 = 1 := by
  have h1 : gibbsWightmanNormSq (concreteGibbsData hH β) (heisenbergEvol hH (t : ℂ) O) = 1 := by
    rw [heisenbergEvol_real_wightmanNormSq hH β t O, hOnorm]
  rw [heisenbergEvol_eq_lanczosTrunc_full hH hO β t hOnorm,
    lanczosTrunc_wightmanNormSq_eq hH hO β t (4 ^ N)] at h1
  exact h1

lemma lanczosTrunc_wightmanNormSq_le_one {N : ℕ} {H O : QubitOp N} (hH : H.IsHermitian)
    (hO : O.IsHermitian) (β t : ℝ)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) (M : ℕ) :
    gibbsWightmanNormSq (concreteGibbsData hH β) (lanczosTrunc hH β O M t) ≤ 1 := by
  rw [lanczosTrunc_wightmanNormSq_eq hH hO β t M]
  have hzero_ge : ∀ n ≥ 4 ^ N, concreteKrylovWavefn hH β O n t = 0 := by
    intro n hn
    rcases lanczos_terminates hH hO β with ⟨k, hk, hbk⟩
    have hOk1 : lanczosOp (concreteGibbsData hH β) H O (k + 1) = 0 :=
      lanczosOp_eq_zero_of_coeff_zero _ H O hbk
    have hOn0 : lanczosOp (concreteGibbsData hH β) H O n = 0 := by
      have h := (lanczos_stays_zero (concreteGibbsData hH β) H O (k + 1) hOk1 hbk (n - (k + 1))).1
      rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
    unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
    rw [hOn0]; simp
  rw [← concreteKrylovWavefn_sum_sq_eq_one hH hO β t hOnorm]
  by_cases hM : M ≤ 4 ^ N
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM) fun _ _ _ ↦ sq_nonneg _
  · have hsplit : ∑ n ∈ Finset.range M, ‖concreteKrylovWavefn hH β O n t‖ ^ 2 =
        ∑ n ∈ Finset.range (4 ^ N), ‖concreteKrylovWavefn hH β O n t‖ ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn ↦ ?_
      have hge : 4 ^ N ≤ n := by simp only [Finset.mem_range] at hn; omega
      rw [hzero_ge n hge, norm_zero, zero_pow (by norm_num)]
    rw [hsplit]

/-- **Item #3 — Genuine Concrete Proposition 4.1(2) on `QubitOp N` (Eq. 4.2)**:
For ANY Hermitian `H ∈ filtrationSubmodule N r` (`1 ≤ r`), Hermitian `O ∈ filtrationSubmodule N s₀`
normalized with `‖O‖_{β,W}² = 1`, inverse temperature `β : ℝ`, and real time `t : ℝ`:
`Re (𝒪(t) | 𝒬^{(β)} 𝒪(t))_β^W ≤ (r - 1) * K_β^W(t) + s₀`. -/
theorem prop_4_1_part2_concrete_operator {N r s₀ : ℕ} (hr : 1 ≤ r)
    {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian) (β t : ℝ)
    (hHf : H ∈ filtrationSubmodule N r) (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
      (wightmanQ G (heisenbergEvol hH (t : ℂ) O))).re ≤
    ((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ) := by
  intro G
  rw [wightmanQ_eq_sum_distSq]
  unfold concreteKrylovComplexity
  apply prop_4_1_q_complexity_bound hr
    (fun n ↦ ‖concreteKrylovWavefn hH β O n t‖ ^ 2)
    (fun s ↦ wightmanDistSq G (filtrationSubmodule N s) (heisenbergEvol hH (t : ℂ) O))
  · intro n; exact sq_nonneg _
  · intro s
    calc wightmanDistSq G (filtrationSubmodule N s) (heisenbergEvol hH (t : ℂ) O)
        ≤ gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O) := wightmanDistSq_le_normSq G _ _
      _ = 1 := by rw [heisenbergEvol_real_wightmanNormSq hH β t O, hOnorm]
  · intro k s hks
    have hAk_mem : lanczosTrunc hH β O (k + 1) t ∈ filtrationSubmodule N s := by
      have h1 := lanczosTrunc_mem_filtration hr (by omega : 1 ≤ k + 1) hH β t hHf hOf
      simp only [Nat.add_sub_cancel] at h1
      have hle : s₀ + k * (r - 1) ≤ s := by rw [mul_comm]; exact hks
      exact filtrationSubmodule_mono hle h1
    have hdist_le : wightmanDistSq G (filtrationSubmodule N s) (heisenbergEvol hH (t : ℂ) O) ≤
        gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t) := by
      unfold wightmanDistSq
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨B, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _
      · exact ⟨lanczosTrunc hH β O (k + 1) t, hAk_mem, rfl⟩
    have htail_norm : gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t) =
        ∑ n ∈ (Finset.range (4 ^ N)).filter (fun n ↦ k < n), ‖concreteKrylovWavefn hH β O n t‖ ^ 2 := by
      have hzero_ge : ∀ n ≥ 4 ^ N, lanczosOp G H O n = 0 := by
        intro n hn
        rcases lanczos_terminates hH hO β with ⟨k₀, hk₀, hbk₀⟩
        have hOk1 : lanczosOp G H O (k₀ + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk₀
        have h := (lanczos_stays_zero G H O (k₀ + 1) hOk1 hbk₀ (n - (k₀ + 1))).1
        rwa [show k₀ + 1 + (n - (k₀ + 1)) = n by omega] at h
      have hdiff_eq : heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t =
          ∑ n ∈ (Finset.range (4 ^ N)).filter (fun n ↦ k < n),
            (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n := by
        rw [heisenbergEvol_eq_lanczosTrunc_full hH hO β t hOnorm]
        unfold lanczosTrunc
        have htrunc_cap : (∑ n ∈ Finset.range (k + 1),
            (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n) =
            ∑ n ∈ (Finset.range (4 ^ N)).filter (fun n ↦ ¬ k < n),
              (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n := by
          by_cases hk4 : k + 1 ≤ 4 ^ N
          · refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
            ext n; simp only [Finset.mem_range, Finset.mem_filter, not_lt]; omega
          · symm
            refine Finset.sum_subset (fun n hn ↦ ?_) (fun n hn hnot ↦ ?_)
            · simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hn ⊢; omega
            · simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hnot
              have hge : 4 ^ N ≤ n := by
                have := Finset.mem_range.mp hn; by_contra hlt; apply hnot; exact ⟨by omega, by omega⟩
              rw [hzero_ge n hge, smul_zero]
        rw [htrunc_cap]
        have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (4 ^ N)) (fun n ↦ k < n)
          (fun n ↦ (Complex.I ^ n * concreteKrylovWavefn hH β O n t) • lanczosOp G H O n)
        rw [← hpart, add_sub_cancel_right]
      rw [hdiff_eq]
      set S := (Finset.range (4 ^ N)).filter (fun n ↦ k < n)
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
        Complex.re_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro m hm
      have hre_pull : (∑ n ∈ S,
          ((Complex.I ^ n * concreteKrylovWavefn hH β O n t) *
            (star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
              (G.ρHalf * (lanczosOp G H O m)ᴴ * G.ρHalf * lanczosOp G H O n).trace)).re) =
          (∑ n ∈ S,
            star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
            (Complex.I ^ n * concreteKrylovWavefn hH β O n t *
              gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O n))).re := by
        rw [← Complex.re_sum]; congr 1; apply Finset.sum_congr rfl; intro n _
        unfold gibbsWightmanInner wightmanInner; ring
      rw [hre_pull, Finset.sum_eq_single m]
      · rw [lanczosOp_orthonormal_all hH hO β m m]
        by_cases hOm : lanczosOp G H O m = 0
        · rw [if_neg (by simp [hOm]), mul_zero, mul_zero, Complex.zero_re]
          have hφ0 : concreteKrylovWavefn hH β O m t = 0 := by
            unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
            rw [hOm]; simp
          rw [hφ0, norm_zero, zero_pow (by norm_num)]
        · rw [if_pos ⟨rfl, hOm⟩, mul_one, Complex.star_def, Complex.conj_mul',
            ← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_I,
            one_pow, one_mul]
      · intro n _ hnm
        rw [lanczosOp_orthonormal_all hH hO β m n, if_neg (by intro h; exact hnm h.1.symm),
          mul_zero, mul_zero]
      · intro hm'; exact absurd hm hm'
    rw [← htail_norm]
    exact hdist_le

end ConcreteLanczosPropertiesAndODE

section ConcreteLemma42MSS

/-- `S_β(1) = 0` for every Gibbs state `G : GibbsData N`. -/
lemma mssThermalSize_one {N : ℕ} (G : GibbsData N) :
    mssThermalSize G (1 : QubitOp N) = 0 := by
  unfold mssThermalSize jBeta
  rw [Matrix.mul_one, G.sq_quarter, sub_self]

/-- Nonnegativity of `Λ_β^{MSS}(s)` (`0 ≤ lambdaMSS G s`), proved from `1 ∈ 𝒱_s` and `S_β(1) = 0`. -/
theorem lambdaMSS_nonneg {N : ℕ} (G : GibbsData N) (s : ℕ) :
    0 ≤ lambdaMSS G s := by
  unfold lambdaMSS
  apply le_csSup
  · refine ⟨(N : ℝ), ?_⟩
    rintro r ⟨A, _, hAnorm, rfl⟩
    unfold mssThermalSize
    have hle := (totalSizeOp_bounds (jBeta G.ρQuarter A)).2
    have hbg := (totalSizeOp_bounds G.ρHalf).1
    have hhs : hsNormSq (jBeta G.ρQuarter A) = 1 := by
      unfold gibbsWightmanNormSq gibbsWightmanInner at hAnorm
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hAnorm
      exact hAnorm
    rw [hhs, mul_one] at hle
    linarith
  · refine ⟨1, ?_, ?_, (mssThermalSize_one G).symm⟩
    · have h1 : (1 : QubitOp N) = pauliString (fun _ ↦ 0) := by
        unfold pauliString; rw [← kronOp_one]; congr 1; funext _
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
      rw [h1]
      exact Submodule.subset_span ⟨fun _ ↦ 0, by simp [stringWeight], rfl⟩
    · unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_one, G.sq_half, G.trace_one,
        Complex.one_re]

/-- Static thermal-size bound for any sub-normalized operator `A ∈ 𝒱_s` with `‖A‖_{β,W}² ≤ 1`:
`S_β(A) ≤ Λ_β^{MSS}(s)` (zero laundered `hlead` hypothesis!). -/
theorem mssThermalSize_le_lambdaMSS_of_mem {N s : ℕ} (G : GibbsData N) {A : QubitOp N}
    (hA : A ∈ filtrationSubmodule N s) (hAnorm : gibbsWightmanNormSq G A ≤ 1) :
    mssThermalSize G A ≤ lambdaMSS G s := by
  have hΛnn := lambdaMSS_nonneg G s
  have hBbg := (totalSizeOp_bounds G.ρHalf).1
  by_cases h0 : gibbsWightmanNormSq G A = 0
  · have hA0 := eq_zero_of_gibbsWightmanNormSq_eq_zero G h0
    rw [hA0]; unfold mssThermalSize jBeta
    simp only [Matrix.mul_zero, Matrix.zero_mul, totalSizeOp, siteSizeOp, partialTraceSite,
      Finset.sum_const_zero, hsInner, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re]
    linarith
  · have hpos : 0 < gibbsWightmanNormSq G A :=
      lt_of_le_of_ne (gibbsWightmanNormSq_nonneg G A) (Ne.symm h0)
    set nrm : ℝ := Real.sqrt (gibbsWightmanNormSq G A)
    have hnrm_pos : 0 < nrm := Real.sqrt_pos.mpr hpos
    set A' : QubitOp N := ((nrm⁻¹ : ℝ) : ℂ) • A
    have hA'_mem : A' ∈ filtrationSubmodule N s := Submodule.smul_mem _ _ hA
    have hA'_norm : gibbsWightmanNormSq G A' = 1 := by
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner A'
      simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      have him : (gibbsWightmanInner G A A).im = 0 := by
        have hconj := gibbsWightmanInner_conj_symm G A A
        rw [Complex.star_def] at hconj
        have h1 := congrArg Complex.im hconj
        simp only [Complex.conj_im] at h1; linarith
      have hre : (G.ρHalf * Aᴴ * G.ρHalf * A).trace = (gibbsWightmanNormSq G A : ℂ) :=
        Complex.ext rfl (by simp [him])
      change (((nrm⁻¹ : ℝ) : ℂ) * (((nrm⁻¹ : ℝ) : ℂ) * (G.ρHalf * Aᴴ * G.ρHalf * A).trace)).re = 1
      rw [hre]
      have hsq : nrm ^ 2 = gibbsWightmanNormSq G A := Real.sq_sqrt hpos.le
      rw [← hsq]; push_cast
      have hneC : (nrm : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnrm_pos.ne'
      have h1 : (nrm : ℂ)⁻¹ * ((nrm : ℂ)⁻¹ * (nrm : ℂ) ^ 2) = 1 := by field_simp [hneC]
      rw [h1, Complex.one_re]
    have hle_Λ : mssThermalSize G A' ≤ lambdaMSS G s := by
      unfold lambdaMSS
      apply le_csSup
      · refine ⟨(N : ℝ), ?_⟩
        rintro r ⟨B, _, hBnorm, rfl⟩
        unfold mssThermalSize
        have hle := (totalSizeOp_bounds (jBeta G.ρQuarter B)).2
        have hhs : hsNormSq (jBeta G.ρQuarter B) = 1 := by
          unfold gibbsWightmanNormSq gibbsWightmanInner at hBnorm
          rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hBnorm
          exact hBnorm
        rw [hhs, mul_one] at hle; linarith
      · exact ⟨A', hA'_mem, hA'_norm, rfl⟩
    have hscale : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re =
        gibbsWightmanNormSq G A * (hsInner (jBeta G.ρQuarter A') (totalSizeOp (jBeta G.ρQuarter A'))).re := by
      have hA_eq : A = (nrm : ℂ) • A' := by
        dsimp only [A']; rw [smul_smul]
        have : (nrm : ℂ) * ((nrm⁻¹ : ℝ) : ℂ) = 1 := by
          push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnrm_pos.ne')
        rw [this, one_smul]
      have hj : jBeta G.ρQuarter A = (nrm : ℂ) • jBeta G.ρQuarter A' := by
        rw [hA_eq]; unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul]
      have hS : totalSizeOp ((nrm : ℂ) • jBeta G.ρQuarter A') =
          (nrm : ℂ) • totalSizeOp (jBeta G.ρQuarter A') := by
        unfold totalSizeOp siteSizeOp partialTraceSite
        simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, smul_sub]
        apply Finset.sum_congr rfl; intro x _
        congr 1; rw [smul_comm]
      rw [hj, hS]
      unfold hsInner
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
        smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      have hmul : (nrm : ℂ) * ((nrm : ℂ) * ((jBeta G.ρQuarter A')ᴴ * totalSizeOp (jBeta G.ρQuarter A')).trace) =
          ((gibbsWightmanNormSq G A : ℝ) : ℂ) *
            ((jBeta G.ρQuarter A')ᴴ * totalSizeOp (jBeta G.ρQuarter A')).trace := by
        rw [← Real.sq_sqrt hpos.le]; push_cast; ring
      rw [hmul, Complex.re_ofReal_mul]
    unfold mssThermalSize at hle_Λ ⊢
    rw [hscale]
    nlinarith

/-- **Item #4 — Genuine Concrete Lemma 4.2 on `mssThermalSize` & `lambdaMSS` (Eq. 4.3)**:
For ANY Hermitian `H ∈ filtrationSubmodule N r` (`1 ≤ r`), Hermitian `O ∈ filtrationSubmodule N s₀`
normalized with `‖O‖_{β,W}² = 1`, `M ≥ 1`, `β : ℝ`, and `t : ℝ`, letting
`G := concreteGibbsData hH β`, `s_M := s₀ + (M - 1) * (r - 1)`, and
`ε_M := Real.sqrt (gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t))`:
`mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤ lambdaMSS G s_M + 2 * N * ε_M + N * ε_M ^ 2`.
Zero laundered hypotheses! -/
theorem lemma_4_2_mss_thermal_size_concrete {N r s₀ M : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp N} (hH : H.IsHermitian) (hO : O.IsHermitian) (β t : ℝ)
    (hHf : H ∈ filtrationSubmodule N r) (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    let G := concreteGibbsData hH β
    let s_M : ℕ := s₀ + (M - 1) * (r - 1)
    let ε_M : ℝ := Real.sqrt (gibbsWightmanNormSq G
      (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t))
    mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
      lambdaMSS G s_M + 2 * (N : ℝ) * ε_M + (N : ℝ) * ε_M ^ 2 := by
  intro G s_M ε_M
  set A_M := lanczosTrunc hH β O M t
  set R_M := heisenbergEvol hH (t : ℂ) O - A_M
  set MA := jBeta G.ρQuarter A_M
  set MR := jBeta G.ρQuarter R_M
  have hsplit : heisenbergEvol hH (t : ℂ) O = A_M + R_M := by simp [R_M]
  have hJO : jBeta G.ρQuarter (heisenbergEvol hH (t : ℂ) O) = MA + MR := by
    unfold jBeta; rw [hsplit, Matrix.mul_add, Matrix.add_mul]
  have hSadd : totalSizeOp (MA + MR) = totalSizeOp MA + totalSizeOp MR := by
    unfold totalSizeOp siteSizeOp partialTraceSite
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add, add_sub_add_comm]
  have hexpand : (hsInner (jBeta G.ρQuarter (heisenbergEvol hH (t : ℂ) O))
      (totalSizeOp (jBeta G.ρQuarter (heisenbergEvol hH (t : ℂ) O)))).re =
      (hsInner MA (totalSizeOp MA)).re + 2 * (hsInner MA (totalSizeOp MR)).re +
      (hsInner MR (totalSizeOp MR)).re := by
    rw [hJO, hSadd]
    unfold hsInner
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
    simp only [Complex.add_re]
    have hsym := totalSizeOp_symm_re MA MR
    change (hsInner MA (totalSizeOp MA)).re + (hsInner MA (totalSizeOp MR)).re +
      ((hsInner MR (totalSizeOp MA)).re + (hsInner MR (totalSizeOp MR)).re) = _
    rw [← hsym]; ring
  have hAmem : A_M ∈ filtrationSubmodule N s_M :=
    lanczosTrunc_mem_filtration hr hM hH β t hHf hOf
  have hAnorm : gibbsWightmanNormSq G A_M ≤ 1 :=
    lanczosTrunc_wightmanNormSq_le_one hH hO β t hOnorm M
  have hlead : mssThermalSize G A_M ≤ lambdaMSS G s_M :=
    mssThermalSize_le_lambdaMSS_of_mem G hAmem hAnorm
  have hMA_norm : hsNormSq MA ≤ 1 := by
    unfold gibbsWightmanNormSq gibbsWightmanInner at hAnorm
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hAnorm
    exact hAnorm
  have hMR_norm : hsNormSq MR = ε_M ^ 2 := by
    have h1 : hsNormSq MR = gibbsWightmanNormSq G R_M := by
      unfold gibbsWightmanNormSq gibbsWightmanInner
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]; rfl
    rw [h1, Real.sq_sqrt (gibbsWightmanNormSq_nonneg G R_M)]
  have hSA_le : (hsInner MA (totalSizeOp MA)).re ≤ (N : ℝ) := by
    calc (hsInner MA (totalSizeOp MA)).re
        ≤ (N : ℝ) * hsNormSq MA := (totalSizeOp_bounds MA).2
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hMA_norm (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  have hSR_le : (hsInner MR (totalSizeOp MR)).re ≤ (N : ℝ) * ε_M ^ 2 := by
    rw [← hMR_norm]; exact (totalSizeOp_bounds MR).2
  have hcross : (hsInner MA (totalSizeOp MR)).re ≤ (N : ℝ) * ε_M := by
    have hcs := totalSizeOp_cauchy_schwarz MA MR
    have hprod : (hsInner MA (totalSizeOp MA)).re * (hsInner MR (totalSizeOp MR)).re ≤
        ((N : ℝ) * ε_M) ^ 2 := by
      calc (hsInner MA (totalSizeOp MA)).re * (hsInner MR (totalSizeOp MR)).re
          ≤ (N : ℝ) * ((N : ℝ) * ε_M ^ 2) :=
            mul_le_mul hSA_le hSR_le (totalSizeOp_bounds MR).1 (Nat.cast_nonneg N)
        _ = ((N : ℝ) * ε_M) ^ 2 := by ring
    have hsq : ((hsInner MA (totalSizeOp MR)).re) ^ 2 ≤ ((N : ℝ) * ε_M) ^ 2 := le_trans hcs hprod
    have hnn : 0 ≤ (N : ℝ) * ε_M := mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)
    calc (hsInner MA (totalSizeOp MR)).re
        ≤ |(hsInner MA (totalSizeOp MR)).re| := le_abs_self _
      _ = Real.sqrt (((hsInner MA (totalSizeOp MR)).re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (((N : ℝ) * ε_M) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (N : ℝ) * ε_M := Real.sqrt_sq hnn
  unfold mssThermalSize at hlead ⊢
  rw [hexpand]
  linarith

end ConcreteLemma42MSS

end KrylovChaos
