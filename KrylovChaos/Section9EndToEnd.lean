/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.GaussianSmearingBridge
import KrylovChaos.BimodalFullRank
import KrylovChaos.DoubleWellKrylovLimit
import KrylovChaos.DoubleWellTunneling
import KrylovChaos.TimeOrderedOTOC
import KrylovChaos.AllTimeLiebRobinson
import KrylovChaos.Milestone4Section9AppB
import Mathlib.Tactic

/-!
# Section 9 & Appendix B Concrete End-to-End Theorems

Establishes concrete operator-level and spectral theorems for Section 9 and Appendix B:
1. `concreteTwoTimeOTOC`, `concreteOTOC_gaussianSmearBochner_eq_2d_conv`,
   `prop_9_1_part1_concrete_2d_otoc_smearing`, and `prop_9_1_part1_geom_mean_sqrt_n`:
   exact 2D Gaussian convolution identity for `concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V`,
   finite-window OTOC Lyapunov preservation directly on `concreteOTOC`, and the geometric-mean
   Lanczos bound `(∏_{k=1}^n b_k)^(1/n) ≤ C √n` from Gaussian-smeared spectral moments.
2. `eq91BimodalProb`, `eq91BimodalGibbs`, `eq91WitnessOp`, `eq91Bimodal_mssThermalSize_lower`,
   `eq91Bimodal_lambdaMSS_lower`, and `prop_9_1_part2_eq91_violates_H2`:
   exact qubit-1-conditioned bimodal state `ρ_ε = (1 - ε) ρ + ε I / 2^N` (Eq. 9.1) as `GibbsData N`
   with 1-local witness `A = √2 |1⟩⟨1|_{x₀}` (`‖A‖_{ρ_ε,W} = 1`), giving
   `λ_{MSS}(ρ_ε, 1) ≥ ((N - 1)/4) * (1 - ε - 2 √(2 ε / 2^N))` and violating Hypothesis (H2)
   for every `δ ∈ [0, 1)`.
3. `doubleWellK0`, `doubleWellK1`, `doubleWell_lanczos_orthonormal`,
   `doubleWell_lanczos_tridiag_closure`, `doubleWell_krylov_complexity_from_lanczos`, and
   `lemma_B_1_bulk_eigenvalues_in_band`:
   explicit 2D orthonormal Lanczos basis `|K₀⟩, |K₁⟩` for `doubleWellTridiag D E_B`, derivation
   of `K(t) = sin²((E_- - E_+) t / 2)` from `doubleWellPsiEvol`, and Courant–Fischer localization
   of the remaining `D - 2` eigenvalues in `[E_B - 2, E_B + 2]`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section Prop91Part1Concrete2DAndGeomMean

/-- Concrete two-time thermal OTOC
`F_{W,V}(t₁, t₂) = Tr(J_β(W(t₁)) V J_β(W(t₂)) V)` on `QubitOp N`. -/
noncomputable def concreteTwoTimeOTOC {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (t₁ t₂ : ℝ) : ℂ :=
  Matrix.trace (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W) * V *
    jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W) * V)

lemma concreteTwoTimeOTOC_diag {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W V : QubitOp N) (t : ℝ) :
    concreteTwoTimeOTOC hH β W V t t = concreteOTOC hH β W V (t : ℂ) := by
  unfold concreteTwoTimeOTOC concreteOTOC; rfl

private lemma continuous_heisenbergEvol_entry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (W : QubitOp N) (i j : QubitIdx N) :
    Continuous (fun s : ℝ ↦ (heisenbergEvol hH (s : ℂ) W) i j) := by
  unfold heisenbergEvol complexPropagator hermFunc
  have hdiag : ∀ (c : ℂ), Continuous (fun s : ℝ ↦
      Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (c * (s : ℂ) * (hH.eigenvalues k : ℂ)))) := by
    intro c
    refine continuous_matrix fun a b ↦ ?_
    simp only [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp only [↓reduceIte]
      exact Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    · simp only [hab, ↓reduceIte]; exact continuous_const
  have hmat : Continuous (fun s : ℝ ↦
      ((hH.eigenvectorUnitary : QubitOp N) *
        Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues k : ℂ))) *
        (hH.eigenvectorUnitary : QubitOp N)ᴴ) * W *
      ((hH.eigenvectorUnitary : QubitOp N) *
        Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues k : ℂ))) *
        (hH.eigenvectorUnitary : QubitOp N)ᴴ)) := by
    have h1 : Continuous (fun s : ℝ ↦
        (hH.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (Complex.I * (s : ℂ) * (hH.eigenvalues k : ℂ))) *
          (hH.eigenvectorUnitary : QubitOp N)ᴴ) :=
      (continuous_const.mul (hdiag Complex.I)).mul continuous_const
    have h2 : Continuous (fun s : ℝ ↦
        (hH.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues k : ℂ))) *
          (hH.eigenvectorUnitary : QubitOp N)ᴴ) := by
      have hdiag2 : Continuous (fun s : ℝ ↦
          Matrix.diagonal (fun k : QubitIdx N ↦ Complex.exp (Complex.I * (-(s : ℂ)) * (hH.eigenvalues k : ℂ)))) := by
        refine continuous_matrix fun a b ↦ ?_
        simp only [Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab; simp only [↓reduceIte]
          exact Complex.continuous_exp.comp
            ((continuous_const.mul Complex.continuous_ofReal.neg).mul continuous_const)
        · simp only [hab, ↓reduceIte]; exact continuous_const
      exact (continuous_const.mul hdiag2).mul continuous_const
    exact (h1.mul continuous_const).mul h2
  exact (continuous_apply_apply i j).comp hmat

private lemma norm_heisenbergEvol_entry_le {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (W : QubitOp N) (s : ℝ) (i j : QubitIdx N) :
    ‖(heisenbergEvol hH (s : ℂ) W) i j‖ ≤ opNorm W := by
  have h1 : ‖(heisenbergEvol hH (s : ℂ) W) i j‖ ≤ opNorm (heisenbergEvol hH (s : ℂ) W) := by
    have hv := ContinuousLinearMap.le_opNorm (opToCLM (heisenbergEvol hH (s : ℂ) W))
      (EuclideanSpace.single j (1 : ℂ))
    have hunit : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (QubitIdx N))‖ = 1 := by
      simp
    rw [hunit, mul_one] at hv
    have hcoord : ‖(heisenbergEvol hH (s : ℂ) W) i j‖ ≤
        ‖opToCLM (heisenbergEvol hH (s : ℂ) W) (EuclideanSpace.single j (1 : ℂ))‖ := by
      have hi := PiLp.norm_apply_le (opToCLM (heisenbergEvol hH (s : ℂ) W)
        (EuclideanSpace.single j (1 : ℂ))) i
      simpa [opToCLM, Matrix.mulVec, dotProduct] using hi
    exact le_trans hcoord hv
  have h2 : opNorm (heisenbergEvol hH (s : ℂ) W) ≤ opNorm W := by
    have hunit : opNorm (heisenbergEvol hH (s : ℂ) W) = opNorm W :=
      opNorm_heisenbergEvol_real hH s W
    exact hunit.le
  exact le_trans h1 h2

private lemma integrable_gaussianKernel {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussianKernel σ) := by
  have hconst : Integrable (fun s : ℝ ↦ Real.exp (-(1 / (2 * σ ^ 2)) * s ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  exact (hconst.const_mul (1 / (Real.sqrt (2 * Real.pi) * σ))).congr (Eventually.of_forall fun s ↦ by
    unfold gaussianKernel
    rw [div_eq_mul_inv, mul_comm (Real.exp _), ← one_div]
    congr 1; congr 1; ring)

private lemma integrable_gaussianKernel_mul_heisenbergEvol_entry {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) {σ : ℝ} (hσ : 0 < σ) (W : QubitOp N) (i j : QubitIdx N) :
    Integrable (fun s : ℝ ↦ ((gaussianKernel σ s : ℝ) : ℂ) * (heisenbergEvol hH (s : ℂ) W) i j) := by
  have hg_int : Integrable (gaussianKernel σ) := integrable_gaussianKernel hσ
  refine (hg_int.const_mul (opNorm W)).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (by unfold gaussianKernel; fun_prop)).mul
      (continuous_heisenbergEvol_entry hH W i j)).aestronglyMeasurable
  · filter_upwards with s
    have hgnn : 0 ≤ gaussianKernel σ s := by unfold gaussianKernel; positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgnn, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_heisenbergEvol_entry_le hH W s i j) hgnn

/-- **Exact 2D Bochner-Convolution Identity for `concreteOTOC` (Proposition 9.1(1))**:
For every `σ > 0`, Hermitian `H : QubitOp N`, `W₀, V : QubitOp N`, and `β, t : ℝ`:
`concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V t =
  ∬ g_σ(s₁) g_σ(s₂) F_{W₀,V}(t + s₁, t + s₂) ds₁ ds₂`. -/
set_option maxHeartbeats 400000 in
theorem concreteOTOC_gaussianSmearBochner_eq_2d_conv {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) {σ : ℝ} (hσ : 0 < σ) (W₀ V : QubitOp N) (t : ℝ) :
    concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V (t : ℂ) =
      ∫ s₁ : ℝ, ((gaussianKernel σ s₁ : ℝ) : ℂ) *
        (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) *
          concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)) := by
  let L : QubitOp N := gibbsRhoQuarter hH β * complexPropagator hH (t : ℂ)
  let R : QubitOp N := complexPropagator hH (-(t : ℂ)) * gibbsRhoQuarter hH β * V
  have hLR : ∀ (A : QubitOp N),
      jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t : ℂ) A) * V = L * A * R := by
    intro A; unfold jBeta heisenbergEvol L R; simp only [Matrix.mul_assoc]
  have hLR_shift : ∀ (s : ℝ),
      L * heisenbergEvol hH (s : ℂ) W₀ * R =
      jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH ((t + s : ℝ) : ℂ) W₀) * V := by
    intro s
    rw [← hLR, Complex.ofReal_add, ← heisenbergEvol_add hH (t : ℂ) (s : ℂ) W₀]
  have htrace_expand : ∀ (A B : QubitOp N),
      Matrix.trace (L * A * R * (L * B * R)) =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N,
        ∑ l : QubitIdx N, ∑ p : QubitIdx N, ∑ q : QubitIdx N,
          ((L i j * R k l * L l p * R q i) * A j k * B p q) := by
    intro A B
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc ∑ l : QubitIdx N, (∑ k : QubitIdx N, (∑ j : QubitIdx N, L i j * A j k) * R k l) *
          (∑ q : QubitIdx N, (∑ p : QubitIdx N, L l p * B p q) * R q i)
        = ∑ l : QubitIdx N, ∑ k : QubitIdx N, ∑ j : QubitIdx N, ∑ q : QubitIdx N, ∑ p : QubitIdx N,
            ((L i j * R k l * L l p * R q i) * A j k * B p q) := by
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦
            Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by ring
      _ = ∑ j : QubitIdx N, ∑ k : QubitIdx N, ∑ l : QubitIdx N, ∑ p : QubitIdx N, ∑ q : QubitIdx N,
            ((L i j * R k l * L l p * R q i) * A j k * B p q) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_comm
  have hOTOC_lhs : concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V (t : ℂ) =
      Matrix.trace (L * gaussianSmearBochner hH σ W₀ * R * (L * gaussianSmearBochner hH σ W₀ * R)) := by
    unfold concreteOTOC; rw [hLR]
  have hOTOC_two : ∀ s₁ s₂ : ℝ, concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂) =
      Matrix.trace (L * heisenbergEvol hH (s₁ : ℂ) W₀ * R * (L * heisenbergEvol hH (s₂ : ℂ) W₀ * R)) := by
    intro s₁ s₂; unfold concreteTwoTimeOTOC; rw [hLR_shift s₁, hLR_shift s₂]
  have hint_e := integrable_gaussianKernel_mul_heisenbergEvol_entry hH hσ W₀
  have hinner_eq : ∀ s₁ : ℝ,
      (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)) =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N, ∑ k : QubitIdx N,
        ∑ l : QubitIdx N, ∑ p : QubitIdx N, ∑ q : QubitIdx N,
          ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
            (gaussianSmearBochner hH σ W₀) p q) := by
    intro s₁
    simp_rw [hOTOC_two s₁, htrace_expand, Finset.mul_sum]
    have hint6 : ∀ i j k l p q, Integrable (fun s₂ : ℝ ↦
        ((gaussianKernel σ s₂ : ℝ) : ℂ) *
          ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
            (heisenbergEvol hH (s₂ : ℂ) W₀) p q)) := fun i j k l p q ↦ by
      have hrew : (fun s₂ : ℝ ↦ ((gaussianKernel σ s₂ : ℝ) : ℂ) *
          ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
            (heisenbergEvol hH (s₂ : ℂ) W₀) p q)) =
          fun s₂ : ℝ ↦ ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k) *
            (((gaussianKernel σ s₂ : ℝ) : ℂ) * (heisenbergEvol hH (s₂ : ℂ) W₀) p q) := by
        funext s₂; ring
      rw [hrew]; exact (hint_e p q).const_mul _
    rw [integral_finset_sum _ fun i _ ↦ integrable_finset_sum _ fun j _ ↦
        integrable_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
        integrable_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finset_sum _ fun j _ ↦ integrable_finset_sum _ fun k _ ↦
        integrable_finset_sum _ fun l _ ↦ integrable_finset_sum _ fun p _ ↦
        integrable_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
        integrable_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_finset_sum _ fun l _ ↦ integrable_finset_sum _ fun p _ ↦
        integrable_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [integral_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [integral_finset_sum _ fun q _ ↦ hint6 i j k l p q]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hrew : (fun s₂ : ℝ ↦ ((gaussianKernel σ s₂ : ℝ) : ℂ) *
        ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
          (heisenbergEvol hH (s₂ : ℂ) W₀) p q)) =
        fun s₂ : ℝ ↦ ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k) *
          (((gaussianKernel σ s₂ : ℝ) : ℂ) * (heisenbergEvol hH (s₂ : ℂ) W₀) p q) := by
      funext s₂; ring
    rw [hrew, integral_const_mul]
    rfl
  rw [hOTOC_lhs, htrace_expand]
  simp_rw [hinner_eq, Finset.mul_sum]
  have hint_out6 : ∀ i j k l p q, Integrable (fun s₁ : ℝ ↦
      ((gaussianKernel σ s₁ : ℝ) : ℂ) *
        ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
          (gaussianSmearBochner hH σ W₀) p q)) := fun i j k l p q ↦ by
    have hrew : (fun s₁ : ℝ ↦ ((gaussianKernel σ s₁ : ℝ) : ℂ) *
        ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
          (gaussianSmearBochner hH σ W₀) p q)) =
        fun s₁ : ℝ ↦ ((L i j * R k l * L l p * R q i) * (gaussianSmearBochner hH σ W₀) p q) *
          (((gaussianKernel σ s₁ : ℝ) : ℂ) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k) := by
      funext s₁; ring
    rw [hrew]; exact (hint_e j k).const_mul _
  rw [integral_finset_sum _ fun i _ ↦ integrable_finset_sum _ fun j _ ↦
      integrable_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
      integrable_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finset_sum _ fun j _ ↦ integrable_finset_sum _ fun k _ ↦
      integrable_finset_sum _ fun l _ ↦ integrable_finset_sum _ fun p _ ↦
      integrable_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
      integrable_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finset_sum _ fun l _ ↦ integrable_finset_sum _ fun p _ ↦
      integrable_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [integral_finset_sum _ fun p _ ↦ integrable_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [integral_finset_sum _ fun q _ ↦ hint_out6 i j k l p q]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hrew : (fun s₁ : ℝ ↦ ((gaussianKernel σ s₁ : ℝ) : ℂ) *
      ((L i j * R k l * L l p * R q i) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k *
        (gaussianSmearBochner hH σ W₀) p q)) =
      fun s₁ : ℝ ↦ ((L i j * R k l * L l p * R q i) * (gaussianSmearBochner hH σ W₀) p q) *
        (((gaussianKernel σ s₁ : ℝ) : ℂ) * (heisenbergEvol hH (s₁ : ℂ) W₀) j k) := by
    funext s₁; ring
  rw [hrew, integral_const_mul]
  change (L i j * R k l * L l p * R q i) * (gaussianSmearBochner hH σ W₀) j k *
      (gaussianSmearBochner hH σ W₀) p q =
    L i j * R k l * L l p * R q i * (gaussianSmearBochner hH σ W₀) p q *
      (gaussianSmearBochner hH σ W₀) j k
  ring

/-- Real-part 2D Gaussian convolution identity for `concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V t`. -/
set_option maxHeartbeats 400000 in
theorem concreteOTOC_gaussianSmearBochner_re_eq_2d_conv {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) {σ : ℝ} (hσ : 0 < σ) (W₀ V : QubitOp N) (t : ℝ) :
    (concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V (t : ℂ)).re =
      ∫ s₁ : ℝ, gaussianKernel σ s₁ *
        (∫ s₂ : ℝ, gaussianKernel σ s₂ *
          (concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re) := by
  have hg_int : Integrable (gaussianKernel σ) := integrable_gaussianKernel hσ
  have hcont_two : Continuous (fun p : ℝ × ℝ ↦ concreteTwoTimeOTOC hH β W₀ V p.1 p.2) := by
    unfold concreteTwoTimeOTOC
    have htr : Continuous (fun M : QubitOp N ↦ Matrix.trace M) :=
      continuous_finset_sum _ fun i _ ↦ continuous_apply_apply i i
    have hj : Continuous (fun s : ℝ ↦ jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (s : ℂ) W₀)) := by
      unfold jBeta
      refine (continuous_const.mul ?_).mul continuous_const
      exact continuous_matrix fun i j ↦ continuous_heisenbergEvol_entry hH W₀ i j
    exact htr.comp ((((hj.comp continuous_fst).mul continuous_const).mul
      (hj.comp continuous_snd)).mul continuous_const)
  have hbdd_two : ∃ M : ℝ, 0 ≤ M ∧ ∀ t₁ t₂ : ℝ, ‖concreteTwoTimeOTOC hH β W₀ V t₁ t₂‖ ≤ M := by
    let G := concreteGibbsData hH β
    refine ⟨(2 : ℝ) ^ N * (opNorm G.ρQuarter) ^ 4 * (opNorm W₀) ^ 2 * (opNorm V) ^ 2, by positivity,
      fun t₁ t₂ ↦ ?_⟩
    unfold concreteTwoTimeOTOC
    have htr_le : ∀ A : QubitOp N, ‖Matrix.trace A‖ ≤ (2 : ℝ) ^ N * opNorm A := fun A ↦ by
      unfold Matrix.trace Matrix.diag
      calc ‖∑ i : QubitIdx N, A i i‖ ≤ ∑ i : QubitIdx N, ‖A i i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : QubitIdx N, opNorm A := Finset.sum_le_sum fun i _ ↦ by
            have hv := ContinuousLinearMap.le_opNorm (opToCLM A) (EuclideanSpace.single i (1 : ℂ))
            have hu : ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (QubitIdx N))‖ = 1 := by
              simp
            rw [hu, mul_one] at hv
            exact le_trans (by simpa [opToCLM, Matrix.mulVec, dotProduct] using
              PiLp.norm_apply_le (opToCLM A (EuclideanSpace.single i (1 : ℂ))) i) hv
        _ = (2 : ℝ) ^ N * opNorm A := by
            simp [Fintype.card_fun, Fintype.card_fin]
    have hj_le : ∀ s : ℝ, opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (s : ℂ) W₀)) ≤
        (opNorm G.ρQuarter) ^ 2 * opNorm W₀ := fun s ↦ by
      unfold jBeta
      calc opNorm (gibbsRhoQuarter hH β * heisenbergEvol hH (s : ℂ) W₀ * gibbsRhoQuarter hH β)
          ≤ opNorm (gibbsRhoQuarter hH β * heisenbergEvol hH (s : ℂ) W₀) * opNorm (gibbsRhoQuarter hH β) :=
            opNorm_mul_le _ _
        _ ≤ (opNorm (gibbsRhoQuarter hH β) * opNorm (heisenbergEvol hH (s : ℂ) W₀)) * opNorm (gibbsRhoQuarter hH β) :=
            mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
        _ = (opNorm G.ρQuarter) ^ 2 * opNorm W₀ := by
            rw [opNorm_heisenbergEvol_real hH s W₀]; change _ = (opNorm (gibbsRhoQuarter hH β)) ^ 2 * opNorm W₀; ring
    refine le_trans (htr_le _) ?_
    have hmul : opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V *
        jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V) ≤
        ((opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V) * ((opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V) := by
      have h1 : opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V) ≤
          (opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V :=
        le_trans (opNorm_mul_le _ _) (mul_le_mul_of_nonneg_right (hj_le t₁) (opNorm_nonneg _))
      have h2 : opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V) ≤
          (opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V :=
        le_trans (opNorm_mul_le _ _) (mul_le_mul_of_nonneg_right (hj_le t₂) (opNorm_nonneg _))
      calc opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V *
            jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V)
          = opNorm ((jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V) *
            (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V)) := by
              simp only [Matrix.mul_assoc]
        _ ≤ opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V) *
            opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V) :=
              opNorm_mul_le _ _
        _ ≤ _ := mul_le_mul h1 h2 (opNorm_nonneg _)
            (mul_nonneg (mul_nonneg (sq_nonneg _) (opNorm_nonneg _)) (opNorm_nonneg _))
    calc (2 : ℝ) ^ N * opNorm (jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₁ : ℂ) W₀) * V *
            jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (t₂ : ℂ) W₀) * V)
        ≤ (2 : ℝ) ^ N * (((opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V) *
            ((opNorm G.ρQuarter) ^ 2 * opNorm W₀ * opNorm V)) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (2 : ℝ) ^ N * (opNorm G.ρQuarter) ^ 4 * (opNorm W₀) ^ 2 * (opNorm V) ^ 2 := by ring
  rcases hbdd_two with ⟨M, hM_nn, hM_bd⟩
  have hint_in : ∀ s₁ : ℝ, Integrable (fun s₂ : ℝ ↦
      ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)) := fun s₁ ↦ by
    refine (hg_int.const_mul M).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp (by unfold gaussianKernel; fun_prop)).mul
        (hcont_two.comp (continuous_const.prodMk (continuous_const.add continuous_id)))).aestronglyMeasurable
    · filter_upwards with s₂
      have hgnn : 0 ≤ gaussianKernel σ s₂ := by unfold gaussianKernel; positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgnn, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM_bd _ _) hgnn
  have hint_out : Integrable (fun s₁ : ℝ ↦ ((gaussianKernel σ s₁ : ℝ) : ℂ) *
      (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂))) := by
    have hcont_in : Continuous (fun s₁ : ℝ ↦
        ∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)) := by
      refine continuous_of_dominated
        (bound := fun s₂ : ℝ ↦ gaussianKernel σ s₂ * M) ?_ ?_ (hg_int.mul_const M) ?_
      · intro s₁; exact (hint_in s₁).aestronglyMeasurable
      · intro s₁; filter_upwards with s₂
        have hgnn : 0 ≤ gaussianKernel σ s₂ := by unfold gaussianKernel; positivity
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgnn]
        exact mul_le_mul_of_nonneg_left (hM_bd _ _) hgnn
      · filter_upwards with s₂
        exact continuous_const.mul
          (hcont_two.comp ((continuous_const.add continuous_id).prodMk continuous_const))
    refine (hg_int.const_mul M).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp (by unfold gaussianKernel; fun_prop)).mul
        hcont_in).aestronglyMeasurable
    · filter_upwards with s₁
      have hgnn : 0 ≤ gaussianKernel σ s₁ := by unfold gaussianKernel; positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgnn, mul_comm]
      have hbd_in : ‖∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) *
          concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)‖ ≤ M := by
        calc ‖∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)‖
            ≤ ∫ s₂ : ℝ, ‖((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ s₂ : ℝ, gaussianKernel σ s₂ * M := by
              refine integral_mono (hint_in s₁).norm (hg_int.mul_const M) fun s₂ ↦ ?_
              have hgnn2 : 0 ≤ gaussianKernel σ s₂ := by unfold gaussianKernel; positivity
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgnn2]
              exact mul_le_mul_of_nonneg_left (hM_bd _ _) hgnn2
          _ = M := by rw [integral_mul_const, integral_gaussianKernel_eq_one hσ, one_mul]
      exact mul_le_mul_of_nonneg_right hbd_in hgnn
  rw [concreteOTOC_gaussianSmearBochner_eq_2d_conv hH β hσ W₀ V t]
  change Complex.reCLM (∫ s₁ : ℝ, ((gaussianKernel σ s₁ : ℝ) : ℂ) *
      (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂))) = _
  rw [← Complex.reCLM.integral_comp_comm hint_out]
  refine integral_congr_ae (Eventually.of_forall fun s₁ ↦ ?_)
  change (((gaussianKernel σ s₁ : ℝ) : ℂ) *
      (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂))).re = _
  rw [Complex.re_ofReal_mul]
  congr 1
  change Complex.reCLM (∫ s₂ : ℝ, ((gaussianKernel σ s₂ : ℝ) : ℂ) *
      concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)) = _
  rw [← Complex.reCLM.integral_comp_comm (hint_in s₁)]
  refine integral_congr_ae (Eventually.of_forall fun s₂ ↦ ?_)
  change (((gaussianKernel σ s₂ : ℝ) : ℂ) * concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re = _
  rw [Complex.re_ofReal_mul]

/-- **Proposition 9.1(1) — Concrete 2D Finite-Window OTOC Lyapunov Preservation**:
Applies `concreteOTOC_gaussianSmearBochner_re_eq_2d_conv` directly to `prop_9_1_part1_2d_finite_window_otoc`
so the finite-window OTOC Lyapunov bound holds directly on `concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V t`. -/
set_option maxHeartbeats 400000 in
theorem prop_9_1_part1_concrete_2d_otoc_smearing {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (W₀ V : QubitOp N) {σ Δt lamL F_d ε M_bound C_R t : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lamL) (hΔ : σ ^ 2 * (lamL / 2) ≤ Δt)
    (hM : 0 ≤ M_bound) (hCR : 0 ≤ C_R)
    (hF_bdd : ∀ t₁ t₂ : ℝ, |(concreteTwoTimeOTOC hH β W₀ V t₁ t₂).re| ≤ M_bound)
    (hF_win : ∀ s₁ s₂ : ℝ, |s₁| ≤ Δt → |s₂| ≤ Δt →
      |(concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re -
        (F_d - ε * Real.exp (lamL * (t + (s₁ + s₂) / 2)))| ≤ C_R) :
    |(concreteOTOC hH β (gaussianSmearBochner hH σ W₀) V (t : ℂ)).re -
      (F_d - ε * Real.exp (σ ^ 2 * lamL ^ 2 / 4) * Real.exp (lamL * t))| ≤
      C_R +
      2 * (M_bound + |F_d|) * Real.exp (-(Δt ^ 2) / (2 * σ ^ 2)) +
      2 * |ε| * Real.exp (lamL * t) * Real.exp (σ ^ 2 * lamL ^ 2 / 4) *
        Real.exp (-((Δt - σ ^ 2 * (lamL / 2)) ^ 2) / (2 * σ ^ 2)) := by
  rw [concreteOTOC_gaussianSmearBochner_re_eq_2d_conv hH β hσ W₀ V t]
  have hcont_two : Continuous (fun p : ℝ × ℝ ↦ (concreteTwoTimeOTOC hH β W₀ V p.1 p.2).re) := by
    refine Complex.continuous_re.comp ?_
    unfold concreteTwoTimeOTOC
    have htr : Continuous (fun M : QubitOp N ↦ Matrix.trace M) :=
      continuous_finset_sum _ fun i _ ↦ continuous_apply_apply i i
    have hj : Continuous (fun s : ℝ ↦ jBeta (gibbsRhoQuarter hH β) (heisenbergEvol hH (s : ℂ) W₀)) := by
      unfold jBeta
      refine (continuous_const.mul ?_).mul continuous_const
      exact continuous_matrix fun i j ↦ continuous_heisenbergEvol_entry hH W₀ i j
    exact htr.comp ((((hj.comp continuous_fst).mul continuous_const).mul
      (hj.comp continuous_snd)).mul continuous_const)
  have hg_int : Integrable (gaussianKernel σ) := integrable_gaussianKernel hσ
  have hF_meas : ∀ s₁ : ℝ, AEStronglyMeasurable
      (fun s₂ : ℝ ↦ (concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re) volume := fun s₁ ↦
    (hcont_two.comp (continuous_const.prodMk (continuous_const.add continuous_id))).aestronglyMeasurable
  have hF_outer_meas : AEStronglyMeasurable
      (fun s₁ : ℝ ↦ ∫ s₂ : ℝ, gaussianKernel σ s₂ *
        (concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re) volume := by
    have hcont_out : Continuous (fun s₁ : ℝ ↦ ∫ s₂ : ℝ, gaussianKernel σ s₂ *
        (concreteTwoTimeOTOC hH β W₀ V (t + s₁) (t + s₂)).re) := by
      refine continuous_of_dominated (bound := fun s₂ : ℝ ↦ gaussianKernel σ s₂ * M_bound)
        ?_ ?_ (hg_int.mul_const M_bound) ?_
      · intro s₁
        exact ((by unfold gaussianKernel; fun_prop : Continuous _).aestronglyMeasurable).mul (hF_meas s₁)
      · intro s₁; filter_upwards with s₂
        have hgnn : 0 ≤ gaussianKernel σ s₂ := by unfold gaussianKernel; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgnn]
        exact mul_le_mul_of_nonneg_left (hF_bdd _ _) hgnn
      · filter_upwards with s₂
        exact continuous_const.mul
          (hcont_two.comp ((continuous_const.add continuous_id).prodMk continuous_const))
    exact hcont_out.aestronglyMeasurable
  exact prop_9_1_part1_2d_finite_window_otoc hσ hlam hΔ hM hCR
    (fun t₁ t₂ ↦ (concreteTwoTimeOTOC hH β W₀ V t₁ t₂).re)
    hF_meas hF_outer_meas hF_bdd hF_win

private lemma jacobiMat_entry_nonneg {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (i j : Fin D) :
    0 ≤ jacobiMat D b i j := by
  unfold jacobiMat
  simp only [Matrix.of_apply]
  split_ifs <;> [exact hb _; exact hb _; exact le_rfl]

private lemma jacobiMat_pow_entry_nonneg {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ∀ (m : ℕ) (i j : Fin D), 0 ≤ ((jacobiMat D b) ^ m) i j
  | 0, i, j => by rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | m + 1, i, j => by
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ ↦
        mul_nonneg (jacobiMat_pow_entry_nonneg b hb m i k) (jacobiMat_entry_nonneg b hb k j)

private lemma jacobiMat_pow_asc_lower {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ∀ (m : ℕ) (hm : m < D),
      ∏ k ∈ Finset.range m, b (k + 1) ≤ ((jacobiMat D b) ^ m) ⟨0, by omega⟩ ⟨m, hm⟩
  | 0, hm => by simp [pow_zero]
  | m + 1, hm => by
      rw [Finset.prod_range_succ, pow_succ, Matrix.mul_apply]
      have hterm := Finset.single_le_sum
        (f := fun k : Fin D ↦ ((jacobiMat D b) ^ m) ⟨0, by omega⟩ k * jacobiMat D b k ⟨m + 1, hm⟩)
        (fun k _ ↦ mul_nonneg (jacobiMat_pow_entry_nonneg b hb m _ k) (jacobiMat_entry_nonneg b hb k _))
        (Finset.mem_univ ⟨m, by omega⟩)
      have hstep : jacobiMat D b ⟨m, by omega⟩ ⟨m + 1, hm⟩ = b (m + 1) := by
        unfold jacobiMat; simp
      rw [hstep] at hterm
      exact le_trans (mul_le_mul_of_nonneg_right (jacobiMat_pow_asc_lower b hb m (by omega)) (hb (m + 1))) hterm

private lemma jacobiMat_pow_desc_lower {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ∀ (m : ℕ) (hm : m < D),
      ∏ k ∈ Finset.range m, b (k + 1) ≤ ((jacobiMat D b) ^ m) ⟨m, hm⟩ ⟨0, by omega⟩
  | 0, hm => by simp [pow_zero]
  | m + 1, hm => by
      rw [Finset.prod_range_succ, pow_succ', Matrix.mul_apply]
      have hterm := Finset.single_le_sum
        (f := fun k : Fin D ↦ jacobiMat D b ⟨m + 1, hm⟩ k * ((jacobiMat D b) ^ m) k ⟨0, by omega⟩)
        (fun k _ ↦ mul_nonneg (jacobiMat_entry_nonneg b hb _ k) (jacobiMat_pow_entry_nonneg b hb m k _))
        (Finset.mem_univ ⟨m, by omega⟩)
      have hstep : jacobiMat D b ⟨m + 1, hm⟩ ⟨m, by omega⟩ = b (m + 1) := by
        unfold jacobiMat; simp only [Matrix.of_apply]
        rw [if_neg (by omega), if_pos rfl]
      rw [hstep] at hterm
      have hmul : (∏ k ∈ Finset.range m, b (k + 1)) * b (m + 1) ≤
          b (m + 1) * ((jacobiMat D b) ^ m) ⟨m, by omega⟩ ⟨0, by omega⟩ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (jacobiMat_pow_desc_lower b hb m (by omega)) (hb (m + 1))
      exact le_trans hmul hterm

private lemma jacobiMat_pow_two_n_ge_prod_sq (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (n : ℕ) :
    (∏ k ∈ Finset.range n, b (k + 1)) ^ 2 ≤
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
  have hpow : (jacobiMat (2 * n + 1) b) ^ (2 * n) =
      (jacobiMat (2 * n + 1) b) ^ n * (jacobiMat (2 * n + 1) b) ^ n := by
    rw [two_mul, pow_add]
  rw [hpow, Matrix.mul_apply]
  have hterm := Finset.single_le_sum
    (f := fun k : Fin (2 * n + 1) ↦
      ((jacobiMat (2 * n + 1) b) ^ n) ⟨0, Nat.succ_pos _⟩ k *
      ((jacobiMat (2 * n + 1) b) ^ n) k ⟨0, Nat.succ_pos _⟩)
    (fun k _ ↦ mul_nonneg (jacobiMat_pow_entry_nonneg b hb n _ k)
      (jacobiMat_pow_entry_nonneg b hb n k _))
    (Finset.mem_univ ⟨n, by omega⟩)
  have h1 := jacobiMat_pow_asc_lower (D := 2 * n + 1) b hb n (by omega)
  have h2 := jacobiMat_pow_desc_lower (D := 2 * n + 1) b hb n (by omega)
  have hpnn : 0 ≤ ∏ k ∈ Finset.range n, b (k + 1) := Finset.prod_nonneg fun k _ ↦ hb (k + 1)
  rw [sq]
  exact le_trans (mul_le_mul h1 h2 hpnn (jacobiMat_pow_entry_nonneg b hb n _ _)) hterm

/-- **Proposition 9.1(1) — Geometric-Mean Sublinear Lanczos Bound `(∏_{k=1}^n b_k)^(1/n) ≤ C √n`**:
For ANY finite spectral measure `μ` on `ℝ`, ANY smearing width `σ > 0`, and Lanczos coefficients `b`
matching the even moments of `μ_σ = exp(-σ² ω²) dμ`, for EVERY `n ≥ 1`:
`(∏_{k=1}^n b_k) ^ (1 / n) ≤ (√(μ(ℝ) + 1) / (σ √e)) * √n`. -/
theorem prop_9_1_part1_geom_mean_sqrt_n (μ : Measure ℝ) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : 0 < σ) (b : ℕ → ℝ) (hb0 : 0 ≤ b 0) (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      let μ_σ := μ.withDensity (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)))
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ_σ)
    {n : ℕ} (hn : 1 ≤ n) :
    (∏ k ∈ Finset.range n, b (k + 1)) ^ ((1 : ℝ) / (n : ℝ)) ≤
      (Real.sqrt ((μ Set.univ).toReal + 1) / (σ * Real.sqrt (Real.exp 1))) * Real.sqrt (n : ℝ) := by
  have hb_nn : ∀ k, 0 ≤ b k := fun k ↦ by
    cases k with
    | zero => exact hb0
    | succ m => exact (hb_pos (m + 1) (by omega)).le
  set μ_σ : Measure ℝ := μ.withDensity (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpt_bd : ∀ ω : ℝ, ω ^ (2 * n) * Real.exp (-(σ ^ 2) * ω ^ 2) ≤
      ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n := by
    intro ω
    set x : ℝ := σ ^ 2 * ω ^ 2
    have hx_nn : 0 ≤ x := by dsimp only [x]; positivity
    have hxn : x ^ n * Real.exp (-x) ≤ ((n : ℝ) / Real.exp 1) ^ n := by
      have h1 : x / (n : ℝ) ≤ Real.exp (x / (n : ℝ) - 1) := by
        have := Real.add_one_le_exp (x / (n : ℝ) - 1); linarith
      have h2 : (x / (n : ℝ)) ^ n ≤ (Real.exp (x / (n : ℝ) - 1)) ^ n :=
        pow_le_pow_left₀ (by positivity) h1 n
      have h3 : (Real.exp (x / (n : ℝ) - 1)) ^ n = Real.exp x * (Real.exp 1)⁻¹ ^ n := by
        rw [← Real.exp_nat_mul]
        have harg : (n : ℝ) * (x / (n : ℝ) - 1) = x + -(n : ℝ) := by
          field_simp [hn_pos.ne']
        rw [harg, Real.exp_add, show -(n : ℝ) = (n : ℝ) * (-1) by ring,
          Real.exp_nat_mul, Real.exp_neg]
      rw [h3, div_pow] at h2
      have h4 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (n : ℝ) ^ n * Real.exp (-x) by positivity)
      have hlhs : x ^ n / (n : ℝ) ^ n * ((n : ℝ) ^ n * Real.exp (-x)) = x ^ n * Real.exp (-x) := by
        have hnn : (n : ℝ) ^ n ≠ 0 := by positivity
        field_simp [hnn]
      have hrhs : Real.exp x * (Real.exp 1)⁻¹ ^ n * ((n : ℝ) ^ n * Real.exp (-x)) =
          ((n : ℝ) / Real.exp 1) ^ n := by
        have hcancel : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rw [div_pow, inv_pow]
        calc Real.exp x * ((Real.exp 1) ^ n)⁻¹ * ((n : ℝ) ^ n * Real.exp (-x))
            = (Real.exp x * Real.exp (-x)) * ((n : ℝ) ^ n * ((Real.exp 1) ^ n)⁻¹) := by ring
          _ = 1 * ((n : ℝ) ^ n / (Real.exp 1) ^ n) := by rw [hcancel, div_eq_mul_inv]
          _ = (n : ℝ) ^ n / (Real.exp 1) ^ n := one_mul _
      linarith
    have hrew : ω ^ (2 * n) * Real.exp (-(σ ^ 2) * ω ^ 2) = (x ^ n * Real.exp (-x)) / (σ ^ 2) ^ n := by
      dsimp only [x]
      have hσne : (σ ^ 2) ^ n ≠ 0 := by positivity
      rw [mul_pow, pow_mul, neg_mul]
      field_simp [hσne]
    rw [hrew]
    calc (x ^ n * Real.exp (-x)) / (σ ^ 2) ^ n
        ≤ ((n : ℝ) / Real.exp 1) ^ n / (σ ^ 2) ^ n := div_le_div_of_nonneg_right hxn (by positivity)
      _ = ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n := by rw [← div_pow, div_div]
  set B : ℝ := ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n
  have hB_pos : 0 < B := by dsimp only [B]; positivity
  have hmeas_g : Measurable (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_id.pow_const 2)))
  have hmeas_pow : Measurable (fun ω : ℝ ↦ ENNReal.ofReal (ω ^ (2 * n))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const (2 * n))
  have hlint : ∫⁻ ω, ENNReal.ofReal (ω ^ (2 * n)) ∂μ_σ ≤ ENNReal.ofReal (((μ Set.univ).toReal + 1) * B) := by
    dsimp only [μ_σ]
    rw [lintegral_withDensity_eq_lintegral_mul₀ hmeas_g.aemeasurable hmeas_pow.aemeasurable]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)) * ENNReal.ofReal (ω ^ (2 * n)) ∂μ
        ≤ ∫⁻ _ω, ENNReal.ofReal B ∂μ := by
          refine lintegral_mono fun ω ↦ ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
          exact ENNReal.ofReal_le_ofReal (hpt_bd ω)
      _ = ENNReal.ofReal B * μ Set.univ := lintegral_const _
      _ = ENNReal.ofReal (B * (μ Set.univ).toReal) := by
          rw [ENNReal.ofReal_mul hB_pos.le, ENNReal.ofReal_toReal (measure_ne_top μ Set.univ)]
      _ ≤ ENNReal.ofReal (((μ Set.univ).toReal + 1) * B) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
  have hint_pow : ∫ ω : ℝ, ω ^ (2 * n) ∂μ_σ ≤ ((μ Set.univ).toReal + 1) * B := by
    have hnn : ∀ ω : ℝ, 0 ≤ ω ^ (2 * n) := fun ω ↦ by rw [pow_mul]; exact pow_nonneg (sq_nonneg ω) n
    have h_eq : ∫ ω : ℝ, ω ^ (2 * n) ∂μ_σ = (∫⁻ ω, ENNReal.ofReal (ω ^ (2 * n)) ∂μ_σ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
        (measurable_id.pow_const (2 * n)).aestronglyMeasurable
    rw [h_eq]
    have hfin : ENNReal.ofReal (((μ Set.univ).toReal + 1) * B) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (∫⁻ ω, ENNReal.ofReal (ω ^ (2 * n)) ∂μ_σ).toReal
        ≤ (ENNReal.ofReal (((μ Set.univ).toReal + 1) * B)).toReal := ENNReal.toReal_mono hfin hlint
      _ = ((μ Set.univ).toReal + 1) * B := ENNReal.toReal_ofReal (by positivity)
  have hprod_sq : (∏ k ∈ Finset.range n, b (k + 1)) ^ 2 ≤ ((μ Set.univ).toReal + 1) * B := by
    calc (∏ k ∈ Finset.range n, b (k + 1)) ^ 2
        ≤ ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ :=
          jacobiMat_pow_two_n_ge_prod_sq b hb_nn n
      _ = ∫ ω : ℝ, ω ^ (2 * n) ∂μ_σ := hmom_eq n
      _ ≤ ((μ Set.univ).toReal + 1) * B := hint_pow
  set P : ℝ := ∏ k ∈ Finset.range n, b (k + 1)
  have hP_nn : 0 ≤ P := Finset.prod_nonneg fun k _ ↦ hb_nn (k + 1)
  set M1 : ℝ := (μ Set.univ).toReal + 1
  have hM1_ge1 : (1 : ℝ) ≤ M1 := by dsimp only [M1]; linarith [ENNReal.toReal_nonneg (a := μ Set.univ)]
  have hrpow := Real.rpow_le_rpow (sq_nonneg P) hprod_sq (show 0 ≤ (1 : ℝ) / (2 * (n : ℝ)) by positivity)
  have hlhs_rpow : (P ^ 2) ^ ((1 : ℝ) / (2 * (n : ℝ))) = P ^ ((1 : ℝ) / (n : ℝ)) := by
    rw [← Real.rpow_natCast P 2, ← Real.rpow_mul hP_nn]
    congr 1; push_cast; field_simp [hn_pos.ne']
  have hB_rpow : B ^ ((1 : ℝ) / (2 * (n : ℝ))) =
      Real.sqrt (n : ℝ) / (σ * Real.sqrt (Real.exp 1)) := by
    dsimp only [B]
    rw [← Real.rpow_natCast _ n, ← Real.rpow_mul (by positivity),
      show (n : ℝ) * (1 / (2 * (n : ℝ))) = (1 / 2 : ℝ) by field_simp [hn_pos.ne'],
      ← Real.sqrt_eq_rpow, Real.sqrt_div hn_pos.le, Real.sqrt_mul (Real.exp_pos 1).le,
      Real.sqrt_sq hσ.le, mul_comm (Real.sqrt (Real.exp 1))]
  have hM1_rpow : M1 ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ Real.sqrt M1 := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow_of_exponent_le hM1_ge1 ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
    simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden
  rw [hlhs_rpow, Real.mul_rpow (by linarith) hB_pos.le, hB_rpow] at hrpow
  calc P ^ ((1 : ℝ) / (n : ℝ))
      ≤ M1 ^ ((1 : ℝ) / (2 * (n : ℝ))) * (Real.sqrt (n : ℝ) / (σ * Real.sqrt (Real.exp 1))) := hrpow
    _ ≤ Real.sqrt M1 * (Real.sqrt (n : ℝ) / (σ * Real.sqrt (Real.exp 1))) :=
        mul_le_mul_of_nonneg_right hM1_rpow (by positivity)
    _ = (Real.sqrt M1 / (σ * Real.sqrt (Real.exp 1))) * Real.sqrt (n : ℝ) := by ring

end Prop91Part1Concrete2DAndGeomMean

section Prop91Part2Eq91Bimodal

/-- Bit-flip on site `x` of `QubitIdx N`. -/
private def eq91Flip {N : ℕ} (x : Fin N) (s : QubitIdx N) : QubitIdx N :=
  Function.update s x (1 - s x)

private lemma eq91Flip_eq91Flip {N : ℕ} (x : Fin N) (s : QubitIdx N) :
    eq91Flip x (eq91Flip x s) = s := by
  funext y; unfold eq91Flip
  by_cases hy : y = x
  · subst hy; simp only [Function.update_self]
    generalize hb : s y = b; fin_cases b <;> simp
  · simp [Function.update_of_ne hy]

private lemma eq91Flip_ne_self {N : ℕ} (x : Fin N) (s : QubitIdx N) :
    eq91Flip x s ≠ s := by
  intro h
  have hx := congrFun h x
  unfold eq91Flip at hx; simp only [Function.update_self] at hx
  generalize hb : s x = b; rw [hb] at hx; fin_cases b <;> simp_all

/-- The unique peak basis state `|1⟩_{x₀} ⊗ |0⋯0⟩_{y ≠ x₀}` in Eq. (9.1). -/
def eq91PeakIdx (N : ℕ) (x₀ : Fin N) : QubitIdx N :=
  Function.update (allZeroIdx N) x₀ 1

/-- Diagonal probabilities of the exact Eq. (9.1) qubit-`x₀`-conditioned bimodal state
`ρ_ε = (1 - ε) ((1/2)|0⟩⟨0|_{x₀} ⊗ I/2^{N-1} + (1/2)|1⟩⟨1|_{x₀} ⊗ |0⋯0⟩⟨0⋯0|) + ε I/2^N`:
- if `s x₀ = 0`: `1 / 2^N`
- if `s = eq91PeakIdx N x₀`: `(1 - ε) / 2 + ε / 2^N`
- if `s x₀ = 1` and `s ≠ eq91PeakIdx N x₀`: `ε / 2^N`. -/
noncomputable def eq91BimodalProb (N : ℕ) (x₀ : Fin N) (ε : ℝ) (s : QubitIdx N) : ℝ :=
  if s x₀ = 0 then 1 / (2 : ℝ) ^ N
  else if s = eq91PeakIdx N x₀ then (1 - ε) / 2 + ε / (2 : ℝ) ^ N
  else ε / (2 : ℝ) ^ N

lemma eq91BimodalProb_pos {N : ℕ} (x₀ : Fin N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (s : QubitIdx N) : 0 < eq91BimodalProb N x₀ ε s := by
  unfold eq91BimodalProb
  split_ifs
  · positivity
  · have h1 : 0 < (1 - ε) / 2 := by linarith
    have h2 : 0 < ε / (2 : ℝ) ^ N := by positivity
    linarith
  · positivity

private lemma card_qubitIdx_at_site {N : ℕ} (x₀ : Fin N) (v : Fin 2) :
    (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = v)).card = 2 ^ (N - 1) := by
  have h1 : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card =
      (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1)).card := by
    refine Finset.card_bij (fun s _ ↦ eq91Flip x₀ s) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      simp [eq91Flip, hs]
    · intro s₁ _ s₂ _ h
      have := congrArg (eq91Flip x₀) h
      rwa [eq91Flip_eq91Flip, eq91Flip_eq91Flip] at this
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine ⟨eq91Flip x₀ t, ?_, eq91Flip_eq91Flip x₀ t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [eq91Flip, ht]
  have htot : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card +
      (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1)).card = 2 ^ N := by
    have hdisj : Disjoint (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0))
        (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1)) := by
      rw [Finset.disjoint_left]; intro s h0 h1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
      rw [h0] at h1; exact absurd h1 (by decide)
    have hunion : Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0) ∪
        Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1) = Finset.univ := by
      ext s; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      generalize h : s x₀ = b; fin_cases b <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  have hN : 1 ≤ N := Fin.pos x₀
  have h2N : 2 ^ N = 2 * 2 ^ (N - 1) := by
    conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
    ring
  have hc0 : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card = 2 ^ (N - 1) := by omega
  have hc1 : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1)).card = 2 ^ (N - 1) := by omega
  fin_cases v
  · exact hc0
  · exact hc1

lemma eq91BimodalProb_sum_one_sector {N : ℕ} (x₀ : Fin N) (ε : ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1), eq91BimodalProb N x₀ ε s = 1 / 2 := by
  have hN : 1 ≤ N := Fin.pos x₀
  have hpeak_mem : eq91PeakIdx N x₀ ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1) := by
    simp [eq91PeakIdx]
  have hterm : ∀ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1),
      eq91BimodalProb N x₀ ε s =
      (if s = eq91PeakIdx N x₀ then (1 - ε) / 2 else 0) + ε / (2 : ℝ) ^ N := by
    intro s hs
    have hs1 : s x₀ = 1 := (Finset.mem_filter.mp hs).2
    have hs0 : s x₀ ≠ 0 := by rw [hs1]; decide
    unfold eq91BimodalProb
    rw [if_neg hs0]; split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hpeak_mem,
    Finset.sum_const, card_qubitIdx_at_site x₀ 1, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h2N : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ (N - 1) := by
    conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
    ring
  rw [h2N]
  have h2ne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
  field_simp [h2ne]; ring

lemma eq91BimodalProb_sum {N : ℕ} (x₀ : Fin N) (ε : ℝ) :
    ∑ s : QubitIdx N, eq91BimodalProb N x₀ ε s = 1 := by
  have hN : 1 ≤ N := Fin.pos x₀
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : QubitIdx N ↦ s x₀ = 0) (eq91BimodalProb N x₀ ε)).symm
  rw [hsplit]
  have h0 : ∑ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0), eq91BimodalProb N x₀ ε s = 1 / 2 := by
    have hterm : ∀ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0),
        eq91BimodalProb N x₀ ε s = 1 / (2 : ℝ) ^ N := fun s hs ↦ by
      unfold eq91BimodalProb; rw [if_pos (Finset.mem_filter.mp hs).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_qubitIdx_at_site x₀ 0, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    have h2N : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ (N - 1) := by
      conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
      ring
    rw [h2N]
    have h2ne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
    field_simp [h2ne]
  have hfilt1 : Finset.univ.filter (fun s : QubitIdx N ↦ ¬s x₀ = 0) =
      Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 1) := by
    ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    generalize h : s x₀ = b; fin_cases b <;> simp
  rw [h0, hfilt1, eq91BimodalProb_sum_one_sector]; norm_num

/-- Full-rank `GibbsData N` for the exact Eq. (9.1) qubit-`x₀`-conditioned bimodal state `ρ_ε`. -/
noncomputable def eq91BimodalGibbs (N : ℕ) (x₀ : Fin N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    GibbsData N where
  ρβ := Matrix.diagonal (fun s ↦ (eq91BimodalProb N x₀ ε s : ℂ))
  ρHalf := Matrix.diagonal (fun s ↦ (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ))
  ρQuarter := Matrix.diagonal (fun s ↦ (Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) : ℂ))
  ρQuarterInv := Matrix.diagonal (fun s ↦ ((Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)))⁻¹ : ℂ))
  ρβ_herm := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρHalf_herm := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρQuarter_herm := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρQuarterInv_herm := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  sq_quarter := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  sq_half := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (eq91BimodalProb_pos x₀ hε0 hε1 s).le]
  inv_left := by
    rw [Matrix.diagonal_mul_diagonal]; ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀]
      · simp
      · exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (eq91BimodalProb_pos x₀ hε0 hε1 i))).ne'
    · rfl
  inv_right := by
    rw [Matrix.diagonal_mul_diagonal]; ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀]
      · simp
      · exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (eq91BimodalProb_pos x₀ hε0 hε1 i))).ne'
    · rfl
  trace_one := by
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, eq91BimodalProb_sum x₀ ε, Complex.ofReal_one]

/-- Exact 1-local witness `A = √2 |1⟩⟨1|_{x₀} = (√2 / 2) (I - Z_{x₀}) ∈ filtrationSubmodule N 1`. -/
noncomputable def eq91WitnessOp {N : ℕ} (x₀ : Fin N) : QubitOp N :=
  (((Real.sqrt 2 / 2 : ℝ) : ℂ)) • ((1 : QubitOp N) - pauliSite x₀ 3)

lemma eq91WitnessOp_eq_diagonal {N : ℕ} (x₀ : Fin N) :
    eq91WitnessOp x₀ = Matrix.diagonal (fun s : QubitIdx N ↦
      ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ)) := by
  ext s t
  simp only [eq91WitnessOp, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  have hZ : pauliSite x₀ 3 s t = if s = t then (if s x₀ = 0 then 1 else -1) else 0 := by
    unfold pauliSite pauliString kronOp; simp only [Matrix.of_apply]
    by_cases hst : s = t
    · subst hst; rw [if_pos rfl]
      rw [← Finset.prod_subset (Finset.subset_univ ({x₀} : Finset (Fin N)))]
      · simp only [Finset.prod_singleton, Function.update_self]
        generalize hb : s x₀ = b; fin_cases b <;> simp [pauliMat, pauliZ]
      · intro y _ hy
        have hne : y ≠ x₀ := by simpa [Finset.mem_singleton] using hy
        rw [Function.update_of_ne hne]
        generalize hb : s y = b; fin_cases b <;> simp [pauliMat]
    · rw [if_neg hst]
      have hne_c : ∃ y : Fin N, s y ≠ t y := by by_contra h; push Not at h; exact hst (funext h)
      rcases hne_c with ⟨y, hy⟩
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      by_cases hyx : y = x₀
      · subst hyx; rw [Function.update_self]
        generalize h1 : s y = v1; generalize h2 : t y = v2
        rw [h1, h2] at hy; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat, pauliZ]
      · rw [Function.update_of_ne hyx]
        generalize h1 : s y = v1; generalize h2 : t y = v2
        rw [h1, h2] at hy; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat]
  rw [hZ]
  by_cases hst : s = t
  · subst hst; rw [if_pos rfl, if_pos rfl]
    generalize hb : s x₀ = b; fin_cases b <;> simp [sub_neg_eq_add] <;> ring
  · rw [if_neg hst, if_neg hst, if_neg hst]; simp

lemma eq91WitnessOp_mem_filtration {N : ℕ} (x₀ : Fin N) :
    eq91WitnessOp x₀ ∈ filtrationSubmodule N 1 := by
  unfold eq91WitnessOp
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · have h1 : (1 : QubitOp N) = pauliString (fun _ : Fin N ↦ (0 : Fin 4)) := by
      ext s t; unfold pauliString kronOp; simp only [Matrix.one_apply, Matrix.of_apply]
      by_cases hst : s = t
      · subst hst; rw [if_pos rfl]; symm; apply Finset.prod_eq_one; intro y _
        generalize hb : s y = b; fin_cases b <;> simp [pauliMat]
      · rw [if_neg hst]
        have hne_c : ∃ y : Fin N, s y ≠ t y := by by_contra h; push Not at h; exact hst (funext h)
        rcases hne_c with ⟨y, hy⟩
        symm; apply Finset.prod_eq_zero (Finset.mem_univ y)
        generalize h1 : s y = v1; generalize h2 : t y = v2
        rw [h1, h2] at hy; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat]
    rw [h1]; apply Submodule.subset_span
    exact ⟨fun _ ↦ 0, by unfold stringWeight; simp, rfl⟩
  · unfold pauliSite; apply Submodule.subset_span
    refine ⟨Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x₀ 3, ?_, rfl⟩
    unfold stringWeight
    have hsub : Finset.univ.filter (fun y : Fin N ↦ Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x₀ 3 y ≠ 0) ⊆
        {x₀} := by
      intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hy ⊢
      by_contra hne; exact hy (Function.update_of_ne hne _ _)
    exact le_trans (Finset.card_le_card hsub) (by simp)

lemma eq91WitnessOp_isHermitian {N : ℕ} (x₀ : Fin N) : (eq91WitnessOp x₀).IsHermitian := by
  rw [eq91WitnessOp_eq_diagonal]
  ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

/-- Exact unit Wightman norm `‖√2 |1⟩⟨1|_{x₀}‖_{ρ_ε,W}² = 1` for EVERY `ε ∈ (0, 1)`. -/
theorem eq91WitnessOp_wightmanNormSq {N : ℕ} (x₀ : Fin N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gibbsWightmanNormSq (eq91BimodalGibbs N x₀ hε0 hε1) (eq91WitnessOp x₀) = 1 := by
  set G := eq91BimodalGibbs N x₀ hε0 hε1
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
  rw [(eq91WitnessOp_isHermitian x₀).eq, eq91WitnessOp_eq_diagonal]
  change (Matrix.diagonal (fun s : QubitIdx N ↦ (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ)) *
    Matrix.diagonal (fun s : QubitIdx N ↦ ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ)) *
    Matrix.diagonal (fun s : QubitIdx N ↦ (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ)) *
    Matrix.diagonal (fun s : QubitIdx N ↦ ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ))).trace.re = 1
  simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  have hterm : ∀ s : QubitIdx N,
      ((Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ) *
        ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ) *
        (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ) *
        ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ)).re =
      if s x₀ = 1 then 2 * eq91BimodalProb N x₀ ε s else 0 := by
    intro s
    have hmul : (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ) *
        ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ) *
        (Real.sqrt (eq91BimodalProb N x₀ ε s) : ℂ) *
        ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ) =
        (((Real.sqrt (eq91BimodalProb N x₀ ε s) * Real.sqrt (eq91BimodalProb N x₀ ε s)) *
          ((if s x₀ = 1 then Real.sqrt 2 else 0) * (if s x₀ = 1 then Real.sqrt 2 else 0)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hmul, Complex.ofReal_re, Real.mul_self_sqrt (eq91BimodalProb_pos x₀ hε0 hε1 s).le]
    split_ifs
    · rw [Real.mul_self_sqrt (by norm_num)]; ring
    · ring
  simp_rw [hterm, ← Finset.sum_filter, ← Finset.mul_sum, eq91BimodalProb_sum_one_sector]
  norm_num

/-- Direct single-site HS inner product formula for real diagonal matrices using `eq91Flip`. -/
private lemma eq91_hsInner_siteSizeOp_real_diagonal {N : ℕ} (x : Fin N) (d : QubitIdx N → ℝ) :
    let M : QubitOp N := Matrix.diagonal (fun s ↦ (d s : ℂ))
    (hsInner M (siteSizeOp x M)).re =
      (1 / 4 : ℝ) * ∑ s : QubitIdx N, (d s - d (eq91Flip x s)) ^ 2 := by
  intro M
  have h1 := hsInner_siteSizeOp_real_diagonal x d
  have hflip_sum : ∑ s : QubitIdx N, d (eq91Flip x s) ^ 2 = ∑ s : QubitIdx N, d s ^ 2 :=
    Fintype.sum_equiv (Function.Involutive.toPerm (eq91Flip x) (eq91Flip_eq91Flip x)) _ _ fun _ ↦ rfl
  have hexp : ∑ s : QubitIdx N, (d s - d (eq91Flip x s)) ^ 2 =
      2 * ∑ s : QubitIdx N, (d s ^ 2 - d s * d (eq91Flip x s)) := by
    have hsq : ∀ s, (d s - d (eq91Flip x s)) ^ 2 =
        d s ^ 2 + d (eq91Flip x s) ^ 2 - 2 * (d s * d (eq91Flip x s)) := fun s ↦ by ring
    simp_rw [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  have hbm : (hsInner M (siteSizeOp x M)).re =
      (1 / 2 : ℝ) * ∑ s : QubitIdx N, (d s ^ 2 - d s * d (eq91Flip x s)) := h1
  linarith

/-- **Proposition 9.1(2) — Exact Eq. (9.1) Thermal Size Lower Bound**:
For `N ≥ 2`, any `x₀ : Fin N`, and any `ε ∈ (0, 1)`, the 1-local witness `A = √2 |1⟩⟨1|_{x₀}` satisfies
`mssThermalSize (eq91BimodalGibbs N x₀ hε0 hε1) A ≥ ((N - 1) / 4) * (1 - ε - 2 √(2 ε / 2^N))`. -/
theorem eq91Bimodal_mssThermalSize_lower {N : ℕ} (hN : 2 ≤ N) (x₀ : Fin N)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((N - 1 : ℝ) / 4) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N)) ≤
      mssThermalSize (eq91BimodalGibbs N x₀ hε0 hε1) (eq91WitnessOp x₀) := by
  set G := eq91BimodalGibbs N x₀ hε0 hε1
  set r : QubitIdx N → ℝ := fun s ↦ Real.sqrt (eq91BimodalProb N x₀ ε s)
  set a : QubitIdx N → ℝ := fun s ↦ if s x₀ = 1 then Real.sqrt 2 * r s else 0
  have hj_eq : jBeta G.ρQuarter (eq91WitnessOp x₀) = Matrix.diagonal (fun s ↦ (a s : ℂ)) := by
    unfold jBeta; rw [eq91WitnessOp_eq_diagonal]
    change Matrix.diagonal (fun s ↦ (Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) : ℂ)) *
      Matrix.diagonal (fun s ↦ ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ)) *
      Matrix.diagonal (fun s ↦ (Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) : ℂ)) = _
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1; funext s
    have hmul : (Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) : ℂ) *
        ((if s x₀ = 1 then Real.sqrt 2 else 0 : ℝ) : ℂ) *
        (Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) : ℂ) =
        (((Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s)) *
           Real.sqrt (Real.sqrt (eq91BimodalProb N x₀ ε s))) *
          (if s x₀ = 1 then Real.sqrt 2 else 0) : ℝ) : ℂ) := by push_cast; ring
    rw [hmul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
    dsimp only [a, r]; split_ifs <;> simp [mul_comm]
  have hsplit : mssThermalSize G (eq91WitnessOp x₀) =
      ∑ y : Fin N, ((hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
        (siteSizeOp y (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re -
        (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
          (siteSizeOp y (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re) := by
    unfold mssThermalSize totalSizeOp
    rw [hj_eq]
    have h1 : ∀ M : QubitOp N, (hsInner M (∑ y : Fin N, siteSizeOp y M)).re =
        ∑ y : Fin N, (hsInner M (siteSizeOp y M)).re := fun M ↦ by
      unfold hsInner; rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    rw [h1, h1, ← Finset.sum_sub_distrib]
    rfl
  rw [hsplit]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  have hx0_nn : 0 ≤ (hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
      (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re -
      (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
        (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re := by
    have ha_x0 : (hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
        (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re = 1 / 2 := by
      have h1 : (hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
          (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re =
          (1 / 2 : ℝ) * ∑ s : QubitIdx N, (a s ^ 2 - a s * a (eq91Flip x₀ s)) :=
        hsInner_siteSizeOp_real_diagonal x₀ a
      rw [h1]
      have hterm : ∀ s : QubitIdx N, a s ^ 2 - a s * a (eq91Flip x₀ s) =
          if s x₀ = 1 then 2 * eq91BimodalProb N x₀ ε s else 0 := by
        intro s; dsimp only [a, r]
        by_cases hs1 : s x₀ = 1
        · have hfl : eq91Flip x₀ s x₀ ≠ 1 := by simp [eq91Flip, hs1]
          simp only [hs1, ↓reduceIte, hfl, mul_zero, sub_zero, mul_pow,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
            Real.sq_sqrt (eq91BimodalProb_pos x₀ hε0 hε1 s).le]
        · simp only [hs1, ↓reduceIte]; ring
      simp_rw [hterm, ← Finset.sum_filter, ← Finset.mul_sum, eq91BimodalProb_sum_one_sector]
      norm_num
    have hr_x0 : (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
        (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re ≤ 1 / 2 := by
      have h1 : (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
          (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re =
          (1 / 2 : ℝ) * ∑ s : QubitIdx N, (r s ^ 2 - r s * r (eq91Flip x₀ s)) :=
        hsInner_siteSizeOp_real_diagonal x₀ r
      rw [h1]
      have hsum_le : ∑ s : QubitIdx N, (r s ^ 2 - r s * r (eq91Flip x₀ s)) ≤ 1 := by
        calc ∑ s : QubitIdx N, (r s ^ 2 - r s * r (eq91Flip x₀ s))
            ≤ ∑ s : QubitIdx N, r s ^ 2 := Finset.sum_le_sum fun s _ ↦ by
              have : 0 ≤ r s * r (eq91Flip x₀ s) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
              linarith
          _ = ∑ s : QubitIdx N, eq91BimodalProb N x₀ ε s := Finset.sum_congr rfl fun s _ ↦
              Real.sq_sqrt (eq91BimodalProb_pos x₀ hε0 hε1 s).le
          _ = 1 := eq91BimodalProb_sum x₀ ε
      linarith
    linarith
  have hy_lower : ∀ y ∈ Finset.univ.erase x₀,
      (1 / 4 : ℝ) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N)) ≤
        (hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
          (siteSizeOp y (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re -
        (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
          (siteSizeOp y (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re := by
    intro y hy
    have hyx : y ≠ x₀ := (Finset.mem_erase.mp hy).1
    rw [eq91_hsInner_siteSizeOp_real_diagonal y a, eq91_hsInner_siteSizeOp_real_diagonal y r]
    have hterm_eq : ∀ s : QubitIdx N,
        (a s - a (eq91Flip y s)) ^ 2 - (r s - r (eq91Flip y s)) ^ 2 =
        if s x₀ = 1 then (r s - r (eq91Flip y s)) ^ 2 else 0 := by
      intro s
      have hfl_x0 : eq91Flip y s x₀ = s x₀ := Function.update_of_ne hyx.symm _ _
      by_cases hs1 : s x₀ = 1
      · rw [if_pos hs1]
        have ha1 : a s = Real.sqrt 2 * r s := if_pos hs1
        have ha2 : a (eq91Flip y s) = Real.sqrt 2 * r (eq91Flip y s) := if_pos (by rw [hfl_x0, hs1])
        rw [ha1, ha2, ← mul_sub, mul_pow, Real.sq_sqrt (by norm_num)]; ring
      · rw [if_neg hs1]
        have hs0 : s x₀ = 0 := by
          generalize hb : s x₀ = b; rw [hb] at hs1; fin_cases b <;> simp_all
        have hfl0 : eq91Flip y s x₀ = 0 := by rw [hfl_x0, hs0]
        have ha1 : a s = 0 := if_neg hs1
        have ha2 : a (eq91Flip y s) = 0 := if_neg (by rw [hfl_x0]; exact hs1)
        have hr_eq : r s = r (eq91Flip y s) := by
          dsimp only [r]; unfold eq91BimodalProb; rw [if_pos hs0, if_pos hfl0]
        rw [ha1, ha2, hr_eq]; ring
    have hdiff_eq : (1 / 4 : ℝ) * ∑ s : QubitIdx N, (a s - a (eq91Flip y s)) ^ 2 -
        (1 / 4 : ℝ) * ∑ s : QubitIdx N, (r s - r (eq91Flip y s)) ^ 2 =
        (1 / 4 : ℝ) * ∑ s : QubitIdx N, (if s x₀ = 1 then (r s - r (eq91Flip y s)) ^ 2 else 0) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1; exact Finset.sum_congr rfl fun s _ ↦ hterm_eq s
    rw [hdiff_eq]
    set pk := eq91PeakIdx N x₀
    have hpk1 : pk x₀ = 1 := by simp [pk, eq91PeakIdx]
    have hflpk1 : eq91Flip y pk x₀ = 1 := by rw [eq91Flip, Function.update_of_ne hyx.symm, hpk1]
    have hne_pk : pk ≠ eq91Flip y pk := (eq91Flip_ne_self y pk).symm
    have hsub_le : ((if pk x₀ = 1 then (r pk - r (eq91Flip y pk)) ^ 2 else 0) +
        (if eq91Flip y pk x₀ = 1 then (r (eq91Flip y pk) - r (eq91Flip y (eq91Flip y pk))) ^ 2 else 0)) ≤
        ∑ s : QubitIdx N, (if s x₀ = 1 then (r s - r (eq91Flip y s)) ^ 2 else 0) := by
      have hpair := Finset.sum_le_sum_of_subset_of_nonneg
        (s := ({pk, eq91Flip y pk} : Finset (QubitIdx N))) (t := Finset.univ)
        (f := fun s : QubitIdx N ↦ if s x₀ = 1 then (r s - r (eq91Flip y s)) ^ 2 else 0)
        (Finset.subset_univ _) (fun s _ _ ↦ by split_ifs <;> positivity)
      rwa [Finset.sum_pair hne_pk] at hpair
    rw [if_pos hpk1, if_pos hflpk1, eq91Flip_eq91Flip] at hsub_le
    have hp_pk : eq91BimodalProb N x₀ ε pk = (1 - ε) / 2 + ε / (2 : ℝ) ^ N := by
      unfold eq91BimodalProb
      have h0 : pk x₀ ≠ 0 := by rw [hpk1]; decide
      rw [if_neg h0, if_pos rfl]
    have hp_fl : eq91BimodalProb N x₀ ε (eq91Flip y pk) = ε / (2 : ℝ) ^ N := by
      unfold eq91BimodalProb
      have h0 : eq91Flip y pk x₀ ≠ 0 := by rw [hflpk1]; decide
      rw [if_neg h0, if_neg hne_pk.symm]
    have hsq_bd : (1 - ε) / 2 - Real.sqrt (2 * ε / (2 : ℝ) ^ N) ≤ (r pk - r (eq91Flip y pk)) ^ 2 := by
      dsimp only [r]; rw [hp_pk, hp_fl]
      set u : ℝ := (1 - ε) / 2 + ε / (2 : ℝ) ^ N
      set v : ℝ := ε / (2 : ℝ) ^ N
      have hu_nn : 0 ≤ u := by dsimp only [u]; positivity
      have hv_nn : 0 ≤ v := by dsimp only [v]; positivity
      have hexp_sq : (Real.sqrt u - Real.sqrt v) ^ 2 = u + v - 2 * Real.sqrt (u * v) := by
        rw [sub_sq, Real.sq_sqrt hu_nn, Real.sq_sqrt hv_nn, Real.sqrt_mul hu_nn]; ring
      rw [hexp_sq]
      have hu_le : u ≤ 1 / 2 := by
        dsimp only [u]
        have h2N : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
          have : 2 ^ 1 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast this
        have hdiv : ε / (2 : ℝ) ^ N ≤ ε / 2 := div_le_div_of_nonneg_left hε0.le (by norm_num) h2N
        linarith
      have h2sqrt : 2 * Real.sqrt (u * v) ≤ Real.sqrt (2 * ε / (2 : ℝ) ^ N) := by
        have huv : 4 * (u * v) ≤ 2 * ε / (2 : ℝ) ^ N := by
          calc 4 * (u * v) ≤ 4 * ((1 / 2 : ℝ) * v) := by nlinarith
            _ = 2 * ε / (2 : ℝ) ^ N := by dsimp only [v]; ring
        calc 2 * Real.sqrt (u * v) = Real.sqrt 4 * Real.sqrt (u * v) := by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          _ = Real.sqrt (4 * (u * v)) := (Real.sqrt_mul (by norm_num) _).symm
          _ ≤ Real.sqrt (2 * ε / (2 : ℝ) ^ N) := Real.sqrt_le_sqrt huv
      dsimp only [u, v] at h2sqrt ⊢
      linarith
    have h2sq : (r pk - r (eq91Flip y pk)) ^ 2 + (r (eq91Flip y pk) - r pk) ^ 2 =
        2 * (r pk - r (eq91Flip y pk)) ^ 2 := by ring
    linarith
  have hsum_ge : ((N - 1 : ℝ) / 4) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N)) ≤
      ∑ y ∈ Finset.univ.erase x₀, ((hsInner (Matrix.diagonal (fun s ↦ (a s : ℂ)))
        (siteSizeOp y (Matrix.diagonal (fun s ↦ (a s : ℂ))))).re -
        (hsInner (Matrix.diagonal (fun s ↦ (r s : ℂ)))
          (siteSizeOp y (Matrix.diagonal (fun s ↦ (r s : ℂ))))).re) := by
    calc ((N - 1 : ℝ) / 4) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N))
        = ((Finset.univ.erase x₀).card : ℝ) *
            ((1 / 4 : ℝ) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N))) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, Fintype.card_fin,
            Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]; ring
      _ = ∑ _y ∈ Finset.univ.erase x₀, ((1 / 4 : ℝ) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hy_lower
  linarith

private lemma eq91_mssThermalSize_bddAbove {N : ℕ} (G : GibbsData N) (s : ℕ) :
    BddAbove { r : ℝ | ∃ A ∈ filtrationSubmodule N s,
      gibbsWightmanNormSq G A = 1 ∧ r = mssThermalSize G A } := by
  refine ⟨(3 / 2 : ℝ) * (N : ℝ) + |(hsInner G.ρHalf (totalSizeOp G.ρHalf)).re|, ?_⟩
  rintro r ⟨A, _, hAnorm, rfl⟩
  unfold mssThermalSize
  have hM_norm : (hsInner (jBeta G.ρQuarter A) (jBeta G.ρQuarter A)).re = 1 := by
    have hiso := (prop_2_2_lanczos_invariance G 0 (by simp)).1 A A
    unfold gibbsWightmanNormSq at hAnorm
    rw [← hiso]; exact hAnorm
  have htotal : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re =
      ∑ x : Fin N, (hsInner (jBeta G.ρQuarter A) (siteSizeOp x (jBeta G.ρQuarter A))).re := by
    unfold totalSizeOp hsInner; rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  have hle : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re ≤ (3 / 2 : ℝ) * (N : ℝ) := by
    rw [htotal]
    calc ∑ x : Fin N, (hsInner (jBeta G.ρQuarter A) (siteSizeOp x (jBeta G.ρQuarter A))).re
        ≤ ∑ _x : Fin N, (3 / 2 : ℝ) := by
          apply Finset.sum_le_sum; intro x _
          set M := jBeta G.ρQuarter A
          have hsite_eq : siteSizeOp x M = (1 / 4 : ℂ) • ∑ α : Fin 3,
              (M - pauliSite x α.succ * M * pauliSite x α.succ) := by
            unfold siteSizeOp partialTraceSite
            rw [Fin.sum_univ_succ, pauliSite_zero, Matrix.one_mul, Matrix.mul_one,
              Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ext i j; simp; ring
          rw [hsite_eq]; unfold hsInner
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum,
            show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, Complex.re_sum]
          have h3 : ∑ α : Fin 3, (Mᴴ * (M - pauliSite x α.succ * M * pauliSite x α.succ)).trace.re ≤
              ∑ _α : Fin 3, (2 : ℝ) := by
            apply Finset.sum_le_sum; intro α _
            set U := pauliSite x α.succ
            have hU_h : Uᴴ = U := (pauliSite_herm x α.succ).eq
            have hU_sq : U * U = 1 := pauliSite_sq x α.succ
            have hnn : 0 ≤ (hsInner (M + U * M * U) (M + U * M * U)).re := hsNormSq_nonneg _
            have hUMU : (hsInner (U * M * U) (U * M * U)).re = (hsInner M M).re := by
              unfold hsInner
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hU_h]
              have h1 : U * Mᴴ * U * (U * M * U) = U * (Mᴴ * M) * U := by
                calc U * Mᴴ * U * (U * M * U) = U * Mᴴ * (U * U) * M * U := by simp only [Matrix.mul_assoc]
                  _ = U * (Mᴴ * M) * U := by rw [hU_sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
              rw [h1, Matrix.trace_mul_cycle, hU_sq, Matrix.one_mul]
            have hsym : (hsInner (U * M * U) M).re = (hsInner M (U * M * U)).re := by
              unfold hsInner
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hU_h]
              have h1 : (U * Mᴴ * U * M).trace = (Mᴴ * (U * M * U)).trace := by
                rw [Matrix.trace_mul_cycle]; simp only [Matrix.mul_assoc]
              rw [h1]
            have hexp : (hsInner (M + U * M * U) (M + U * M * U)).re =
                2 * (hsInner M M).re + 2 * (hsInner M (U * M * U)).re := by
              unfold hsInner at hUMU hsym ⊢
              simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
                Complex.add_re]
              linarith
            have hdiff : (Mᴴ * (M - U * M * U)).trace.re = (hsInner M M).re - (hsInner M (U * M * U)).re := by
              unfold hsInner; rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
            linarith
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
          linarith
      _ = (3 / 2 : ℝ) * (N : ℝ) := by simp [mul_comm]
  linarith [neg_abs_le (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re]

/-- **Proposition 9.1(2) — Exact Eq. (9.1) `lambdaMSS` Lower Bound at `s = 1`**. -/
theorem eq91Bimodal_lambdaMSS_lower {N : ℕ} (hN : 2 ≤ N) (x₀ : Fin N)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((N - 1 : ℝ) / 4) * (1 - ε - 2 * Real.sqrt (2 * ε / (2 : ℝ) ^ N)) ≤
      lambdaMSS (eq91BimodalGibbs N x₀ hε0 hε1) 1 := by
  unfold lambdaMSS
  refine le_trans (eq91Bimodal_mssThermalSize_lower hN x₀ hε0 hε1) ?_
  exact le_csSup (eq91_mssThermalSize_bddAbove _ 1)
    ⟨eq91WitnessOp x₀, eq91WitnessOp_mem_filtration x₀,
     eq91WitnessOp_wightmanNormSq x₀ hε0 hε1, rfl⟩

/-- **Proposition 9.1(2) — Exact Eq. (9.1) Violates Hypothesis (H2) for Every `δ ∈ [0, 1)`**:
For ANY `δ ∈ [0, 1)` and ANY `C₁, C₂ ≥ 0`, there exist `N ≥ 2` and `ε ∈ (0, 1)` such that the
exact Eq. (9.1) full-rank bimodal state `eq91BimodalGibbs N ⟨0, _⟩ hε0 hε1` violates
`lambdaMSS G 1 ≤ C₁ * 1 + C₂ * N^δ * 1^(1 - δ)`. -/
theorem prop_9_1_part2_eq91_violates_H2 {δ C₁ C₂ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1),
      C₁ * (1 : ℝ) + C₂ * (N : ℝ) ^ δ * (1 : ℝ) ^ (1 - δ) <
        lambdaMSS (eq91BimodalGibbs N ⟨0, by omega⟩ hε0 hε1) 1 := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(1 - δ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop h1mδ).comp tendsto_natCast_atTop_atTop
  have hlim_tot : Tendsto (fun N : ℕ ↦
      (C₁ + 1 / 8) * (N : ℝ) ^ (-1 : ℝ) + C₂ * (N : ℝ) ^ (-(1 - δ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop one_pos).comp tendsto_natCast_atTop_atTop
    simpa using (h1.const_mul (C₁ + 1 / 8)).add (hlim.const_mul C₂)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hlim_tot) (1 / 8) (by norm_num)
  set N : ℕ := max N₀ 2
  have hN : 2 ≤ N := le_max_right _ _
  have hN_ge : N₀ ≤ N := le_max_left _ _
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  refine ⟨N, hN, 1 / 32, by norm_num, by norm_num, ?_⟩
  have hlow := eq91Bimodal_lambdaMSS_lower hN ⟨0, by omega⟩ (by norm_num : (0 : ℝ) < 1 / 32)
    (by norm_num : (1 / 32 : ℝ) < 1)
  have h2N : (4 : ℝ) ≤ (2 : ℝ) ^ N := by
    have : 2 ^ 2 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    exact_mod_cast this
  have hsqrt_le : Real.sqrt (2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N) ≤ 1 / 8 := by
    have hle : 2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N ≤ (1 / 8 : ℝ) ^ 2 := by
      calc 2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N ≤ (1 / 16 : ℝ) / 4 := by
              rw [show (2 : ℝ) * (1 / 32 : ℝ) = 1 / 16 by norm_num]
              exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2N
        _ = (1 / 8 : ℝ) ^ 2 := by norm_num
    calc Real.sqrt (2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N) ≤ Real.sqrt ((1 / 8 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 1 / 8 := Real.sqrt_sq (by norm_num)
  have hge_eighth : ((N : ℝ) - 1) / 8 ≤ lambdaMSS (eq91BimodalGibbs N ⟨0, by omega⟩
      (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)) 1 := by
    have hfac : (1 / 2 : ℝ) ≤ 1 - (1 / 32 : ℝ) - 2 * Real.sqrt (2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N) := by
      linarith
    have hnn : 0 ≤ ((N : ℝ) - 1) / 4 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    calc ((N : ℝ) - 1) / 8 = (((N : ℝ) - 1) / 4) * (1 / 2) := by ring
      _ ≤ (((N : ℝ) - 1) / 4) * (1 - (1 / 32 : ℝ) - 2 * Real.sqrt (2 * (1 / 32 : ℝ) / (2 : ℝ) ^ N)) :=
          mul_le_mul_of_nonneg_left hfac hnn
      _ ≤ _ := hlow
  have hsmall := hN₀ N hN_ge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  have hmulN := mul_lt_mul_of_pos_right hsmall hN_pos
  have h1 : (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) = 1 := by
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hN_pos.ne']
  have h2 : (N : ℝ) ^ (-(1 - δ)) * (N : ℝ) = (N : ℝ) ^ δ := by
    calc (N : ℝ) ^ (-(1 - δ)) * (N : ℝ) = (N : ℝ) ^ (-(1 - δ)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (-(1 - δ) + 1) := (Real.rpow_add hN_pos _ _).symm
      _ = (N : ℝ) ^ δ := by congr 1; ring
  have hrhs_eq : ((C₁ + 1 / 8) * (N : ℝ) ^ (-1 : ℝ) + C₂ * (N : ℝ) ^ (-(1 - δ))) * (N : ℝ) =
      C₁ + 1 / 8 + C₂ * (N : ℝ) ^ δ := by
    rw [add_mul, mul_assoc, mul_assoc, h1, h2, mul_one]
  rw [hrhs_eq] at hmulN
  rw [Real.one_rpow, mul_one, mul_one]
  linarith

end Prop91Part2Eq91Bimodal

section Prop91Part3LanczosAndBulkBand

/-- Zeroth Lanczos vector `|K₀⟩ = |ψ₀⟩ = (|φ_+⟩ + |φ_-⟩) / √2 ∈ ℂ^D`. -/
noncomputable def doubleWellK0 {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) : Fin D → ℂ :=
  doubleWellPsi0 hD hEB

/-- First Lanczos vector `|K₁⟩ = (|φ_+⟩ - |φ_-⟩) / √2 ∈ ℂ^D`. -/
noncomputable def doubleWellK1 {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) : Fin D → ℂ :=
  let P := doubleWellGround hD hEB
  fun j ↦ (((P.φp j - P.φm j) / Real.sqrt 2 : ℝ) : ℂ)

/-- Standard Hermitian inner product `⟨u | v⟩ = ∑ j, star (u j) * v j` on `ℂ^D`. -/
noncomputable def vecInner {D : ℕ} (u v : Fin D → ℂ) : ℂ :=
  ∑ j : Fin D, starRingEnd ℂ (u j) * v j

private lemma doubleWellGround_orth {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    let P := doubleWellGround hD hEB
    ∑ j : Fin D, P.φp j * P.φm j = 0 := by
  intro P
  have hpar : ∀ j : Fin D, P.φp (revFin j) = P.φp j ∧ P.φm (revFin j) = -P.φm j := by
    intro j
    have hp := congrFun P.hpar_p j
    have hm := congrFun P.hpar_m j
    rw [parityMat_mulVec] at hp hm
    exact ⟨hp, hm⟩
  have hswap : ∑ j : Fin D, P.φp j * P.φm j = ∑ j : Fin D, P.φp (revFin j) * P.φm (revFin j) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm revFin revFin_revFin) _ _ fun _ ↦ rfl).symm
  have hneg : ∑ j : Fin D, P.φp (revFin j) * P.φm (revFin j) = -(∑ j : Fin D, P.φp j * P.φm j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [(hpar j).1, (hpar j).2]; ring
  linarith

/-- **Orthonormality of the 2D Double-Well Lanczos Basis `{|K₀⟩, |K₁⟩} ⊆ ℂ^D`**. -/
theorem doubleWell_lanczos_orthonormal {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    vecInner (doubleWellK0 hD hEB) (doubleWellK0 hD hEB) = 1 ∧
    vecInner (doubleWellK1 hD hEB) (doubleWellK1 hD hEB) = 1 ∧
    vecInner (doubleWellK0 hD hEB) (doubleWellK1 hD hEB) = 0 := by
  set P := doubleWellGround hD hEB
  have horth := doubleWellGround_orth hD hEB
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold vecInner doubleWellK0 doubleWellPsi0
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    norm_cast
    have hsum : ∑ j : Fin D, (P.φp j + P.φm j) / Real.sqrt 2 * ((P.φp j + P.φm j) / Real.sqrt 2) =
        ((∑ j : Fin D, P.φp j ^ 2) + 2 * (∑ j : Fin D, P.φp j * P.φm j) + (∑ j : Fin D, P.φm j ^ 2)) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have : (P.φp j + P.φm j) / Real.sqrt 2 * ((P.φp j + P.φm j) / Real.sqrt 2) =
          (P.φp j + P.φm j) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hsq2]; ring
    rw [hsum, P.hnorm_p, P.hnorm_m, horth]; norm_num
  · unfold vecInner doubleWellK1
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    norm_cast
    have hsum : ∑ j : Fin D, (P.φp j - P.φm j) / Real.sqrt 2 * ((P.φp j - P.φm j) / Real.sqrt 2) =
        ((∑ j : Fin D, P.φp j ^ 2) - 2 * (∑ j : Fin D, P.φp j * P.φm j) + (∑ j : Fin D, P.φm j ^ 2)) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have : (P.φp j - P.φm j) / Real.sqrt 2 * ((P.φp j - P.φm j) / Real.sqrt 2) =
          (P.φp j - P.φm j) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hsq2]; ring
    rw [hsum, P.hnorm_p, P.hnorm_m, horth]; norm_num
  · unfold vecInner doubleWellK0 doubleWellPsi0 doubleWellK1
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    norm_cast
    have hsum : ∑ j : Fin D, (P.φp j + P.φm j) / Real.sqrt 2 * ((P.φp j - P.φm j) / Real.sqrt 2) =
        ((∑ j : Fin D, P.φp j ^ 2) - (∑ j : Fin D, P.φm j ^ 2)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have : (P.φp j + P.φm j) / Real.sqrt 2 * ((P.φp j - P.φm j) / Real.sqrt 2) =
          (P.φp j ^ 2 - P.φm j ^ 2) / (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hsq2]
    rw [hsum, P.hnorm_p, P.hnorm_m]; norm_num

/-- **Exact 2D Lanczos Tridiagonal Closure of `doubleWellTridiag D E_B` on `span{|K₀⟩, |K₁⟩}`**:
With `a₀ = (E_+ + E_-) / 2` and `b₁ = (E_+ - E_-) / 2 ≠ 0`:
`ℒ |K₀⟩ = a₀ |K₀⟩ + b₁ |K₁⟩` and `ℒ |K₁⟩ = b₁ |K₀⟩ + a₀ |K₁⟩` (hence `b₂ = 0`). -/
theorem doubleWell_lanczos_tridiag_closure {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    let P := doubleWellGround hD hEB
    let L_ℂ := (doubleWellTridiag D E_B).map Complex.ofReal
    let a₀ : ℂ := (((P.Ep + P.Em) / 2 : ℝ) : ℂ)
    let b₁ : ℂ := (((P.Ep - P.Em) / 2 : ℝ) : ℂ)
    L_ℂ *ᵥ doubleWellK0 hD hEB = a₀ • doubleWellK0 hD hEB + b₁ • doubleWellK1 hD hEB ∧
    L_ℂ *ᵥ doubleWellK1 hD hEB = b₁ • doubleWellK0 hD hEB + a₀ • doubleWellK1 hD hEB := by
  intro P L_ℂ a₀ b₁
  have hp_j : ∀ j : Fin D, ∑ k : Fin D, ((doubleWellTridiag D E_B j k : ℝ) : ℂ) * (P.φp k : ℂ) =
      (P.Ep : ℂ) * (P.φp j : ℂ) := fun j ↦ by
    have h := congrFun P.heig_p j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact_mod_cast h
  have hm_j : ∀ j : Fin D, ∑ k : Fin D, ((doubleWellTridiag D E_B j k : ℝ) : ℂ) * (P.φm k : ℂ) =
      (P.Em : ℂ) * (P.φm j : ℂ) := fun j ↦ by
    have h := congrFun P.heig_m j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact_mod_cast h
  have hsplit : ∀ (j : Fin D) (s : ℂ), ∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) *
      (((P.φp k : ℂ) + s * (P.φm k : ℂ)) / (Real.sqrt 2 : ℂ)) =
      ((∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (P.φp k : ℂ)) +
       s * (∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (P.φm k : ℂ))) / (Real.sqrt 2 : ℂ) := by
    intro j s; rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ by ring
  constructor
  · ext j
    simp only [L_ℂ, doubleWellK0, doubleWellPsi0, doubleWellK1, a₀, b₁,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub]
    have h1 := hsplit j 1; simp only [one_mul] at h1
    change ∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (((P.φp k : ℂ) + (P.φm k : ℂ)) / (Real.sqrt 2 : ℂ)) = _
    rw [h1, hp_j j, hm_j j]; push_cast; ring
  · ext j
    simp only [L_ℂ, doubleWellK0, doubleWellPsi0, doubleWellK1, a₀, b₁,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub]
    have h1 := hsplit j (-1); simp only [neg_one_mul, ← sub_eq_add_neg] at h1
    change ∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (((P.φp k : ℂ) - (P.φm k : ℂ)) / (Real.sqrt 2 : ℂ)) = _
    rw [h1, hp_j j, hm_j j]; push_cast; ring

/-- **Exact Derivation of `doubleWellKrylovK` from `doubleWellPsiEvol` and `{|K₀⟩, |K₁⟩}`**:
For every `t : ℝ`, the Lanczos amplitudes `c₀(t) = ⟨K₀ | ψ(t)⟩` and `c₁(t) = ⟨K₁ | ψ(t)⟩` of
`ψ(t) = doubleWellPsiEvol hD hEB t` satisfy:
1. `‖c₀(t)‖² + ‖c₁(t)‖² = 1`, and
2. `0 * ‖c₀(t)‖² + 1 * ‖c₁(t)‖² = doubleWellKrylovK hD hEB t = sin²((E_- - E_+) t / 2)`. -/
theorem doubleWell_krylov_complexity_from_lanczos {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B)
    (t : ℝ) :
    ‖vecInner (doubleWellK0 hD hEB) (doubleWellPsiEvol hD hEB t)‖ ^ 2 +
      ‖vecInner (doubleWellK1 hD hEB) (doubleWellPsiEvol hD hEB t)‖ ^ 2 = 1 ∧
    (0 : ℝ) * ‖vecInner (doubleWellK0 hD hEB) (doubleWellPsiEvol hD hEB t)‖ ^ 2 +
      (1 : ℝ) * ‖vecInner (doubleWellK1 hD hEB) (doubleWellPsiEvol hD hEB t)‖ ^ 2 =
      doubleWellKrylovK hD hEB t := by
  set P := doubleWellGround hD hEB
  set ep : ℂ := Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ))
  set em : ℂ := Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ))
  have horth := doubleWellGround_orth hD hEB
  have hsq2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hφp2 : ∑ j : Fin D, (P.φp j : ℂ) * (P.φp j : ℂ) = 1 := by
    have : ∑ j : Fin D, P.φp j * P.φp j = 1 := by simpa [sq] using P.hnorm_p
    exact_mod_cast this
  have hφm2 : ∑ j : Fin D, (P.φm j : ℂ) * (P.φm j : ℂ) = 1 := by
    have : ∑ j : Fin D, P.φm j * P.φm j = 1 := by simpa [sq] using P.hnorm_m
    exact_mod_cast this
  have hφpm : ∑ j : Fin D, (P.φp j : ℂ) * (P.φm j : ℂ) = 0 := by exact_mod_cast horth
  have hφmp : ∑ j : Fin D, (P.φm j : ℂ) * (P.φp j : ℂ) = 0 := by
    have : ∑ j : Fin D, P.φm j * P.φp j = 0 := by simpa [mul_comm] using horth
    exact_mod_cast this
  have hc0 : vecInner (doubleWellK0 hD hEB) (doubleWellPsiEvol hD hEB t) = (ep + em) / 2 := by
    unfold vecInner doubleWellK0 doubleWellPsi0 doubleWellPsiEvol
    change ∑ j : Fin D, (starRingEnd ℂ) ((((P.φp j : ℝ) + P.φm j) / Real.sqrt 2 : ℝ) : ℂ) *
      ((ep * (P.φp j : ℂ) + em * (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ)) = (ep + em) / 2
    simp only [Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_add]
    have hsum : ∑ j : Fin D, ((P.φp j : ℂ) + (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ) *
        ((ep * (P.φp j : ℂ) + em * (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ)) =
        (ep * (∑ j : Fin D, (P.φp j : ℂ) * (P.φp j : ℂ)) +
         em * (∑ j : Fin D, (P.φp j : ℂ) * (P.φm j : ℂ)) +
         ep * (∑ j : Fin D, (P.φm j : ℂ) * (P.φp j : ℂ)) +
         em * (∑ j : Fin D, (P.φm j : ℂ) * (P.φm j : ℂ))) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hden : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      field_simp [hden]; rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 by rw [sq, hsq2]]
    rw [hsum, hφp2, hφpm, hφmp, hφm2]; ring
  have hc1 : vecInner (doubleWellK1 hD hEB) (doubleWellPsiEvol hD hEB t) = (ep - em) / 2 := by
    unfold vecInner doubleWellK1 doubleWellPsiEvol
    change ∑ j : Fin D, (starRingEnd ℂ) ((((P.φp j : ℝ) - P.φm j) / Real.sqrt 2 : ℝ) : ℂ) *
      ((ep * (P.φp j : ℂ) + em * (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ)) = (ep - em) / 2
    simp only [Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_sub]
    have hsum : ∑ j : Fin D, ((P.φp j : ℂ) - (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ) *
        ((ep * (P.φp j : ℂ) + em * (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ)) =
        (ep * (∑ j : Fin D, (P.φp j : ℂ) * (P.φp j : ℂ)) +
         em * (∑ j : Fin D, (P.φp j : ℂ) * (P.φm j : ℂ)) -
         ep * (∑ j : Fin D, (P.φm j : ℂ) * (P.φp j : ℂ)) -
         em * (∑ j : Fin D, (P.φm j : ℂ) * (P.φm j : ℂ))) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hden : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      field_simp [hden]; rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 by rw [sq, hsq2]]
    rw [hsum, hφp2, hφpm, hφmp, hφm2]; ring
  set θ : ℝ := (P.Em - P.Ep) * t / 2
  set φ : ℝ := -(P.Ep + P.Em) * t / 2
  have hep_fac : ep = Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; dsimp only [ep, φ, θ]; congr 1; push_cast; ring
  have hem_fac : em = Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((-(θ : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]; dsimp only [em, φ, θ]; congr 1; push_cast; ring
  have hnorm_c0 : ‖(ep + em) / 2‖ ^ 2 = Real.cos θ ^ 2 := by
    have heq : (ep + em) / 2 = Complex.exp ((φ : ℂ) * Complex.I) * (Real.cos θ : ℂ) := by
      rw [hep_fac, hem_fac, ← mul_add, mul_div_assoc]
      congr 1; rw [Complex.ofReal_cos, Complex.cos]; ring_nf
    rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm_c1 : ‖(ep - em) / 2‖ ^ 2 = Real.sin θ ^ 2 := by
    have heq : (ep - em) / 2 = Complex.exp ((φ : ℂ) * Complex.I) * Complex.I * (Real.sin θ : ℂ) := by
      rw [hep_fac, hem_fac, ← mul_sub, mul_div_assoc]
      rw [Complex.ofReal_sin, Complex.sin]
      have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
      have hsimp : (Complex.exp (-(↑θ * Complex.I)) - Complex.exp (↑θ * Complex.I)) * Complex.I / 2 * Complex.I =
          (Complex.exp (↑θ * Complex.I) - Complex.exp (-(↑θ * Complex.I))) / 2 := by
        linear_combination (Complex.exp (-(↑θ * Complex.I)) - Complex.exp (↑θ * Complex.I)) / 2 * hI2
      calc Complex.exp (↑φ * Complex.I) * ((Complex.exp (↑θ * Complex.I) - Complex.exp (-↑θ * Complex.I)) / 2)
          = Complex.exp (↑φ * Complex.I) * ((Complex.exp (↑θ * Complex.I) - Complex.exp (-(↑θ * Complex.I))) / 2) := by
            congr 2; congr 1; congr 1; ring
        _ = Complex.exp (↑φ * Complex.I) * ((Complex.exp (-(↑θ * Complex.I)) - Complex.exp (↑θ * Complex.I)) *
              Complex.I / 2 * Complex.I) := by rw [← hsimp]
        _ = _ := by ring
    rw [heq, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, one_mul, one_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hc0, hc1, hnorm_c0, hnorm_c1]
  refine ⟨Real.cos_sq_add_sin_sq θ, ?_⟩
  simp only [zero_mul, one_mul, zero_add, doubleWellKrylovK, θ, P]

/-- Elementary linear algebra: any 3 pairs `(a₁, b₁), (a₂, b₂), (a₃, b₃) ∈ ℝ²` have a nonzero
real linear combination `(c₁, c₂, c₃) ≠ (0, 0, 0)` with `∑ cᵢ aᵢ = 0` and `∑ cᵢ bᵢ = 0`. -/
private lemma exists_nonzero_annihilator_three_pairs (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    ∃ c₁ c₂ c₃ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
      c₁ * a₁ + c₂ * a₂ + c₃ * a₃ = 0 ∧ c₁ * b₁ + c₂ * b₂ + c₃ * b₃ = 0 := by
  by_cases h1 : a₂ * b₃ - a₃ * b₂ ≠ 0 ∨ a₃ * b₁ - a₁ * b₃ ≠ 0 ∨ a₁ * b₂ - a₂ * b₁ ≠ 0
  · exact ⟨a₂ * b₃ - a₃ * b₂, a₃ * b₁ - a₁ * b₃, a₁ * b₂ - a₂ * b₁, h1, by ring, by ring⟩
  · push Not at h1
    by_cases ha1 : a₁ ≠ 0
    · refine ⟨-a₂, a₁, 0, Or.inr (Or.inl ha1), by ring, ?_⟩
      linarith [h1.2.2]
    · push Not at ha1
      by_cases hb1 : b₁ ≠ 0
      · refine ⟨-b₂, b₁, 0, Or.inr (Or.inl hb1), ?_, by ring⟩
        rw [ha1] at h1 ⊢; linarith [h1.2.2]
      · push Not at hb1
        exact ⟨1, 0, 0, Or.inl one_ne_zero, by simp [ha1], by simp [hb1]⟩

/-- **Lemma B.1 — Courant–Fischer Bulk Eigenvalue Band `[E_B - 2, E_B + 2]`**:
For every `D ≥ 4` and `E_B > 2`, letting `hL := doubleWellTridiag_isHermitian D E_B`:
1. Every eigenvalue satisfies `hL.eigenvalues k ≤ E_B + 2`.
2. At most `2` eigenindices satisfy `hL.eigenvalues k < E_B - 2`.
3. At least `D - 2` eigenvalues lie in `[E_B - 2, E_B + 2]`. -/
theorem lemma_B_1_bulk_eigenvalues_in_band {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    let hL := doubleWellTridiag_isHermitian D E_B
    (∀ k : Fin D, hL.eigenvalues k ≤ E_B + 2) ∧
    (Finset.univ.filter (fun k : Fin D ↦ hL.eigenvalues k < E_B - 2)).card ≤ 2 ∧
    D - 2 ≤ (Finset.univ.filter (fun k : Fin D ↦ E_B - 2 ≤ hL.eigenvalues k ∧
      hL.eigenvalues k ≤ E_B + 2)).card := by
  intro hL
  have hD2 : 2 ≤ D := by omega
  let U : Matrix (Fin D) (Fin D) ℝ := (hL.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℝ)
  have hU1 : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff.mp hL.eigenvectorUnitary.2
  have hU2 : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff'.mp hL.eigenvectorUnitary.2
  have hspec : doubleWellTridiag D E_B = U * Matrix.diagonal hL.eigenvalues * Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hL.spectral_theorem
  let e : Fin D → Fin D → ℝ := fun k i ↦ U i k
  have heig : ∀ k : Fin D, doubleWellTridiag D E_B *ᵥ e k = hL.eigenvalues k • e k := by
    intro k
    have hmul : doubleWellTridiag D E_B * U = U * Matrix.diagonal hL.eigenvalues := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hU2, Matrix.mul_one]
    ext i
    have h1 := congrFun (congrFun hmul i) k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h1
    simpa [Matrix.mulVec, dotProduct, e, Pi.smul_apply, smul_eq_mul, mul_comm] using h1
  have hortho : ∀ k₁ k₂ : Fin D, dotProduct (e k₁) (e k₂) = if k₁ = k₂ then 1 else 0 := by
    intro k₁ k₂
    have h1 := congrFun (congrFun hU2 k₁) k₂
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simpa [dotProduct, e, Matrix.transpose_apply] using h1
  have hupper : ∀ k : Fin D, hL.eigenvalues k ≤ E_B + 2 := by
    intro k
    have hq := doubleWellTridiag_quadForm hD2 E_B (e k)
    have hhop := path_hopping_quad_le hD2 (e k)
    have hdot1 : dotProduct (e k) (e k) = 1 := by rw [hortho k k, if_pos rfl]
    have hsum1 : ∑ i : Fin D, e k i ^ 2 = 1 := by simpa [dotProduct, sq] using hdot1
    have hlhs : dotProduct (e k) (doubleWellTridiag D E_B *ᵥ e k) = hL.eigenvalues k := by
      rw [heig k, dotProduct_smul, smul_eq_mul, hdot1, mul_one]
    have hbulk_le : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), e k i ^ 2 ≤
        ∑ i : Fin D, e k i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ ↦ sq_nonneg _
    have hEB_nn : 0 ≤ E_B := by linarith
    have h1 : E_B * ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), e k i ^ 2 ≤
        E_B * 1 := mul_le_mul_of_nonneg_left (hsum1 ▸ hbulk_le) hEB_nn
    have h2 : 2 * ∑ i : Fin (D - 1), e k ⟨i.val, by omega⟩ * e k ⟨i.val + 1, by omega⟩ ≤
        2 * ∑ i : Fin D, e k i ^ 2 := (abs_le.mp hhop).2
    linarith
  have hlow_card : (Finset.univ.filter (fun k : Fin D ↦ hL.eigenvalues k < E_B - 2)).card ≤ 2 := by
    by_contra hgt; push Not at hgt
    set S := Finset.univ.filter (fun k : Fin D ↦ hL.eigenvalues k < E_B - 2)
    have h3 : 3 ≤ S.card := hgt
    obtain ⟨k₁, hk₁, hk₁_card⟩ : ∃ k₁ ∈ S, 2 ≤ (S.erase k₁).card := by
      rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨k₁, hk₁⟩
      exact ⟨k₁, hk₁, by rw [Finset.card_erase_of_mem hk₁]; omega⟩
    obtain ⟨k₂, hk₂, hk₂_card⟩ : ∃ k₂ ∈ S.erase k₁, 1 ≤ ((S.erase k₁).erase k₂).card := by
      rcases Finset.card_pos.mp (by omega : 0 < (S.erase k₁).card) with ⟨k₂, hk₂⟩
      exact ⟨k₂, hk₂, by rw [Finset.card_erase_of_mem hk₂]; omega⟩
    rcases Finset.card_pos.mp hk₂_card with ⟨k₃, hk₃⟩
    have hne12 : k₁ ≠ k₂ := (Finset.mem_erase.mp hk₂).1.symm
    have hne13 : k₁ ≠ k₃ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk₃).2).1.symm
    have hne23 : k₂ ≠ k₃ := (Finset.mem_erase.mp hk₃).1.symm
    have hlt1 : hL.eigenvalues k₁ < E_B - 2 := (Finset.mem_filter.mp hk₁).2
    have hlt2 : hL.eigenvalues k₂ < E_B - 2 := (Finset.mem_filter.mp (Finset.mem_erase.mp hk₂).2).2
    have hlt3 : hL.eigenvalues k₃ < E_B - 2 :=
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk₃).2).2).2
    rcases exists_nonzero_annihilator_three_pairs
      (e k₁ ⟨0, by omega⟩) (e k₂ ⟨0, by omega⟩) (e k₃ ⟨0, by omega⟩)
      (e k₁ ⟨D - 1, by omega⟩) (e k₂ ⟨D - 1, by omega⟩) (e k₃ ⟨D - 1, by omega⟩) with
      ⟨c₁, c₂, c₃, hcnz, hbd0, hbd1⟩
    let v : Fin D → ℝ := c₁ • e k₁ + c₂ • e k₂ + c₃ • e k₃
    have hv0 : v ⟨0, by omega⟩ = 0 := by simpa [v] using hbd0
    have hv1 : v ⟨D - 1, by omega⟩ = 0 := by simpa [v] using hbd1
    have hv_norm : dotProduct v v = c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 := by
      dsimp only [v]
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        hortho, ↓reduceIte, if_neg hne12, if_neg hne12.symm, if_neg hne13, if_neg hne13.symm,
        if_neg hne23, if_neg hne23.symm]
      ring
    have hv_pos : 0 < dotProduct v v := by
      rw [hv_norm]
      rcases hcnz with h | h | h
      · linarith [sq_pos_of_ne_zero h, sq_nonneg c₂, sq_nonneg c₃]
      · linarith [sq_nonneg c₁, sq_pos_of_ne_zero h, sq_nonneg c₃]
      · linarith [sq_nonneg c₁, sq_nonneg c₂, sq_pos_of_ne_zero h]
    have hv_quad_lt : dotProduct v (doubleWellTridiag D E_B *ᵥ v) < (E_B - 2) * dotProduct v v := by
      have hLv : doubleWellTridiag D E_B *ᵥ v =
          (c₁ * hL.eigenvalues k₁) • e k₁ + (c₂ * hL.eigenvalues k₂) • e k₂ +
          (c₃ * hL.eigenvalues k₃) • e k₃ := by
        dsimp only [v]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, heig, smul_smul]
      have hval : dotProduct v (doubleWellTridiag D E_B *ᵥ v) =
          hL.eigenvalues k₁ * c₁ ^ 2 + hL.eigenvalues k₂ * c₂ ^ 2 + hL.eigenvalues k₃ * c₃ ^ 2 := by
        rw [hLv]; dsimp only [v]
        simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
          hortho, ↓reduceIte, if_neg hne12, if_neg hne12.symm, if_neg hne13, if_neg hne13.symm,
          if_neg hne23, if_neg hne23.symm]
        ring
      rw [hval, hv_norm]
      rcases hcnz with h | h | h
      · have h1 := mul_lt_mul_of_pos_right hlt1 (sq_pos_of_ne_zero h)
        have h2 := mul_le_mul_of_nonneg_right hlt2.le (sq_nonneg c₂)
        have h3 := mul_le_mul_of_nonneg_right hlt3.le (sq_nonneg c₃)
        linarith
      · have h1 := mul_le_mul_of_nonneg_right hlt1.le (sq_nonneg c₁)
        have h2 := mul_lt_mul_of_pos_right hlt2 (sq_pos_of_ne_zero h)
        have h3 := mul_le_mul_of_nonneg_right hlt3.le (sq_nonneg c₃)
        linarith
      · have h1 := mul_le_mul_of_nonneg_right hlt1.le (sq_nonneg c₁)
        have h2 := mul_le_mul_of_nonneg_right hlt2.le (sq_nonneg c₂)
        have h3 := mul_lt_mul_of_pos_right hlt3 (sq_pos_of_ne_zero h)
        linarith
    have hv_quad_ge : (E_B - 2) * dotProduct v v ≤ dotProduct v (doubleWellTridiag D E_B *ᵥ v) := by
      have hq := doubleWellTridiag_quadForm hD2 E_B v
      have hhop := path_hopping_quad_le hD2 v
      have hbulk_eq : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 =
          ∑ i : Fin D, v i ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs with hi
        · rfl
        · push Not at hi
          rcases hi with h0 | h1
          · have hi0 : i = ⟨0, by omega⟩ := Fin.ext h0
            rw [hi0, hv0]; norm_num
          · have hi1 : i = ⟨D - 1, by omega⟩ := Fin.ext h1
            rw [hi1, hv1]; norm_num
      have hdot_eq : dotProduct v v = ∑ i : Fin D, v i ^ 2 := by simp [dotProduct, sq]
      have hhop_lo : -(2 * ∑ i : Fin D, v i ^ 2) ≤
          2 * ∑ i : Fin (D - 1), v ⟨i.val, by omega⟩ * v ⟨i.val + 1, by omega⟩ := (abs_le.mp hhop).1
      rw [hbulk_eq] at hq
      rw [hdot_eq]; linarith
    linarith
  have hband_card : D - 2 ≤ (Finset.univ.filter (fun k : Fin D ↦
      E_B - 2 ≤ hL.eigenvalues k ∧ hL.eigenvalues k ≤ E_B + 2)).card := by
    have hcomp : Finset.univ.filter (fun k : Fin D ↦ ¬(hL.eigenvalues k < E_B - 2)) =
        Finset.univ.filter (fun k : Fin D ↦ E_B - 2 ≤ hL.eigenvalues k ∧ hL.eigenvalues k ≤ E_B + 2) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact ⟨fun h ↦ ⟨h, hupper k⟩, fun h ↦ h.1⟩
    have hadd := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun k : Fin D ↦ hL.eigenvalues k < E_B - 2)
    rw [Finset.card_univ, Fintype.card_fin, hcomp] at hadd
    omega
  exact ⟨hupper, hlow_card, hband_card⟩

end Prop91Part3LanczosAndBulkBand

end KrylovChaos
