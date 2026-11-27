/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.CausalExpansion
import KrylovChaos.ClusterCumulantAndDecoupling
import KrylovChaos.Milestone3Sections678
import KrylovChaos.TimeOrderedOTOC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# All-Time Finite-Range Lieb–Robinson Bound and Lattice Light-Cone Decay (Corollary 6.5)

Proves the unconditional all-time (`∀ t : ℝ`) finite-range Lieb–Robinson bound on `QubitOp N`
using the Nachtergaele–Sims integral-inequality iteration (with no short-time restriction
`2 |t| r J < 1`):
1. `opNorm_le_add_integral_of_deriv_comm_herm`: norm-preserving differential inequality
   `K'(s) = i [M(s), K(s)] + R(s)` with `M(s)` Hermitian implies
   `opNorm (K t) ≤ opNorm (K 0) + ∫_0^t opNorm (R s) ds` for all `t ≥ 0`.
2. `all_time_lieb_robinson_factorial_nonneg` and `all_time_lieb_robinson_exp`:
   for any `r`-local finite-range (`diam X ≤ R_int`) Hermitian Hamiltonian `H = ∑ X ∈ E, h X`
   with `h X = (h X)ᴴ`, local strength `∑_{X ∋ x} ‖h_X‖_op ≤ J`, `O ∈ supportedOn U₀`,
   `B ∈ supportedOn V`, and `∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y`, for ALL `t : ℝ`:
   `‖[O(t), B]‖_op ≤ 2 ‖O‖_op ‖B‖_op |U₀| ((2 r J |t|)^{m+1} / (m+1)!)`
   and `‖[O(t), B]‖_op ≤ 2 ‖O‖_op ‖B‖_op |U₀| exp(2 e r J |t| - (m + 1))`.
-/

namespace KrylovChaos

open Matrix

section NormPreservingDerivation

/-- `opNorm` is preserved under real-time Heisenberg evolution `heisenbergEvol hH (t : ℂ) A`. -/
lemma opNorm_heisenbergEvol_real {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (t : ℝ) (A : QubitOp N) :
    opNorm (heisenbergEvol hH (t : ℂ) A) = opNorm A := by
  set U := complexPropagator hH (t : ℂ)
  have hU_adj : Uᴴ = complexPropagator hH (-(t : ℂ)) := by
    dsimp only [U]
    rw [complexPropagator_conjTranspose, Complex.conj_ofReal]
  have hU_mul : U * Uᴴ = 1 := by
    rw [hU_adj]; unfold U complexPropagator; rw [hermFunc_mul]
    have h1 : (fun E : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (E : ℂ)) *
        Complex.exp (Complex.I * (-(t : ℂ)) * (E : ℂ))) = fun _ ↦ 1 := by
      funext E; rw [← Complex.exp_add]
      have : Complex.I * (t : ℂ) * (E : ℂ) + Complex.I * (-(t : ℂ)) * (E : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [h1, hermFunc_one]
  have hU_mul' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU_mul
  have hU_le : opNorm U ≤ 1 := opNorm_unitary_le hU_mul'
  have hUH_le : opNorm Uᴴ ≤ 1 := opNorm_unitary_le (by rw [Matrix.conjTranspose_conjTranspose]; exact hU_mul)
  have hA_nn : 0 ≤ opNorm A := opNorm_nonneg A
  have hle : opNorm (U * A * Uᴴ) ≤ opNorm A := by
    calc opNorm (U * A * Uᴴ)
        ≤ opNorm (U * A) * opNorm Uᴴ := opNorm_mul_le _ _
      _ ≤ (opNorm U * opNorm A) * opNorm Uᴴ :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * opNorm A) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hU_le hA_nn) hUH_le
            (opNorm_nonneg _) (by linarith)
      _ = opNorm A := by ring
  have hge : opNorm A ≤ opNorm (U * A * Uᴴ) := by
    have hUAU_nn : 0 ≤ opNorm (U * A * Uᴴ) := opNorm_nonneg _
    have hrec : A = Uᴴ * (U * A * Uᴴ) * U := by
      calc A = 1 * A * 1 := by simp
        _ = (Uᴴ * U) * A * (Uᴴ * U) := by rw [hU_mul']
        _ = Uᴴ * (U * A * Uᴴ) * U := by simp only [Matrix.mul_assoc]
    calc opNorm A = opNorm (Uᴴ * (U * A * Uᴴ) * U) := by rw [← hrec]
      _ ≤ opNorm (Uᴴ * (U * A * Uᴴ)) * opNorm U := opNorm_mul_le _ _
      _ ≤ (opNorm Uᴴ * opNorm (U * A * Uᴴ)) * opNorm U :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * opNorm (U * A * Uᴴ)) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hUH_le hUAU_nn) hU_le
            (opNorm_nonneg _) (by linarith)
      _ = opNorm (U * A * Uᴴ) := by ring
  have heq : heisenbergEvol hH (t : ℂ) A = U * A * Uᴴ := by
    unfold heisenbergEvol; rw [← hU_adj]
  rw [heq]
  exact le_antisymm hle hge

/-- Continuous linear map embedding `QubitOp N` into bounded operators on `EuclideanSpace ℂ (QubitIdx N)`. -/
noncomputable def opToCLM_CLM (N : ℕ) :
    QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
  LinearMap.toContinuousLinearMap
    { toFun := opToCLM
      map_add' := opToCLM_add
      map_smul' := fun c A ↦ by simp [opToCLM_smul] }

lemma opNorm_eq_norm_opToCLM_CLM {N : ℕ} (A : QubitOp N) :
    opNorm A = ‖opToCLM_CLM N A‖ := rfl

lemma continuous_opNorm {N : ℕ} : Continuous (opNorm (N := N)) :=
  continuous_norm.comp (opToCLM_CLM N).continuous

/-- Matrix decomposition into standard basis units `Matrix.single i j 1`. -/
private lemma matrix_eq_sum_single {N : ℕ} (A : QubitOp N) :
    A = ∑ i : QubitIdx N, ∑ j : QubitIdx N, A i j • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hjb; simp [hjb]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hia
    apply Finset.sum_eq_zero; intro j _
    simp [hia]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Lift entrywise `HasDerivAt` on `QubitOp N` to `HasDerivAt` of `opToCLM_CLM N ∘ D`. -/
private lemma hasDerivAt_opToCLM_of_entry {N : ℕ} (D : ℝ → QubitOp N) (D' : QubitOp N) (s : ℝ)
    (hD : ∀ i j : QubitIdx N, HasDerivAt (fun u : ℝ ↦ D u i j) (D' i j) s) :
    HasDerivAt (fun u : ℝ ↦ opToCLM_CLM N (D u)) (opToCLM_CLM N D') s := by
  have heq : (fun u : ℝ ↦ opToCLM_CLM N (D u)) =
      fun u : ℝ ↦ ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        (D u i j) • opToCLM_CLM N (Matrix.single i j (1 : ℂ)) := by
    funext u
    conv_lhs => rw [matrix_eq_sum_single (D u)]
    simp only [map_sum, map_smul]
  have heq' : opToCLM_CLM N D' =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        (D' i j) • opToCLM_CLM N (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [matrix_eq_sum_single D']
    simp only [map_sum, map_smul]
  rw [heq, heq']
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (hD i j).smul_const (opToCLM_CLM N (Matrix.single i j (1 : ℂ)))

/-- Entrywise continuity of `heisenbergEvol hH (s : ℂ) A`. -/
private lemma continuous_heisenbergEvol_real {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (A : QubitOp N) : Continuous (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) A) :=
  continuous_matrix fun i j ↦ continuous_iff_continuousAt.mpr fun s ↦
    (heisenbergEvol_entry_hasDerivAt hH A s i j).continuousAt

/-- At `t = 0`, `heisenbergEvol hH 0 A = A`. -/
private lemma heisenbergEvol_zero_real {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (A : QubitOp N) :
    heisenbergEvol hH 0 A = A := by
  unfold heisenbergEvol complexPropagator
  have h0 : (fun E : ℝ ↦ Complex.exp (Complex.I * 0 * (E : ℂ))) = fun _ ↦ 1 := by
    funext E; simp
  have h0' : (fun E : ℝ ↦ Complex.exp (Complex.I * -0 * (E : ℂ))) = fun _ ↦ 1 := by
    funext E; simp
  rw [h0, h0', hermFunc_one, Matrix.one_mul, Matrix.mul_one]

/-- **Norm-Preserving Differential Inequality**:
If `K, M, R : ℝ → QubitOp N` satisfy entrywise `K'(s) = i [M(s), K(s)] + R(s)` with `M(s)`
Hermitian and `R` continuous, then for all `t ≥ 0`:
`opNorm (K t) ≤ opNorm (K 0) + ∫ s in (0 : ℝ)..t, opNorm (R s)`. -/
theorem opNorm_le_add_integral_of_deriv_comm_herm {N : ℕ}
    (K M R : ℝ → QubitOp N)
    (hK_deriv : ∀ (s : ℝ) (i j : QubitIdx N),
      HasDerivAt (fun u : ℝ ↦ K u i j) ((Complex.I • matComm (M s) (K s) + R s) i j) s)
    (hM_herm : ∀ s : ℝ, (M s).IsHermitian)
    (hR_cont : Continuous R)
    {t : ℝ} (ht : 0 ≤ t) :
    opNorm (K t) ≤ opNorm (K 0) + ∫ s in (0 : ℝ)..t, opNorm (R s) := by
  have hK_cont : Continuous K :=
    continuous_matrix fun i j ↦ continuous_iff_continuousAt.mpr fun s ↦ (hK_deriv s i j).continuousAt
  have hRn_cont : Continuous (fun s ↦ opNorm (R s)) := continuous_opNorm.comp hR_cont
  have hInt_cont : Continuous (fun s ↦ ∫ u in (0 : ℝ)..s, opNorm (R u)) :=
    intervalIntegral.continuous_primitive (fun a b ↦ hRn_cont.intervalIntegrable a b) 0
  suffices hε : ∀ ε : ℝ, 0 < ε →
      opNorm (K t) - (∫ u in (0 : ℝ)..t, opNorm (R u)) - ε * t ≤ opNorm (K 0) by
    by_contra hlt
    push Not at hlt
    by_cases ht0 : t = 0
    · subst ht0; simp at hlt
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      set δ := (opNorm (K t) - (opNorm (K 0) + ∫ s in (0 : ℝ)..t, opNorm (R s))) / (2 * t)
      have hδpos : 0 < δ := by positivity
      have h1 := hε δ hδpos
      have h2 : δ * t = (opNorm (K t) - (opNorm (K 0) + ∫ s in (0 : ℝ)..t, opNorm (R s))) / 2 := by
        dsimp only [δ]; field_simp [htpos.ne']
      linarith
  intro ε hε
  let ψ : ℝ → ℝ := fun s ↦ opNorm (K s) - (∫ u in (0 : ℝ)..s, opNorm (R u)) - ε * s
  have hψ_cont : Continuous ψ :=
    ((continuous_opNorm.comp hK_cont).sub hInt_cont).sub (continuous_const.mul continuous_id)
  have hψ0 : ψ 0 = opNorm (K 0) := by simp [ψ]
  by_contra hgt
  push Not at hgt
  let S : Set ℝ := { s ∈ Set.Icc (0 : ℝ) t | ψ s ≤ ψ 0 }
  have hS_ne : S.Nonempty := ⟨0, ⟨⟨le_rfl, ht⟩, le_rfl⟩⟩
  have hS_closed : IsClosed S :=
    isClosed_Icc.inter (isClosed_le hψ_cont continuous_const)
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed (fun _ hs ↦ hs.1)
  have hs₀_mem : sSup S ∈ S := hS_compact.sSup_mem hS_ne
  set s₀ : ℝ := sSup S
  have hs₀_le_t : s₀ ≤ t := hs₀_mem.1.2
  have hs₀_lt_t : s₀ < t := by
    refine lt_of_le_of_ne hs₀_le_t ?_
    intro heq
    have h1 : ψ t ≤ ψ 0 := heq ▸ hs₀_mem.2
    dsimp only [ψ] at h1
    linarith [hψ0]
  have hgt_after : ∀ s, s₀ < s → s ≤ t → ψ 0 < ψ s := by
    intro s hs1 hs2
    by_contra hle
    push Not at hle
    have hmem : s ∈ S := ⟨⟨le_trans hs₀_mem.1.1 hs1.le, hs2⟩, hle⟩
    have : s ≤ s₀ := le_csSup hS_compact.bddAbove hmem
    linarith
  let D : ℝ → QubitOp N := fun δ ↦ K (s₀ + δ) - heisenbergEvol (hM_herm s₀) (δ : ℂ) (K s₀)
  have hD0 : D 0 = 0 := by
    dsimp only [D]; rw [add_zero, Complex.ofReal_zero, heisenbergEvol_zero_real, sub_self]
  have hD_entry : ∀ i j : QubitIdx N, HasDerivAt (fun δ : ℝ ↦ D δ i j) (R s₀ i j) 0 := by
    intro i j
    have hK_shift : HasDerivAt (fun δ : ℝ ↦ K (s₀ + δ) i j)
        ((Complex.I • matComm (M s₀) (K s₀) + R s₀) i j) 0 := by
      have h1 : HasDerivAt (fun δ : ℝ ↦ s₀ + δ) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add s₀
      have hK_s0 : HasDerivAt (fun u : ℝ ↦ K u i j)
          ((Complex.I • matComm (M s₀) (K s₀) + R s₀) i j) (s₀ + 0) := by
        simpa using hK_deriv s₀ i j
      have h2 := hK_s0.scomp (0 : ℝ) h1
      simpa [Function.comp_def] using h2
    have hE_deriv : HasDerivAt (fun δ : ℝ ↦ heisenbergEvol (hM_herm s₀) (δ : ℂ) (K s₀) i j)
        ((Complex.I • matComm (M s₀) (K s₀)) i j) 0 := by
      have h1 := heisenbergEvol_entry_hasDerivAt (hM_herm s₀) (K s₀) 0 i j
      simpa [heisenbergEvol_zero_real] using h1
    exact (hK_shift.sub hE_deriv).congr_deriv (by simp only [Matrix.add_apply]; ring)
  let φ : ℝ → (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
    fun δ ↦ opToCLM_CLM N (D δ)
  have hφ_deriv : HasDerivAt φ (opToCLM_CLM N (R s₀)) 0 :=
    hasDerivAt_opToCLM_of_entry D (R s₀) 0 hD_entry
  have hφ0 : φ 0 = 0 := by simp [φ, hD0]
  have hφ_slope := hφ_deriv.tendsto_slope_zero_right
  have hInt_deriv : HasDerivAt (fun s : ℝ ↦ ∫ u in (0 : ℝ)..s, opNorm (R u)) (opNorm (R s₀)) s₀ :=
    intervalIntegral.integral_hasDerivAt_right
      (hRn_cont.intervalIntegrable 0 s₀)
      (hRn_cont.stronglyMeasurableAtFilter _ _)
      hRn_cont.continuousAt
  have hInt_slope : Filter.Tendsto
      (fun δ : ℝ ↦ δ⁻¹ * ((∫ u in (0 : ℝ)..(s₀ + δ), opNorm (R u)) - ∫ u in (0 : ℝ)..s₀, opNorm (R u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (opNorm (R s₀))) := by
    simpa [slope_def_field, div_eq_inv_mul] using hInt_deriv.tendsto_slope_zero_right
  have h1_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖δ⁻¹ • φ δ - opToCLM_CLM N (R s₀)‖ < ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hφ_slope) (ε / 4) (by linarith)
    refine h.mono fun δ hδ ↦ ?_
    simpa [slope, hφ0, dist_eq_norm] using hδ
  have h2_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |δ⁻¹ * ((∫ u in (0 : ℝ)..(s₀ + δ), opNorm (R u)) - ∫ u in (0 : ℝ)..s₀, opNorm (R u)) -
        opNorm (R s₀)| < ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hInt_slope) (ε / 4) (by linarith)
    refine h.mono fun δ hδ ↦ ?_
    simpa [Real.dist_eq] using hδ
  have h3_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < t - s₀ :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (sub_pos.mpr hs₀_lt_t))
  have h4_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ :=
    self_mem_nhdsWithin
  rcases ((h1_ev.and h2_ev).and (h3_ev.and h4_ev)).exists with ⟨δ, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hD_norm : opNorm (D δ) ≤ δ * (opNorm (R s₀) + ε / 4) := by
    have htri : ‖δ⁻¹ • φ δ‖ ≤ ‖opToCLM_CLM N (R s₀)‖ + ε / 4 := by
      have := norm_sub_norm_le (δ⁻¹ • φ δ) (opToCLM_CLM N (R s₀))
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h4)] at htri
    have hmul := mul_le_mul_of_nonneg_left htri h4.le
    rw [← mul_assoc, mul_inv_cancel₀ h4.ne', one_mul] at hmul
    exact hmul
  have hK_diff : opNorm (K (s₀ + δ)) - opNorm (K s₀) ≤ opNorm (D δ) := by
    have h1eq : K (s₀ + δ) = heisenbergEvol (hM_herm s₀) (δ : ℂ) (K s₀) + D δ := by
      dsimp only [D]; abel
    have h2le : opNorm (K (s₀ + δ)) ≤ opNorm (heisenbergEvol (hM_herm s₀) (δ : ℂ) (K s₀)) + opNorm (D δ) := by
      rw [h1eq]; exact opNorm_add_le _ _
    rw [opNorm_heisenbergEvol_real (hM_herm s₀) δ (K s₀)] at h2le
    linarith
  have hInt_diff : δ * (opNorm (R s₀) - ε / 4) ≤
      (∫ u in (0 : ℝ)..(s₀ + δ), opNorm (R u)) - ∫ u in (0 : ℝ)..s₀, opNorm (R u) := by
    have hlow : opNorm (R s₀) - ε / 4 ≤
        δ⁻¹ * ((∫ u in (0 : ℝ)..(s₀ + δ), opNorm (R u)) - ∫ u in (0 : ℝ)..s₀, opNorm (R u)) := by
      linarith [(abs_lt.mp h2).1]
    have hmul := mul_le_mul_of_nonneg_left hlow h4.le
    rw [← mul_assoc, mul_inv_cancel₀ h4.ne', one_mul] at hmul
    exact hmul
  have hψ_dec : ψ (s₀ + δ) < ψ s₀ := by
    dsimp only [ψ]
    nlinarith
  have hψ_gt : ψ 0 < ψ (s₀ + δ) := hgt_after (s₀ + δ) (by linarith) (by linarith)
  linarith [hs₀_mem.2]

end NormPreservingDerivation

section AllTimeLiebRobinson

private lemma isHermitian_heisenbergEvol_real {N : ℕ} {H A : QubitOp N}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (s : ℝ) :
    (heisenbergEvol hH (s : ℂ) A).IsHermitian := by
  unfold heisenbergEvol
  have hc1 : (complexPropagator hH (s : ℂ))ᴴ = complexPropagator hH (-(s : ℂ)) := by
    rw [complexPropagator_conjTranspose, Complex.conj_ofReal]
  have hc2 : (complexPropagator hH (-(s : ℂ)))ᴴ = complexPropagator hH (s : ℂ) := by
    rw [complexPropagator_conjTranspose, map_neg, Complex.conj_ofReal, neg_neg]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hc1, hc2, hA.eq,
    Matrix.mul_assoc]

private lemma heisenbergEvol_mul {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (A B : QubitOp N) :
    heisenbergEvol hH z (A * B) = heisenbergEvol hH z A * heisenbergEvol hH z B := by
  unfold heisenbergEvol complexPropagator
  have h1 : hermFunc hH (fun E ↦ Complex.exp (Complex.I * -z * (E : ℂ))) *
      hermFunc hH (fun E ↦ Complex.exp (Complex.I * z * (E : ℂ))) = 1 := by
    rw [hermFunc_mul]
    have hf : (fun E : ℝ ↦ Complex.exp (Complex.I * -z * (E : ℂ)) *
        Complex.exp (Complex.I * z * (E : ℂ))) = fun _ ↦ 1 := by
      funext E; rw [← Complex.exp_add]
      have : Complex.I * -z * (E : ℂ) + Complex.I * z * (E : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [hf, hermFunc_one]
  set P := hermFunc hH (fun E ↦ Complex.exp (Complex.I * z * (E : ℂ)))
  set Q := hermFunc hH (fun E ↦ Complex.exp (Complex.I * -z * (E : ℂ)))
  calc P * (A * B) * Q
      = P * A * 1 * B * Q := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = P * A * (Q * P) * B * Q := by rw [h1]
    _ = (P * A * Q) * (P * B * Q) := by simp only [Matrix.mul_assoc]

private lemma heisenbergEvol_sub {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (A B : QubitOp N) :
    heisenbergEvol hH z (A - B) = heisenbergEvol hH z A - heisenbergEvol hH z B := by
  unfold heisenbergEvol; simp [Matrix.mul_sub, Matrix.sub_mul]

private lemma heisenbergEvol_sum {N : ℕ} {ι : Type*} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (s : Finset ι) (f : ι → QubitOp N) :
    heisenbergEvol hH z (∑ i ∈ s, f i) = ∑ i ∈ s, heisenbergEvol hH z (f i) := by
  unfold heisenbergEvol
  rw [Matrix.mul_sum, Matrix.sum_mul]

private lemma heisenbergEvol_comm {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (A B : QubitOp N) :
    heisenbergEvol hH z (matComm A B) = matComm (heisenbergEvol hH z A) (heisenbergEvol hH z B) := by
  unfold matComm
  rw [heisenbergEvol_sub, heisenbergEvol_mul, heisenbergEvol_mul]

private lemma heisenbergEvol_self {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z : ℂ) :
    heisenbergEvol hH z H = H := by
  unfold heisenbergEvol complexPropagator
  have hHid : H = hermFunc hH (fun E : ℝ ↦ (E : ℂ)) := (hermFunc_id hH).symm
  have hstep : hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * z * (E : ℂ))) * H *
      hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * -z * (E : ℂ))) =
      hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * z * (E : ℂ))) *
      hermFunc hH (fun E : ℝ ↦ (E : ℂ)) *
      hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * -z * (E : ℂ))) := by
    exact congrArg (fun M ↦ hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * z * (E : ℂ))) * M *
      hermFunc hH (fun E : ℝ ↦ Complex.exp (Complex.I * -z * (E : ℂ)))) hHid
  rw [hstep, hermFunc_mul, hermFunc_mul]
  have hf : (fun E : ℝ ↦ Complex.exp (Complex.I * z * (E : ℂ)) * (E : ℂ) *
      Complex.exp (Complex.I * -z * (E : ℂ))) = fun E : ℝ ↦ (E : ℂ) := by
    funext E
    calc Complex.exp (Complex.I * z * (E : ℂ)) * (E : ℂ) * Complex.exp (Complex.I * -z * (E : ℂ))
        = (Complex.exp (Complex.I * z * (E : ℂ)) * Complex.exp (Complex.I * -z * (E : ℂ))) * (E : ℂ) := by ring
      _ = Complex.exp (Complex.I * z * (E : ℂ) + Complex.I * -z * (E : ℂ)) * (E : ℂ) := by
          rw [← Complex.exp_add]
      _ = (E : ℂ) := by
          have : Complex.I * z * (E : ℂ) + Complex.I * -z * (E : ℂ) = 0 := by ring
          rw [this, Complex.exp_zero, one_mul]
  rw [hf, hermFunc_id hH]

private lemma matComm_jacobi {N : ℕ} (X Y Z : QubitOp N) :
    matComm (matComm X Y) Z = matComm X (matComm Y Z) - matComm Y (matComm X Z) := by
  unfold matComm; noncomm_ring

/-- One-step Nachtergaele–Sims integral inequality for any local operator `A ∈ supportedOn U`. -/
theorem lieb_robinson_integral_step {N : ℕ}
    (E : Finset (Finset (Fin N)))
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hh_herm : ∀ X ∈ E, (h X).IsHermitian)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {U : Finset (Fin N)} {A : QubitOp N} (B : QubitOp N) (hA : A ∈ supportedOn U)
    {t : ℝ} (ht : 0 ≤ t) :
    opNorm (matComm (heisenbergEvol hH (t : ℂ) A) B) ≤
      opNorm (matComm A B) +
      2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
        ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) := by
  classical
  let Hbd : QubitOp N := ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U), h Y
  have hHbd_herm : Hbd.IsHermitian := by
    dsimp only [Hbd]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun Y hY ↦ (hh_herm Y (Finset.mem_filter.mp hY).1).eq
  have hcomm_eq : matComm (∑ X ∈ E, h X) A = matComm Hbd A := by
    dsimp only [Hbd]
    unfold matComm
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro X hXE hnot
    simp only [Finset.mem_filter, not_and, not_not] at hnot
    have hdisj : Disjoint X U := hnot hXE
    have hcomm := supportedOn_comm_of_disjoint hdisj (hsupp X) hA
    rw [hcomm, sub_self]
  let K : ℝ → QubitOp N := fun s ↦ matComm (heisenbergEvol hH (s : ℂ) A) B
  let M : ℝ → QubitOp N := fun s ↦ heisenbergEvol hH (s : ℂ) Hbd
  let R : ℝ → QubitOp N := fun s ↦
    -(Complex.I • matComm (heisenbergEvol hH (s : ℂ) A) (matComm (M s) B))
  have hK_deriv : ∀ (s : ℝ) (i j : QubitIdx N),
      HasDerivAt (fun u : ℝ ↦ K u i j) ((Complex.I • matComm (M s) (K s) + R s) i j) s := by
    intro s i j
    have hmulL : HasDerivAt (fun u : ℝ ↦ (heisenbergEvol hH (u : ℂ) A * B) i j)
        (((Complex.I • matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A)) * B) i j) s := by
      simp only [Matrix.mul_apply]
      apply HasDerivAt.fun_sum; intro k _
      exact (heisenbergEvol_entry_hasDerivAt hH A s i k).mul_const (B k j)
    have hmulR : HasDerivAt (fun u : ℝ ↦ (B * heisenbergEvol hH (u : ℂ) A) i j)
        ((B * (Complex.I • matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A))) i j) s := by
      simp only [Matrix.mul_apply]
      apply HasDerivAt.fun_sum; intro k _
      exact (heisenbergEvol_entry_hasDerivAt hH A s k j).const_mul (B i k)
    have h2 : matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A) =
        matComm (M s) (heisenbergEvol hH (s : ℂ) A) := by
      calc matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A)
          = matComm (heisenbergEvol hH (s : ℂ) (∑ X ∈ E, h X)) (heisenbergEvol hH (s : ℂ) A) := by
              rw [heisenbergEvol_self hH]
        _ = heisenbergEvol hH (s : ℂ) (matComm (∑ X ∈ E, h X) A) :=
              (heisenbergEvol_comm hH _ _ _).symm
        _ = heisenbergEvol hH (s : ℂ) (matComm Hbd A) := by rw [hcomm_eq]
        _ = matComm (M s) (heisenbergEvol hH (s : ℂ) A) := heisenbergEvol_comm hH _ _ _
    have hmat : (Complex.I • matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A)) * B -
        B * (Complex.I • matComm (∑ X ∈ E, h X) (heisenbergEvol hH (s : ℂ) A)) =
        Complex.I • matComm (M s) (K s) + R s := by
      rw [h2, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      change Complex.I • matComm (matComm (M s) (heisenbergEvol hH (s : ℂ) A)) B =
        Complex.I • matComm (M s) (K s) + R s
      rw [matComm_jacobi, smul_sub, sub_eq_add_neg]
    exact (hmulL.sub hmulR).congr_deriv (congrFun (congrFun hmat i) j)
  have hM_herm : ∀ s : ℝ, (M s).IsHermitian := fun s ↦
    isHermitian_heisenbergEvol_real hH hHbd_herm s
  have hR_cont : Continuous R := by
    have hA_cont : Continuous (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) A) :=
      continuous_heisenbergEvol_real hH A
    have hM_cont : Continuous M := continuous_heisenbergEvol_real hH Hbd
    dsimp only [R, matComm]
    fun_prop
  have hstep := opNorm_le_add_integral_of_deriv_comm_herm K M R hK_deriv hM_herm hR_cont ht
  have hK0 : K 0 = matComm A B := by
    dsimp only [K]; rw [Complex.ofReal_zero, heisenbergEvol_zero_real]
  rw [hK0] at hstep
  have hA_nn : 0 ≤ opNorm A := opNorm_nonneg A
  have hR_le : ∀ s : ℝ, opNorm (R s) ≤
      2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
        opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) := by
    intro s
    have hcomm_op : ∀ X Y : QubitOp N, opNorm (matComm X Y) ≤ 2 * opNorm X * opNorm Y := by
      intro X Y
      unfold matComm
      have hsub : X * Y - Y * X = X * Y + (-1 : ℂ) • (Y * X) := by rw [neg_one_smul, sub_eq_add_neg]
      rw [hsub]
      calc opNorm (X * Y + (-1 : ℂ) • (Y * X))
          ≤ opNorm (X * Y) + opNorm ((-1 : ℂ) • (Y * X)) := opNorm_add_le _ _
        _ = opNorm (X * Y) + opNorm (Y * X) := by rw [opNorm_smul]; simp
        _ ≤ opNorm X * opNorm Y + opNorm Y * opNorm X := add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
        _ = 2 * opNorm X * opNorm Y := by ring
    have hRnorm : opNorm (R s) = opNorm (matComm (heisenbergEvol hH (s : ℂ) A) (matComm (M s) B)) := by
      dsimp only [R]
      have hneg : -(Complex.I • matComm (heisenbergEvol hH (s : ℂ) A) (matComm (M s) B)) =
          (-Complex.I) • matComm (heisenbergEvol hH (s : ℂ) A) (matComm (M s) B) := by
        rw [neg_smul]
      rw [hneg, opNorm_smul]
      simp
    rw [hRnorm]
    have hMB_eq : matComm (M s) B = ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
        matComm (heisenbergEvol hH (s : ℂ) (h Y)) B := by
      dsimp only [M, Hbd]
      rw [heisenbergEvol_sum]
      unfold matComm
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc opNorm (matComm (heisenbergEvol hH (s : ℂ) A) (matComm (M s) B))
        ≤ 2 * opNorm (heisenbergEvol hH (s : ℂ) A) * opNorm (matComm (M s) B) := hcomm_op _ _
      _ = 2 * opNorm A * opNorm (matComm (M s) B) := by rw [opNorm_heisenbergEvol_real hH s A]
      _ ≤ 2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
            opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [hMB_eq]
          exact opNorm_sum_le _ _
  have hInt_le : ∫ s in (0 : ℝ)..t, opNorm (R s) ≤
      2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
        ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) := by
    have hcont_Y : ∀ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
        Continuous (fun s : ℝ ↦ opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B)) := by
      intro Y _
      have hc : Continuous (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) (h Y)) :=
        continuous_heisenbergEvol_real hH (h Y)
      refine continuous_opNorm.comp ?_
      unfold matComm; fun_prop
    have hsum_int : (∫ s in (0 : ℝ)..t,
        2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
          opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B)) =
        2 * opNorm A * ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U),
          ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact intervalIntegral.integral_finset_sum fun Y hY ↦
        (hcont_Y Y hY).intervalIntegrable 0 t
    rw [← hsum_int]
    refine intervalIntegral.integral_mono_on ht
      ((continuous_opNorm.comp hR_cont).intervalIntegrable 0 t)
      ((continuous_const.mul (continuous_finset_sum _ hcont_Y)).intervalIntegrable 0 t)
      (fun s _ ↦ hR_le s)
  linarith

/-- Recursive Lieb–Robinson path-sum coefficients `lrPathCoeff E h B V k X`. -/
noncomputable def lrPathCoeff {N : ℕ} [DecidableEq (Finset (Fin N))]
    (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N)
    (B : QubitOp N) (V : Finset (Fin N)) : ℕ → Finset (Fin N) → ℝ
  | 0, X => if Disjoint X V then 0 else 2 * opNorm (h X) * opNorm B
  | k + 1, X => 2 * opNorm (h X) *
      ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X), lrPathCoeff E h B V k Y

/-- Vanishing of Lieb–Robinson path-sum coefficients below the light-cone distance. -/
lemma lrPathCoeff_zero_of_sep {N R_int : ℕ} [DecidableEq (Finset (Fin N))]
    (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N)))
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (B : QubitOp N) (V : Finset (Fin N)) :
    ∀ k : ℕ, ∀ X : Finset (Fin N),
      (∀ x ∈ X, ∀ v ∈ V, k * R_int < dist x v) →
      lrPathCoeff E h B V k X = 0 := by
  intro k
  induction k with
  | zero =>
    intro X hsep
    simp only [lrPathCoeff]
    rw [if_pos]
    rw [Finset.disjoint_left]
    intro x hxX hxV
    have h0 := hsep x hxX x hxV
    rw [hself x] at h0; omega
  | succ k ih =>
    intro X hsep
    simp only [lrPathCoeff]
    have hsum0 : ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X), lrPathCoeff E h B V k Y = 0 := by
      apply Finset.sum_eq_zero; intro Y hY
      rcases Finset.mem_filter.mp hY with ⟨hYE, hnd⟩
      rcases Finset.not_disjoint_iff.mp hnd with ⟨z, hzY, hzX⟩
      apply ih Y
      intro y hyY v hvV
      have hd1 : dist z v ≤ dist z y + dist y v := htri z y v
      have hd2 : dist z y ≤ R_int := hdiam Y hYE z hzY y hyY
      have hd3 : (k + 1) * R_int < dist z v := hsep z hzX v hvV
      have : (k + 1) * R_int = k * R_int + R_int := by ring
      omega
    rw [hsum0, mul_zero]

private lemma sum_touching_opNorm_le {N : ℕ}
    (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (h Y) ≤ J)
    (U : Finset (Fin N)) :
    ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U), opNorm (h Y) ≤ (U.card : ℝ) * J := by
  have hsub : E.filter (fun Y ↦ ¬Disjoint Y U) ⊆
      U.biUnion (fun x ↦ E.filter (fun Y ↦ x ∈ Y)) := by
    intro Y hY
    rcases Finset.mem_filter.mp hY with ⟨hYE, hnd⟩
    rcases Finset.not_disjoint_iff.mp hnd with ⟨x, hxY, hxU⟩
    exact Finset.mem_biUnion.mpr ⟨x, hxU, Finset.mem_filter.mpr ⟨hYE, hxY⟩⟩
  calc ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U), opNorm (h Y)
      ≤ ∑ Y ∈ U.biUnion (fun x ↦ E.filter (fun Y ↦ x ∈ Y)), opNorm (h Y) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ opNorm_nonneg _
    _ ≤ ∑ x ∈ U, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (h Y) :=
        real_sum_biUnion_le _ _ _ fun _ _ ↦ opNorm_nonneg _
    _ ≤ ∑ _x ∈ U, J := Finset.sum_le_sum fun x _ ↦ hsite x
    _ = (U.card : ℝ) * J := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Inductive `k`-step Nachtergaele–Sims bound for `f_X(t) = ‖[h_X(t), B]‖_op` for ALL `t ≥ 0`. -/
lemma lieb_robinson_iterated_bound {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hh_herm : ∀ X ∈ E, (h X).IsHermitian)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (h Y) ≤ J)
    {V : Finset (Fin N)} {B : QubitOp N} (hB : B ∈ supportedOn V) :
    ∀ k : ℕ, ∀ X ∈ E, ∀ t : ℝ, 0 ≤ t →
      opNorm (matComm (heisenbergEvol hH (t : ℂ) (h X)) B) ≤
        (∑ j ∈ Finset.range k, lrPathCoeff E h B V j X * (t ^ j / (j.factorial : ℝ))) +
        2 * opNorm (h X) * opNorm B * ((2 * (r : ℝ) * J * t) ^ k / (k.factorial : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro X _ t _
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one]
    unfold matComm
    have hsub : heisenbergEvol hH (t : ℂ) (h X) * B - B * heisenbergEvol hH (t : ℂ) (h X) =
        heisenbergEvol hH (t : ℂ) (h X) * B + (-1 : ℂ) • (B * heisenbergEvol hH (t : ℂ) (h X)) := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [hsub]
    calc opNorm (heisenbergEvol hH (t : ℂ) (h X) * B + (-1 : ℂ) • (B * heisenbergEvol hH (t : ℂ) (h X)))
        ≤ opNorm (heisenbergEvol hH (t : ℂ) (h X) * B) +
            opNorm ((-1 : ℂ) • (B * heisenbergEvol hH (t : ℂ) (h X))) := opNorm_add_le _ _
      _ = opNorm (heisenbergEvol hH (t : ℂ) (h X) * B) +
            opNorm (B * heisenbergEvol hH (t : ℂ) (h X)) := by rw [opNorm_smul]; simp
      _ ≤ opNorm (heisenbergEvol hH (t : ℂ) (h X)) * opNorm B +
            opNorm B * opNorm (heisenbergEvol hH (t : ℂ) (h X)) :=
          add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
      _ = 2 * opNorm (h X) * opNorm B := by rw [opNorm_heisenbergEvol_real hH t (h X)]; ring
  | succ k ih =>
    intro X hXE t ht
    have hstep := lieb_robinson_integral_step E h hsupp hh_herm hH B (hsupp X) ht
    have hf0 : opNorm (matComm (h X) B) ≤ lrPathCoeff E h B V 0 X := by
      simp only [lrPathCoeff]
      by_cases hd : Disjoint X V
      · rw [if_pos hd]
        have hcomm := supportedOn_comm_of_disjoint hd (hsupp X) hB
        unfold matComm; rw [hcomm, sub_self]; simp [opNorm, opToCLM]
      · rw [if_neg hd]
        unfold matComm
        have hsub : h X * B - B * h X = h X * B + (-1 : ℂ) • (B * h X) := by
          rw [neg_one_smul, sub_eq_add_neg]
        rw [hsub]
        calc opNorm (h X * B + (-1 : ℂ) • (B * h X))
            ≤ opNorm (h X * B) + opNorm ((-1 : ℂ) • (B * h X)) := opNorm_add_le _ _
          _ = opNorm (h X * B) + opNorm (B * h X) := by rw [opNorm_smul]; simp
          _ ≤ opNorm (h X) * opNorm B + opNorm B * opNorm (h X) :=
              add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
          _ = 2 * opNorm (h X) * opNorm B := by ring
    have hpow_int : ∀ j : ℕ, ∫ s in (0 : ℝ)..t, s ^ j / (j.factorial : ℝ) =
        t ^ (j + 1) / ((j + 1).factorial : ℝ) := by
      intro j
      rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero j), sub_zero]
      rw [div_div, Nat.factorial_succ]
      push_cast; ring
    have hint_Y : ∀ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X),
        ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) ≤
          (∑ j ∈ Finset.range k, lrPathCoeff E h B V j Y * (t ^ (j + 1) / ((j + 1).factorial : ℝ))) +
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) := by
      intro Y hY
      have hYE := (Finset.mem_filter.mp hY).1
      have hcont_lhs : Continuous (fun s : ℝ ↦ opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B)) := by
        have hc : Continuous (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) (h Y)) :=
          continuous_heisenbergEvol_real hH (h Y)
        refine continuous_opNorm.comp ?_
        unfold matComm; fun_prop
      have hcont_sum : Continuous (fun s : ℝ ↦
          ∑ j ∈ Finset.range k, lrPathCoeff E h B V j Y * (s ^ j / (j.factorial : ℝ))) :=
        continuous_finset_sum _ fun j _ ↦ by fun_prop
      have hcont_rem : Continuous (fun s : ℝ ↦
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ k / (k.factorial : ℝ))) := by
        fun_prop
      have hmono := intervalIntegral.integral_mono_on ht
        (hcont_lhs.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
        ((hcont_sum.add hcont_rem).intervalIntegrable (μ := MeasureTheory.volume) 0 t)
        (fun s hs ↦ ih Y hYE s hs.1)
      refine le_trans hmono ?_
      dsimp only [Pi.add_apply]
      rw [intervalIntegral.integral_add
        (hcont_sum.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
        (hcont_rem.intervalIntegrable (μ := MeasureTheory.volume) 0 t)]
      have h1 : ∫ s in (0 : ℝ)..t,
          ∑ j ∈ Finset.range k, lrPathCoeff E h B V j Y * (s ^ j / (j.factorial : ℝ)) =
          ∑ j ∈ Finset.range k, lrPathCoeff E h B V j Y * (t ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
        rw [intervalIntegral.integral_finset_sum fun j _ ↦
          (by fun_prop : Continuous fun s : ℝ ↦
            lrPathCoeff E h B V j Y * (s ^ j / (j.factorial : ℝ))).intervalIntegrable
            (μ := MeasureTheory.volume) 0 t]
        apply Finset.sum_congr rfl; intro j _
        rw [intervalIntegral.integral_const_mul, hpow_int j]
      have h2 : ∫ s in (0 : ℝ)..t,
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ k / (k.factorial : ℝ)) =
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) := by
        have hrew : (fun s : ℝ ↦ 2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ k / (k.factorial : ℝ))) =
            fun s : ℝ ↦ (2 * opNorm (h Y) * opNorm B * (2 * (r : ℝ) * J) ^ k) * (s ^ k / (k.factorial : ℝ)) := by
          funext s; rw [mul_pow]; ring
        rw [hrew, intervalIntegral.integral_const_mul, hpow_int k]; ring
      rw [h1, h2]
    have hsum_Y := Finset.sum_le_sum hint_Y
    rw [Finset.sum_add_distrib] at hsum_Y
    have hmain_eq : 2 * opNorm (h X) *
        ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X),
          ∑ j ∈ Finset.range k, lrPathCoeff E h B V j Y * (t ^ (j + 1) / ((j + 1).factorial : ℝ)) =
        ∑ j ∈ Finset.range k, lrPathCoeff E h B V (j + 1) X * (t ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [← Finset.sum_mul, ← mul_assoc]
      rfl
    have hrem_le : 2 * opNorm (h X) *
        ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X),
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) ≤
        2 * opNorm (h X) * opNorm B * ((2 * (r : ℝ) * J * t) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
      have hfac : ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X),
          2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) =
          (∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X), opNorm (h Y)) *
            (2 * opNorm B * (2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro Y _; ring
      rw [hfac]
      have htouch : ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y X), opNorm (h Y) ≤ (r : ℝ) * J :=
        le_trans (sum_touching_opNorm_le E h hJ hsite X)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard X hXE) hJ)
      have hnn : 0 ≤ 2 * opNorm B * (2 * (r : ℝ) * J) ^ k * (t ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
        have := opNorm_nonneg B; positivity
      have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htouch hnn)
        (by have := opNorm_nonneg (h X); linarith : 0 ≤ 2 * opNorm (h X))
      refine le_trans hmul ?_
      rw [mul_pow, pow_succ]
      ring_nf; exact le_rfl
    have hrange : ∑ j ∈ Finset.range (k + 1), lrPathCoeff E h B V j X * (t ^ j / (j.factorial : ℝ)) =
        lrPathCoeff E h B V 0 X +
        ∑ j ∈ Finset.range k, lrPathCoeff E h B V (j + 1) X * (t ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      ring
    rw [hrange]
    have hmul_sum := mul_le_mul_of_nonneg_left hsum_Y
      (by have := opNorm_nonneg (h X); linarith : 0 ≤ 2 * opNorm (h X))
    rw [mul_add, hmain_eq] at hmul_sum
    linarith

/-- **All-Time Finite-Range Lieb–Robinson Bound (Factorial Form, `t ≥ 0`)**:
For any `r`-local (`1 ≤ r`) finite-range (`diam X ≤ R_int`) Hermitian Hamiltonian
`H = ∑ X ∈ E, h X` with `h X = (h X)ᴴ`, local strength `≤ J`, `O ∈ supportedOn U₀`,
`B ∈ supportedOn V`, and `∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y`, for ALL `t ≥ 0`:
`opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B) ≤
  2 * opNorm O * opNorm B * (U₀.card : ℝ) * ((2 * (r : ℝ) * J * t) ^ (m + 1) / ((m + 1).factorial : ℝ))`. -/
theorem all_time_lieb_robinson_factorial_nonneg {N r R_int : ℕ} (hr : 1 ≤ r)
    (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hh_herm : ∀ X ∈ E, (h X).IsHermitian)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (h Y) ≤ J)
    {U₀ V : Finset (Fin N)} {O B : QubitOp N}
    (hO : O ∈ supportedOn U₀) (hB : B ∈ supportedOn V)
    (m : ℕ) (hsep : ∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y)
    {t : ℝ} (ht : 0 ≤ t) :
    opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B) ≤
      2 * opNorm O * opNorm B * (U₀.card : ℝ) *
        ((2 * (r : ℝ) * J * t) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
  classical
  have hstep := lieb_robinson_integral_step E h hsupp hh_herm hH B hO ht
  have hdisj : Disjoint U₀ V := by
    rw [Finset.disjoint_left]
    intro x hxU hxV
    have h0 := hsep x hxU x hxV
    rw [hself x] at h0; omega
  have hf0 : opNorm (matComm O B) = 0 := by
    have hcomm := supportedOn_comm_of_disjoint hdisj hO hB
    unfold matComm; rw [hcomm, sub_self]; simp [opNorm, opToCLM]
  rw [hf0, zero_add] at hstep
  have hY_bound : ∀ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U₀), ∀ s : ℝ, 0 ≤ s →
      opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) ≤
        2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ m / (m.factorial : ℝ)) := by
    intro Y hY s hs
    rcases Finset.mem_filter.mp hY with ⟨hYE, hnd⟩
    rcases Finset.not_disjoint_iff.mp hnd with ⟨z, hzY, hzU₀⟩
    have hit := lieb_robinson_iterated_bound E hcard h hsupp hh_herm hH hJ hsite hB m Y hYE s hs
    have hsum0 : ∑ j ∈ Finset.range m, lrPathCoeff E h B V j Y * (s ^ j / (j.factorial : ℝ)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hc0 : lrPathCoeff E h B V j Y = 0 := by
        apply lrPathCoeff_zero_of_sep dist hself htri E hdiam h B V j Y
        intro y hyY v hvV
        have hd1 : dist z v ≤ dist z y + dist y v := htri z y v
        have hd2 : dist z y ≤ R_int := hdiam Y hYE z hzY y hyY
        have hd3 : m * R_int < dist z v := hsep z hzU₀ v hvV
        have hjm' : (j + 1) * R_int ≤ m * R_int := Nat.mul_le_mul_right R_int hjm
        have : (j + 1) * R_int = j * R_int + R_int := by ring
        omega
      rw [hc0, zero_mul]
    rw [hsum0, zero_add] at hit
    exact hit
  have hint_Y : ∀ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U₀),
      ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) ≤
        2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ))) := by
    intro Y hY
    have hcont_lhs : Continuous (fun s : ℝ ↦ opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B)) := by
      have hc : Continuous (fun s : ℝ ↦ heisenbergEvol hH (s : ℂ) (h Y)) :=
        continuous_heisenbergEvol_real hH (h Y)
      refine continuous_opNorm.comp ?_; unfold matComm; fun_prop
    have hcont_rhs : Continuous (fun s : ℝ ↦
        2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ m / (m.factorial : ℝ))) := by
      fun_prop
    have hmono := intervalIntegral.integral_mono_on ht
      (hcont_lhs.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
      (hcont_rhs.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
      (fun s hs ↦ hY_bound Y hY s hs.1)
    refine le_trans hmono ?_
    have hrew : (fun s : ℝ ↦ 2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J * s) ^ m / (m.factorial : ℝ))) =
        fun s : ℝ ↦ (2 * opNorm (h Y) * opNorm B * (2 * (r : ℝ) * J) ^ m) * (s ^ m / (m.factorial : ℝ)) := by
      funext s; rw [mul_pow]; ring
    rw [hrew, intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow,
      zero_pow (Nat.succ_ne_zero m), sub_zero, div_div, Nat.factorial_succ]
    push_cast; ring_nf; exact le_rfl
  have hsum_le : ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U₀),
      ∫ s in (0 : ℝ)..t, opNorm (matComm (heisenbergEvol hH (s : ℂ) (h Y)) B) ≤
      (U₀.card : ℝ) * J * (2 * opNorm B * (2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ))) := by
    have h1 := Finset.sum_le_sum hint_Y
    have h2 : ∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U₀),
        2 * opNorm (h Y) * opNorm B * ((2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ))) =
        (∑ Y ∈ E.filter (fun Y ↦ ¬Disjoint Y U₀), opNorm (h Y)) *
          (2 * opNorm B * (2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ))) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro Y _; ring
    rw [h2] at h1
    refine le_trans h1 ?_
    apply mul_le_mul_of_nonneg_right (sum_touching_opNorm_le E h hJ hsite U₀)
    have := opNorm_nonneg B; positivity
  refine le_trans hstep ?_
  have hO_nn := opNorm_nonneg O
  have hmul := mul_le_mul_of_nonneg_left hsum_le (by linarith : 0 ≤ 2 * opNorm O)
  refine le_trans hmul ?_
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcore : 2 * opNorm O * ((U₀.card : ℝ) * J * (2 * opNorm B * (2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ)))) ≤
      2 * opNorm O * ((U₀.card : ℝ) * ((r : ℝ) * J) * (2 * opNorm B * (2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ)))) := by
    have hB_nn := opNorm_nonneg B
    have hJ_le : J ≤ (r : ℝ) * J := le_mul_of_one_le_left hJ hr1
    have hnn1 : 0 ≤ 2 * opNorm O := by linarith
    have hnn2 : 0 ≤ 2 * opNorm B * (2 * (r : ℝ) * J) ^ m * (t ^ (m + 1) / ((m + 1).factorial : ℝ)) := by positivity
    have hnn3 : 0 ≤ (U₀.card : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ_le hnn3) hnn2) hnn1
  refine le_trans hcore ?_
  rw [mul_pow, pow_succ]
  ring_nf; exact le_rfl

/-- Elementary factorial-to-exponential tail bound: for `u ≥ 0` and `k : ℕ`,
`u ^ k / k! ≤ exp (e * u - k)`. -/
lemma pow_div_factorial_le_exp_sub {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    u ^ k / (k.factorial : ℝ) ≤ Real.exp (Real.exp 1 * u - (k : ℝ)) := by
  have h1 : (Real.exp 1 * u) ^ k / (k.factorial : ℝ) ≤ Real.exp (Real.exp 1 * u) :=
    Real.pow_div_factorial_le_exp (Real.exp 1 * u) (by positivity) k
  have h2 : Real.exp (Real.exp 1 * u - (k : ℝ)) = Real.exp (Real.exp 1 * u) * Real.exp (-(k : ℝ)) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have h3 : (Real.exp 1) ^ k = Real.exp (k : ℝ) := by
    rw [← Real.exp_nat_mul]; simp
  rw [mul_pow, h3, mul_div_assoc] at h1
  rw [h2]
  have hmul := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(k : ℝ))).le
  have hcancel : Real.exp (k : ℝ) * (u ^ k / (k.factorial : ℝ)) * Real.exp (-(k : ℝ)) =
      u ^ k / (k.factorial : ℝ) := by
    calc Real.exp (k : ℝ) * (u ^ k / (k.factorial : ℝ)) * Real.exp (-(k : ℝ))
        = (Real.exp (k : ℝ) * Real.exp (-(k : ℝ))) * (u ^ k / (k.factorial : ℝ)) := by ring
      _ = Real.exp ((k : ℝ) + -(k : ℝ)) * (u ^ k / (k.factorial : ℝ)) := by rw [← Real.exp_add]
      _ = u ^ k / (k.factorial : ℝ) := by simp
  linarith

/-- **All-Time Finite-Range Lieb–Robinson Bound (Exponential Form, `∀ t : ℝ`)**:
For ANY `t : ℝ` (with NO short-time restriction!), any `r`-local (`1 ≤ r`) finite-range
(`diam X ≤ R_int`) Hermitian Hamiltonian `H = ∑ X ∈ E, h X` with `h X = (h X)ᴴ` and local
strength `≤ J`, `O ∈ supportedOn U₀`, `B ∈ supportedOn V`, and `∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y`:
`opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B) ≤
  2 * opNorm O * opNorm B * (U₀.card : ℝ) * Real.exp (2 * Real.exp 1 * (r : ℝ) * J * |t| - ((m + 1 : ℕ) : ℝ))`. -/
theorem all_time_lieb_robinson_exp {N r R_int : ℕ} (hr : 1 ≤ r)
    (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hh_herm : ∀ X ∈ E, (h X).IsHermitian)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (h Y) ≤ J)
    {U₀ V : Finset (Fin N)} {O B : QubitOp N}
    (hO : O ∈ supportedOn U₀) (hB : B ∈ supportedOn V)
    (m : ℕ) (hsep : ∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y)
    (t : ℝ) :
    opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B) ≤
      2 * opNorm O * opNorm B * (U₀.card : ℝ) *
        Real.exp (2 * Real.exp 1 * (r : ℝ) * J * |t| - ((m + 1 : ℕ) : ℝ)) := by
  have hO_nn := opNorm_nonneg O
  have hB_nn := opNorm_nonneg B
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    have hfac := all_time_lieb_robinson_factorial_nonneg hr dist hself htri E hcard hdiam h hsupp
      hh_herm hH hJ hsite hO hB m hsep ht
    have hexp := pow_div_factorial_le_exp_sub (by positivity : 0 ≤ 2 * (r : ℝ) * J * t) (m + 1)
    have heq : Real.exp 1 * (2 * (r : ℝ) * J * t) = 2 * Real.exp 1 * (r : ℝ) * J * t := by ring
    rw [heq] at hexp
    refine le_trans hfac ?_
    apply mul_le_mul_of_nonneg_left hexp
    positivity
  · push Not at ht
    rw [abs_of_neg ht]
    let hneg : Finset (Fin N) → QubitOp N := fun X ↦ -h X
    have hneg_supp : ∀ X, hneg X ∈ supportedOn X := fun X ↦ (supportedOn X).neg_mem (hsupp X)
    have hneg_herm : ∀ X ∈ E, (hneg X).IsHermitian := fun X hX ↦ by
      dsimp only [hneg]; rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, (hh_herm X hX).eq]
    have hnegH_eq : (∑ X ∈ E, hneg X) = -(∑ X ∈ E, h X) := by
      simp [hneg, Finset.sum_neg_distrib]
    have hnegH : (∑ X ∈ E, hneg X).IsHermitian := by
      rw [hnegH_eq, Matrix.IsHermitian, Matrix.conjTranspose_neg, hH.eq]
    have hneg_site : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), opNorm (hneg Y) ≤ J := by
      intro x
      have heq_n : ∀ Y, opNorm (hneg Y) = opNorm (h Y) := fun Y ↦ by
        dsimp only [hneg]
        have : -h Y = (-1 : ℂ) • h Y := by rw [neg_one_smul]
        rw [this, opNorm_smul]; simp
      simp_rw [heq_n]; exact hsite x
    have hevol_eq : heisenbergEvol hH (t : ℂ) O = heisenbergEvol hnegH ((-t : ℝ) : ℂ) O := by
      have hprop : ∀ s : ℝ, complexPropagator hH (s : ℂ) = complexPropagator hnegH ((-s : ℝ) : ℂ) := by
        intro s
        have h1 := hasSum_hermFunc_exp hH (Complex.I * (s : ℂ))
        have h2 := hasSum_hermFunc_exp hnegH (Complex.I * ((-s : ℝ) : ℂ))
        have hterm : ∀ k : ℕ,
            ((Complex.I * (s : ℂ)) ^ k / (k.factorial : ℂ)) • (∑ X ∈ E, h X) ^ k =
            ((Complex.I * ((-s : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) • (∑ X ∈ E, hneg X) ^ k := by
          intro k
          have hpow_neg : (∑ X ∈ E, hneg X) ^ k = (-1 : ℂ) ^ k • (∑ X ∈ E, h X) ^ k := by
            rw [hnegH_eq, show -(∑ X ∈ E, h X) = (-1 : ℂ) • (∑ X ∈ E, h X) by rw [neg_one_smul],
              smul_pow]
          rw [hpow_neg, smul_smul]
          congr 1
          push_cast
          have : (Complex.I * -(s : ℂ)) ^ k * (-1 : ℂ) ^ k = (Complex.I * (s : ℂ)) ^ k := by
            rw [← mul_pow]; congr 1; ring
          calc (Complex.I * (s : ℂ)) ^ k / (k.factorial : ℂ)
              = ((Complex.I * -(s : ℂ)) ^ k * (-1 : ℂ) ^ k) / (k.factorial : ℂ) := by rw [this]
            _ = (Complex.I * -(s : ℂ)) ^ k / (k.factorial : ℂ) * (-1 : ℂ) ^ k := by ring
        simp_rw [hterm] at h1
        exact h1.unique h2
      unfold heisenbergEvol
      have hp1 := hprop t
      have hp2 := hprop (-t)
      simp only [neg_neg, Complex.ofReal_neg] at hp1 hp2 ⊢
      rw [hp1, hp2]
    rw [hevol_eq]
    have hnt : 0 ≤ -t := by linarith
    have hfac := all_time_lieb_robinson_factorial_nonneg hr dist hself htri E hcard hdiam hneg
      hneg_supp hneg_herm hnegH hJ hneg_site hO hB m hsep (t := -t) hnt
    have hexp := pow_div_factorial_le_exp_sub (by positivity : 0 ≤ 2 * (r : ℝ) * J * (-t)) (m + 1)
    have heq : Real.exp 1 * (2 * (r : ℝ) * J * (-t)) = 2 * Real.exp 1 * (r : ℝ) * J * (-t) := by ring
    rw [heq] at hexp
    refine le_trans hfac ?_
    apply mul_le_mul_of_nonneg_left hexp
    positivity

end AllTimeLiebRobinson

end KrylovChaos
