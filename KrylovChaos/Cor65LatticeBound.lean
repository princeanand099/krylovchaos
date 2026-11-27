/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.AllTimeLiebRobinson
import KrylovChaos.EntropicDecoupling
import KrylovChaos.HighTempParams
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# All-Time Finite-Range Lattice Bound (Corollary 6.5, Eq. 6.10)

Wires `all_time_lieb_robinson_exp` (`AllTimeLiebRobinson.lean`), the shifted commutator
`otocI` (`ShiftedThermalSize.lean`), and unconditional entropic background decoupling
`prop_6_4_part2_unconditional` (`EntropicDecoupling.lean`) to prove Corollary 6.5 (Eq. 6.10)
for ALL real times `t : ℝ` and ALL `N ≥ 1`, strictly on top of Mathlib `v4.35.0`:
1. `gibbsWightmanNormSq_le_opNorm_sq`: `‖X‖_{β,W}² ≤ ‖X‖_op²` for any `X : QubitOp N`.
2. `opNorm_heisenbergEvol_real_le`: `‖O(t)‖_op ≤ ‖O‖_op` for any real `t : ℝ`.
3. `cor_6_5_all_time_eq_6_10`: for any `r`-local finite-range Hermitian Hamiltonian on a
   `d`-dimensional lattice (interaction diameter `≤ R_int`, ball volume `≤ C_vol * (R + 1)^d`),
   `β ∈ [0, highTempBetaWC r Jsite]`, and `s₀`-local `O` (`‖O‖_{β,W} = 1`, `opNorm O ≤ C_O`),
   proves BOTH `otocI hH β (O(t)) ≤ C_LR * (1 + v_LR * |t|) ^ d` and Eq. (6.10) for ALL `t : ℝ`.
-/

namespace KrylovChaos

open scoped BigOperators Matrix
open Matrix Complex Filter Topology

section WightmanAndUnitaryNormHelpers

/-- For any `X : QubitOp N` and Gibbs state `G = concreteGibbsData hH β`,
`gibbsWightmanNormSq G X ≤ opNorm X ^ 2`. -/
lemma gibbsWightmanNormSq_le_opNorm_sq {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (X : QubitOp N) :
    gibbsWightmanNormSq (concreteGibbsData hH β) X ≤ opNorm X ^ 2 := by
  set G := concreteGibbsData hH β
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set Z : ℝ := gibbsPartitionFn hH β
  have hZpos : 0 < Z := gibbsPartitionFn_pos hH β
  let p : QubitIdx N → ℝ := fun i ↦ Real.exp (-β * hH.eigenvalues i) / Z
  have hp_pos : ∀ i, 0 < p i := fun i ↦ div_pos (Real.exp_pos _) hZpos
  have hp_sum : ∑ i : QubitIdx N, p i = 1 := by
    dsimp only [p]; rw [← Finset.sum_div]; exact div_self hZpos.ne'
  set Y : QubitOp N := Uᴴ * X * U
  have hU_unit : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hU'_unit : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hnorm_Y : opNorm Y ≤ opNorm X := by
    have hU_le : opNorm U ≤ 1 := by
      unfold opNorm
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
      rw [one_mul]
      have heq : ‖opToCLM U v‖ ^ 2 = ‖v‖ ^ 2 := by
        simp only [EuclideanSpace.norm_sq_eq, opToCLM, LinearMap.coe_toContinuousLinearMap',
          Matrix.toEuclideanLin_apply]
        have hinner : ∀ w : QubitIdx N → ℂ,
            (∑ i, star (w i) * w i) = ∑ i, ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
          intro w; apply Finset.sum_congr rfl; intro i _
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
        have h1 : ∑ i, star ((U.mulVec v.ofLp) i) * (U.mulVec v.ofLp) i =
            ∑ i, star (v.ofLp i) * v.ofLp i := by
          have hmul : (U.mulVec v.ofLp) ⬝ᵥ star (U.mulVec v.ofLp) =
              v.ofLp ⬝ᵥ star v.ofLp := by
            calc (U.mulVec v.ofLp) ⬝ᵥ star (U.mulVec v.ofLp)
                = star (U.mulVec v.ofLp) ⬝ᵥ (U.mulVec v.ofLp) := dotProduct_comm _ _
              _ = (star v.ofLp ᵥ* Uᴴ) ⬝ᵥ (U.mulVec v.ofLp) := by rw [Matrix.star_mulVec]
              _ = star v.ofLp ⬝ᵥ ((Uᴴ * U).mulVec v.ofLp) := by
                  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
              _ = star v.ofLp ⬝ᵥ v.ofLp := by rw [hU'_unit, Matrix.one_mulVec]
              _ = v.ofLp ⬝ᵥ star v.ofLp := dotProduct_comm _ _
          simpa [dotProduct, mul_comm] using hmul
        rw [hinner, hinner] at h1
        have hre := congrArg Complex.re h1
        simpa [Complex.re_sum] using hre
      nlinarith [norm_nonneg (opToCLM U v), norm_nonneg v]
    have hU'_le : opNorm Uᴴ ≤ 1 := by rw [opNorm_conjTranspose]; exact hU_le
    calc opNorm (Uᴴ * X * U) ≤ opNorm (Uᴴ * X) * opNorm U := opNorm_mul_le _ _
      _ ≤ (opNorm Uᴴ * opNorm X) * opNorm U := mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * opNorm X) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hU'_le (opNorm_nonneg _)) hU_le (opNorm_nonneg _) (by positivity)
      _ = opNorm X := by ring
  have hQ_eq : G.ρQuarter = U * Matrix.diagonal (fun i ↦ ((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ)) * Uᴴ := by
    dsimp only [G, concreteGibbsData, hermFunc, p]
    congr 2; ext i j
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      have hpow : (Real.exp (-β * hH.eigenvalues i) / Z) ^ ((1 : ℝ) / 4) =
          Real.sqrt (Real.sqrt (Real.exp (-β * hH.eigenvalues i) / Z)) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        norm_num
      have hdiv : Real.exp (-(β / 4) * hH.eigenvalues i) / Z ^ ((1 : ℝ) / 4) =
          (Real.exp (-β * hH.eigenvalues i) / Z) ^ ((1 : ℝ) / 4) := by
        rw [Real.div_rpow (Real.exp_pos _).le hZpos.le, ← Real.exp_mul]
        congr 2; ring
      rw [← hpow, ← hdiv]
      simp [Complex.ofReal_div, Complex.ofReal_exp]
    · rfl
  have hJ_eq : jBeta G.ρQuarter X =
      U * (Matrix.diagonal (fun i ↦ ((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ)) * Y *
        Matrix.diagonal (fun j ↦ ((Real.sqrt (Real.sqrt (p j)) : ℝ) : ℂ))) * Uᴴ := by
    unfold jBeta
    rw [hQ_eq]
    dsimp only [Y]
    calc U * Matrix.diagonal _ * Uᴴ * X * (U * Matrix.diagonal _ * Uᴴ)
        = U * (Matrix.diagonal _ * (Uᴴ * X * U) * Matrix.diagonal _) * Uᴴ := by
          simp only [Matrix.mul_assoc]
  have hW_eq : gibbsWightmanNormSq G X =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N, Real.sqrt (p i) * Real.sqrt (p j) * ‖Y i j‖ ^ 2 := by
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
    rw [hJ_eq]
    set M : QubitOp N := Matrix.diagonal (fun i ↦ ((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ)) * Y *
      Matrix.diagonal (fun j ↦ ((Real.sqrt (Real.sqrt (p j)) : ℝ) : ℂ))
    have htr : ((U * M * Uᴴ)ᴴ * (U * M * Uᴴ)).trace = (Mᴴ * M).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (U * Mᴴ * Uᴴ * (U * M * Uᴴ)).trace
          = (U * (Mᴴ * (Uᴴ * U) * M) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (U * (Mᴴ * M) * Uᴴ).trace := by rw [hU'_unit, Matrix.mul_one]
        _ = (Uᴴ * (U * (Mᴴ * M))).trace := Matrix.trace_mul_comm _ _
        _ = ((Uᴴ * U) * (Mᴴ * M)).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * M).trace := by rw [hU'_unit, Matrix.one_mul]
    rw [htr]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hMij : M i j = ((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ) * Y i j *
        ((Real.sqrt (Real.sqrt (p j)) : ℝ) : ℂ) := by
      simp [M, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [hMij]
    have hstar : star (((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ) * Y i j *
        ((Real.sqrt (Real.sqrt (p j)) : ℝ) : ℂ)) *
        (((Real.sqrt (Real.sqrt (p i)) : ℝ) : ℂ) * Y i j *
        ((Real.sqrt (Real.sqrt (p j)) : ℝ) : ℂ)) =
        ((Real.sqrt (p i) * Real.sqrt (p j) * ‖Y i j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      have hsqi : (Real.sqrt (Real.sqrt (p i))) ^ 2 = Real.sqrt (p i) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have hsqj : (Real.sqrt (Real.sqrt (p j))) ^ 2 = Real.sqrt (p j) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have hY : (starRingEnd ℂ) (Y i j) * Y i j = (‖Y i j‖ : ℂ) ^ 2 := Complex.conj_mul' (Y i j)
      push_cast
      calc ((Real.sqrt (Real.sqrt (p j)) : ℂ) * ((starRingEnd ℂ) (Y i j) * (Real.sqrt (Real.sqrt (p i)) : ℂ))) *
            ((Real.sqrt (Real.sqrt (p i)) : ℂ) * Y i j * (Real.sqrt (Real.sqrt (p j)) : ℂ))
          = ((Real.sqrt (Real.sqrt (p i)) : ℂ) ^ 2) * ((Real.sqrt (Real.sqrt (p j)) : ℂ) ^ 2) *
              ((starRingEnd ℂ) (Y i j) * Y i j) := by ring
        _ = (Real.sqrt (p i) : ℂ) * (Real.sqrt (p j) : ℂ) * (‖Y i j‖ : ℂ) ^ 2 := by
            rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hsqi, hsqj, hY]
    rw [hstar, Complex.ofReal_re]
  rw [hW_eq]
  have hcol_le : ∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖Y i j‖ ^ 2 ≤ opNorm Y ^ 2 := by
    intro j
    have hv := ContinuousLinearMap.le_opNorm (opToCLM Y) (EuclideanSpace.single j (1 : ℂ))
    have hnorm_e : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
    rw [hnorm_e, mul_one] at hv
    have hsq : ‖opToCLM Y (EuclideanSpace.single j (1 : ℂ))‖ ^ 2 ≤ opNorm Y ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hlhs : ‖opToCLM Y (EuclideanSpace.single j (1 : ℂ))‖ ^ 2 = ∑ i : QubitIdx N, ‖Y i j‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl; intro i _
      simp [opToCLM, Matrix.mulVec, dotProduct]
    rwa [hlhs] at hsq
  have hrow_le : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖Y i j‖ ^ 2 ≤ opNorm Y ^ 2 := by
    intro i
    have hv := ContinuousLinearMap.le_opNorm (opToCLM Yᴴ) (EuclideanSpace.single i (1 : ℂ))
    have hnorm_e : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by simp
    rw [hnorm_e, mul_one] at hv
    have hsq : ‖opToCLM Yᴴ (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 ≤ opNorm Yᴴ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv 2
    rw [opNorm_conjTranspose] at hsq
    have hlhs : ‖opToCLM Yᴴ (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 = ∑ j : QubitIdx N, ‖Y i j‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl; intro j _
      simp [opToCLM, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    rwa [hlhs] at hsq
  have hamgm : ∀ i j : QubitIdx N,
      Real.sqrt (p i) * Real.sqrt (p j) * ‖Y i j‖ ^ 2 ≤
        (1 / 2 : ℝ) * (p i * ‖Y i j‖ ^ 2 + p j * ‖Y i j‖ ^ 2) := by
    intro i j
    have h1 : Real.sqrt (p i) * Real.sqrt (p j) ≤ (p i + p j) / 2 := by
      have hsq : 0 ≤ (Real.sqrt (p i) - Real.sqrt (p j)) ^ 2 := sq_nonneg _
      have hsi : Real.sqrt (p i) ^ 2 = p i := Real.sq_sqrt (hp_pos i).le
      have hsj : Real.sqrt (p j) ^ 2 = p j := Real.sq_sqrt (hp_pos j).le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖Y i j‖)
    linarith
  calc ∑ i : QubitIdx N, ∑ j : QubitIdx N, Real.sqrt (p i) * Real.sqrt (p j) * ‖Y i j‖ ^ 2
      ≤ ∑ i : QubitIdx N, ∑ j : QubitIdx N, (1 / 2 : ℝ) * (p i * ‖Y i j‖ ^ 2 + p j * ‖Y i j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hamgm i j
    _ = (1 / 2 : ℝ) * (∑ i : QubitIdx N, p i * ∑ j : QubitIdx N, ‖Y i j‖ ^ 2 +
          ∑ j : QubitIdx N, p j * ∑ i : QubitIdx N, ‖Y i j‖ ^ 2) := by
        simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
        congr 1; congr 1
        · apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
        · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) * (∑ i : QubitIdx N, p i * opNorm Y ^ 2 +
          ∑ j : QubitIdx N, p j * opNorm Y ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hrow_le i) (hp_pos i).le)
          (Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcol_le j) (hp_pos j).le)
    _ = opNorm Y ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hp_sum]; ring
    _ ≤ opNorm X ^ 2 := pow_le_pow_left₀ (opNorm_nonneg Y) hnorm_Y 2

/-- Real-time Heisenberg evolution preserves operator norm: `opNorm (heisenbergEvol hH (t : ℂ) O) ≤ opNorm O`. -/
lemma opNorm_heisenbergEvol_real_le {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (t : ℝ) (O : QubitOp N) :
    opNorm (heisenbergEvol hH (t : ℂ) O) ≤ opNorm O := by
  set U := complexPropagator hH (t : ℂ)
  have hU_neg : complexPropagator hH (-(t : ℂ)) = Uᴴ := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose]
    congr 1; funext x
    rw [Complex.star_def, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; congr 1; ring
  have hU'_unit : Uᴴ * U = 1 := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose, hermFunc_mul]
    have hfun : (fun x : ℝ ↦ star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) = fun _ ↦ 1 := by
      funext x
      rw [Complex.star_def, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      rw [← Complex.exp_add]
      have h0 : -Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero]
    rw [hfun, hermFunc_one]
  have hU_le : opNorm U ≤ 1 := by
    unfold opNorm
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
    rw [one_mul]
    have heq : ‖opToCLM U v‖ ^ 2 = ‖v‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, opToCLM, LinearMap.coe_toContinuousLinearMap',
        Matrix.toEuclideanLin_apply]
      have hinner : ∀ w : QubitIdx N → ℂ,
          (∑ i, star (w i) * w i) = ∑ i, ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
        intro w; apply Finset.sum_congr rfl; intro i _
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
      have h1 : ∑ i, star ((U.mulVec v.ofLp) i) * (U.mulVec v.ofLp) i =
          ∑ i, star (v.ofLp i) * v.ofLp i := by
        have hmul : (U.mulVec v.ofLp) ⬝ᵥ star (U.mulVec v.ofLp) =
            v.ofLp ⬝ᵥ star v.ofLp := by
          calc (U.mulVec v.ofLp) ⬝ᵥ star (U.mulVec v.ofLp)
              = star (U.mulVec v.ofLp) ⬝ᵥ (U.mulVec v.ofLp) := dotProduct_comm _ _
            _ = (star v.ofLp ᵥ* Uᴴ) ⬝ᵥ (U.mulVec v.ofLp) := by rw [Matrix.star_mulVec]
            _ = star v.ofLp ⬝ᵥ ((Uᴴ * U).mulVec v.ofLp) := by
                rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
            _ = star v.ofLp ⬝ᵥ v.ofLp := by rw [hU'_unit, Matrix.one_mulVec]
            _ = v.ofLp ⬝ᵥ star v.ofLp := dotProduct_comm _ _
        simpa [dotProduct, mul_comm] using hmul
      rw [hinner, hinner] at h1
      have hre := congrArg Complex.re h1
      simpa [Complex.re_sum] using hre
    nlinarith [norm_nonneg (opToCLM U v), norm_nonneg v]
  have hU'_le : opNorm Uᴴ ≤ 1 := by rw [opNorm_conjTranspose]; exact hU_le
  unfold heisenbergEvol
  rw [hU_neg]
  calc opNorm (U * O * Uᴴ) ≤ opNorm (U * O) * opNorm Uᴴ := opNorm_mul_le _ _
    _ ≤ (opNorm U * opNorm O) * opNorm Uᴴ := mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
    _ ≤ (1 * opNorm O) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hU_le (opNorm_nonneg _)) hU'_le (opNorm_nonneg _) (by positivity)
    _ = opNorm O := by ring

end WightmanAndUnitaryNormHelpers

section Corollary65LatticeBound

/-- Purely dimensional tail constant `∑' n : ℕ, ((n + 1 : ℝ) ^ d) * exp(-(n : ℝ) / 2)`. -/
noncomputable def latticeShellTailConst (d : ℕ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2)

lemma summable_latticeShellTail (d : ℕ) :
    Summable (fun n : ℕ ↦ ((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2)) := by
  have hlt : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hpos : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  refine summable_of_ratio_norm_eventually_le (r := (Real.exp (-(1 / 2 : ℝ)) + 1) / 2) (by linarith) ?_
  set r0 : ℝ := (Real.exp (-(1 / 2 : ℝ)) + 1) / 2
  have hgt : Real.exp (-(1 / 2 : ℝ)) < r0 := by dsimp only [r0]; linarith
  have hlim : Tendsto (fun n : ℕ ↦ (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ d) * Real.exp (-(1 / 2 : ℝ)))
      atTop (nhds (1 * Real.exp (-(1 / 2 : ℝ)))) := by
    have h1 : Tendsto (fun n : ℕ ↦ (n + 2 : ℝ) / (n + 1 : ℝ)) atTop (nhds 1) := by
      have hrew : (fun n : ℕ ↦ (n + 2 : ℝ) / (n + 1 : ℝ)) = fun n : ℕ ↦ 1 + 1 / ((n : ℝ) + 1) := by
        funext n; have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hn]; ring
      rw [hrew]
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using tendsto_const_nhds.add h0
    simpa [one_pow] using (h1.pow d).mul_const (Real.exp (-(1 / 2 : ℝ)))
  rw [one_mul] at hlim
  have hev := (tendsto_order.mp hlim).2 r0 hgt
  refine hev.mono fun n hn ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hexp_step : Real.exp (-((n + 1 : ℕ) : ℝ) / 2) = Real.exp (-(n : ℝ) / 2) * Real.exp (-(1 / 2 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have hpow_step : ((n + 1 + 1 : ℝ) ^ d) = ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ d * ((n + 1 : ℝ) ^ d) := by
    rw [div_pow, div_mul_cancel₀ _ (by positivity)]
    congr 1; ring
  push_cast at hexp_step ⊢
  rw [hexp_step, hpow_step]
  calc (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ d * (n + 1 : ℝ) ^ d) * (Real.exp (-(n : ℝ) / 2) * Real.exp (-(1 / 2 : ℝ)))
      = (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ d * Real.exp (-(1 / 2 : ℝ))) * ((n + 1 : ℝ) ^ d * Real.exp (-(n : ℝ) / 2)) := by ring
    _ ≤ r0 * ((n + 1 : ℝ) ^ d * Real.exp (-(n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hn.le (by positivity)

lemma latticeShellTailConst_nonneg (d : ℕ) : 0 ≤ latticeShellTailConst d :=
  tsum_nonneg fun _ ↦ by positivity

/-- Any causal union of length `k` starting from `{x}` under interactions of diameter `≤ R_int`
lies inside the metric ball `{y | dist x y ≤ k * R_int}`. -/
private lemma causalUnion_subset_ball {N R_int : ℕ}
    (dist : Fin N → Fin N → ℕ) (hself : ∀ x, dist x x = 0)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N))) (hdiam : ∀ X ∈ E, ∀ a ∈ X, ∀ b ∈ X, dist a b ≤ R_int)
    (x : Fin N) :
    ∀ (k : ℕ) (f : Fin k → Finset (Fin N)),
      (∀ j, f j ∈ E) → isCausalSeqOp {x} f →
      causalUnionOp {x} f ⊆ Finset.univ.filter (fun y : Fin N ↦ dist x y ≤ k * R_int) := by
  intro k
  induction k with
  | zero =>
    intro f _ _ y hy
    simp only [causalUnionOp, Finset.mem_singleton] at hy
    subst hy
    simp [hself]
  | succ k ih =>
    intro f hf hcs y hy
    unfold causalUnionOp at hy
    have htail_in : ∀ j : Fin k, Fin.tail f j ∈ E := fun j ↦ hf j.succ
    have hsub_tail := ih (Fin.tail f) htail_in hcs.2
    rcases Finset.mem_union.mp hy with hy0 | hyt
    · rcases hcs.1 with ⟨z, hz⟩
      rcases Finset.mem_inter.mp hz with ⟨hz0, hzt⟩
      have hz_dist : dist x z ≤ k * R_int := (Finset.mem_filter.mp (hsub_tail hzt)).2
      have hzy : dist z y ≤ R_int := hdiam (f 0) (hf 0) z hz0 y hy0
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
      calc dist x y ≤ dist x z + dist z y := htri x z y
        _ ≤ k * R_int + R_int := Nat.add_le_add hz_dist hzy
        _ = (k + 1) * R_int := by ring
    · have hyt' := (Finset.mem_filter.mp (hsub_tail hyt)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
      calc dist x y ≤ k * R_int := hyt'
        _ ≤ (k + 1) * R_int := Nat.mul_le_mul_right R_int (Nat.le_succ k)

/-- Explicit lattice Lieb–Robinson prefactor for `otocI` in Corollary 6.5 (Eq. 6.10). -/
noncomputable def cor65LatticeConst (R_int s₀ d : ℕ) (C_vol C_O : ℝ) : ℝ :=
  24 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * ((4 * (R_int : ℝ) + 1) ^ d) *
    (1 + latticeShellTailConst d)

/-- **Corollary 6.5 (All-Time Finite-Range Lattice Bound on `otocI` and `mssThermalSize`, Eq. 6.10)**:
For any `N ≥ 1`, `r`-local finite-range Hermitian Hamiltonian `H = ∑ Z ∈ E, h Z` (`r ≥ 2`,
interaction diameter `≤ R_int`, site strength `≤ Jsite`) on a `d`-dimensional lattice with
polynomial ball volume `|{y | dist x y ≤ R}| ≤ C_vol * (R + 1)^d`, inverse temperature
`β ∈ [0, highTempBetaWC r Jsite]`, and `s₀`-local observable `O ∈ supportedOn U₀`
(`U₀.card ≤ s₀`, `‖O‖_{β,W} = 1`, `opNorm O ≤ C_O`, `1 ≤ C_O`), letting
`v_LR := 2 * Real.exp 1 * r * Jsite` and `C_LR := cor65LatticeConst R_int s₀ d C_vol C_O`,
for ALL real times `t : ℝ`:
1. `otocI hH β (heisenbergEvol hH (t : ℂ) O) ≤ C_LR * (1 + v_LR * |t|) ^ d`,
2. **Eq. (6.10)**:
   `mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
     C_LR * (1 + v_LR * |t|) ^ d +
     2 * √(C_LR * (1 + v_LR * |t|) ^ d) * √(N + bgDecouplingC2 r s₀ C_O * √N) +
     bgDecouplingC2 r s₀ C_O * √N`. -/
theorem cor_6_5_all_time_eq_6_10 {N r R_int s₀ d : ℕ}
    (hN : 1 ≤ N) (hr : 2 ≤ r) (hRint : 1 ≤ R_int)
    (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (hsym : ∀ x y : Fin N, dist x y = dist y x)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    {C_vol : ℝ} (hCvol : 0 < C_vol)
    (hvol : ∀ (x : Fin N) (R : ℕ),
      ((Finset.univ.filter (fun y : Fin N ↦ dist x y ≤ R)).card : ℝ) ≤ C_vol * ((R : ℝ) + 1) ^ d)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty)
    (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (hdiam : ∀ Z ∈ E, ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hh_herm : ∀ Z ∈ E, (h Z).IsHermitian)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ s₀)
    {O : QubitOp N} (hO_supp : O ∈ supportedOn U₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    {C_O : ℝ} (hCO_ge1 : 1 ≤ C_O) (hCO : opNorm O ≤ C_O) (t : ℝ) :
    let G := concreteGibbsData hH β
    let Ot := heisenbergEvol hH (t : ℂ) O
    let v_LR := 2 * Real.exp 1 * (r : ℝ) * Jsite
    let C_LR := cor65LatticeConst R_int s₀ d C_vol C_O
    otocI hH β Ot ≤ C_LR * (1 + v_LR * |t|) ^ d ∧
    mssThermalSize G Ot ≤
      C_LR * (1 + v_LR * |t|) ^ d +
      2 * Real.sqrt (C_LR * (1 + v_LR * |t|) ^ d) *
        Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) +
      bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) := by
  intro G Ot v_LR C_LR
  have hCLR_nn : 0 ≤ C_LR := by
    dsimp only [C_LR, cor65LatticeConst]
    have := latticeShellTailConst_nonneg d
    positivity
  have hvLR_nn : 0 ≤ v_LR := by dsimp only [v_LR]; positivity
  have hOt_norm : opNorm Ot ≤ C_O := le_trans (opNorm_heisenbergEvol_real_le hH t O) hCO
  have hβ_q : β * (r : ℝ) * Jsite / 2 ≤ 1 / 4 := by
    have h6r : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
      calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
        _ ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    have h1 : β * (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hβ (by positivity : 0 ≤ 4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite)
      unfold highTempBetaWC at this
      rwa [one_div_mul_cancel (by positivity)] at this
    have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith [mul_nonneg hβ0 (mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hJ.le)]
  set zβ : ℂ := -Complex.I * ((β / 4 : ℝ) : ℂ)
  have hzβ_norm : ‖zβ‖ = β / 4 := by
    dsimp only [zβ]
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hq_le : 2 * ‖zβ‖ * (r : ℝ) * Jsite ≤ 1 / 4 := by rw [hzβ_norm]; linarith
  have hterm_norm : ∀ (x : Fin N) (α : Fin 3) (k : ℕ),
      opNorm (((Complex.I * zβ) ^ k / (k.factorial : ℂ)) • adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ)) ≤
        2 * (1 / 2 : ℝ) ^ k := by
    intro x α k
    rw [opNorm_smul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, hzβ_norm, Complex.norm_natCast]
    have had_le : opNorm (adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ)) ≤
        (2 : ℝ) ^ k * ((k + 1).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by
      rw [adPowMat_eq_sum_causal E h hh_supp (pauliSite_mem_supportedOn x α) k]
      have h1 : opNorm (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            iterComm h f (pauliSite x α.succ)) ≤
          (2 : ℝ) ^ k * fwdCausalSum E (fun Z ↦ opNorm (h Z)) k {x} := by
        calc _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                opNorm (iterComm h f (pauliSite x α.succ)) := opNorm_sum_le _ _
          _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                (2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (f j))) * 1 := by
              refine Finset.sum_le_sum fun f _ ↦ le_trans (opNorm_iterComm_le h (pauliSite x α.succ) f)
                (mul_le_mul_of_nonneg_left (opNorm_pauliSite_le x α) (by positivity))
          _ = (2 : ℝ) ^ k * fwdCausalSum E (fun Z ↦ opNorm (h Z)) k {x} := by
              unfold fwdCausalSum; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro f _; ring
      have hfwd := fwdCausalSum_general_le (by omega : 1 ≤ r) E hE_card (fun Z ↦ opNorm (h Z))
        (fun _ _ ↦ opNorm_nonneg _) hJ.le hH_site k {x}
      have hprod : (∏ j : Fin k, ((({x} : Finset (Fin N)).card : ℝ) + (j.val : ℝ) * (r : ℝ))) ≤
          ((k + 1).factorial : ℝ) * (r : ℝ) ^ k := by
        have haux : ∀ m : ℕ, ∏ j : Fin m, ((1 : ℝ) + (j.val : ℝ) * (r : ℝ)) ≤
            ((m + 1).factorial : ℝ) * (r : ℝ) ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [Fin.prod_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
            have hstep : (1 : ℝ) + (m : ℝ) * (r : ℝ) ≤ ((m + 2 : ℕ) : ℝ) * (r : ℝ) := by
              push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m]
            have hmul := mul_le_mul ihm hstep (by positivity) (by positivity)
            rw [Nat.factorial_succ (m + 1), Nat.cast_mul, pow_succ]
            linarith [show ((m + 1).factorial : ℝ) * (r : ℝ) ^ m * (((m + 2 : ℕ) : ℝ) * (r : ℝ)) =
              ((m + 1 + 1 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) * ((r : ℝ) ^ m * (r : ℝ)) by push_cast; ring]
        simpa using haux k
      calc _ ≤ (2 : ℝ) ^ k * fwdCausalSum E (fun Z ↦ opNorm (h Z)) k {x} := h1
        _ ≤ (2 : ℝ) ^ k * (((∏ j : Fin k, ((({x} : Finset (Fin N)).card : ℝ) + (j.val : ℝ) * (r : ℝ))) * Jsite ^ k)) :=
            mul_le_mul_of_nonneg_left hfwd (by positivity)
        _ ≤ (2 : ℝ) ^ k * ((((k + 1).factorial : ℝ) * (r : ℝ) ^ k) * Jsite ^ k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod (pow_nonneg hJ.le k)) (by positivity)
        _ = (2 : ℝ) ^ k * ((k + 1).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by rw [mul_pow]; ring
    have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (β / 4) ^ k / (k.factorial : ℝ) * opNorm (adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ))
        ≤ (β / 4) ^ k / (k.factorial : ℝ) * ((2 : ℝ) ^ k * ((k + 1).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k) :=
          mul_le_mul_of_nonneg_left had_le (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite / 2) ^ k := by
          rw [Nat.factorial_succ, Nat.cast_mul, show (β * (r : ℝ) * Jsite / 2) ^ k =
            (β / 4) ^ k * (2 : ℝ) ^ k * ((r : ℝ) * Jsite) ^ k by rw [← mul_pow, ← mul_pow]; congr 1; ring]
          field_simp [hkf.ne']
      _ ≤ (2 : ℝ) ^ (k + 1) * (1 / 4 : ℝ) ^ k :=
          mul_le_mul hk1_le (pow_le_pow_left₀ (by positivity) hβ_q k) (by positivity) (by positivity)
      _ = 2 * (1 / 2 : ℝ) ^ k := by
          rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
  have hotoc_le : otocI hH β Ot ≤ C_LR * (1 + v_LR * |t|) ^ d := by
    by_cases hU0_empty : U₀ = ∅
    · have hcomm0 : ∀ (x : Fin N) (α : Fin 3),
          matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)) = 0 := by
        intro x α
        have hO_comm : ∀ B : QubitOp N, matComm O B = 0 := by
          intro B
          have hmem : O ∈ supportedOn (∅ : Finset (Fin N)) := hU0_empty ▸ hO_supp
          unfold supportedOn at hmem
          refine Submodule.span_induction (p := fun A _ ↦ matComm A B = 0) ?_ ?_ ?_ ?_ hmem
          · rintro A ⟨a, ha, rfl⟩
            have ha0 : a = 0 := by
              funext j; by_contra hne; exact Finset.notMem_empty j (ha j hne)
            subst ha0; simp [pauliString_zero, matComm]
          · simp [matComm]
          · intro A₁ A₂ _ _ h1 h2; rw [matComm_add_left, h1, h2, add_zero]
          · intro c A _ h1; rw [matComm_smul_left, h1, smul_zero]
        have hO_evol : Ot = O := by
          dsimp only [Ot]; unfold heisenbergEvol
          have hcomm_prop : complexPropagator hH (t : ℂ) * O = O * complexPropagator hH (t : ℂ) := by
            have := hO_comm (complexPropagator hH (t : ℂ))
            unfold matComm at this; exact (sub_eq_zero.mp this).symm
          have hmul1 : complexPropagator hH (t : ℂ) * complexPropagator hH (-(t : ℂ)) = 1 := by
            unfold complexPropagator; rw [hermFunc_mul]
            have : (fun e : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (e : ℂ)) *
                Complex.exp (Complex.I * -(t : ℂ) * (e : ℂ))) = fun _ ↦ 1 := by
              funext e; rw [← Complex.exp_add]; rw [show Complex.I * (t : ℂ) * (e : ℂ) +
                Complex.I * -(t : ℂ) * (e : ℂ) = 0 by ring, Complex.exp_zero]
            rw [this, hermFunc_one]
          calc complexPropagator hH (t : ℂ) * O * complexPropagator hH (-(t : ℂ))
              = O * (complexPropagator hH (t : ℂ) * complexPropagator hH (-(t : ℂ))) := by
                rw [hcomm_prop, Matrix.mul_assoc]
            _ = O := by rw [hmul1, Matrix.mul_one]
        rw [hO_evol]; exact hO_comm _
      unfold otocI
      have hsum0 : ∑ x : Fin N, ∑ α : Fin 3,
          gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) = 0 := by
        apply Finset.sum_eq_zero; intro x _
        apply Finset.sum_eq_zero; intro α _
        rw [hcomm0 x α]; simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner]
      rw [show (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
          gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) = 0 by
        rw [hsum0, mul_zero]]
      positivity
    · have hU0_ne : U₀.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0_empty
      set L₀ : ℕ := Nat.ceil (4 * v_LR * |t|)
      have hL0_ge : 4 * v_LR * |t| ≤ (L₀ : ℝ) := Nat.le_ceil _
      have hL0_le : (L₀ : ℝ) ≤ 4 * v_LR * |t| + 1 := by
        have := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * v_LR * |t|)
        linarith
      have hsite_unif : ∀ (x : Fin N) (α : Fin 3),
          gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ≤ 64 * C_O ^ 2 := by
        intro x α
        have hσ_le : opNorm (heisenbergEvol hH zβ (pauliSite x α.succ)) ≤ 4 := by
          have hhas := hasSum_heisenbergEvol_adPow hH zβ (pauliSite x α.succ)
          let φ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
            LinearMap.toContinuousLinearMap
              { toFun := opToCLM, map_add' := opToCLM_add, map_smul' := fun c A ↦ by simp [opToCLM_smul] }
          have hclm := hhas.map φ φ.continuous
          have hsg : Summable (fun k : ℕ ↦ 2 * (1 / 2 : ℝ) ^ k) :=
            (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
          have hsn : Summable (fun k : ℕ ↦ opNorm (((Complex.I * zβ) ^ k / (k.factorial : ℂ)) •
              adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ))) :=
            Summable.of_nonneg_of_le (fun _ ↦ opNorm_nonneg _) (hterm_norm x α) hsg
          calc opNorm (heisenbergEvol hH zβ (pauliSite x α.succ))
              = ‖∑' k : ℕ, opToCLM (((Complex.I * zβ) ^ k / (k.factorial : ℂ)) •
                  adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ))‖ := by unfold opNorm; rw [hclm.tsum_eq]
            _ ≤ ∑' k : ℕ, opNorm (((Complex.I * zβ) ^ k / (k.factorial : ℂ)) •
                  adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ)) := norm_tsum_le_tsum_norm hsn
            _ ≤ ∑' k : ℕ, 2 * (1 / 2 : ℝ) ^ k := hsn.tsum_le_tsum (hterm_norm x α) hsg
            _ = 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := tsum_mul_left
            _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
        have hc_le : opNorm (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ≤ 8 * C_O := by
          unfold matComm
          calc opNorm (Ot * heisenbergEvol hH zβ (pauliSite x α.succ) - heisenbergEvol hH zβ (pauliSite x α.succ) * Ot)
              ≤ opNorm (Ot * heisenbergEvol hH zβ (pauliSite x α.succ)) +
                  opNorm (heisenbergEvol hH zβ (pauliSite x α.succ) * Ot) := opNorm_sub_le _ _
            _ ≤ opNorm Ot * opNorm (heisenbergEvol hH zβ (pauliSite x α.succ)) +
                  opNorm (heisenbergEvol hH zβ (pauliSite x α.succ)) * opNorm Ot :=
                add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
            _ ≤ C_O * 4 + 4 * C_O := add_le_add
                (mul_le_mul hOt_norm hσ_le (opNorm_nonneg _) (by positivity))
                (mul_le_mul hσ_le hOt_norm (opNorm_nonneg _) (by norm_num))
            _ = 8 * C_O := by ring
        calc gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)))
            ≤ opNorm (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ^ 2 :=
              gibbsWightmanNormSq_le_opNorm_sq hH β _
          _ ≤ (8 * C_O) ^ 2 := pow_le_pow_left₀ (opNorm_nonneg _) hc_le 2
          _ = 64 * C_O ^ 2 := by ring
      have hsite_decay : ∀ (n : ℕ) (x : Fin N) (α : Fin 3),
          (∀ u ∈ U₀, (L₀ + 2 + n) * R_int < dist u x) →
          gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ≤
            64 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2) := by
        intro n x α hsep_x
        set L : ℕ := L₀ + 2 + n
        set m : ℕ := L / 2
        let T : ℕ → QubitOp N := fun k ↦
          ((Complex.I * zβ) ^ k / (k.factorial : ℂ)) • adPowMat (∑ Z ∈ E, h Z) k (pauliSite x α.succ)
        have hT_supp : ∀ k : ℕ, T k ∈ supportedOn (Finset.univ.filter (fun y : Fin N ↦ dist x y ≤ k * R_int)) := by
          intro k
          dsimp only [T]
          refine (supportedOn _).smul_mem _ ?_
          rw [adPowMat_eq_sum_causal E h hh_supp (pauliSite_mem_supportedOn x α) k]
          refine Submodule.sum_mem _ fun f hf ↦ ?_
          have hfE : ∀ j, f j ∈ E := fun j ↦ Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 j
          have hcs : isCausalSeqOp {x} f := (Finset.mem_filter.mp hf).2
          exact supportedOn_mono (causalUnion_subset_ball dist hself htri E hdiam x k f hfE hcs)
            (iterComm_mem_supportedOn h hh_supp (pauliSite_mem_supportedOn x α) f)
        have hhas_comm : HasSum (fun k : ℕ ↦ opToCLM (matComm Ot (T k)))
            (opToCLM (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)))) := by
          have hhas := hasSum_heisenbergEvol_adPow hH zβ (pauliSite x α.succ)
          let ψ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
            LinearMap.toContinuousLinearMap
              { toFun := fun A ↦ opToCLM (matComm Ot A)
                map_add' := fun A B ↦ by rw [matComm_add_right, opToCLM_add]
                map_smul' := fun c A ↦ by simp [matComm_smul_right, opToCLM_smul] }
          exact hhas.map ψ ψ.continuous
        have hterm_comm : ∀ k : ℕ, opNorm (matComm Ot (T k)) ≤
            if k ≤ m then 4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k
            else 4 * C_O * (1 / 2 : ℝ) ^ k := by
          intro k
          split_ifs with hkm
          · have hsep_k : ∀ u ∈ U₀, ∀ y ∈ Finset.univ.filter (fun y : Fin N ↦ dist x y ≤ k * R_int),
                m * R_int < dist u y := by
              intro u hu y hy
              have hyx : dist x y ≤ k * R_int := (Finset.mem_filter.mp hy).2
              have hux : L * R_int < dist u x := hsep_x u hu
              have htri1 : dist u x ≤ dist u y + dist y x := htri u y x
              rw [hsym y x] at htri1
              have hLm : m + k ≤ L := by dsimp only [m]; omega
              have hmul_le : m * R_int + k * R_int ≤ L * R_int := by
                rw [← Nat.add_mul]; exact Nat.mul_le_mul_right R_int hLm
              omega
            have hlr := all_time_lieb_robinson_exp (by omega : 1 ≤ r) dist hself htri E hE_card hdiam
              h hh_supp hh_herm hH hJ.le hH_site hO_supp (hT_supp k) m hsep_k t
            have hTk := hterm_norm x α k
            have hexp_le : Real.exp (v_LR * |t| - ((m + 1 : ℕ) : ℝ)) ≤ Real.exp (-(n : ℝ) / 4) := by
              apply Real.exp_le_exp.mpr
              have hm1 : (L : ℝ) / 2 ≤ ((m + 1 : ℕ) : ℝ) := by
                have : L ≤ 2 * (m + 1) := by dsimp only [m]; omega
                have h2 : (L : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast this
                linarith
              have hL_cast : (L : ℝ) = (L₀ : ℝ) + 2 + (n : ℝ) := by dsimp only [L]; push_cast; ring
              linarith
            have hU0_cast : (U₀.card : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hU₀
            calc opNorm (matComm Ot (T k))
                ≤ 2 * opNorm O * opNorm (T k) * (U₀.card : ℝ) * Real.exp (v_LR * |t| - ((m + 1 : ℕ) : ℝ)) := hlr
              _ ≤ 2 * C_O * (2 * (1 / 2 : ℝ) ^ k) * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) := by
                  have h1 : 2 * opNorm O ≤ 2 * C_O := by linarith
                  have h2 : 2 * opNorm O * opNorm (T k) ≤ 2 * C_O * (2 * (1 / 2 : ℝ) ^ k) :=
                    mul_le_mul h1 hTk (opNorm_nonneg _) (by positivity)
                  have h3 : 2 * opNorm O * opNorm (T k) * (U₀.card : ℝ) ≤
                      2 * C_O * (2 * (1 / 2 : ℝ) ^ k) * (s₀ : ℝ) :=
                    mul_le_mul h2 hU0_cast (Nat.cast_nonneg _) (by positivity)
                  exact mul_le_mul h3 hexp_le (Real.exp_pos _).le (by positivity)
              _ = 4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k := by ring
          · unfold matComm
            have hTk := hterm_norm x α k
            calc opNorm (Ot * T k - T k * Ot)
                ≤ opNorm (Ot * T k) + opNorm (T k * Ot) := opNorm_sub_le _ _
              _ ≤ opNorm Ot * opNorm (T k) + opNorm (T k) * opNorm Ot :=
                  add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
              _ ≤ C_O * (2 * (1 / 2 : ℝ) ^ k) + (2 * (1 / 2 : ℝ) ^ k) * C_O :=
                  add_le_add (mul_le_mul hOt_norm hTk (opNorm_nonneg _) (by positivity))
                    (mul_le_mul hTk hOt_norm (opNorm_nonneg _) (by positivity))
              _ = 4 * C_O * (1 / 2 : ℝ) ^ k := by ring
        have hsg1 : Summable (fun k : ℕ ↦ 4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        have hsg2 : Summable (fun k : ℕ ↦ if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0) :=
          Summable.of_nonneg_of_le (fun _ ↦ by split_ifs <;> positivity)
            (fun k ↦ by split_ifs <;> positivity)
            ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
        have hdom : ∀ k : ℕ, opNorm (matComm Ot (T k)) ≤
            4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k +
            (if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0) := by
          intro k
          have h1 := hterm_comm k
          by_cases hkm : k ≤ m
          · rw [if_pos hkm] at h1
            rw [if_neg (by omega : ¬m < k), add_zero]; exact h1
          · rw [if_neg hkm] at h1
            rw [if_pos (by omega : m < k)]
            linarith [show 0 ≤ 4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k by positivity]
        have hsn : Summable (fun k : ℕ ↦ opNorm (matComm Ot (T k))) :=
          Summable.of_nonneg_of_le (fun _ ↦ opNorm_nonneg _) hdom (hsg1.add hsg2)
        have htail2 : (∑' k : ℕ, if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0) ≤
            8 * C_O * Real.exp (-(n : ℝ) / 4) := by
          have hshift : (∑' k : ℕ, if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0) =
              ∑' j : ℕ, 4 * C_O * (1 / 2 : ℝ) ^ (j + (m + 1)) := by
            have hsum_split := hsg2.sum_add_tsum_nat_add (m + 1)
            have hfin0 : ∑ i ∈ Finset.range (m + 1), (if m < i then 4 * C_O * (1 / 2 : ℝ) ^ i else 0) = 0 := by
              apply Finset.sum_eq_zero; intro i hi
              rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
            rw [hfin0, zero_add] at hsum_split
            rw [← hsum_split]
            apply tsum_congr; intro j
            rw [if_pos (by omega : m < j + (m + 1))]
          rw [hshift]
          have hrew : (fun j : ℕ ↦ 4 * C_O * (1 / 2 : ℝ) ^ (j + (m + 1))) =
              fun j : ℕ ↦ (4 * C_O * (1 / 2 : ℝ) ^ (m + 1)) * (1 / 2 : ℝ) ^ j := by
            funext j; rw [pow_add]; ring
          rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          have hhalf_le : (1 / 2 : ℝ) ^ (m + 1) ≤ Real.exp (-(n : ℝ) / 4) := by
            have h12 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
              have hexp1 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
                have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
                  rw [← Real.exp_nat_mul]; norm_num
                have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
                nlinarith [Real.exp_pos (1 / 2 : ℝ)]
              rw [Real.exp_neg, one_div]
              exact inv_anti₀ (Real.exp_pos _) hexp1
            calc (1 / 2 : ℝ) ^ (m + 1) ≤ (Real.exp (-(1 / 2 : ℝ))) ^ (m + 1) :=
                  pow_le_pow_left₀ (by norm_num) h12 (m + 1)
              _ = Real.exp (-(((m + 1 : ℕ) : ℝ) / 2)) := by rw [← Real.exp_nat_mul]; congr 1; ring
              _ ≤ Real.exp (-(n : ℝ) / 4) := by
                  apply Real.exp_le_exp.mpr
                  have : n ≤ 2 * (m + 1) := by dsimp only [m, L]; omega
                  have h2 : (n : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast this
                  linarith
          have h8 : 4 * C_O * (1 / 2 : ℝ) ^ (m + 1) * ((1 - (1 / 2 : ℝ))⁻¹) = 8 * C_O * (1 / 2 : ℝ) ^ (m + 1) := by
            norm_num; ring
          rw [h8]
          exact mul_le_mul_of_nonneg_left hhalf_le (by positivity)
        have hcomm_op : opNorm (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ≤
            8 * C_O * ((s₀ : ℝ) + 1) * Real.exp (-(n : ℝ) / 4) := by
          calc opNorm (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)))
              = ‖∑' k : ℕ, opToCLM (matComm Ot (T k))‖ := by unfold opNorm; rw [hhas_comm.tsum_eq]
            _ ≤ ∑' k : ℕ, opNorm (matComm Ot (T k)) := norm_tsum_le_tsum_norm hsn
            _ ≤ ∑' k : ℕ, (4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k +
                  (if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0)) := hsn.tsum_le_tsum hdom (hsg1.add hsg2)
            _ = (∑' k : ℕ, 4 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) * (1 / 2 : ℝ) ^ k) +
                  (∑' k : ℕ, if m < k then 4 * C_O * (1 / 2 : ℝ) ^ k else 0) := hsg1.tsum_add hsg2
            _ ≤ 8 * C_O * (s₀ : ℝ) * Real.exp (-(n : ℝ) / 4) + 8 * C_O * Real.exp (-(n : ℝ) / 4) := by
                apply add_le_add _ htail2
                rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
                norm_num; ring_nf; exact le_rfl
            _ = 8 * C_O * ((s₀ : ℝ) + 1) * Real.exp (-(n : ℝ) / 4) := by ring
        calc gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)))
            ≤ opNorm (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ))) ^ 2 :=
              gibbsWightmanNormSq_le_opNorm_sq hH β _
          _ ≤ (8 * C_O * ((s₀ : ℝ) + 1) * Real.exp (-(n : ℝ) / 4)) ^ 2 :=
              pow_le_pow_left₀ (opNorm_nonneg _) hcomm_op 2
          _ = 64 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2) := by
              rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]; congr 1 <;> ring
      let S_in : Finset (Fin N) := Finset.univ.filter (fun x ↦ ∃ u ∈ U₀, dist u x ≤ (L₀ + 2) * R_int)
      let shell : ℕ → Finset (Fin N) := fun n ↦
        Finset.univ.filter (fun x ↦
          (∀ u ∈ U₀, (L₀ + 2 + n) * R_int < dist u x) ∧
          (∃ u ∈ U₀, dist u x ≤ (L₀ + 3 + n) * R_int))
      set D_max : ℕ := Finset.univ.sup (fun p : Fin N × Fin N ↦ dist p.1 p.2)
      set M_max : ℕ := D_max + 1
      have hcover : (Finset.univ : Finset (Fin N)) ⊆ S_in ∪ (Finset.range M_max).biUnion shell := by
        intro x _
        by_cases hin : x ∈ S_in
        · exact Finset.mem_union_left _ hin
        · apply Finset.mem_union_right
          have hout : ∀ u ∈ U₀, (L₀ + 2) * R_int < dist u x := by
            intro u hu; by_contra hle; push Not at hle
            exact hin (Finset.mem_filter.mpr ⟨Finset.mem_univ x, u, hu, hle⟩)
          obtain ⟨u₀, hu₀, hmin⟩ := U₀.exists_min_image (fun u ↦ dist u x) hU0_ne
          have hgt0 : (L₀ + 2) * R_int < dist u₀ x := hout u₀ hu₀
          set n : ℕ := (dist u₀ x - (L₀ + 2) * R_int - 1) / R_int
          have hn_lt : n < M_max := by
            have hdle : dist u₀ x ≤ D_max :=
              Finset.le_sup (f := fun p : Fin N × Fin N ↦ dist p.1 p.2) (Finset.mem_univ (u₀, x))
            have hdiv : n ≤ dist u₀ x := by
              dsimp only [n]
              calc (dist u₀ x - (L₀ + 2) * R_int - 1) / R_int
                  ≤ dist u₀ x - (L₀ + 2) * R_int - 1 := Nat.div_le_self _ _
                _ ≤ dist u₀ x := by omega
            omega
          refine Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn_lt, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_, ?_⟩⟩
          · intro u hu
            have hle_u : dist u₀ x ≤ dist u x := hmin u hu
            have hmul : n * R_int ≤ dist u₀ x - (L₀ + 2) * R_int - 1 := Nat.div_mul_le_self _ _
            have hadd : (L₀ + 2 + n) * R_int = (L₀ + 2) * R_int + n * R_int := by ring
            omega
          · refine ⟨u₀, hu₀, ?_⟩
            have hrem : dist u₀ x - (L₀ + 2) * R_int - 1 < (n + 1) * R_int := by
              dsimp only [n]
              have := Nat.lt_div_mul_add (a := dist u₀ x - (L₀ + 2) * R_int - 1) (by omega : 0 < R_int)
              linarith
            have hadd : (L₀ + 3 + n) * R_int = (L₀ + 2) * R_int + (n + 1) * R_int := by ring
            omega
      have hvol_in : (S_in.card : ℝ) ≤ (s₀ : ℝ) * C_vol * (((L₀ + 2) * R_int : ℝ) + 1) ^ d := by
        have hsub : S_in ⊆ U₀.biUnion (fun u ↦ Finset.univ.filter (fun x : Fin N ↦ dist u x ≤ (L₀ + 2) * R_int)) := by
          intro x hx; rcases (Finset.mem_filter.mp hx).2 with ⟨u, hu, hd⟩
          exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hd⟩⟩
        have hcard_le : (S_in.card : ℝ) ≤ ∑ u ∈ U₀, ((Finset.univ.filter (fun x : Fin N ↦ dist u x ≤ (L₀ + 2) * R_int)).card : ℝ) := by
          exact_mod_cast le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        calc (S_in.card : ℝ) ≤ ∑ u ∈ U₀, C_vol * ((((L₀ + 2) * R_int : ℕ) : ℝ) + 1) ^ d :=
              le_trans hcard_le (Finset.sum_le_sum fun u _ ↦ hvol u _)
          _ = (U₀.card : ℝ) * (C_vol * (((L₀ + 2) * R_int : ℝ) + 1) ^ d) := by
              rw [Finset.sum_const, nsmul_eq_mul]; push_cast; rfl
          _ ≤ (s₀ : ℝ) * C_vol * (((L₀ + 2) * R_int : ℝ) + 1) ^ d := by
              have hU : (U₀.card : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hU₀
              have hnn : 0 ≤ C_vol * (((L₀ + 2) * R_int : ℝ) + 1) ^ d := by positivity
              nlinarith
      have hvol_shell : ∀ n : ℕ, ((shell n).card : ℝ) ≤
          (s₀ : ℝ) * C_vol * (((L₀ + 3) * R_int : ℝ) + 1) ^ d * ((n + 1 : ℝ) ^ d) := by
        intro n
        have hsub : shell n ⊆ U₀.biUnion (fun u ↦ Finset.univ.filter (fun x : Fin N ↦ dist u x ≤ (L₀ + 3 + n) * R_int)) := by
          intro x hx; rcases (Finset.mem_filter.mp hx).2.2 with ⟨u, hu, hd⟩
          exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hd⟩⟩
        have hcard_le : ((shell n).card : ℝ) ≤ ∑ u ∈ U₀, ((Finset.univ.filter (fun x : Fin N ↦ dist u x ≤ (L₀ + 3 + n) * R_int)).card : ℝ) := by
          exact_mod_cast le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        have hrad : ((((L₀ + 3 + n) * R_int : ℕ) : ℝ) + 1) ≤ (((L₀ + 3) * R_int : ℝ) + 1) * (n + 1 : ℝ) := by
          push_cast
          have hR_ge1 : (1 : ℝ) ≤ (R_int : ℝ) := by exact_mod_cast hRint
          nlinarith [Nat.cast_nonneg (α := ℝ) L₀, Nat.cast_nonneg (α := ℝ) n]
        have hpow : ((((L₀ + 3 + n) * R_int : ℕ) : ℝ) + 1) ^ d ≤
            (((L₀ + 3) * R_int : ℝ) + 1) ^ d * (n + 1 : ℝ) ^ d := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hrad d
        calc ((shell n).card : ℝ) ≤ ∑ u ∈ U₀, C_vol * ((((L₀ + 3 + n) * R_int : ℕ) : ℝ) + 1) ^ d :=
              le_trans hcard_le (Finset.sum_le_sum fun u _ ↦ hvol u _)
          _ = (U₀.card : ℝ) * (C_vol * ((((L₀ + 3 + n) * R_int : ℕ) : ℝ) + 1) ^ d) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (s₀ : ℝ) * (C_vol * ((((L₀ + 3) * R_int : ℝ) + 1) ^ d * (n + 1 : ℝ) ^ d)) := by
              have hU : (U₀.card : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hU₀
              exact mul_le_mul hU (mul_le_mul_of_nonneg_left hpow hCvol.le) (by positivity) (Nat.cast_nonneg s₀)
          _ = (s₀ : ℝ) * C_vol * (((L₀ + 3) * R_int : ℝ) + 1) ^ d * ((n + 1 : ℝ) ^ d) := by ring
      have hrad_tot : (((L₀ + 3) * R_int : ℝ) + 1) ^ d ≤ (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ d
        have hR_ge1 : (1 : ℝ) ≤ (R_int : ℝ) := by exact_mod_cast hRint
        nlinarith [hL0_le, abs_nonneg t]
      have hrad_in : (((L₀ + 2) * R_int : ℝ) + 1) ^ d ≤ (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d :=
        le_trans (pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) R_int]) d) hrad_tot
      let f_site : Fin N → ℝ := fun x ↦
        ∑ α : Fin 3, gibbsWightmanNormSq G (matComm Ot (heisenbergEvol hH zβ (pauliSite x α.succ)))
      have hf_nn : ∀ x : Fin N, 0 ≤ f_site x := fun x ↦
        Finset.sum_nonneg fun α _ ↦ gibbsWightmanNormSq_nonneg G _
      have hsum_split : ∑ x : Fin N, f_site x ≤
          (∑ x ∈ S_in, f_site x) + ∑ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x := by
        calc ∑ x : Fin N, f_site x
            ≤ ∑ x ∈ S_in ∪ (Finset.range M_max).biUnion shell, f_site x :=
              Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ ↦ hf_nn _
          _ ≤ (∑ x ∈ S_in, f_site x) + ∑ x ∈ (Finset.range M_max).biUnion shell, f_site x :=
              Finset.sum_union_le (fun _ _ ↦ hf_nn _)
          _ ≤ (∑ x ∈ S_in, f_site x) + ∑ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x :=
              add_le_add_left (real_sum_biUnion_le _ _ _ fun _ _ ↦ hf_nn _) _
      have hsum_in : ∑ x ∈ S_in, f_site x ≤
          192 * C_O ^ 2 * (s₀ : ℝ) * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d := by
        have h1 : ∑ x ∈ S_in, f_site x ≤ (S_in.card : ℝ) * (192 * C_O ^ 2) := by
          calc ∑ x ∈ S_in, f_site x ≤ ∑ _x ∈ S_in, (3 : ℝ) * (64 * C_O ^ 2) := by
                refine Finset.sum_le_sum fun x _ ↦ ?_
                calc f_site x ≤ ∑ _α : Fin 3, 64 * C_O ^ 2 := Finset.sum_le_sum fun α _ ↦ hsite_unif x α
                  _ = (3 : ℝ) * (64 * C_O ^ 2) := by simp
            _ = (S_in.card : ℝ) * (192 * C_O ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        calc ∑ x ∈ S_in, f_site x ≤ ((s₀ : ℝ) * C_vol * (((L₀ + 2) * R_int : ℝ) + 1) ^ d) * (192 * C_O ^ 2) :=
              le_trans h1 (mul_le_mul_of_nonneg_right hvol_in (by positivity))
          _ ≤ ((s₀ : ℝ) * C_vol * ((4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d)) * (192 * C_O ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrad_in (by positivity)) (by positivity)
          _ = 192 * C_O ^ 2 * (s₀ : ℝ) * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d := by ring
      have hsum_out : ∑ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x ≤
          192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d *
            latticeShellTailConst d * (1 + v_LR * |t|) ^ d := by
        have hper_n : ∀ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x ≤
            (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) *
              (((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2)) := by
          intro n _
          have h1 : ∑ x ∈ shell n, f_site x ≤
              ((shell n).card : ℝ) * (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by
            calc ∑ x ∈ shell n, f_site x
                ≤ ∑ _x ∈ shell n, (3 : ℝ) * (64 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by
                  refine Finset.sum_le_sum fun x hx ↦ ?_
                  have hsep_x := (Finset.mem_filter.mp hx).2.1
                  calc f_site x ≤ ∑ _α : Fin 3, 64 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2) :=
                        Finset.sum_le_sum fun α _ ↦ hsite_decay n x α hsep_x
                    _ = (3 : ℝ) * (64 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by simp
              _ = ((shell n).card : ℝ) * (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]; ring
          have hs0_le : (s₀ : ℝ) ≤ (s₀ : ℝ) + 1 := by linarith
          calc ∑ x ∈ shell n, f_site x
              ≤ ((s₀ : ℝ) * C_vol * (((L₀ + 3) * R_int : ℝ) + 1) ^ d * ((n + 1 : ℝ) ^ d)) *
                  (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) :=
                le_trans h1 (mul_le_mul_of_nonneg_right (hvol_shell n) (by positivity))
            _ ≤ (((s₀ : ℝ) + 1) * C_vol * ((4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) * ((n + 1 : ℝ) ^ d)) *
                  (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_right hs0_le hCvol.le) hrad_tot (by positivity) (by positivity)
            _ = (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) *
                  (((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2)) := by ring
        calc ∑ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x
            ≤ ∑ n ∈ Finset.range M_max,
                (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) *
                  (((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2)) := Finset.sum_le_sum hper_n
          _ = (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) *
                ∑ n ∈ Finset.range M_max, ((n + 1 : ℝ) ^ d) * Real.exp (-(n : ℝ) / 2) := (Finset.mul_sum _ _ _).symm
          _ ≤ (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d) *
                latticeShellTailConst d :=
              mul_le_mul_of_nonneg_left
                ((summable_latticeShellTail d).sum_le_tsum (Finset.range M_max) (fun _ _ ↦ by positivity))
                (by positivity)
          _ = 192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d *
                latticeShellTailConst d * (1 + v_LR * |t|) ^ d := by ring
      unfold otocI
      have hs0_cub : (s₀ : ℝ) ≤ ((s₀ : ℝ) + 1) ^ 3 := by
        have hs0_nn : 0 ≤ (s₀ : ℝ) := Nat.cast_nonneg s₀
        nlinarith [sq_nonneg ((s₀ : ℝ) + 1)]
      have hsum_in' : ∑ x ∈ S_in, f_site x ≤
          192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d := by
        refine le_trans hsum_in ?_
        have hfac : 0 ≤ 192 * C_O ^ 2 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d := by positivity
        nlinarith
      calc (1 / 8 : ℝ) * ∑ x : Fin N, f_site x
          ≤ (1 / 8 : ℝ) * ((∑ x ∈ S_in, f_site x) + ∑ n ∈ Finset.range M_max, ∑ x ∈ shell n, f_site x) :=
            mul_le_mul_of_nonneg_left hsum_split (by norm_num)
        _ ≤ (1 / 8 : ℝ) * (192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d * (1 + v_LR * |t|) ^ d +
              192 * C_O ^ 2 * ((s₀ : ℝ) + 1) ^ 3 * C_vol * (4 * (R_int : ℝ) + 1) ^ d *
                latticeShellTailConst d * (1 + v_LR * |t|) ^ d) :=
            mul_le_mul_of_nonneg_left (add_le_add hsum_in' hsum_out) (by norm_num)
        _ = C_LR * (1 + v_LR * |t|) ^ d := by dsimp only [C_LR, cor65LatticeConst]; ring
  have h64 := (prop_6_4_part2_unconditional hN hr E hE_ne hE_card h hh_supp hH hJ hH_site hβ0 hβ hU₀ hO_supp hOnorm hCO_ge1 hCO t).2.2
  refine ⟨hotoc_le, ?_⟩
  have hrt : Real.sqrt (otocI hH β Ot) ≤ Real.sqrt (C_LR * (1 + v_LR * |t|) ^ d) :=
    Real.sqrt_le_sqrt hotoc_le
  have hmul : 2 * Real.sqrt (otocI hH β Ot) * Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) ≤
      2 * Real.sqrt (C_LR * (1 + v_LR * |t|) ^ d) * Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrt (by norm_num)) (Real.sqrt_nonneg _)
  linarith

end Corollary65LatticeBound

end KrylovChaos
