/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.LanczosMoments
import KrylovChaos.KrylovTail
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# Section 3: Concrete Finite-Chain Unitary Evolution `exp(i t T_D) e_0` & Proved Infinite-Chain Fatou Bound

Closes the concrete Section 3 semigroup and infinite-chain bridge gaps:
1. **Concrete Hermitian Jacobi Operator `jacobiCLM D b`** on `EuclideanSpace ℂ (Fin D)` and
   its unitary one-parameter group `jacobiUnitary D b t = exp(t • (i • jacobiCLM D b))`.
2. **Exact Group Law, Unitarity & Schrödinger/Lanczos ODE** (Eq. 2.7):
   - `jacobiUnitary_zero`: `U(0) = 1`
   - `jacobiUnitary_add`: `U(t + s) = U(t) ∘ U(s)`
   - `jacobiUnitary_norm_preserve`: `‖U(t) v‖ = ‖v‖` (exact probability conservation)
   - `hasDerivAt_exp_smul_real`: `HasDerivAt (fun t : ℝ ↦ exp(t • A)) (A * exp(t • A)) t`
   - `jacobiWavefn_ode`: `HasDerivAt (fun t ↦ U(t) e_0) ((i • T_D) (U(t) e_0)) t`
3. **Ground-Up Infinite-Chain Fatou Bound** (`fatou_tsum_le_of_pointwise_tendsto` &
   `theorem_1_1a_infinite_fatou_proved`):
   discharges the `hfatou` hypothesis of `KrylovTail.theorem_1_1a_infinite_tail_and_complexity`
   directly from pointwise convergence `|φ_m^{(N)}(t)|² → |φ_m(t)|²`, finite-chain unitarity,
   and the uniform finite-chain MGF bound.
-/

namespace KrylovChaos

section BanachExpDeriv

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- Convert a summable `ℕ × ℕ` series into a Cauchy-product antidiagonal series. -/
private lemma tsum_prod_eq_tsum_antidiag_real {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    (h : ℕ × ℕ → G) (hh : Summable h) :
    (∑' p : ℕ × ℕ, h p) = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, h p := by
  let e : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ≃ ℕ × ℕ :=
    Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ ↦ p.1 + p.2)
  have hcomp : Summable (fun q : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ↦ h (e q)) :=
    hh.comp_injective e.injective
  have hfib : ∀ m : ℕ, Fintype {p : ℕ × ℕ // p.1 + p.2 = m} := fun m ↦
    Fintype.ofEquiv (Finset.antidiagonal m)
      { toFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mp p.2⟩
        invFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mpr p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have h1 : (∑' p : ℕ × ℕ, h p) = ∑' q : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m}, h (e q) :=
    (e.tsum_eq h).symm
  rw [h1, hcomp.tsum_sigma' (fun m ↦ (hasSum_fintype _).summable)]
  refine tsum_congr fun m ↦ ?_
  haveI := hfib m
  rw [tsum_fintype]
  refine Finset.sum_bij (fun p _ ↦ p.1) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_antidiagonal.mpr p.2
  · intro p₁ _ p₂ _ hp; exact Subtype.ext hp
  · intro p hp; exact ⟨⟨p, Finset.mem_antidiagonal.mp hp⟩, Finset.mem_univ _, rfl⟩
  · intro p _; rfl

/-- Exponential addition formula for commuting elements in any complete normed `ℝ`-algebra
(requires neither `NormOneClass` nor `NormedAlgebra ℚ`). -/
private lemma exp_add_of_commute_real {x y : E} (hxy : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y := by
  let f : ℕ → E := fun j ↦ ((j.factorial : ℝ)⁻¹) • x ^ j
  let g : ℕ → E := fun k ↦ ((k.factorial : ℝ)⁻¹) • y ^ k
  have hfx : NormedSpace.exp x = ∑' j : ℕ, f j := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := E)]
  have hgy : NormedSpace.exp y = ∑' k : ℕ, g k := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := E)]
  have hxy_exp : NormedSpace.exp (x + y) = ∑' m : ℕ, ((m.factorial : ℝ)⁻¹) • (x + y) ^ m := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := E)]
  have hfn : Summable (fun j : ℕ ↦ ‖f j‖) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖x‖))
    calc ‖f (j + 1)‖ = ((j + 1).factorial : ℝ)⁻¹ * ‖x ^ (j + 1)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ((j + 1).factorial : ℝ)⁻¹ * ‖x‖ ^ (j + 1) := by
            gcongr; exact norm_pow_le' _ (Nat.succ_pos j)
      _ = ‖x‖ ^ (j + 1) / ((j + 1).factorial : ℝ) := by ring
  have hgn : Summable (fun k : ℕ ↦ ‖g k‖) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖y‖))
    calc ‖g (k + 1)‖ = ((k + 1).factorial : ℝ)⁻¹ * ‖y ^ (k + 1)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ((k + 1).factorial : ℝ)⁻¹ * ‖y‖ ^ (k + 1) := by
            gcongr; exact norm_pow_le' _ (Nat.succ_pos k)
      _ = ‖y‖ ^ (k + 1) / ((k + 1).factorial : ℝ) := by ring
  have hprod_summ : Summable (fun p : ℕ × ℕ ↦ f p.1 * g p.2) :=
    summable_mul_of_summable_norm hfn hgn
  rw [hfx, hgy, tsum_mul_tsum_of_summable_norm hfn hgn,
    tsum_prod_eq_tsum_antidiag_real _ hprod_summ, hxy_exp]
  refine tsum_congr fun m ↦ ?_
  rw [hxy.add_pow m, Finset.smul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k ↦ f j * g k) m]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfac_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hj_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hmj_ne : ((m - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - j))
  have hchoose : ((m.factorial : ℝ)⁻¹) * (Nat.choose m j : ℝ) =
      ((j.factorial : ℝ)⁻¹) * (((m - j).factorial : ℝ)⁻¹) := by
    have hnat : (Nat.choose m j : ℝ) * (j.factorial : ℝ) * ((m - j).factorial : ℝ) =
        (m.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjm
    field_simp [hfac_ne, hj_ne, hmj_ne]
    linear_combination hnat
  simp only [f, g, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (((m - j).factorial : ℝ)⁻¹), ← hchoose, ← nsmul_eq_mul',
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

/-- Helper: `‖exp(h • A) - 1 - h • A‖ ≤ |h|^2 * ‖A‖^2 * exp(|h| * ‖A‖)` (no `NormOneClass` needed). -/
private lemma norm_exp_smul_sub_one_sub_le (A : E) (h : ℝ) :
    ‖NormedSpace.exp (h • A) - 1 - h • A‖ ≤
    |h| ^ 2 * ‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) := by
  have hexp : NormedSpace.exp (h • A) = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (h • A) ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := E)]
  have hterm_le : ∀ n : ℕ, 1 ≤ n →
      ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖ ≤ (|h| * ‖A‖) ^ n / (n.factorial : ℝ) := by
    intro n hn
    calc ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖
        = (n.factorial : ℝ)⁻¹ * ‖(h • A) ^ n‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (n.factorial : ℝ)⁻¹ * ‖h • A‖ ^ n := by
            gcongr; exact norm_pow_le' _ hn
      _ = (|h| * ‖A‖) ^ n / (n.factorial : ℝ) := by
            rw [norm_smul, Real.norm_eq_abs]; ring
  have hsumm_norm : Summable (fun n : ℕ ↦ ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ hterm_le (n + 1) (Nat.succ_pos n))
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial (|h| * ‖A‖)))
  have hsumm : Summable (fun n : ℕ ↦ ((n.factorial : ℝ)⁻¹) • (h • A) ^ n) :=
    hsumm_norm.of_norm
  have hsplit := hsumm.sum_add_tsum_nat_add 2
  have hfirst2 : (∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) • (h • A) ^ i) = 1 + h • A := by
    simp [Finset.sum_range_succ]
  rw [hfirst2, ← hexp] at hsplit
  have hdiff : NormedSpace.exp (h • A) - 1 - h • A =
      ∑' n : ℕ, (((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2) := by
    rw [← hsplit]; abel
  rw [hdiff]
  have htail_le : ∀ n : ℕ,
      ‖(((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2)‖ ≤
      (|h| ^ 2 * ‖A‖ ^ 2) * ((|h| * ‖A‖) ^ n / (n.factorial : ℝ)) := by
    intro n
    have hfac : (n.factorial : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 2)
    have h1 := hterm_le (n + 2) (by omega)
    have hpow : (|h| * ‖A‖) ^ (n + 2) = (|h| ^ 2 * ‖A‖ ^ 2) * (|h| * ‖A‖) ^ n := by
      rw [pow_add, mul_pow]; ring
    calc ‖(((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2)‖
        ≤ (|h| * ‖A‖) ^ (n + 2) / ((n + 2).factorial : ℝ) := h1
      _ ≤ (|h| * ‖A‖) ^ (n + 2) / (n.factorial : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr (Nat.factorial_pos n)) hfac
      _ = (|h| ^ 2 * ‖A‖ ^ 2) * ((|h| * ‖A‖) ^ n / (n.factorial : ℝ)) := by rw [hpow]; ring
  have htail_summ : Summable (fun n : ℕ ↦ ‖(((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) htail_le
      ((Real.summable_pow_div_factorial (|h| * ‖A‖)).mul_left _)
  have hexp_real : ∑' n : ℕ, (|h| * ‖A‖) ^ n / (n.factorial : ℝ) = Real.exp (|h| * ‖A‖) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc ‖∑' n : ℕ, (((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖(((n + 2).factorial : ℝ)⁻¹) • (h • A) ^ (n + 2)‖ :=
          norm_tsum_le_tsum_norm htail_summ
    _ ≤ ∑' n : ℕ, (|h| ^ 2 * ‖A‖ ^ 2) * ((|h| * ‖A‖) ^ n / (n.factorial : ℝ)) :=
          htail_summ.tsum_le_tsum htail_le ((Real.summable_pow_div_factorial _).mul_left _)
    _ = (|h| ^ 2 * ‖A‖ ^ 2) * ∑' n : ℕ, (|h| * ‖A‖) ^ n / (n.factorial : ℝ) := tsum_mul_left
    _ = |h| ^ 2 * ‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) := by rw [hexp_real]

/-- **Exact Derivative of the Banach-Algebra Exponential One-Parameter Group**:
`HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • A)) (A * NormedSpace.exp (t • A)) t`. -/
theorem hasDerivAt_exp_smul_real (A : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A)) (A * NormedSpace.exp (t • A)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hcomm : ∀ s₁ s₂ : ℝ, Commute (s₁ • A) (s₂ • A) := by
    intro s₁ s₂
    unfold Commute SemiconjBy
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [smul_comm]
  have hbound : ∀ h : ℝ, h ≠ 0 →
      ‖h⁻¹ • (NormedSpace.exp ((t + h) • A) - NormedSpace.exp (t • A)) -
        A * NormedSpace.exp (t • A)‖ ≤
      |h| * (‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) * ‖NormedSpace.exp (t • A)‖) := by
    intro h hh
    have hadd : NormedSpace.exp ((t + h) • A) =
        NormedSpace.exp (h • A) * NormedSpace.exp (t • A) := by
      rw [add_smul, add_comm (t • A) (h • A)]
      exact exp_add_of_commute_real (hcomm h t)
    have hrew : h⁻¹ • (NormedSpace.exp ((t + h) • A) - NormedSpace.exp (t • A)) -
        A * NormedSpace.exp (t • A) =
        (h⁻¹ • (NormedSpace.exp (h • A) - 1 - h • A)) * NormedSpace.exp (t • A) := by
      rw [hadd]
      symm
      rw [smul_mul_assoc, sub_mul, sub_mul, one_mul, smul_mul_assoc,
        smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul]
    rw [hrew]
    calc ‖(h⁻¹ • (NormedSpace.exp (h • A) - 1 - h • A)) * NormedSpace.exp (t • A)‖
        ≤ ‖h⁻¹ • (NormedSpace.exp (h • A) - 1 - h • A)‖ * ‖NormedSpace.exp (t • A)‖ :=
            norm_mul_le _ _
      _ = |h|⁻¹ * ‖NormedSpace.exp (h • A) - 1 - h • A‖ * ‖NormedSpace.exp (t • A)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ |h|⁻¹ * (|h| ^ 2 * ‖A‖ ^ 2 * Real.exp (|h| * ‖A‖)) * ‖NormedSpace.exp (t • A)‖ := by
            gcongr; exact norm_exp_smul_sub_one_sub_le A h
      _ = |h| * (‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) * ‖NormedSpace.exp (t • A)‖) := by
            have habs : |h| ≠ 0 := abs_ne_zero.mpr hh
            field_simp [habs]
  have htend : Filter.Tendsto
      (fun h : ℝ ↦ |h| * (‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) * ‖NormedSpace.exp (t • A)‖))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have hcont : Continuous (fun h : ℝ ↦
        |h| * (‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) * ‖NormedSpace.exp (t • A)‖)) := by
      fun_prop
    have h0 := hcont.tendsto (0 : ℝ)
    simp only [abs_zero, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ htend
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact hbound h hh

end BanachExpDeriv

section FiniteChainUnitary

/-- Concrete `D × D` tridiagonal Jacobi operator on `EuclideanSpace ℂ (Fin D)`. -/
noncomputable def jacobiCLM (D : ℕ) (b : ℕ → ℝ) :
    EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ WithLp.toLp 2 (fun i : Fin D ↦
        ∑ j : Fin D, ((jacobiMat D b i j : ℝ) : ℂ) * v j)
      map_add' := fun u v ↦ by
        ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        ext i; simp [Finset.mul_sum, mul_left_comm] }

/-- `jacobiCLM D b` is self-adjoint on `EuclideanSpace ℂ (Fin D)`. -/
theorem jacobiCLM_isSelfAdjoint (D : ℕ) (b : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (jacobiCLM D b) = jacobiCLM D b := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    jacobiCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Complex.star_def, map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsym : jacobiMat D b j i = jacobiMat D b i j := by
    have := congrFun (congrFun (jacobiMat_transpose D b) i) j
    simpa [Matrix.transpose_apply] using this
  rw [hsym]
  ring

/-- Concrete unitary one-parameter propagator `U_D(t) = exp(t • (i • T_D))` on
`EuclideanSpace ℂ (Fin D)`. -/
noncomputable def jacobiUnitary (D : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D) :=
  NormedSpace.exp (t • (Complex.I • jacobiCLM D b))

lemma jacobiUnitary_zero (D : ℕ) (b : ℕ → ℝ) :
    jacobiUnitary D b 0 = 1 := by
  simp [jacobiUnitary]

lemma jacobiUnitary_add (D : ℕ) (b : ℕ → ℝ) (t s : ℝ) :
    jacobiUnitary D b (t + s) = jacobiUnitary D b t * jacobiUnitary D b s := by
  unfold jacobiUnitary
  rw [add_smul]
  refine exp_add_of_commute_real ?_
  unfold Commute SemiconjBy
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm Complex.I s, smul_comm Complex.I t, smul_comm s t]

/-- `U_D(t)` is unitary: `‖U_D(t) v‖ = ‖v‖` for all `t : ℝ` and `v`. -/
theorem jacobiUnitary_norm_preserve (D : ℕ) (b : ℕ → ℝ) (t : ℝ)
    (v : EuclideanSpace ℂ (Fin D)) :
    ‖jacobiUnitary D b t v‖ = ‖v‖ := by
  have hderiv_op : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ jacobiUnitary D b r)
        ((Complex.I • jacobiCLM D b) * jacobiUnitary D b s) s :=
    fun s ↦ hasDerivAt_exp_smul_real (Complex.I • jacobiCLM D b) s
  have hderiv_vec : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ jacobiUnitary D b r v)
        (Complex.I • jacobiCLM D b (jacobiUnitary D b s v)) s := by
    intro s
    let hclm := (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin D)) v).restrictScalars ℝ
    exact hclm.hasFDerivAt.comp_hasDerivAt s (hderiv_op s)
  have hderiv_sq : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ ‖jacobiUnitary D b r v‖ ^ 2) 0 s := by
    intro s
    have hinner := HasDerivAt.inner ℝ (hderiv_vec s) (hderiv_vec s)
    have hfun : (fun r : ℝ ↦ ‖jacobiUnitary D b r v‖ ^ 2) =
        fun r : ℝ ↦ @inner ℝ (EuclideanSpace ℂ (Fin D)) _ (jacobiUnitary D b r v)
          (jacobiUnitary D b r v) := by
      ext r; exact (real_inner_self_eq_norm_sq _).symm
    rw [hfun]
    have hskew :
        @inner ℝ (EuclideanSpace ℂ (Fin D)) _ (jacobiUnitary D b s v)
          (Complex.I • jacobiCLM D b (jacobiUnitary D b s v)) = 0 := by
      set w := jacobiUnitary D b s v
      have hre_inner : @inner ℝ (EuclideanSpace ℂ (Fin D)) _ w (Complex.I • jacobiCLM D b w) =
          (inner ℂ w (Complex.I • jacobiCLM D b w)).re := by
        rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [Complex.inner, RCLike.inner_apply, Complex.mul_re]
        ring
      rw [hre_inner, inner_smul_right]
      have hreal : (inner ℂ w (jacobiCLM D b w)).im = 0 := by
        have hsa := jacobiCLM_isSelfAdjoint D b
        have hconj : star (inner ℂ w (jacobiCLM D b w)) = inner ℂ w (jacobiCLM D b w) := by
          calc star (inner ℂ w (jacobiCLM D b w))
              = inner ℂ (jacobiCLM D b w) w := inner_conj_symm _ _
            _ = inner ℂ w (ContinuousLinearMap.adjoint (jacobiCLM D b) w) :=
                  (ContinuousLinearMap.adjoint_inner_right (jacobiCLM D b) w w).symm
            _ = inner ℂ w (jacobiCLM D b w) := by rw [hsa]
        have := congrArg Complex.im hconj
        simp [Complex.star_def] at this
        linarith
      simp [Complex.mul_re, hreal]
    have hskew2 :
        @inner ℝ (EuclideanSpace ℂ (Fin D)) _
          (Complex.I • jacobiCLM D b (jacobiUnitary D b s v))
          (jacobiUnitary D b s v) = 0 := by
      rw [real_inner_comm]; exact hskew
    rw [hskew, hskew2, add_zero] at hinner
    exact hinner
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hderiv_sq s).differentiableAt) (fun s ↦ (hderiv_sq s).deriv) t 0
  rw [jacobiUnitary_zero] at hconst
  simp only [ContinuousLinearMap.one_apply] at hconst
  nlinarith [norm_nonneg (jacobiUnitary D b t v), norm_nonneg v]

/-- **Exact Lanczos ODE (Eq. 2.7)** for the concrete finite-chain Krylov wavefunction
`φ_D(t) = exp(i t T_D) e_0`:
`d/dt φ_D(t) = i T_D φ_D(t)`. -/
theorem jacobiWavefn_ode {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) :
    let e0 : EuclideanSpace ℂ (Fin D) := EuclideanSpace.single ⟨0, hD⟩ 1
    HasDerivAt (fun r : ℝ ↦ jacobiUnitary D b r e0)
      ((Complex.I • jacobiCLM D b) (jacobiUnitary D b t e0)) t := by
  intro e0
  let hclm := (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin D)) e0).restrictScalars ℝ
  exact hclm.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_real (Complex.I • jacobiCLM D b) t)

end FiniteChainUnitary

section InfiniteChainFatou

/-- **Ground-Up Fatou Bound for Weighted Series on `ℕ`**:
If `f : ℕ → ℕ → ℝ` satisfies `0 ≤ f N m`, converges pointwise `f N m → g m` as `N → ∞`,
`w : ℕ → ℝ` satisfies `0 ≤ w m`, and for every `N` the finite partial sum satisfies
`∑ m ∈ Finset.range N, w m * f N m ≤ B`, then:
1. For every `M : ℕ`, `∑ m ∈ Finset.range M, w m * g m ≤ B`,
2. `Summable (fun m ↦ w m * g m)`, and
3. `∑' m : ℕ, w m * g m ≤ B`. -/
theorem fatou_tsum_le_of_pointwise_tendsto (f : ℕ → ℕ → ℝ) (g w : ℕ → ℝ) (B : ℝ)
    (hf_nn : ∀ N m, 0 ≤ f N m)
    (hw_nn : ∀ m, 0 ≤ w m)
    (hlim : ∀ m, Filter.Tendsto (fun N ↦ f N m) Filter.atTop (nhds (g m)))
    (hunif : ∀ N, ∑ m ∈ Finset.range N, w m * f N m ≤ B) :
    (∀ M, ∑ m ∈ Finset.range M, w m * g m ≤ B) ∧
    Summable (fun m ↦ w m * g m) ∧
    (∑' m : ℕ, w m * g m) ≤ B := by
  have hg_nn : ∀ m, 0 ≤ g m := fun m ↦
    ge_of_tendsto' (hlim m) (fun N ↦ hf_nn N m)
  have hpartial : ∀ M : ℕ, ∑ m ∈ Finset.range M, w m * g m ≤ B := by
    intro M
    have htend : Filter.Tendsto (fun N ↦ ∑ m ∈ Finset.range M, w m * f N m)
        Filter.atTop (nhds (∑ m ∈ Finset.range M, w m * g m)) :=
      tendsto_finset_sum _ fun m _ ↦ (hlim m).const_mul (w m)
    refine le_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop M] with N hNM
    calc ∑ m ∈ Finset.range M, w m * f N m
        ≤ ∑ m ∈ Finset.range N, w m * f N m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
            (fun m _ _ ↦ mul_nonneg (hw_nn m) (hf_nn N m))
      _ ≤ B := hunif N
  have hsumm : Summable (fun m ↦ w m * g m) :=
    summable_of_sum_range_le (fun m ↦ mul_nonneg (hw_nn m) (hg_nn m)) hpartial
  have htsum : ∑' m : ℕ, w m * g m ≤ B := by
    exact le_of_tendsto (hsumm.hasSum.tendsto_sum_nat)
      (Filter.Eventually.of_forall hpartial)
  exact ⟨hpartial, hsumm, htsum⟩

/-- **Theorem 1.1(a) Infinite-Chain Fatou Tail & Complexity Bound (Zero `hfatou` Hypothesis)**:
Discharges the `hfatou` hypothesis of `KrylovTail.theorem_1_1a_infinite_tail_and_complexity`
directly from pointwise convergence `p_N(m) → p(m)`, finite-chain unitarity (`∑ p_N ≤ 1`),
and the uniform finite-chain MGF bound, proving:
1. Summability and MGF bound `∑' m, exp(θ m) p_m ≤ exp(A)`,
2. Exponential tail bound `∑' m, (if M₀ ≤ m then p_m else 0) ≤ exp(-θ M₀ + A)`, and
3. Infinite-chain Krylov complexity bound `∑' m, m p_m ≤ (1 / θ) (A + 1)`. -/
theorem theorem_1_1a_infinite_fatou_proved
    (pN : ℕ → ℕ → ℝ) (p : ℕ → ℝ) {α γ t θ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hθ : 0 < θ)
    (hpN_nn : ∀ N m, 0 ≤ pN N m)
    (hunit : ∀ N, ∑ m ∈ Finset.range N, pN N m ≤ 1)
    (hlim : ∀ m, Filter.Tendsto (fun N ↦ pN N m) Filter.atTop (nhds (p m)))
    (hmgf : ∀ N, ∑ m ∈ Finset.range N, Real.exp (θ * (m : ℝ)) * pN N m ≤
        Real.exp (γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1))) :
    let A := γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1)
    Summable (fun m : ℕ ↦ Real.exp (θ * (m : ℝ)) * p m) ∧
    (∑' m : ℕ, Real.exp (θ * (m : ℝ)) * p m) ≤ Real.exp A ∧
    (∀ M₀ : ℕ, (∑' m : ℕ, if M₀ ≤ m then p m else 0) ≤ Real.exp (-(θ * (M₀ : ℝ)) + A)) ∧
    Summable (fun m : ℕ ↦ (m : ℝ) * p m) ∧
    (∑' m : ℕ, (m : ℝ) * p m) ≤ (1 / θ) * (A + 1) := by
  intro A
  have hsinh_nn : 0 ≤ Real.sinh θ := by
    rw [Real.sinh_eq]
    have : Real.exp (-θ) ≤ Real.exp θ := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg (div_nonneg hγ hα.le)
    have : 1 ≤ Real.exp (2 * α * Real.sinh θ * t) := Real.one_le_exp (by positivity)
    linarith
  have hfat_mgf := fatou_tsum_le_of_pointwise_tendsto pN p
    (fun m : ℕ ↦ Real.exp (θ * (m : ℝ))) (Real.exp A) hpN_nn
    (fun _ ↦ (Real.exp_pos _).le) hlim hmgf
  have hfat_prob := fatou_tsum_le_of_pointwise_tendsto pN p
    (fun _ : ℕ ↦ 1) 1 hpN_nn (fun _ ↦ by norm_num) hlim (by simpa using hunit)
  have hp_nn : ∀ m : ℕ, 0 ≤ p m := fun m ↦ ge_of_tendsto' (hlim m) (fun N ↦ hpN_nn N m)
  have htail : ∀ M₀ : ℕ,
      (∑' m : ℕ, if M₀ ≤ m then p m else 0) ≤ Real.exp (-(θ * (M₀ : ℝ)) + A) := by
    intro M₀
    have hdom : ∀ m : ℕ,
        (if M₀ ≤ m then p m else 0) ≤
        Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) := by
      intro m
      split_ifs with hm
      · have h1 : 1 ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by
            have : (M₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
            nlinarith)
        calc p m = 1 * p m := (one_mul _).symm
          _ ≤ (Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ))) * p m :=
                mul_le_mul_of_nonneg_right h1 (hp_nn m)
          _ = Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) := by ring
      · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hp_nn m))
    have hsumm_t : Summable (fun m : ℕ ↦ if M₀ ≤ m then p m else 0) :=
      Summable.of_nonneg_of_le (fun m ↦ by split_ifs <;> [exact hp_nn m; exact le_refl 0])
        hdom (hfat_mgf.2.1.mul_left _)
    calc ∑' m : ℕ, (if M₀ ≤ m then p m else 0)
        ≤ ∑' m : ℕ, Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) :=
            hsumm_t.tsum_le_tsum hdom (hfat_mgf.2.1.mul_left _)
      _ = Real.exp (-(θ * (M₀ : ℝ))) * ∑' m : ℕ, Real.exp (θ * (m : ℝ)) * p m := tsum_mul_left
      _ ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp A :=
            mul_le_mul_of_nonneg_left hfat_mgf.2.2 (Real.exp_pos _).le
      _ = Real.exp (-(θ * (M₀ : ℝ)) + A) := (Real.exp_add _ _).symm
  have hcomp_partial : ∀ M : ℕ, ∑ m ∈ Finset.range M, (m : ℝ) * p m ≤ (1 / θ) * (A + 1) := by
    intro M
    have hstep : ∀ m : ℕ,
        θ * ((m : ℝ) * p m) ≤ A * p m + (Real.exp A)⁻¹ * (Real.exp (θ * (m : ℝ)) * p m) := by
      intro m
      have hexp : θ * (m : ℝ) - A ≤ Real.exp (θ * (m : ℝ) - A) := by
        linarith [Real.add_one_le_exp (θ * (m : ℝ) - A)]
      rw [Real.exp_sub, div_eq_inv_mul] at hexp
      have h1 : θ * (m : ℝ) ≤ A + (Real.exp A)⁻¹ * Real.exp (θ * (m : ℝ)) := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 (hp_nn m)
      linarith
    have hsum_θ :
        θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m) ≤
        A * (∑ m ∈ Finset.range M, p m) +
        (Real.exp A)⁻¹ * (∑ m ∈ Finset.range M, Real.exp (θ * (m : ℝ)) * p m) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun m _ ↦ hstep m
    have hp_le : ∑ m ∈ Finset.range M, p m ≤ 1 := by simpa using hfat_prob.1 M
    have hm_le : ∑ m ∈ Finset.range M, Real.exp (θ * (m : ℝ)) * p m ≤ Real.exp A := hfat_mgf.1 M
    have hbound : θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m) ≤ A + 1 := by
      calc θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m)
          ≤ A * 1 + (Real.exp A)⁻¹ * Real.exp A := by
              have h1 := mul_le_mul_of_nonneg_left hp_le hA_nn
              have h2 := mul_le_mul_of_nonneg_left hm_le (inv_nonneg.mpr (Real.exp_pos A).le)
              linarith
        _ = A + 1 := by rw [mul_one, inv_mul_cancel₀ (Real.exp_pos A).ne']
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hθ]
    linarith
  have hcomp_summ : Summable (fun m : ℕ ↦ (m : ℝ) * p m) :=
    summable_of_sum_range_le (fun m ↦ mul_nonneg (Nat.cast_nonneg m) (hp_nn m)) hcomp_partial
  have hcomp_tsum : ∑' m : ℕ, (m : ℝ) * p m ≤ (1 / θ) * (A + 1) :=
    le_of_tendsto (hcomp_summ.hasSum.tendsto_sum_nat)
      (Filter.Eventually.of_forall hcomp_partial)
  exact ⟨hfat_mgf.2.1, hfat_mgf.2.2, htail, hcomp_summ, hcomp_tsum⟩

end InfiniteChainFatou

end KrylovChaos
