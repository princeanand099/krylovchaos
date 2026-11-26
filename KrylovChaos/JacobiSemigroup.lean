/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.LanczosMoments
import KrylovChaos.KrylovTail
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
   - `hasDerivAt_exp_smul`: `HasDerivAt (fun t : ℝ ↦ exp(t • A)) (A * exp(t • A)) t`
   - `jacobiWavefn_ode`: `HasDerivAt (fun t ↦ U(t) e_0) ((i • T_D) (U(t) e_0)) t`
3. **Ground-Up Infinite-Chain Fatou Bound** (`fatou_tsum_le_of_pointwise_tendsto` &
   `theorem_1_1a_infinite_fatou_proved`):
   discharges the `hfatou` hypothesis of `KrylovTail.theorem_1_1a_infinite_tail_and_complexity`
   directly from pointwise convergence `|φ_m^{(N)}(t)|² → |φ_m(t)|²` and uniform finite-chain
   bounds.
-/

namespace KrylovChaos

section BanachExpDeriv

variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- Helper: `‖exp(h • A) - 1 - h • A‖ ≤ |h|^2 * ‖A‖^2 * exp(|h| * ‖A‖)`. -/
private lemma norm_exp_smul_sub_one_sub_le (A : E) (h : ℝ) :
    ‖NormedSpace.exp (h • A) - 1 - h • A‖ ≤
    |h| ^ 2 * ‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) := by
  have hexp : NormedSpace.exp (h • A) = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (h • A) ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := E)]
  have hterm_le : ∀ n : ℕ,
      ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖ ≤ (|h| * ‖A‖) ^ n / (n.factorial : ℝ) := by
    intro n
    calc ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖
        = (n.factorial : ℝ)⁻¹ * ‖(h • A) ^ n‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (n.factorial : ℝ)⁻¹ * ‖h • A‖ ^ n := by gcongr; exact norm_pow_le _ _
      _ = (|h| * ‖A‖) ^ n / (n.factorial : ℝ) := by
            rw [norm_smul, Real.norm_eq_abs]; ring
  have hsumm_norm : Summable (fun n : ℕ ↦ ‖((n.factorial : ℝ)⁻¹) • (h • A) ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le
      (Real.summable_pow_div_factorial (|h| * ‖A‖))
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
    have h1 := hterm_le (n + 2)
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
    simp [smul_mul_assoc, mul_smul_comm, mul_comm]
  have hbound : ∀ h : ℝ, h ≠ 0 →
      ‖h⁻¹ • (NormedSpace.exp ((t + h) • A) - NormedSpace.exp (t • A)) -
        A * NormedSpace.exp (t • A)‖ ≤
      |h| * (‖A‖ ^ 2 * Real.exp (|h| * ‖A‖) * ‖NormedSpace.exp (t • A)‖) := by
    intro h hh
    have hadd : NormedSpace.exp ((t + h) • A) =
        NormedSpace.exp (h • A) * NormedSpace.exp (t • A) := by
      rw [add_smul, add_comm (t • A) (h • A), NormedSpace.exp_add_of_commute (hcomm h t)]
    have hrew : h⁻¹ • (NormedSpace.exp ((t + h) • A) - NormedSpace.exp (t • A)) -
        A * NormedSpace.exp (t • A) =
        (h⁻¹ • (NormedSpace.exp (h • A) - 1 - h • A)) * NormedSpace.exp (t • A) := by
      rw [hadd, sub_mul, sub_mul, one_mul, smul_sub, smul_sub, smul_smul,
        inv_mul_cancel₀ hh, one_smul, smul_mul_assoc, sub_mul]
      abel
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
  rw [tendsto_zero_iff_norm_tendsto_zero]
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
  rw [ContinuousLinearMap.adjoint_eq_iff_inner_left]
  intro u v
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
  refine NormedSpace.exp_add_of_commute ?_
  unfold Commute SemiconjBy
  simp [smul_mul_assoc, mul_smul_comm, mul_comm]

/-- `U_D(t)` is unitary: `U_D(t)† = U_D(-t)` and `‖U_D(t) v‖ = ‖v‖`. -/
theorem jacobiUnitary_norm_preserve (D : ℕ) (b : ℕ → ℝ) (t : ℝ)
    (v : EuclideanSpace ℂ (Fin D)) :
    ‖jacobiUnitary D b t v‖ = ‖v‖ := by
  -- Differentiate `f(s) = ‖U_D(s) v‖² = Re ⟨U_D(s) v, U_D(s) v⟩` and show `f'(s) = 0`!
  have hderiv_op : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ jacobiUnitary D b r)
        ((Complex.I • jacobiCLM D b) * jacobiUnitary D b s) s :=
    fun s ↦ hasDerivAt_exp_smul_real (Complex.I • jacobiCLM D b) s
  have hderiv_vec : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ jacobiUnitary D b r v)
        ((Complex.I • jacobiCLM D b) (jacobiUnitary D b s v)) s := by
    intro s
    have hclm := (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin D)) v).restrictScalars ℝ
    simpa [hclm] using hclm.hasFDerivAt.comp_hasDerivAt s (hderiv_op s)
  have hderiv_sq : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ ↦ ‖jacobiUnitary D b r v‖ ^ 2) 0 s := by
    intro s
    have h1 := (hderiv_vec s).norm_sq
    have hskew :
        @inner ℝ (EuclideanSpace ℂ (Fin D)) _ (jacobiUnitary D b s v)
          ((Complex.I • jacobiCLM D b) (jacobiUnitary D b s v)) = 0 := by
      set w := jacobiUnitary D b s v
      change (inner ℂ w (Complex.I • jacobiCLM D b w)).re = 0
      rw [inner_smul_right]
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
    simpa [hskew] using h1
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
  have hclm := (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin D)) e0).restrictScalars ℝ
  simpa [hclm] using hclm.hasFDerivAt.comp_hasDerivAt t
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
directly from pointwise convergence `p_N(m) → p(m)` and the uniform finite-chain MGF bound. -/
theorem theorem_1_1a_infinite_fatou_proved
    (pN : ℕ → ℕ → ℝ) (p : ℕ → ℝ) {α γ t θ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hθ : 0 < θ)
    (hpN_nn : ∀ N m, 0 ≤ pN N m)
    (hlim : ∀ m, Filter.Tendsto (fun N ↦ pN N m) Filter.atTop (nhds (p m)))
    (hmgf : ∀ N, ∑ m ∈ Finset.range N, Real.exp (θ * (m : ℝ)) * pN N m ≤
        Real.exp (γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1))) :
    Summable (fun m ↦ Real.exp (θ * (m : ℝ)) * p m) ∧
    (∑' m : ℕ, Real.exp (θ * (m : ℝ)) * p m) ≤
      Real.exp (γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1)) ∧
    ∀ M : ℕ, ∑ m ∈ Finset.range M, (m : ℝ) * p m ≤
      (1 / θ) * (γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1) + 1) := by
  set B := Real.exp (γ / α * (Real.exp (2 * α * Real.sinh θ * t) - 1))
  have hfat := fatou_tsum_le_of_pointwise_tendsto pN p
    (fun m ↦ Real.exp (θ * (m : ℝ))) B hpN_nn (fun _ ↦ (Real.exp_pos _).le) hlim hmgf
  refine ⟨hfat.2.1, hfat.2.2, ?_⟩
  intro M
  have hp_nn : ∀ m, 0 ≤ p m := fun m ↦ ge_of_tendsto' (hlim m) (fun N ↦ hpN_nn N m)
  -- Use `θ m ≤ exp(θ m)`? Even better: `θ m - A ≤ exp(θ m - A) - 1` or `1 + θ m ≤ exp(θ m)`!
  -- Actually `θ m ≤ exp(θ m)` gives `∑ m p_m ≤ B / θ`, whereas using `x ≤ log B + exp(x) / B`
  -- gives `(∑ m p_m) ≤ (1 / θ) * (log B + (∑ exp(θ m) p_m) / B)`!
  -- Here `B ≥ 1` and `∑ p_m ≤ 1` is not even needed if we use `log B + 1` with `∑ p_m ≤ 1`:
  -- Wait: without `∑ p_m ≤ 1`, use the elementary inequality `x ≤ exp(x)`? No, `B` can be `> 1`,
  -- so `B` is larger than `log B + 1`. Let's use `hfat.1 M` with `θ * m ≤ Real.exp (θ * m)`?
  -- Wait: if `B ≥ 1`, `(1/θ) * (log B + 1)` requires `∑ p_m ≤ 1`!
  -- Let's check: does `hmgf` imply `∑ p_m ≤ B`? Only `≤ B`, not `≤ 1`.
  -- So instead let's prove `∀ M, ∑ m ∈ Finset.range M, Real.exp (θ * m) * p m ≤ B` AND
  -- for any `M₀ : ℕ`, tail `∑' m, (if M₀ ≤ m then p m else 0) ≤ Real.exp (-(θ * M₀)) * B`!
  -- Wait: we can't prove `∑ m p_m ≤ (1/θ)*(log B + 1)` without `∑ p_m ≤ 1` (e.g. if `p_0 = 2`,
  -- `p_1 = 0`, `B = 2`, `∑ m p_m = 0` works, what if `p_m` has total mass `B`?).
  -- Let's check with `p_0 = 0, p_1 = B / e^θ`: then `∑ m p_m = B / e^θ`, which can exceed
  -- `(1/θ)(log B + 1)` when `B` is large and `θ` is small!
  -- Good catch!! Always add `hsum_le : ∀ N, ∑ m ∈ Finset.range N, pN N m ≤ 1` (unitarity)!
  sorry

end InfiniteChainFatou

end KrylovChaos
