/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.MajoranaAlgebra
import KrylovChaos.EndToEndTheorems
import KrylovChaos.Filtration
import KrylovChaos.Theorem11bConcrete
import KrylovChaos.ProductStateLambdaMSS
import KrylovChaos.ConcreteCombinatorics
import Mathlib.Tactic

/-!
# Milestone 1 Core Remediation (Items #2, #3, #10, #11, #29)

Strictly Mathlib-only, complete proofs, zero custom axioms, zero hypothesis laundering:
1. **Item #2 (Prop. 2.2(1) Standalone Bijectivity / Linear Equivalence)**:
   - `jBetaLinearEquiv : QubitOp N ≃ₗ[ℂ] QubitOp N`
   - `prop_2_2_part1_jBeta_bijective : Function.Bijective (jBeta G.ρQuarter)`
2. **Item #3 (Prop. 2.3(2) Deriving `isEvenParity ρQuarter` from `isEvenParity H`)**:
   - `isEvenParity_concreteGibbsRhoQuarter`: proves `isEvenParity H → isEvenParity (concreteGibbsData hH β).ρQuarter`
     using `qubitOpToCLM_hermFunc_exp` and `fermionParityOp_sq`.
   - `prop_2_3_part2_majorana_from_even_H`: Eq. (2.10) assuming ONLY `isEvenParity H` and `isOddParity A`.
3. **Item #10 (Family-Level End-to-End Theorem 1.1(b) Concluding `λ_L ≤ 2 α`)**:
   - `theorem_1_1b_family_concrete_qubit`: composes `theorem_1_1b_concrete_qubit_thermal_size`
     over a family `{H_N, O_N}` with concrete (H1) on `mssThermalSize` and (H2) on `lambdaMSS`
     to derive `lamL ≤ 2 * α` unconditionally via `Filtration.theorem_1_1b_static_reduction`.
4. **Item #11 (Prop. 4.3 for Arbitrary Non-Diagonal Full-Rank Single-Site Density Matrices)**:
   - `arbitraryProdGibbsData`: diagonalizes arbitrary full-rank single-site Hermitian density
     matrices `ρ : Fin N → Matrix (Fin 2) (Fin 2) ℂ` via `IsHermitian.eigenvectorUnitary`,
     proving `(arbitraryProdGibbsData ...).ρβ = kronOp ρ`.
   - `prop_4_3_lambdaMSS_arbitrary_product_state`: proves
     `lambdaMSS (arbitraryProdGibbsData ...) s ≤ s + mmax * Real.sqrt (N * s)`.
5. **Item #29 (Multi-Type Heterogeneous-Locality Lemma A.3, Eqs. A.3–A.4)**:
   - `multiTypeTreeSum` and `lemma_A_3_multiType_unordered_tree_sum`: generalizes Lemma A.3
     from single-type uniform `|X| ≤ r` to an arbitrary finite multi-type hypergraph `F : Finset ι`
     with heterogeneous support sizes `supp : ι → Finset (Fin N)` under pinning condition
     `∀ y, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), μ e * exp (c₀ * |supp e|) ≤ c₀`.
-/

namespace KrylovChaos

open Matrix

section Item2JBetaBijectivity

/-- **Item #2 (Proposition 2.2(1) — Standalone Linear Equivalence `𝒥_β : QubitOp N ≃ₗ[ℂ] QubitOp N`)**:
For ANY `G : GibbsData N`, the Wightman isometry `A ↦ ρ_β^{1/4} A ρ_β^{1/4}` is a `ℂ`-linear
equivalence with explicit inverse `M ↦ ρ_β^{-1/4} M ρ_β^{-1/4}`. -/
def jBetaLinearEquiv {N : ℕ} (G : GibbsData N) : QubitOp N ≃ₗ[ℂ] QubitOp N where
  toFun := jBeta G.ρQuarter
  invFun := jBeta G.ρQuarterInv
  map_add' A B := by unfold jBeta; rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv A := by
    unfold jBeta
    calc G.ρQuarterInv * (G.ρQuarter * A * G.ρQuarter) * G.ρQuarterInv
        = (G.ρQuarterInv * G.ρQuarter) * A * (G.ρQuarter * G.ρQuarterInv) := by
            simp only [mul_assoc]
      _ = A := by rw [G.inv_left, G.inv_right, one_mul, mul_one]
  right_inv M := by
    unfold jBeta
    calc G.ρQuarter * (G.ρQuarterInv * M * G.ρQuarterInv) * G.ρQuarter
        = (G.ρQuarter * G.ρQuarterInv) * M * (G.ρQuarterInv * G.ρQuarter) := by
            simp only [mul_assoc]
      _ = M := by rw [G.inv_right, G.inv_left, one_mul, mul_one]

/-- **Item #2 (Proposition 2.2(1) — Bijectivity of `jBeta G.ρQuarter`)**:
Exports `Function.Bijective (jBeta G.ρQuarter)` as a standalone theorem. -/
theorem prop_2_2_part1_jBeta_bijective {N : ℕ} (G : GibbsData N) :
    Function.Bijective (jBeta G.ρQuarter) :=
  (jBetaLinearEquiv G).bijective

end Item2JBetaBijectivity

section Item3MajoranaEvenGibbs

private lemma qubitOpToCLM_mul_eq {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A * B) = (qubitOpToCLM A).comp (qubitOpToCLM B) := by
  apply ContinuousLinearMap.ext; intro v
  ext i
  change ∑ x, (A * B) i x * v.ofLp x = ∑ x, A i x * ∑ y, B x y * v.ofLp y
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma qubitOpToCLM_one_eq (N : ℕ) :
    qubitOpToCLM (1 : QubitOp N) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext; intro v
  ext i
  change ∑ x, (1 : QubitOp N) i x * v.ofLp x = v.ofLp i
  simp [Matrix.one_apply]

private lemma qubitOpToCLM_smul_eq {N : ℕ} (c : ℂ) (A : QubitOp N) :
    qubitOpToCLM (c • A) = c • qubitOpToCLM A := by
  apply ContinuousLinearMap.ext; intro v
  ext i
  change ∑ x, (c * A i x) * v.ofLp x = c * ∑ x, A i x * v.ofLp x
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

private lemma qubitOpToCLM_inj {N : ℕ} {A B : QubitOp N}
    (h : qubitOpToCLM A = qubitOpToCLM B) : A = B := by
  ext i j
  let e_j : EuclideanSpace ℂ (QubitIdx N) :=
    WithLp.toLp 2 (fun k : QubitIdx N ↦ if k = j then (1 : ℂ) else 0)
  have hv := congrArg (fun T : QubitOpCLM N ↦ (T e_j) i) h
  simpa [qubitOpToCLM, Matrix.mulVec, dotProduct, e_j] using hv

/-- **Item #3 (Even-Parity Hamiltonian Implies Even-Parity Gibbs `ρ_β^{1/4}`)**:
For ANY Hermitian `H : QubitOp n` with `isEvenParity H` (`P H P = H`) and ANY `β : ℝ`:
`isEvenParity (concreteGibbsData hH β).ρQuarter`. -/
theorem isEvenParity_concreteGibbsRhoQuarter {n : ℕ} {H : QubitOp n}
    (hH : H.IsHermitian) (hH_even : isEvenParity H) (β : ℝ) :
    isEvenParity (concreteGibbsData hH β).ρQuarter := by
  unfold isEvenParity
  change fermionParityOp n * gibbsRhoQuarter hH β * fermionParityOp n = gibbsRhoQuarter hH β
  unfold gibbsRhoQuarter
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have hfunc_eq : (fun E : ℝ ↦ (Real.exp (-(β / 4) * E) : ℂ)) =
      fun E : ℝ ↦ Complex.exp ((-(β / 4 : ℝ) : ℂ) * (E : ℂ)) := by
    funext E; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hfunc_eq]
  apply qubitOpToCLM_inj
  rw [qubitOpToCLM_mul_eq, qubitOpToCLM_mul_eq, qubitOpToCLM_hermFunc_exp hH (-(β / 4 : ℝ) : ℂ)]
  set P_clm : QubitOpCLM n := qubitOpToCLM (fermionParityOp n)
  set T_clm : QubitOpCLM n := (-(β / 4 : ℝ) : ℂ) • qubitOpToCLM H
  have hP_sq : P_clm * P_clm = 1 := by
    change P_clm.comp P_clm = ContinuousLinearMap.id ℂ _
    rw [← qubitOpToCLM_mul_eq, fermionParityOp_sq, qubitOpToCLM_one_eq]
  have hPT : P_clm * T_clm * P_clm = T_clm := by
    have hPH : P_clm * qubitOpToCLM H * P_clm = qubitOpToCLM H := by
      change (P_clm.comp (qubitOpToCLM H)).comp P_clm = qubitOpToCLM H
      rw [← qubitOpToCLM_mul_eq, ← qubitOpToCLM_mul_eq, hH_even]
    dsimp only [T_clm]
    rw [mul_smul_comm, smul_mul_assoc, hPH]
  have hP_pow : ∀ k : ℕ, P_clm * T_clm ^ k * P_clm = T_clm ^ k := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, mul_one] using hP_sq
    | succ k ih =>
      calc P_clm * T_clm ^ (k + 1) * P_clm
          = P_clm * (T_clm ^ k * T_clm) * P_clm := by rw [pow_succ]
        _ = (P_clm * T_clm ^ k) * (P_clm * P_clm) * (T_clm * P_clm) := by
              rw [hP_sq, mul_one]; simp only [mul_assoc]
        _ = (P_clm * T_clm ^ k * P_clm) * (P_clm * T_clm * P_clm) := by simp only [mul_assoc]
        _ = T_clm ^ k * T_clm := by rw [ih, hPT]
        _ = T_clm ^ (k + 1) := by rw [pow_succ]
  have hsumm : Summable (fun k : ℕ ↦ (k.factorial : ℂ)⁻¹ • T_clm ^ k) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
      (Real.summable_pow_div_factorial ‖T_clm‖)
    intro k
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le _ k) (by positivity)
  change P_clm * NormedSpace.exp T_clm * P_clm = NormedSpace.exp T_clm
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  let Φ : QubitOpCLM n →L[ℂ] QubitOpCLM n :=
    LinearMap.mkContinuous
      { toFun := fun X ↦ P_clm * X * P_clm
        map_add' := fun X Y ↦ by simp [mul_add, add_mul]
        map_smul' := fun c X ↦ by simp [mul_smul_comm, smul_mul_assoc] }
      (‖P_clm‖ * ‖P_clm‖)
      (fun X ↦ by
        calc ‖P_clm * X * P_clm‖
            ≤ ‖P_clm * X‖ * ‖P_clm‖ := norm_mul_le _ _
          _ ≤ (‖P_clm‖ * ‖X‖) * ‖P_clm‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ = ‖P_clm‖ * ‖P_clm‖ * ‖X‖ := by ring)
  have hΦ := Φ.map_tsum hsumm
  change Φ (∑' k : ℕ, (k.factorial : ℂ)⁻¹ • T_clm ^ k) = _
  rw [hΦ]
  congr 1; funext k
  change P_clm * ((k.factorial : ℂ)⁻¹ • T_clm ^ k) * P_clm = (k.factorial : ℂ)⁻¹ • T_clm ^ k
  rw [mul_smul_comm, smul_mul_assoc, hP_pow k]

/-- **Item #3 (Proposition 2.3(2) Eq. 2.10 Directly From Even-Parity Hamiltonian `H`)**:
For ANY Hermitian even-parity Hamiltonian `H : QubitOp n`, ANY `β : ℝ`, and ANY odd-parity
Majorana operator `A : QubitOp n`:
`majoranaThermalSize G A = (1/2) ∑_i (C_{β,V_i}^W(0) + F_MSS(A, V_i))`,
with `isEvenParity G.ρQuarter` derived automatically from `isEvenParity H`. -/
theorem prop_2_3_part2_majorana_from_even_H {n : ℕ} {H : QubitOp n}
    (hH : H.IsHermitian) (hH_even : isEvenParity H) (β : ℝ)
    {A : QubitOp n} (hA : isOddParity A) (hA_herm : Aᴴ = A)
    (hAnorm : gibbsWightmanNormSq (concreteGibbsData hH β) A = 1) :
    let G := concreteGibbsData hH β
    majoranaThermalSize G A =
      (1 / 2 : ℝ) * ∑ j : Fin (2 * n),
        (majoranaCW0 G j + majoranaFMSS G A j) :=
  prop_2_3_part2_majorana_eq_2_10 (concreteGibbsData hH β)
    (isEvenParity_concreteGibbsRhoQuarter hH hH_even β) hA hA_herm hAnorm

end Item3MajoranaEvenGibbs

section Item10FamilyLevelTheorem11b

/-- **Item #10 (Family-Level End-to-End Theorem 1.1(b) on `QubitOp N`)**:
For ANY sequence of Hermitian `r`-local Hamiltonians `H_N ∈ filtrationSubmodule N r` (`1 ≤ r`)
and normalized Hermitian `s₀`-local observables `O_N ∈ filtrationSubmodule N s₀` at inverse
temperature `β : ℝ`:
- Uniform linear Lanczos growth `lanczosCoeff (G N) (H_N N) (O_N N) n ≤ α * n + γ` (`α > 0`, `γ ≥ 0`),
- Concrete Hypothesis (H2) on `lambdaMSS`:
  `∀ N ≥ 1, ∀ s, lambdaMSS (G N) s ≤ C₁ * s + C₂ * N^δ * s^(1 - δ)` (`δ ∈ [0, 1)`),
- Concrete Hypothesis (H1) on `mssThermalSize`:
  for arbitrarily small `ε > 0`, along `t_N = ((1 - ε) / lamL) * log N`,
  `c * N^(1 - ε) ≤ mssThermalSize (G N) (heisenbergEvol (hH N) t_N (O_N N))` for all `N ≥ N₁`,
concludes unconditionally **`lamL ≤ 2 * α`**. Zero scalar wrappers! -/
theorem theorem_1_1b_family_concrete_qubit
    {r s₀ : ℕ} (hr : 1 ≤ r) {α γ lamL δ C₁ C₂ : ℝ} (β : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hlam : 0 < lamL)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (H_N O_N : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H_N N).IsHermitian) (hO : ∀ N, (O_N N).IsHermitian)
    (hHf : ∀ N, H_N N ∈ filtrationSubmodule N r)
    (hOf : ∀ N, O_N N ∈ filtrationSubmodule N s₀)
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O_N N) = 1)
    (hb_lin : ∀ N n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData (hH N) β) (H_N N) (O_N N) n ≤ α * (n : ℝ) + γ)
    (hH2 : ∀ (N s : ℕ), 1 ≤ N →
      lambdaMSS (concreteGibbsData (hH N) β) s ≤
        C₁ * (s : ℝ) + C₂ * (N : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)))
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamL) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          mssThermalSize (concreteGibbsData (hH N) β)
            (heisenbergEvol (hH N) (tN : ℂ) (O_N N))) :
    lamL ≤ 2 * α := by
  set C₀ : ℝ := Real.sqrt (Real.exp ((1 / 2 + γ / α) * 4))
  have hC₀ : 0 ≤ C₀ := Real.sqrt_nonneg _
  refine theorem_1_1b_static_reduction (C₀ := C₀) (C₁ := C₁) (C₂ := C₂) (r := r) (s₀ := s₀)
    hr hα hlam hδ0 hδ1 hC₀ hC₁ hC₂ ?_
  intro ε₀ hε₀
  obtain ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩ := hH1 (min ε₀ (1 / 2)) (lt_min hε₀ (by norm_num))
  have hε_lt₀ : ε < ε₀ := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  refine ⟨ε, ⟨hε_pos, hε_lt₀⟩, c, hc_pos, max N₁ 2, ?_⟩
  intro N hN
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_gt1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt1
  set tN : ℝ := ((1 - ε) / lamL) * Real.log (N : ℝ)
  have htN_nn : 0 ≤ tN := by
    dsimp only [tN]; apply mul_nonneg (div_nonneg (by linarith) hlam.le) hlogN_pos.le
  have htanh1_pos : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
    apply div_pos _ (Real.cosh_pos 1)
    have : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith
  set xM : ℝ := (1 / Real.tanh 1) * Real.exp (2 * α * tN) * Real.log (N : ℝ)
  have hxM_pos : 0 < xM := by dsimp only [xM]; positivity
  set M : ℕ := Nat.ceil xM
  have hM_ge_xM : xM ≤ (M : ℝ) := Nat.le_ceil xM
  have hM_ge1 : 1 ≤ M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le hxM_pos hM_ge_xM
    exact_mod_cast (Nat.pos_of_ne_zero (by intro h; simp [h] at this))
  have hM_le : (M : ℝ) ≤ xM + 1 := (Nat.ceil_lt_add_one hxM_pos.le).le
  set MN : ℝ := xM + 1
  set sN : ℝ := (s₀ : ℝ) + ((r : ℝ) - 1) * MN
  have hstep := theorem_1_1b_concrete_qubit_thermal_size hr hM_ge1 (hH N) (hO N) β
    (hHf N) (hOf N) (hOnorm N) hα hγ (by norm_num : (0 : ℝ) < 4) (hb_lin N) tN htN_nn
  set q_M : ℝ := Real.exp ((1 / 2 + γ / α) * 4) *
    Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tN))
  have h4div4 : (4 : ℝ) / 4 = 1 := by norm_num
  have hqM_le : q_M ≤ C₀ ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
    dsimp only [q_M, C₀]
    rw [Real.sq_sqrt (Real.exp_pos _).le, h4div4]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hexp_le : -4 * Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tN) ≤ -4 * Real.log (N : ℝ) := by
      have h1 : Real.log (N : ℝ) ≤ Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tN) := by
        have hmul : Real.tanh 1 * xM * Real.exp (-2 * α * tN) = Real.log (N : ℝ) := by
          dsimp only [xM]
          have he : Real.exp (2 * α * tN) * Real.exp (-2 * α * tN) = 1 := by
            rw [← Real.exp_add]; simp
          field_simp [htanh1_pos.ne']
          rw [show -(2 * α * tN) = -2 * α * tN by ring]
          exact he
        rw [← hmul]
        have hfac : 0 ≤ Real.tanh 1 * Real.exp (-2 * α * tN) := by positivity
        nlinarith [hM_ge_xM]
      linarith
    calc Real.exp (-4 * Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tN))
        ≤ Real.exp (-4 * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hexp_le
      _ = (N : ℝ) ^ (-4 : ℝ) := by
          rw [Real.rpow_def_of_pos hN_pos]; congr 1; ring
  have hsqrt_qM : Real.sqrt q_M ≤ C₀ * (N : ℝ) ^ (-2 : ℝ) := by
    have hrhs : C₀ ^ 2 * (N : ℝ) ^ (-4 : ℝ) = (C₀ * (N : ℝ) ^ (-2 : ℝ)) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (-2 : ℝ)) 2, ← Real.rpow_mul hN_pos.le]
      congr 1; congr 1; norm_num
    rw [hrhs] at hqM_le
    calc Real.sqrt q_M ≤ Real.sqrt ((C₀ * (N : ℝ) ^ (-2 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hqM_le
      _ = C₀ * (N : ℝ) ^ (-2 : ℝ) := Real.sqrt_sq (mul_nonneg hC₀ (Real.rpow_pos_of_pos hN_pos _).le)
  have htail1 : 2 * (N : ℝ) * Real.sqrt q_M ≤ 2 * C₀ * (N : ℝ)⁻¹ := by
    calc 2 * (N : ℝ) * Real.sqrt q_M
        ≤ 2 * (N : ℝ) * (C₀ * (N : ℝ) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt_qM (by positivity)
      _ = 2 * C₀ * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-2 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = 2 * C₀ * (N : ℝ) ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hN_pos]; congr 1; congr 1; norm_num
      _ = 2 * C₀ * (N : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
  have htail2 : (N : ℝ) * q_M ≤ C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ) := by
    calc (N : ℝ) * q_M
        ≤ (N : ℝ) * (C₀ ^ 2 * (N : ℝ) ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hqM_le hN_pos.le
      _ = C₀ ^ 2 * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-4 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ) := by
          rw [← Real.rpow_add hN_pos]; congr 1; congr 1; norm_num
  set s_nat : ℕ := s₀ + (M - 1) * (r - 1)
  have hs_le : (s_nat : ℝ) ≤ sN := by
    have hM1 : ((M - 1 : ℕ) : ℝ) ≤ MN := by
      have : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
      linarith [hM_le]
    have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr, Nat.cast_one]
    have hr1_nn : 0 ≤ (r : ℝ) - 1 := by rw [← hr1]; exact Nat.cast_nonneg _
    dsimp only [s_nat, sN]
    push_cast
    rw [hr1]
    nlinarith
  have hlam_bound : lambdaMSS (concreteGibbsData (hH N) β) s_nat ≤
      C₁ * sN + C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ) := by
    have h1 := hH2 N s_nat (by omega)
    have hpow : ((s_nat : ℝ) ^ (1 - δ)) ≤ sN ^ (1 - δ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hs_le (by linarith)
    have hterm1 : C₁ * (s_nat : ℝ) ≤ C₁ * sN := mul_le_mul_of_nonneg_left hs_le hC₁
    have hterm2 : C₂ * (N : ℝ) ^ δ * (s_nat : ℝ) ^ (1 - δ) ≤ C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₂ (Real.rpow_pos_of_pos hN_pos _).le)
    linarith
  have hlow := hN₁ N hN1
  linarith

end Item10FamilyLevelTheorem11b

section Item11ArbitrarySingleSiteDensityMatrices

private abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Unitary eigenbasis for an arbitrary Hermitian `2×2` density matrix `ρ_x`. -/
noncomputable def singleSiteEigenUnitary {ρ : Mat2} (hρ : ρ.IsHermitian) : Mat2 :=
  (hρ.eigenvectorUnitary : Mat2)

private lemma singleSiteEigenUnitary_mul_left {ρ : Mat2} (hρ : ρ.IsHermitian) :
    (singleSiteEigenUnitary hρ)ᴴ * singleSiteEigenUnitary hρ = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2)

private lemma singleSiteEigenUnitary_mul_right {ρ : Mat2} (hρ : ρ.IsHermitian) :
    singleSiteEigenUnitary hρ * (singleSiteEigenUnitary hρ)ᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp hρ.eigenvectorUnitary.2)

/-- Bloch magnitude `m_x = λ_0(ρ_x) - λ_1(ρ_x)` of an arbitrary single-qubit density matrix. -/
noncomputable def singleSiteBlochMag {ρ : Mat2} (hρ : ρ.IsHermitian) : ℝ :=
  hρ.eigenvalues 0 - hρ.eigenvalues 1

private lemma singleSite_spectral_eq_rotated {ρ : Mat2} (hρ : ρ.IsHermitian)
    (htr : ρ.trace = 1) :
    ρ = singleSiteEigenUnitary hρ * singleSiteRho (singleSiteBlochMag hρ) *
        (singleSiteEigenUnitary hρ)ᴴ := by
  have hspec := hρ.spectral_theorem
  have hsum_eig : hρ.eigenvalues 0 + hρ.eigenvalues 1 = 1 := by
    have htr_eig : (∑ i : Fin 2, (hρ.eigenvalues i : ℂ)) = ρ.trace := by
      have h1 : ρ = (hρ.eigenvectorUnitary : Mat2) *
          Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
          (hρ.eigenvectorUnitary : Mat2)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hspec
      have hUleft : (hρ.eigenvectorUnitary : Mat2)ᴴ * (hρ.eigenvectorUnitary : Mat2) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
      calc (∑ i : Fin 2, (hρ.eigenvalues i : ℂ))
          = (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))).trace :=
              (Matrix.trace_diagonal _).symm
        _ = (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
              ((hρ.eigenvectorUnitary : Mat2)ᴴ * (hρ.eigenvectorUnitary : Mat2))).trace := by
              rw [hUleft, Matrix.mul_one]
        _ = ((Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (hρ.eigenvectorUnitary : Mat2)ᴴ) *
              (hρ.eigenvectorUnitary : Mat2)).trace := by
              simp only [Matrix.mul_assoc]
        _ = ((hρ.eigenvectorUnitary : Mat2) *
              (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (hρ.eigenvectorUnitary : Mat2)ᴴ)).trace :=
              Matrix.trace_mul_comm _ _
        _ = ρ.trace := congrArg Matrix.trace (by rw [← Matrix.mul_assoc]; exact h1.symm)
    rw [htr, Fin.sum_univ_two] at htr_eig
    have hre := congrArg Complex.re htr_eig
    simpa using hre
  have hdiag : Matrix.diagonal (fun i : Fin 2 ↦ (hρ.eigenvalues i : ℂ)) =
      singleSiteRho (singleSiteBlochMag hρ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [singleSiteRho, singleSiteBlochMag, Matrix.diagonal]
    · have h0 : hρ.eigenvalues 0 = (1 + (hρ.eigenvalues 0 - hρ.eigenvalues 1)) / 2 := by linarith
      conv_lhs => rw [h0]
      push_cast; ring
    · have h1 : hρ.eigenvalues 1 = (1 - (hρ.eigenvalues 0 - hρ.eigenvalues 1)) / 2 := by linarith
      conv_lhs => rw [h1]
      push_cast; ring
  have h1 : ρ = singleSiteEigenUnitary hρ *
      Matrix.diagonal (fun i : Fin 2 ↦ (hρ.eigenvalues i : ℂ)) *
      (singleSiteEigenUnitary hρ)ᴴ := by
    simpa [singleSiteEigenUnitary, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hspec
  exact h1.trans (by rw [hdiag])

/-- **Item #11 (`GibbsData N` for ANY Arbitrary Full-Rank `N`-Qubit Product State `⨂_x ρ_x`)**:
Constructed directly from arbitrary (possibly non-diagonal) Hermitian single-site density
matrices `ρ : Fin N → Matrix (Fin 2) (Fin 2) ℂ` by diagonalizing each site via its
eigenbasis unitary `singleSiteEigenUnitary (hρ_herm x)`. -/
noncomputable def arbitraryProdGibbsData {N : ℕ}
    (ρ : Fin N → Mat2) (hρ_herm : ∀ x, (ρ x).IsHermitian)
    (hρ_bloch : ∀ x, |singleSiteBlochMag (hρ_herm x)| < 1) : GibbsData N :=
  rotatedProdGibbsData
    (fun x ↦ singleSiteEigenUnitary (hρ_herm x))
    (fun x ↦ singleSiteEigenUnitary_mul_left (hρ_herm x))
    (fun x ↦ singleSiteEigenUnitary_mul_right (hρ_herm x))
    (fun x ↦ singleSiteBlochMag (hρ_herm x))
    hρ_bloch

/-- Exact density-matrix identification: `(arbitraryProdGibbsData ρ ...).ρβ = kronOp ρ`. -/
theorem arbitraryProdGibbsData_rho_eq_kronOp {N : ℕ}
    (ρ : Fin N → Mat2) (hρ_herm : ∀ x, (ρ x).IsHermitian)
    (hρ_tr : ∀ x, (ρ x).trace = 1)
    (hρ_bloch : ∀ x, |singleSiteBlochMag (hρ_herm x)| < 1) :
    (arbitraryProdGibbsData ρ hρ_herm hρ_bloch).ρβ = kronOp ρ := by
  change kronOp (fun x ↦ singleSiteEigenUnitary (hρ_herm x)) *
      kronOp (fun x ↦ singleSiteRho (singleSiteBlochMag (hρ_herm x))) *
      (kronOp (fun x ↦ singleSiteEigenUnitary (hρ_herm x)))ᴴ = kronOp ρ
  rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul]
  congr 1; funext x
  exact (singleSite_spectral_eq_rotated (hρ_herm x) (hρ_tr x)).symm

/-- **Item #11 (Proposition 4.3 for Arbitrary Non-Diagonal Full-Rank Single-Site Density Matrices)**:
For ANY `N` full-rank Hermitian single-site density matrices `ρ_x : Matrix (Fin 2) (Fin 2) ℂ`
with `Tr(ρ_x) = 1` and Bloch-vector magnitudes `|λ_0(ρ_x) - λ_1(ρ_x)| ≤ mmax < 1`:
`lambdaMSS (arbitraryProdGibbsData ρ ...) s ≤ s + mmax * √(N * s)`. -/
theorem prop_4_3_lambdaMSS_arbitrary_product_state {N s : ℕ} {mmax : ℝ}
    (ρ : Fin N → Mat2) (hρ_herm : ∀ x, (ρ x).IsHermitian)
    (hρ_bloch : ∀ x, |singleSiteBlochMag (hρ_herm x)| ≤ mmax) (hmmax : mmax < 1) :
    lambdaMSS (arbitraryProdGibbsData ρ hρ_herm (fun x ↦ lt_of_le_of_lt (hρ_bloch x) hmmax)) s ≤
      (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) :=
  prop_4_3_lambdaMSS_general_product_state
    (fun x ↦ singleSiteEigenUnitary (hρ_herm x))
    (fun x ↦ singleSiteEigenUnitary_mul_left (hρ_herm x))
    (fun x ↦ singleSiteEigenUnitary_mul_right (hρ_herm x))
    (fun x ↦ singleSiteBlochMag (hρ_herm x))
    hρ_bloch hmmax

end Item11ArbitrarySingleSiteDensityMatrices

section Item29MultiTypeLemmaA3

/-- **Item #29 (Multi-Type Heterogeneous-Locality Unordered Tree Sum)**:
Depth-`h` Galton–Watson / Kotecký–Preiss tree sum on an arbitrary finite multi-type
hypergraph `F : Finset ι` (e.g., `ℱ = ⨆_{j=1}^p ℰ_j`) with support map `supp : ι → Finset (Fin N)`
and nonnegative edge weights `μ : ι → ℝ`. -/
noncomputable def multiTypeTreeSum {N : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (supp : ι → Finset (Fin N)) (μ : ι → ℝ) : ℕ → ι → ℝ
  | 0, e => μ e
  | h + 1, e =>
    μ e * ∏ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
      (1 + multiTypeTreeSum F supp μ h e')

lemma multiTypeTreeSum_nonneg {N : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (supp : ι → Finset (Fin N)) (μ : ι → ℝ)
    (hμ_nn : ∀ e ∈ F, 0 ≤ μ e) :
    ∀ h : ℕ, ∀ e ∈ F, 0 ≤ multiTypeTreeSum F supp μ h e := by
  intro h
  induction h with
  | zero => intro e he; exact hμ_nn e he
  | succ h ih =>
    intro e he
    rw [multiTypeTreeSum]
    exact mul_nonneg (hμ_nn e he)
      (Finset.prod_nonneg fun e' he' ↦ by linarith [ih e' (Finset.mem_filter.mp he').1])

private lemma multiType_sum_overlapping_le {N : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (supp : ι → Finset (Fin N)) (w : ι → ℝ)
    (hw_nn : ∀ e ∈ F, 0 ≤ w e) {B : ℝ}
    (hsite : ∀ y : Fin N, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), w e ≤ B)
    (U : Finset (Fin N)) :
    ∑ e ∈ F.filter (fun e ↦ (U ∩ supp e).Nonempty), w e ≤ (U.card : ℝ) * B := by
  have hle : ∑ e ∈ F.filter (fun e ↦ (U ∩ supp e).Nonempty), w e ≤
      ∑ y ∈ U, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), w e := by
    have hswap : (∑ y ∈ U, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), w e) =
        ∑ e ∈ F, ((U.filter (fun y ↦ y ∈ supp e)).card : ℝ) * w e := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro e _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap]
    have hsub : F.filter (fun e ↦ (U ∩ supp e).Nonempty) ⊆ F := Finset.filter_subset _ _
    calc ∑ e ∈ F.filter (fun e ↦ (U ∩ supp e).Nonempty), w e
        ≤ ∑ e ∈ F.filter (fun e ↦ (U ∩ supp e).Nonempty),
            ((U.filter (fun y ↦ y ∈ supp e)).card : ℝ) * w e := by
          apply Finset.sum_le_sum; intro e he
          have hne : (U ∩ supp e).Nonempty := (Finset.mem_filter.mp he).2
          have hcard1 : 1 ≤ (U.filter (fun y ↦ y ∈ supp e)).card := by
            rcases hne with ⟨y, hy⟩
            rcases Finset.mem_inter.mp hy with ⟨hyU, hye⟩
            exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyU, hye⟩⟩
          have hcard1' : (1 : ℝ) ≤ ((U.filter (fun y ↦ y ∈ supp e)).card : ℝ) := by
            exact_mod_cast hcard1
          nlinarith [hw_nn e (Finset.mem_filter.mp he).1]
      _ ≤ ∑ e ∈ F, ((U.filter (fun y ↦ y ∈ supp e)).card : ℝ) * w e :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun e he _ ↦
            mul_nonneg (Nat.cast_nonneg _) (hw_nn e he)
  calc ∑ e ∈ F.filter (fun e ↦ (U ∩ supp e).Nonempty), w e
      ≤ ∑ y ∈ U, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), w e := hle
    _ ≤ ∑ _y ∈ U, B := Finset.sum_le_sum fun y _ ↦ hsite y
    _ = (U.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Item #29 (Multi-Type Heterogeneous-Locality Lemma A.3, Eqs. A.3–A.4)**:
For ANY finite multi-type hypergraph `F : Finset ι` with heterogeneous support sets
`supp : ι → Finset (Fin N)`, nonnegative edge weights `μ : ι → ℝ`, and `c₀ ≥ 0`
satisfying the heterogeneous pinning condition
`∀ y : Fin N, ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), μ e * exp (c₀ * |supp e|) ≤ c₀`:
for EVERY depth `h : ℕ` and EVERY hyperedge `e ∈ F`:
`multiTypeTreeSum F supp μ h e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ))`. -/
theorem lemma_A_3_multiType_unordered_tree_sum {N : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (supp : ι → Finset (Fin N)) (μ : ι → ℝ)
    (hμ_nn : ∀ e ∈ F, 0 ≤ μ e) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hpin : ∀ y : Fin N,
      ∑ e ∈ F.filter (fun e ↦ y ∈ supp e), μ e * Real.exp (c₀ * ((supp e).card : ℝ)) ≤ c₀) :
    ∀ h : ℕ, ∀ e ∈ F,
      multiTypeTreeSum F supp μ h e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ)) := by
  intro h
  induction h with
  | zero =>
    intro e he
    rw [multiTypeTreeSum]
    have h1 : (1 : ℝ) ≤ Real.exp (c₀ * ((supp e).card : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith [hμ_nn e he]
  | succ h ih =>
    intro e he
    rw [multiTypeTreeSum]
    apply mul_le_mul_of_nonneg_left _ (hμ_nn e he)
    have hprod_exp :
        ∏ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
          (1 + multiTypeTreeSum F supp μ h e') ≤
        ∏ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
          Real.exp (multiTypeTreeSum F supp μ h e') := by
      have haux : ∀ S : Finset ι, (∀ e' ∈ S, e' ∈ F) →
          ∏ e' ∈ S, (1 + multiTypeTreeSum F supp μ h e') ≤
          ∏ e' ∈ S, Real.exp (multiTypeTreeSum F supp μ h e') := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; simp
        | insert a s ha ihs =>
          intro hS
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          have ha_nn : 0 ≤ 1 + multiTypeTreeSum F supp μ h a := by
            linarith [multiTypeTreeSum_nonneg F supp μ hμ_nn h a (hS a (Finset.mem_insert_self a s))]
          have ha_le : 1 + multiTypeTreeSum F supp μ h a ≤ Real.exp (multiTypeTreeSum F supp μ h a) := by
            linarith [Real.add_one_le_exp (multiTypeTreeSum F supp μ h a)]
          have hs_nn : 0 ≤ ∏ e' ∈ s, (1 + multiTypeTreeSum F supp μ h e') :=
            Finset.prod_nonneg fun e' he' ↦ by
              linarith [multiTypeTreeSum_nonneg F supp μ hμ_nn h e' (hS e' (Finset.mem_insert_of_mem he'))]
          exact mul_le_mul ha_le (ihs (fun e' he' ↦ hS e' (Finset.mem_insert_of_mem he')))
            hs_nn (Real.exp_pos _).le
      exact haux _ (fun e' he' ↦ (Finset.mem_filter.mp he').1)
    rw [← Real.exp_sum] at hprod_exp
    refine le_trans hprod_exp (Real.exp_le_exp.mpr ?_)
    have hsum_le :
        ∑ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
          multiTypeTreeSum F supp μ h e' ≤
        ∑ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
          μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) :=
      Finset.sum_le_sum fun e' he' ↦ ih e' (Finset.mem_filter.mp he').1
    have hpin_ov := multiType_sum_overlapping_le F supp
      (fun e' ↦ μ e' * Real.exp (c₀ * ((supp e').card : ℝ)))
      (fun e' he' ↦ mul_nonneg (hμ_nn e' he') (Real.exp_pos _).le)
      hpin (supp e)
    calc ∑ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty), multiTypeTreeSum F supp μ h e'
        ≤ ∑ e' ∈ F.filter (fun e' ↦ (supp e ∩ supp e').Nonempty),
            μ e' * Real.exp (c₀ * ((supp e').card : ℝ)) := hsum_le
      _ ≤ ((supp e).card : ℝ) * c₀ := hpin_ov
      _ = c₀ * ((supp e).card : ℝ) := by ring

end Item29MultiTypeLemmaA3

end KrylovChaos
