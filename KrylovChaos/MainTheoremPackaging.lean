/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempSharpBounds
import KrylovChaos.ConcreteOTOCStrip
import KrylovChaos.ConcreteSpectralStrip
import KrylovChaos.TimeOrderedOTOC

/-!
# Packaging Theorems for Eqs. (1.16), (1.17), (1.18), (1.20), (8.1), and (8.4)

Provides clean end-to-end packaging wrappers:
1. **Theorem 1.3(a), Eq. (1.20)** (`theorem_1_3a_high_temp_eq_1_20`): exact two-sided
   high-temperature operator inequality
   `Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`.
2. **Theorem 1.2(c), Eqs. (1.17)–(1.18)** (`theorem_1_2c_general_otoc_strip_three_way`,
   `theorem_1_2c_thermo_limit_otoc_strip_three_way`, `theorem_1_2c_general_otoc_strip_max_width`):
   thermodynamic-limit strip analyticity bundling all three Eq. (1.17) `liminf` upper bounds and
   discharging compact boundedness on `{|Im z| < (1/2) max(r_W, r_V)}` from either `W` or `V`.
3. **Theorem 1.2(b), Eq. (1.16)** (`iteratedDeriv_holo_eq_spectral_moment`,
   `holoStrip_even_moment_bound_unconditional`, `theorem_1_2b_from_holoStripHalfWidth_unconditional`,
   `theorem_1_2b_from_holoStripHalfWidth_ereal`, `theorem_1_2b_from_holoStripHalfWidth_finite`):
   derives all even derivatives at `0` directly from `∃ r₀ > 0, Integrable (cosh (r₀ * ω)) μ` via
   differentiation under the integral sign, removing all derivative-identity hypotheses.
4. **Proposition 8.1** (`prop_8_1_araki_1d_independent_r_R`): independent locality `r` and diameter `R`.
5. **Proposition 8.3, Eq. (8.4)** (`isingPhiMaxExact_le_linear_active`,
   `prop_8_3_ising_explicit_eq_8_4_cosh`, `prop_8_3_ising_explicit_eq_8_4_exp`): active-edge
   vertex-degree hypothesis (`J_{ij} ≠ 0`) and sharp `cosh²(β H_max + (Δ/2) ln 2)` bound.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology Complex

section ExactEq120

/-- **Theorem 1.3(a) (Exact Two-Sided High-Temperature Operator Inequality, Eq. 1.20)**:
Establishes the full two-sided operator inequality
`Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`
for all `0 ≤ β ≤ highTempBetaWC r Jsite` and every `A : QubitOp N`. -/
theorem theorem_1_3a_high_temp_eq_1_20 {N r : ℕ} (hr : 2 ≤ r)
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
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ∧
    ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ≤
      9 * (gibbsWightmanInner G A (wightmanQ G A)).re := by
  rcases highTempBetaWC_discharges_params hr E hcard h hJ hsite hβ0 hβ with
    ⟨hc, hsite_kp, hkp, _, _, _⟩
  exact theorem_1_3a_unconditional E hne hcard h hsupp hH hβ0 hc hsite_kp hkp A

end ExactEq120

section ThreeWayOTOCStrip

private lemma liminf_const_mul_le_of_bdd' {a : ℕ → ℝ} {c B : ℝ}
    (hc : 0 ≤ c) (ha0 : ∀ N, 0 ≤ a N) (haB : ∀ N, a N ≤ B) :
    Filter.liminf (fun N ↦ c * a N) atTop ≤ c * Filter.liminf a atTop := by
  by_cases hc0 : c = 0
  · subst hc0; simp
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hle_a : Filter.IsBoundedUnder (· ≤ ·) atTop a :=
    ⟨B, Filter.eventually_map.mpr (Eventually.of_forall haB)⟩
  have hge_ca : Filter.IsBoundedUnder (· ≥ ·) atTop (fun N ↦ c * a N) :=
    ⟨0, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦ mul_nonneg hc (ha0 N))⟩
  refine Filter.liminf_le_of_le hge_ca fun b hb ↦ ?_
  have hb' : ∀ᶠ N in atTop, b / c ≤ a N := by
    filter_upwards [hb] with N hN
    exact (div_le_iff₀ hc_pos).mpr (by linarith)
  have hle_lim : b / c ≤ Filter.liminf a atTop :=
    Filter.le_liminf_of_le hle_a.isCoboundedUnder_ge hb'
  exact (div_le_iff₀ hc_pos).mp hle_lim |>.trans_eq (mul_comm _ _)

/-- Concrete upper bound `T_{τ,N}(t) ≤ ‖V‖_∞² * C_{β,W,N}^W(2 i τ)` for Hermitian `W, V`. -/
lemma concreteTimeOrderedT_le_opNorm_sq_mul_shift {N : ℕ} {H W V : QubitOp N}
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hV : V.IsHermitian) (β t τ : ℝ) :
    concreteTimeOrderedT hH β W V t τ ≤
      (opNorm V) ^ 2 * concreteWightmanNormAtShift hH β W τ 0 := by
  set z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
  set G := concreteGibbsData hH β
  set B : QubitOp N := jBeta G.ρQuarter (heisenbergEvol hH z W)
  have hz_conj : starRingEnd ℂ z = (t : ℂ) - Complex.I * (τ : ℂ) := by
    dsimp only [z]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hB_adj : Bᴴ = jBeta G.ρQuarter (heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W) := by
    unfold B jBeta
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, G.ρQuarter_herm,
      heisenbergEvol_conjTranspose_of_herm hH hW z, hz_conj, Matrix.mul_assoc]
  have hBB : Bᴴ * B =
      gibbsRhoQuarter hH β *
        heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
        gibbsRhoHalf hH β *
        heisenbergEvol hH ((t : ℂ) + Complex.I * (τ : ℂ)) W *
        gibbsRhoQuarter hH β := by
    rw [hB_adj]
    unfold B jBeta
    have hq : gibbsRhoQuarter hH β * gibbsRhoQuarter hH β = gibbsRhoHalf hH β := G.sq_quarter
    change (gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W * gibbsRhoQuarter hH β) *
      (gibbsRhoQuarter hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β) = _
    calc (gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W * gibbsRhoQuarter hH β) *
          (gibbsRhoQuarter hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β)
        = gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
          (gibbsRhoQuarter hH β * gibbsRhoQuarter hH β) *
          heisenbergEvol hH z W * gibbsRhoQuarter hH β := by simp only [Matrix.mul_assoc]
      _ = gibbsRhoQuarter hH β * heisenbergEvol hH ((t : ℂ) - Complex.I * (τ : ℂ)) W *
          gibbsRhoHalf hH β * heisenbergEvol hH z W * gibbsRhoQuarter hH β := by rw [hq]
  have hT_eq : concreteTimeOrderedT hH β W V t τ = hsNormSq (B * V) := by
    unfold concreteTimeOrderedT hsNormSq hsInner
    rw [← hBB]
    apply congrArg Complex.re
    rw [Matrix.conjTranspose_mul, hV.eq]
    calc (Bᴴ * B * (V * V)).trace
        = ((Bᴴ * B * V) * V).trace := by simp only [Matrix.mul_assoc]
      _ = (V * (Bᴴ * B * V)).trace := Matrix.trace_mul_comm _ _
      _ = (V * Bᴴ * (B * V)).trace := by simp only [Matrix.mul_assoc]
  rw [hT_eq]
  have hle := hsNormSq_mul_right_le_opNorm_sq B V
  have hB_norm : hsNormSq B = concreteWightmanNormAtShift hH β W τ 0 := by
    rw [← concreteWightmanNormAtShift_time_invariant hH β W τ t]
    unfold concreteWightmanNormAtShift gibbsWightmanNormSq gibbsWightmanInner hsNormSq
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
    rfl
  rw [hB_norm] at hle
  exact hle

/-- **Theorem 1.2(c) (General Strip `S_OTOC` Analytic Continuation — Full Three-Way Eq. 1.17)**:
Bundles all three thermodynamic-limit `liminf` upper bounds from Eq. (1.17):
`‖F (t + i τ)‖ ≤ min (C_V ^ 2 * liminf C_W(2iτ), C_W ^ 2 * liminf C_V(-2iτ), liminf T_{τ,N}(t))`. -/
theorem theorem_1_2c_general_otoc_strip_three_way {β S_OTOC C_W C_V : ℝ}
    (hS : 0 < S_OTOC) (hCW : 0 ≤ C_W) (hCV : 0 ≤ C_V)
    (H W V : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H N).IsHermitian) (hW : ∀ N, (W N).IsHermitian) (hV : ∀ N, (V N).IsHermitian)
    (hW_norm : ∀ N, opNorm (W N) ≤ C_W) (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (hcomp_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S_OTOC} →
      ∃ M : ℝ, ∀ N, ∀ z ∈ K, ‖concreteOTOC (hH N) β (W N) (V N) z‖ ≤ M)
    (hshiftW_bdd : ∀ τ : ℝ, |τ| < S_OTOC →
      ∃ B : ℝ, ∀ N, concreteWightmanNormAtShift (hH N) β (W N) τ 0 ≤ B)
    (hshiftV_bdd : ∀ τ : ℝ, |τ| < S_OTOC →
      ∃ B : ℝ, ∀ N, concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0 ≤ B)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      atTop (nhds (F_real t))) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S_OTOC} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F atTop
        {z : ℂ | |z.im| < S_OTOC} ∧
      (∀ (t τ : ℝ), |τ| < S_OTOC →
        ‖F ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
          min (C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop)
            (min (C_W ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) atTop)
              (Filter.liminf (fun N ↦ concreteTimeOrderedT (hH N) β (W N) (V N) t τ) atTop))) := by
  rcases vitali_montel_strip_extension hS
      (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F_real
      (fun N ↦ (differentiable_concreteOTOC (hH N) β (W N) (V N)).differentiableOn)
      hcomp_bdd hreal_lim with ⟨F, hF_holo, hF_unif, hF_real⟩
  refine ⟨F, hF_holo, hF_real, hF_unif, fun t τ hτ ↦ ?_⟩
  set z : ℂ := (t : ℂ) + Complex.I * (τ : ℂ)
  have hz_mem : z ∈ {w : ℂ | |w.im| < S_OTOC} := by
    simp only [Set.mem_setOf_eq, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add]
    exact hτ
  have htend_z : Tendsto (fun N ↦ ‖concreteOTOC (hH N) β (W N) (V N) z‖) atTop (nhds ‖F z‖) :=
    (hF_unif.tendsto_at hz_mem).norm
  rcases hshiftW_bdd τ hτ with ⟨BW, hBW⟩
  rcases hshiftV_bdd τ hτ with ⟨BV, hBV⟩
  have h1 : ‖F z‖ ≤ C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop := by
    have hle_liminf : ‖F z‖ ≤ Filter.liminf
        (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop := by
      rw [← htend_z.liminf_eq]
      have hbdd : Filter.IsBoundedUnder (· ≤ ·) atTop
          (fun N ↦ C_V ^ 2 * concreteWightmanNormAtShift (hH N) β (W N) τ 0) :=
        ⟨C_V ^ 2 * BW, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦
          mul_le_mul_of_nonneg_left (hBW N) (sq_nonneg C_V))⟩
      refine Filter.liminf_le_liminf (Eventually.of_forall fun N ↦ ?_)
        htend_z.isBoundedUnder_ge hbdd.isCoboundedUnder_ge
      have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β t τ).1
      have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
      exact le_trans h3 (mul_le_mul_of_nonneg_right hVsq (gibbsWightmanNormSq_nonneg _ _))
    exact le_trans hle_liminf (liminf_const_mul_le_of_bdd' (sq_nonneg C_V)
      (fun N ↦ gibbsWightmanNormSq_nonneg _ _) hBW)
  have h2 : ‖F z‖ ≤ C_W ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) atTop := by
    have hle_liminf : ‖F z‖ ≤ Filter.liminf
        (fun N ↦ C_W ^ 2 * concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) atTop := by
      rw [← htend_z.liminf_eq]
      have hbdd : Filter.IsBoundedUnder (· ≤ ·) atTop
          (fun N ↦ C_W ^ 2 * concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) :=
        ⟨C_W ^ 2 * BV, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦
          mul_le_mul_of_nonneg_left (hBV N) (sq_nonneg C_W))⟩
      refine Filter.liminf_le_liminf (Eventually.of_forall fun N ↦ ?_)
        htend_z.isBoundedUnder_ge hbdd.isCoboundedUnder_ge
      have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β t τ).2.1
      have hWsq : (opNorm (W N)) ^ 2 ≤ C_W ^ 2 := by nlinarith [opNorm_nonneg (W N), hW_norm N]
      exact le_trans h3 (mul_le_mul_of_nonneg_right hWsq (gibbsWightmanNormSq_nonneg _ _))
    exact le_trans hle_liminf (liminf_const_mul_le_of_bdd' (sq_nonneg C_W)
      (fun N ↦ gibbsWightmanNormSq_nonneg _ _) hBV)
  have h3 : ‖F z‖ ≤ Filter.liminf (fun N ↦ concreteTimeOrderedT (hH N) β (W N) (V N) t τ) atTop := by
    rw [← htend_z.liminf_eq]
    have hbdd : Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun N ↦ concreteTimeOrderedT (hH N) β (W N) (V N) t τ) :=
      ⟨C_V ^ 2 * BW, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦ by
        have hTle := concreteTimeOrderedT_le_opNorm_sq_mul_shift (hH N) (hW N) (hV N) β t τ
        have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
        exact le_trans hTle (mul_le_mul hVsq (hBW N) (gibbsWightmanNormSq_nonneg _ _) (sq_nonneg C_V)))⟩
    refine Filter.liminf_le_liminf (Eventually.of_forall fun N ↦ ?_)
      htend_z.isBoundedUnder_ge hbdd.isCoboundedUnder_ge
    exact concreteOTOC_norm_le_timeOrderedT (hH N) (hW N) (hV N) β t τ
  exact le_min h1 (le_min h2 h3)

/-- **Theorem 1.2(c) (General Strip `S_OTOC = (1/2) max(r_W, r_V)`, Eq. 1.18)**:
Discharges compact boundedness `hcomp_bdd` automatically on `{|Im z| < (1/2) max(r_W, r_V)}`
from uniform boundedness of `C_{β,W,N}^W(2iτ)` on `|τ| ≤ R < r_W / 2` and `C_{β,V,N}^W(-2iτ)`
on `|τ| ≤ R < r_V / 2`, without requiring both operators to share the same strip width. -/
theorem theorem_1_2c_general_otoc_strip_max_width {β rW rV C_W C_V : ℝ}
    (hrW : 0 < rW) (hrV : 0 < rV) (hCW : 0 ≤ C_W) (hCV : 0 ≤ C_V)
    (H W V : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H N).IsHermitian) (hW : ∀ N, (W N).IsHermitian) (hV : ∀ N, (V N).IsHermitian)
    (hW_norm : ∀ N, opNorm (W N) ≤ C_W) (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (hshiftW_unif : ∀ R : ℝ, 0 ≤ R → R < rW / 2 →
      ∃ B : ℝ, ∀ N, ∀ τ : ℝ, |τ| ≤ R → concreteWightmanNormAtShift (hH N) β (W N) τ 0 ≤ B)
    (hshiftV_unif : ∀ R : ℝ, 0 ≤ R → R < rV / 2 →
      ∃ B : ℝ, ∀ N, ∀ τ : ℝ, |τ| ≤ R → concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0 ≤ B)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      atTop (nhds (F_real t))) :
    let S_OTOC : ℝ := (1 / 2 : ℝ) * max rW rV
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S_OTOC} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F atTop
        {z : ℂ | |z.im| < S_OTOC} := by
  intro S_OTOC
  have hS : 0 < S_OTOC := by
    dsimp only [S_OTOC]
    have : 0 < max rW rV := lt_max_of_lt_left hrW
    positivity
  have hcomp_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S_OTOC} →
      ∃ M : ℝ, ∀ N, ∀ z ∈ K, ‖concreteOTOC (hH N) β (W N) (V N) z‖ ≤ M := by
    intro K hK hKsub
    by_cases hKne : K.Nonempty
    · obtain ⟨z₀, hz₀K, hz₀_max⟩ :=
        hK.exists_isMaxOn hKne (continuous_abs.comp Complex.continuous_im).continuousOn
      set R : ℝ := |z₀.im|
      have hR_nn : 0 ≤ R := abs_nonneg _
      have hR_lt : R < S_OTOC := hKsub hz₀K
      have hcases : R < rW / 2 ∨ R < rV / 2 := by
        dsimp only [S_OTOC] at hR_lt
        rcases le_total rW rV with hle | hle
        · right; rw [max_eq_right hle] at hR_lt; linarith
        · left; rw [max_eq_left hle] at hR_lt; linarith
      rcases hcases with hRW | hRV
      · rcases hshiftW_unif R hR_nn hRW with ⟨B, hB⟩
        refine ⟨C_V ^ 2 * B, fun N z hzK ↦ ?_⟩
        have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp
        have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β z.re z.im).1
        rw [← hz_eq] at h3
        have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
        exact le_trans h3 (mul_le_mul hVsq (hB N z.im (hz₀_max hzK))
          (gibbsWightmanNormSq_nonneg _ _) (sq_nonneg C_V))
      · rcases hshiftV_unif R hR_nn hRV with ⟨B, hB⟩
        refine ⟨C_W ^ 2 * B, fun N z hzK ↦ ?_⟩
        have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp
        have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hW N) (hV N) β z.re z.im).2.1
        rw [← hz_eq] at h3
        have hWsq : (opNorm (W N)) ^ 2 ≤ C_W ^ 2 := by nlinarith [opNorm_nonneg (W N), hW_norm N]
        exact le_trans h3 (mul_le_mul hWsq (hB N z.im (hz₀_max hzK))
          (gibbsWightmanNormSq_nonneg _ _) (sq_nonneg C_W))
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨0, fun _ z hz ↦ absurd (hKne ▸ hz) (Set.notMem_empty z)⟩
  rcases vitali_montel_strip_extension hS
      (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F_real
      (fun N ↦ (differentiable_concreteOTOC (hH N) β (W N) (V N)).differentiableOn)
      hcomp_bdd hreal_lim with ⟨F, hF_holo, hF_unif, hF_real⟩
  exact ⟨F, hF_holo, hF_real, hF_unif⟩

/-- **Theorem 1.2(c) (End-to-End Thermodynamic-Limit OTOC Analyticity — Full Three-Way Eq. 1.17)**:
For any uniform `r`-local family `(H_N, W_N, V_N)` with both `W_N` (`|U_W N| ≤ sW`) and
`V_N` (`|U_V N| ≤ sV`) locally supported and uniformly norm-bounded, the unique holomorphic
continuation `F` on `{|Im z| < β / 4 + κ / 2}` satisfies all three thermodynamic-limit
`liminf` upper bounds from Eq. (1.17). -/
theorem theorem_1_2c_thermo_limit_otoc_strip_three_way {r sW sV : ℕ} (hr : 2 ≤ r)
    {Jsite β C_W C_V : ℝ} (hJ : 0 < Jsite) (hβ : 0 ≤ β) (hCW : 0 ≤ C_W) (hCV : 0 ≤ C_V)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hcard : ∀ N, ∀ X ∈ E N, X.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hsupp : ∀ N X, h N X ∈ supportedOn X)
    (hH : ∀ N, (∑ X ∈ E N, h N X).IsHermitian)
    (hsite : ∀ N, ∀ x : Fin N, ∑ X ∈ (E N).filter (fun X ↦ x ∈ X), opNorm (h N X) ≤ Jsite)
    (U_W U_V : (N : ℕ) → Finset (Fin N))
    (hUW : ∀ N, (U_W N).card ≤ sW) (hUV : ∀ N, (U_V N).card ≤ sV)
    (W V : (N : ℕ) → QubitOp N)
    (hWherm : ∀ N, (W N).IsHermitian) (hVherm : ∀ N, (V N).IsHermitian)
    (hW : ∀ N, W N ∈ supportedOn (U_W N)) (hV : ∀ N, V N ∈ supportedOn (U_V N))
    (hW_norm : ∀ N, opNorm (W N) ≤ C_W) (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      atTop (nhds (F_real t))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    let S : ℝ := β / 4 + κ / 2
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F atTop
        {z : ℂ | |z.im| < S} ∧
      (∀ (t τ : ℝ), |τ| < S →
        ‖F ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
          min (C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) atTop)
            (min (C_W ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) atTop)
              (Filter.liminf (fun N ↦ concreteTimeOrderedT (hH N) β (W N) (V N) t τ) atTop))) := by
  intro κ S
  have hκ_pos : 0 < κ := by
    dsimp only [κ]
    have hr1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
    positivity
  have hS_pos : 0 < S := by dsimp only [S]; linarith
  have hshift_any : ∀ (sA : ℕ) (C_A : ℝ) (U_A : (N : ℕ) → Finset (Fin N))
      (A : (N : ℕ) → QubitOp N),
      0 ≤ C_A → (∀ N, (U_A N).card ≤ sA) → (∀ N, (A N).IsHermitian) →
      (∀ N, A N ∈ supportedOn (U_A N)) → (∀ N, opNorm (A N) ≤ C_A) →
      ∀ R : ℝ, 0 ≤ R → R < S →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ N, ∀ τ : ℝ, |τ| ≤ R →
          concreteWightmanNormAtShift (hH N) β (A N) τ 0 ≤ B := by
    intro sA C_A U_A A hCA hUA hAherm hA hA_norm R hR_nn hR_lt
    set κ' : ℝ := max 0 (2 * R - β / 2)
    have hκ'_nn : 0 ≤ κ' := le_max_left _ _
    have hκ'_lt : κ' < κ := by
      dsimp only [κ', S] at hR_lt ⊢
      exact max_lt hκ_pos (by linarith)
    set B : ℝ := 4 * C_A ^ 2 * (1 - κ' / κ) ^ (-((sA : ℝ) / ((r - 1 : ℕ) : ℝ)))
    have h1sub : 0 < 1 - κ' / κ := by rw [sub_pos, div_lt_one hκ_pos]; exact hκ'_lt
    have hB_nn : 0 ≤ B := mul_nonneg (by positivity) (Real.rpow_nonneg h1sub.le _)
    refine ⟨B, hB_nn, fun N τ hτ ↦ ?_⟩
    have h2τ_le : 2 * |τ| ≤ β / 2 + κ' := by
      have : 2 * R - β / 2 ≤ κ' := le_max_right _ _
      linarith
    have h1 := concreteWightmanNormAtShift_le_two_cosh (hH N) (hAherm N) β τ
    have hmono : ∫ ω : ℝ, Real.cosh (2 * τ * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (A N)) ≤
        ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(concreteWightmanSpectralMeasure (hH N) β (A N)) := by
      refine integral_mono (integrable_concreteWightmanSpectralMeasure (hH N) β (A N) _)
        (integrable_concreteWightmanSpectralMeasure (hH N) β (A N) _) fun ω ↦ ?_
      have hxy : |2 * τ * ω| ≤ |(β / 2 + κ') * ω| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (by linarith : 0 ≤ β / 2 + κ')]
        exact mul_le_mul_of_nonneg_right h2τ_le (abs_nonneg ω)
      have hax : Real.cosh (2 * τ * ω) = Real.cosh |2 * τ * ω| := by
        rcases le_total 0 (2 * τ * ω) with hx | hx
        · rw [abs_of_nonneg hx]
        · rw [abs_of_nonpos hx, Real.cosh_neg]
      have hay : Real.cosh ((β / 2 + κ') * ω) = Real.cosh |(β / 2 + κ') * ω| := by
        rcases le_total 0 ((β / 2 + κ') * ω) with hy | hy
        · rw [abs_of_nonneg hy]
        · rw [abs_of_nonpos hy, Real.cosh_neg]
      rw [hax, hay, Real.cosh_eq, Real.cosh_eq]
      set a := Real.exp |2 * τ * ω|
      set b := Real.exp |(β / 2 + κ') * ω|
      have ha1 : 1 ≤ a := Real.one_le_exp (abs_nonneg _)
      have hab : a ≤ b := Real.exp_le_exp.mpr hxy
      rw [Real.exp_neg, Real.exp_neg]
      have hapos : 0 < a := by linarith
      have hbpos : 0 < b := by linarith
      have hdiff : 0 ≤ (b - a) * (a * b - 1) := mul_nonneg (by linarith) (by nlinarith)
      have hinv_diff : b + b⁻¹ - (a + a⁻¹) = (b - a) * (a * b - 1) / (a * b) := by
        field_simp [hapos.ne', hbpos.ne']; ring
      have hnonneg : 0 ≤ (b - a) * (a * b - 1) / (a * b) := div_nonneg hdiff (by positivity)
      linarith
    have h54 := (theorem_1_2a_concrete_spectralMeasure_cosh_bound hr (E N) (hcard N) (h N)
      (hsupp N) (hH N) hJ (hsite N) (hUA N) (hAherm N) (hA N) hβ hκ'_nn hκ'_lt).2
    have hsq : (opNorm (A N)) ^ 2 ≤ C_A ^ 2 := by nlinarith [opNorm_nonneg (A N), hA_norm N]
    have hleB : 2 * (2 * (opNorm (A N)) ^ 2 * (1 - κ' / κ) ^ (-((sA : ℝ) / ((r - 1 : ℕ) : ℝ)))) ≤ B := by
      dsimp only [B]
      have := mul_le_mul_of_nonneg_right (show 4 * (opNorm (A N)) ^ 2 ≤ 4 * C_A ^ 2 by linarith)
        (Real.rpow_nonneg h1sub.le (-((sA : ℝ) / ((r - 1 : ℕ) : ℝ))))
      linarith
    dsimp only [κ] at hleB
    linarith
  have hshiftW_unif := hshift_any sW C_W U_W W hCW hUW hWherm hW hW_norm
  have hshiftV_unif := hshift_any sV C_V U_V V hCV hUV hVherm hV hV_norm
  have hcomp_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | |z.im| < S} →
      ∃ M : ℝ, ∀ N, ∀ z ∈ K, ‖concreteOTOC (hH N) β (W N) (V N) z‖ ≤ M := by
    intro K hK hKsub
    by_cases hKne : K.Nonempty
    · obtain ⟨z₀, hz₀K, hz₀_max⟩ := hK.exists_isMaxOn hKne (continuous_abs.comp Complex.continuous_im).continuousOn
      set R : ℝ := |z₀.im|
      have hR_nn : 0 ≤ R := abs_nonneg _
      have hR_lt : R < S := hKsub hz₀K
      rcases hshiftW_unif R hR_nn hR_lt with ⟨B, hB_nn, hB⟩
      refine ⟨C_V ^ 2 * B, fun N z hzK ↦ ?_⟩
      have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
        apply Complex.ext <;> simp
      have h3 := (concreteOTOC_three_way_eq_1_17 (hH N) (hWherm N) (hVherm N) β z.re z.im).1
      rw [← hz_eq] at h3
      have hVsq : (opNorm (V N)) ^ 2 ≤ C_V ^ 2 := by nlinarith [opNorm_nonneg (V N), hV_norm N]
      have hτR : |z.im| ≤ R := hz₀_max hzK
      exact le_trans h3 (mul_le_mul hVsq (hB N z.im hτR)
        (gibbsWightmanNormSq_nonneg _ _) (sq_nonneg C_V))
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨0, fun _ z hz ↦ absurd (hKne ▸ hz) (Set.notMem_empty z)⟩
  exact theorem_1_2c_general_otoc_strip_three_way hS_pos hCW hCV
    (fun N ↦ ∑ X ∈ E N, h N X) W V hH hWherm hVherm hW_norm hV_norm hcomp_bdd
    (fun τ hτ ↦ by rcases hshiftW_unif |τ| (abs_nonneg τ) hτ with ⟨B, _, hB⟩; exact ⟨B, fun N ↦ hB N τ le_rfl⟩)
    (fun τ hτ ↦ by
      rcases hshiftV_unif |τ| (abs_nonneg τ) hτ with ⟨B, _, hB⟩
      exact ⟨B, fun N ↦ hB N (-τ) (by simpa [abs_neg] using le_rfl)⟩)
    F_real hreal_lim

end ThreeWayOTOCStrip

section ERealHoloStripHalfWidth

/-- Polynomial domination by `cosh`: for any `r₀ > 0`, `k : ℕ`, `ω : ℝ`,
`|ω| ^ k ≤ (2 * k! / r₀ ^ k) * Real.cosh (r₀ * ω)`. -/
private lemma abs_pow_le_cosh_bound {r₀ : ℝ} (hr₀ : 0 < r₀) (k : ℕ) (ω : ℝ) :
    |ω| ^ k ≤ (2 * (k.factorial : ℝ) / r₀ ^ k) * Real.cosh (r₀ * ω) := by
  have hx : 0 ≤ r₀ * |ω| := mul_nonneg hr₀.le (abs_nonneg ω)
  have hpow : (r₀ * |ω|) ^ k / (k.factorial : ℝ) ≤ Real.exp (r₀ * |ω|) :=
    Real.pow_div_factorial_le_exp (r₀ * |ω|) hx k
  have hcosh : Real.exp (r₀ * |ω|) ≤ 2 * Real.cosh (r₀ * ω) := by
    have hca : Real.cosh (r₀ * ω) = Real.cosh (r₀ * |ω|) := by
      rcases le_total 0 ω with hω | hω
      · rw [abs_of_nonneg hω]
      · rw [abs_of_nonpos hω, mul_neg, Real.cosh_neg]
    rw [hca, Real.cosh_eq]
    linarith [Real.exp_pos (-(r₀ * |ω|))]
  have h1 : (r₀ * |ω|) ^ k ≤ (k.factorial : ℝ) * (2 * Real.cosh (r₀ * ω)) := by
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    have hmul := (div_le_iff₀ hfac).mp (le_trans hpow hcosh)
    linarith
  rw [mul_pow] at h1
  have hrk : 0 < r₀ ^ k := pow_pos hr₀ k
  rw [show 2 * (k.factorial : ℝ) / r₀ ^ k * Real.cosh (r₀ * ω) =
      (k.factorial : ℝ) * (2 * Real.cosh (r₀ * ω)) / r₀ ^ k by ring]
  exact (le_div_iff₀' hrk).mpr h1

/-- **Differentiation Under the Integral Sign for Holomorphic Fourier–Stieltjes Transforms**:
If `μ : Measure ℝ` has `Integrable (fun ω ↦ Real.cosh (r₀ * ω)) μ` for some `r₀ > 0`, and
`F : ℂ → ℂ` is holomorphic on `{z : ℂ | |z.im| < R}` (`R > 0`) agreeing on `ℝ` with
`t ↦ ∫ ω, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ`, then for every `k : ℕ`,
`iteratedDeriv k F 0 = Complex.I ^ k * ∫ ω : ℝ, (ω : ℂ) ^ k ∂μ`. -/
theorem iteratedDeriv_holo_eq_spectral_moment (μ : Measure ℝ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hcosh : Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hR : 0 < R) (F : ℂ → ℂ)
    (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_real : ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ)
    (k : ℕ) :
    iteratedDeriv k F 0 = Complex.I ^ k * ∫ ω : ℝ, (ω : ℂ) ^ k ∂μ := by
  let g_k : ℕ → ℝ → ℂ := fun m t ↦
    ∫ ω : ℝ, (Complex.I * (ω : ℂ)) ^ m * Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ
  have hnorm_integrand : ∀ (m : ℕ) (t ω : ℝ),
      ‖(Complex.I * (ω : ℂ)) ^ m * Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ))‖ = |ω| ^ m := by
    intro m t ω
    have hexp_norm : ‖Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ))‖ = 1 := by
      have harg : Complex.I * (t : ℂ) * (ω : ℂ) = ((t * ω : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hexp_norm, mul_one]
  have hint_gk : ∀ (m : ℕ) (t : ℝ),
      Integrable (fun ω : ℝ ↦ (Complex.I * (ω : ℂ)) ^ m * Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ))) μ := by
    intro m t
    have hcont : Continuous (fun ω : ℝ ↦
        (Complex.I * (ω : ℂ)) ^ m * Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ))) := by
      fun_prop
    refine (hcosh.const_mul (2 * (m.factorial : ℝ) / r₀ ^ m)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [hnorm_integrand]
    exact abs_pow_le_cosh_bound hr₀ m ω
  have hderiv_gk : ∀ (m : ℕ) (t : ℝ), HasDerivAt (g_k m) (g_k (m + 1) t) t := by
    intro m t
    let Φ : ℝ → ℝ → ℂ := fun x ω ↦
      (Complex.I * (ω : ℂ)) ^ m * Complex.exp (Complex.I * (x : ℂ) * (ω : ℂ))
    let Φ' : ℝ → ℝ → ℂ := fun x ω ↦
      (Complex.I * (ω : ℂ)) ^ (m + 1) * Complex.exp (Complex.I * (x : ℂ) * (ω : ℂ))
    let bound : ℝ → ℝ := fun ω ↦
      (2 * ((m + 1).factorial : ℝ) / r₀ ^ (m + 1)) * Real.cosh (r₀ * ω)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := Φ) (F' := Φ')
      (x₀ := t) (s := Metric.ball t 1) (bound := bound)
      (Metric.ball_mem_nhds t zero_lt_one)
      (Eventually.of_forall fun x ↦ (hint_gk m x).aestronglyMeasurable)
      (hint_gk m t)
      (hint_gk (m + 1) t).aestronglyMeasurable
      (Eventually.of_forall fun ω x _ ↦ by
        dsimp only [Φ', bound]
        rw [hnorm_integrand]
        exact abs_pow_le_cosh_bound hr₀ (m + 1) ω)
      (hcosh.const_mul _)
      (Eventually.of_forall fun ω x _ ↦ by
        dsimp only [Φ, Φ']
        have h1 : HasDerivAt (fun u : ℝ ↦ Complex.I * (u : ℂ) * (ω : ℂ)) (Complex.I * (ω : ℂ)) x := by
          have h0 : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
          have h2 := (h0.const_mul Complex.I).mul_const (ω : ℂ)
          simpa [mul_one] using h2
        have h3 := h1.cexp
        have h4 := h3.const_mul ((Complex.I * (ω : ℂ)) ^ m)
        convert h4 using 1
        rw [pow_succ]; ring)
    exact h.2
  have hreal_iter : ∀ (m : ℕ) (t : ℝ),
      iteratedDeriv m (fun x : ℝ ↦ F (x : ℂ)) t = g_k m t := by
    intro m
    induction m with
    | zero =>
      intro t
      simp only [iteratedDeriv_zero, g_k, pow_zero, one_mul]
      exact hF_real t
    | succ m ih =>
      intro t
      rw [iteratedDeriv_succ, show iteratedDeriv m (fun x : ℝ ↦ F (x : ℂ)) = g_k m from funext ih]
      exact (hderiv_gk m t).deriv
  have hS_open : IsOpen {z : ℂ | |z.im| < R} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hdiff_iter : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m F) {z : ℂ | |z.im| < R} := by
    intro m
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hF_holo
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hS_open
  have hcomplex_eq_real : ∀ (m : ℕ) (t : ℝ),
      iteratedDeriv m F (t : ℂ) = iteratedDeriv m (fun x : ℝ ↦ F (x : ℂ)) t := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
      intro t
      have ht_mem : (t : ℂ) ∈ {z : ℂ | |z.im| < R} := by
        simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
        exact hR
      have hdiff_m : DifferentiableAt ℂ (iteratedDeriv m F) (t : ℂ) :=
        (hdiff_iter m (t : ℂ) ht_mem).differentiableAt (hS_open.mem_nhds ht_mem)
      have hcomp : HasDerivAt (fun x : ℝ ↦ iteratedDeriv m F (x : ℂ))
          (deriv (iteratedDeriv m F) (t : ℂ)) t :=
        hdiff_m.hasDerivAt.comp_ofReal
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      rw [show iteratedDeriv m (fun x : ℝ ↦ F (x : ℂ)) = fun x : ℝ ↦ iteratedDeriv m F (x : ℂ) from
        (funext ih).symm]
      exact hcomp.deriv.symm
  have h0 := (hcomplex_eq_real k 0).trans (hreal_iter k 0)
  rw [Complex.ofReal_zero] at h0
  rw [h0]
  dsimp only [g_k]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, mul_pow]
  rw [integral_const_mul]

/-- Even-order corollary of `iteratedDeriv_holo_eq_spectral_moment`:
`iteratedDeriv (2 * n) F 0 = (-1 : ℂ) ^ n * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ)`. -/
theorem iteratedDeriv_even_holo_eq_spectral_moment (μ : Measure ℝ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hcosh : Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hR : 0 < R) (F : ℂ → ℂ)
    (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_real : ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ)
    (n : ℕ) :
    iteratedDeriv (2 * n) F 0 =
      ((-1 : ℂ) ^ n) * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ) := by
  rw [iteratedDeriv_holo_eq_spectral_moment μ hr₀ hcosh hR F hF_holo hF_real (2 * n)]
  have hI : Complex.I ^ (2 * n) = (-1 : ℂ) ^ n := by
    rw [pow_mul, Complex.I_sq]
  have hint_real : Integrable (fun ω : ℝ ↦ ω ^ (2 * n)) μ := by
    have hcont : Continuous (fun ω : ℝ ↦ ω ^ (2 * n)) := by fun_prop
    refine (hcosh.const_mul (2 * ((2 * n).factorial : ℝ) / r₀ ^ (2 * n))).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_pow]
    exact abs_pow_le_cosh_bound hr₀ (2 * n) ω
  have hint : (∫ ω : ℝ, (ω : ℂ) ^ (2 * n) ∂μ) = ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ) := by
    have hfn : (fun ω : ℝ ↦ (ω : ℂ) ^ (2 * n)) =
        fun ω : ℝ ↦ Complex.ofRealCLM (ω ^ (2 * n)) := by
      funext ω; simp
    rw [hfn]
    exact Complex.ofRealCLM.integral_comp_comm hint_real
  rw [hI, hint]

/-- Unconditional Cauchy even-moment bound without any external `hF_deriv` hypothesis. -/
theorem holoStrip_even_moment_bound_unconditional (μ : Measure ℝ)
    {R ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < R)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (F : ℂ → ℂ) (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_real : ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ) :
    ∃ M_ρ : ℝ, 0 < M_ρ ∧ ∀ n : ℕ,
      ∫ ω : ℝ, ω ^ (2 * n) ∂μ ≤ ((2 * n).factorial : ℝ) * M_ρ * ρ⁻¹ ^ (2 * n) := by
  rcases hr₀ with ⟨r₀, hr₀_pos, hcosh⟩
  exact holoStrip_even_moment_bound μ hρ_pos hρ_lt F hF_holo
    (iteratedDeriv_even_holo_eq_spectral_moment μ hr₀_pos hcosh (lt_trans hρ_pos hρ_lt) F hF_holo hF_real)

/-- Unconditional Theorem 1.2(b) from a fixed holomorphic strip half-width `R > 0`,
discharging `hF_deriv` automatically from `∃ r₀ > 0, Integrable (cosh (r₀ * ω)) μ`. -/
theorem theorem_1_2b_from_holoStripHalfWidth_unconditional (μ : Measure ℝ) {R : ℝ} (b : ℕ → ℝ)
    (hR_pos : 0 < R)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (F : ℂ → ℂ) (hF_holo : DifferentiableOn ℂ F {z : ℂ | |z.im| < R})
    (hF_real : ∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / R := by
  rcases hr₀ with ⟨r₀, hr₀_pos, hcosh⟩
  exact theorem_1_2b_from_holoStripHalfWidth μ b hR_pos F hF_holo
    (iteratedDeriv_even_holo_eq_spectral_moment μ hr₀_pos hcosh hR_pos F hF_holo hF_real)
    hb_pos hmom_eq

/-- Extended-real quotient `π / r` for `r : EReal` (`π / ⊤ = 0`, `π / (x : ℝ) = (π / x : ℝ)`). -/
noncomputable def piDivEReal (r : EReal) : EReal :=
  if r = ⊤ then (0 : EReal) else if r = ⊥ then ⊤ else ((Real.pi / r.toReal : ℝ) : EReal)

/-- **Theorem 1.2(b) — Unconditional `EReal` Holomorphic Strip Half-Width Chain (Eq. 1.16)**:
Directly in terms of `r_W := holoStripHalfWidth μ` with zero `hF_deriv_all` hypothesis (discharged
automatically from `∃ r₀ > 0, Integrable (cosh (r₀ * ω)) μ`):
`((2 * liminf (b n / n) : ℝ) : EReal) ≤ piDivEReal r_W ≤ ((2π / (β + 2κ) : ℝ) : EReal) < ((2π / β : ℝ) : EReal)`. -/
theorem theorem_1_2b_from_holoStripHalfWidth_ereal (μ : Measure ℝ) (b : ℕ → ℝ)
    {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_lb : ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    let L : ℝ := 2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop
    ((L : EReal) ≤ piDivEReal (holoStripHalfWidth μ)) ∧
    (piDivEReal (holoStripHalfWidth μ) ≤ ((2 * Real.pi / (β + 2 * κ) : ℝ) : EReal)) ∧
    (((2 * Real.pi / (β + 2 * κ) : ℝ) : EReal) < ((2 * Real.pi / β : ℝ) : EReal)) := by
  intro L
  have hβκ_pos : 0 < β / 2 + κ := by linarith
  have hstep_R : ∀ R : ℝ, 0 < R → (R : EReal) < holoStripHalfWidth μ → L ≤ Real.pi / R := by
    intro R hR_pos hR_lt
    unfold holoStripHalfWidth at hR_lt
    rcases lt_sSup_iff.mp hR_lt with ⟨r', ⟨R', rfl, hR'_pos, F, hF_holo, hF_real⟩, hR_lt_R'⟩
    have hR_lt_R'_real : R < R' := EReal.coe_lt_coe_iff.mp hR_lt_R'
    have hbd := theorem_1_2b_from_holoStripHalfWidth_unconditional μ b hR'_pos hr₀ F hF_holo hF_real
      hb_pos hmom_eq
    have hdiv_le : Real.pi / R' ≤ Real.pi / R :=
      div_le_div_of_nonneg_left Real.pi_pos.le hR_pos hR_lt_R'_real.le
    exact le_trans hbd hdiv_le
  have hstrict : (2 * Real.pi / (β + 2 * κ) : ℝ) < 2 * Real.pi / β :=
    div_lt_div_of_pos_left (by positivity) hβ (by linarith)
  have hstrict_e : ((2 * Real.pi / (β + 2 * κ) : ℝ) : EReal) < ((2 * Real.pi / β : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr hstrict
  cases hval : holoStripHalfWidth μ using EReal.rec with
  | bot =>
    rw [hval] at hrW_lb
    exact absurd (lt_of_lt_of_le (EReal.bot_lt_coe (β / 2 + κ)) hrW_lb) (lt_irrefl _)
  | top =>
    have hL_le_0 : L ≤ 0 := by
      have hfn : Tendsto (fun m : ℕ ↦ Real.pi / ((m : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      refine ge_of_tendsto hfn ?_
      filter_upwards with m
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      exact hstep_R ((m : ℝ) + 1) hm_pos (by rw [hval]; exact EReal.coe_lt_top _)
    refine ⟨?_, ?_, hstrict_e⟩
    · simp only [piDivEReal, ↓reduceIte]
      exact EReal.coe_le_coe_iff.mpr hL_le_0
    · simp only [piDivEReal, ↓reduceIte]
      exact EReal.coe_le_coe_iff.mpr (by positivity)
  | coe rW =>
    rw [hval] at hrW_lb
    have hrW_ge : β / 2 + κ ≤ rW := EReal.coe_le_coe_iff.mp hrW_lb
    have hrW_pos : 0 < rW := by linarith
    have hL_le_rW : L ≤ Real.pi / rW := by
      let seq : ℕ → ℝ := fun m ↦ rW - rW / ((m : ℝ) + 2)
      have hseq_tend : Tendsto seq atTop (nhds rW) := by
        have hdiv : Tendsto (fun m : ℕ ↦ rW / ((m : ℝ) + 2)) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [seq] using tendsto_const_nhds.sub hdiv
      have hfn_tend : Tendsto (fun m : ℕ ↦ Real.pi / seq m) atTop (nhds (Real.pi / rW)) :=
        (continuousAt_const.div continuousAt_id hrW_pos.ne').tendsto.comp hseq_tend
      refine ge_of_tendsto hfn_tend ?_
      filter_upwards with m
      have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hseq_pos : 0 < seq m := by
        dsimp only [seq]
        have h1 : rW / ((m : ℝ) + 2) ≤ rW / 2 := div_le_div_of_nonneg_left hrW_pos.le (by norm_num) hm2
        linarith
      have hseq_lt : seq m < rW := by
        dsimp only [seq]; linarith [div_pos hrW_pos (by linarith : (0 : ℝ) < (m : ℝ) + 2)]
      exact hstep_R (seq m) hseq_pos (by rw [hval]; exact EReal.coe_lt_coe_iff.mpr hseq_lt)
    have hmid : Real.pi / rW ≤ 2 * Real.pi / (β + 2 * κ) := by
      have heq : Real.pi / (β / 2 + κ) = 2 * Real.pi / (β + 2 * κ) := by
        field_simp [hβκ_pos.ne', (show β + 2 * κ ≠ 0 by linarith)]
      rw [← heq]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hβκ_pos hrW_ge
    refine ⟨?_, ?_, hstrict_e⟩
    · simp only [piDivEReal, EReal.coe_ne_top, EReal.coe_ne_bot, EReal.toReal_coe, ↓reduceIte]
      exact EReal.coe_le_coe_iff.mpr hL_le_rW
    · simp only [piDivEReal, EReal.coe_ne_top, EReal.coe_ne_bot, EReal.toReal_coe, ↓reduceIte]
      exact EReal.coe_le_coe_iff.mpr hmid

/-- **Theorem 1.2(b) — Unconditional Finite `holoStripHalfWidth` Real-Valued Chain (Eq. 1.16)**:
When `holoStripHalfWidth μ = (r_W : EReal)` is finite, extracts the exact real-valued chain
`2 * liminf (b n / n) ≤ π / r_W ≤ 2π / (β + 2κ) < 2π / β` with zero `hF_deriv_all` hypothesis. -/
theorem theorem_1_2b_from_holoStripHalfWidth_finite (μ : Measure ℝ) (b : ℕ → ℝ)
    {β κ r_W : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_eq : holoStripHalfWidth μ = (r_W : EReal))
    (hrW_lb : β / 2 + κ ≤ r_W)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / r_W ∧
    Real.pi / r_W ≤ 2 * Real.pi / (β + 2 * κ) ∧
    2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
  have h := theorem_1_2b_from_holoStripHalfWidth_ereal μ b hβ hκ
    (by rw [hrW_eq]; exact EReal.coe_le_coe_iff.mpr hrW_lb) hr₀ hb_pos hmom_eq
  rw [hrW_eq] at h
  simp only [piDivEReal, EReal.coe_ne_top, EReal.coe_ne_bot, EReal.toReal_coe, ↓reduceIte,
    EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff] at h
  exact h

end ERealHoloStripHalfWidth

section Araki1DIndependentRangeAndIsingActiveDegree

/-- **Proposition 8.1 (Independent Locality `r` and Diameter `R` Parameterization)**:
For any 1D interaction hypergraph `E` with nonempty supports of cardinality `≤ r` and
diameter `∀ x y ∈ X, |(x.val : ℤ) - (y.val : ℤ)| ≤ R`, applies `prop_8_1_araki_1d_complete`
with range `R + 1`. -/
theorem prop_8_1_araki_1d_independent_r_R {N r R : ℕ}
    (E : Finset (Finset (Fin N)))
    (hne : ∀ X ∈ E, X.Nonempty)
    (_hcard : ∀ X ∈ E, X.card ≤ r)
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, |(x.val : ℤ) - (y.val : ℤ)| ≤ (R : ℤ))
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (β : ℝ) (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β (R + 1) J) ^ 2 *
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ∧
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ∧
    (∀ C_RP : ℝ,
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
        C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re →
      otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β (R + 1) J) ^ 2 * C_RP *
        (gibbsWightmanInner G A (wightmanQ G A)).re) := by
  have h1d : is1DFiniteRange N (R + 1) E := by
    intro X hX
    refine ⟨hne X hX, fun x hx y hy ↦ ?_⟩
    have hd := (abs_le.mp (hdiam X hX x hx y hy)).2
    omega
  exact prop_8_1_araki_1d_complete (by omega : 1 ≤ R + 1) E h1d h hsupp hH hJ hsite β A

/-- Zero-coupling edges have zero Hubbard–Stratonovich parameter: `isingHSParam β 0 = 0`. -/
lemma isingHSParam_zero (β : ℝ) : isingHSParam β 0 = 0 := by
  unfold isingHSParam
  simp

/-- **Active-Edge Linear Bound on `isingPhiMaxExact`**:
Counts ONLY nonzero-coupling edges (`J e.1.1 e.1.2 ≠ 0`), matching `Δ := max_i #{j : J_{ij} ≠ 0}`:
`isingPhiMaxExact β J hfield ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2`. -/
theorem isingPhiMaxExact_le_linear_active {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N,
        if J e.1.1 e.1.2 ≠ 0 then
          ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))
        else 0) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max) :
    isingPhiMaxExact β J hfield ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2 := by
  unfold isingPhiMaxExact
  have hB_nn : 0 ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2 := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hfold_le : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ) (B : ℝ),
      0 ≤ B → (∀ a ∈ S, g a ≤ B) → S.fold max 0 g ≤ B := by
    intro S g B hB hg
    classical
    induction S using Finset.induction_on with
    | empty => simpa using hB
    | insert a t hat ih =>
      rw [Finset.fold_insert hat]
      exact max_le (hg a (Finset.mem_insert_self a t))
        (ih fun x hx ↦ hg x (Finset.mem_insert_of_mem hx))
  refine hfold_le Finset.univ _ _ hB_nn fun i _ ↦ ?_
  have hsum_le : ∑ e : IsingEdge N,
        ((if e.1.1 = i then isingHSParam β (J e.1.1 e.1.2) else 0) +
         (if e.1.2 = i then isingHSParam β (J e.1.1 e.1.2) else 0)) ≤
      β * (∑ e : IsingEdge N,
        ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0))) +
      ((1 / 2 : ℝ) * Real.log 2) *
        (∑ e : IsingEdge N,
          if J e.1.1 e.1.2 ≠ 0 then
            ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))
          else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro e _
    by_cases hJ0 : J e.1.1 e.1.2 = 0
    · simp [hJ0, isingHSParam_zero]
    · have hc := isingHSParam_le_linear hβ (J e.1.1 e.1.2)
      simp only [hJ0, ne_eq, not_false_eq_true, ↓reduceIte]
      split_ifs <;> linarith
  have hloc_i := mul_le_mul_of_nonneg_left (hloc i) hβ
  have hdeg_i := mul_le_mul_of_nonneg_left (hdeg i) (show 0 ≤ (1 / 2 : ℝ) * Real.log 2 by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); positivity)
  linarith

/-- **Proposition 8.3 (Exact Eq. 8.4 `cosh²` Bound with Active-Edge Vertex Degree `Δ`)**:
Counts only nonzero couplings `J e.1.1 e.1.2 ≠ 0` and yields the sharp manuscript constant
`cosh²(β H_max + (Δ / 2) ln 2)`. -/
theorem prop_8_3_ising_explicit_eq_8_4_cosh {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N,
        if J e.1.1 e.1.2 ≠ 0 then
          ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))
        else 0) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max)
    (f : SpinConfig N → ℝ) :
    glauberDirichlet (isingGibbsMeasure β J hfield) f ≤
      (Real.cosh (β * H_max + ((Δ : ℝ) / 2) * Real.log 2)) ^ 2 *
        degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  have h1 := prop_8_3_classical_ising_reverse_poincare_eq_8_4 hβ J hfield f
  have hphi := isingPhiMaxExact_le_linear_active hβ hHmax J hfield hdeg hloc
  have hphi_nn : 0 ≤ isingPhiMaxExact β J hfield := by
    unfold isingPhiMaxExact
    have hfold_nn : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ), 0 ≤ S.fold max 0 g := by
      intro S g; classical
      induction S using Finset.induction_on with
      | empty => simp
      | insert a t hat ih => rw [Finset.fold_insert hat]; exact le_trans ih (le_max_right _ _)
    exact hfold_nn Finset.univ _
  have hcosh_mono : Real.cosh (isingPhiMaxExact β J hfield) ≤
      Real.cosh (β * H_max + ((Δ : ℝ) / 2) * Real.log 2) := by
    rw [Real.cosh_eq, Real.cosh_eq]
    set a := Real.exp (isingPhiMaxExact β J hfield)
    set b := Real.exp (β * H_max + ((Δ : ℝ) / 2) * Real.log 2)
    have ha1 : 1 ≤ a := Real.one_le_exp hphi_nn
    have hab : a ≤ b := Real.exp_le_exp.mpr hphi
    rw [Real.exp_neg, Real.exp_neg]
    have hapos : 0 < a := by linarith
    have hbpos : 0 < b := by linarith
    have hdiff : 0 ≤ (b - a) * (a * b - 1) := mul_nonneg (by linarith) (by nlinarith)
    have hinv_diff : b + b⁻¹ - (a + a⁻¹) = (b - a) * (a * b - 1) / (a * b) := by
      field_simp [hapos.ne', hbpos.ne']; ring
    have hnonneg : 0 ≤ (b - a) * (a * b - 1) / (a * b) := div_nonneg hdiff (by positivity)
    linarith
  have hcosh_sq : (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 ≤
      (Real.cosh (β * H_max + ((Δ : ℝ) / 2) * Real.log 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.cosh_pos _).le hcosh_mono 2
  have hQ_nn : 0 ≤ degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
    unfold degreeFiltrationQ distSqDegree
    apply Finset.sum_nonneg; intro k _
    apply Real.sInf_nonneg; rintro _ ⟨g, _, rfl⟩
    apply Finset.sum_nonneg; intro σ _
    have hμ_nn : 0 ≤ isingGibbsMeasure β J hfield σ := by
      unfold isingGibbsMeasure
      exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    exact mul_nonneg hμ_nn (sq_nonneg _)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcosh_sq hQ_nn)

/-- Corollary of `prop_8_3_ising_explicit_eq_8_4_cosh` yielding the exponential bound
`2 ^ Δ * exp(2 β H_max)` with active-edge vertex degree `Δ`. -/
theorem prop_8_3_ising_explicit_eq_8_4_exp {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N,
        if J e.1.1 e.1.2 ≠ 0 then
          ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))
        else 0) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max)
    (f : SpinConfig N → ℝ) :
    glauberDirichlet (isingGibbsMeasure β J hfield) f ≤
      (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) *
        degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  have h1 := prop_8_3_ising_explicit_eq_8_4_cosh hβ hHmax J hfield hdeg hloc f
  set x : ℝ := β * H_max + ((Δ : ℝ) / 2) * Real.log 2
  have hx_nn : 0 ≤ x := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hcosh_le : (Real.cosh x) ^ 2 ≤ (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) := by
    have hce : Real.cosh x ≤ Real.exp x := by
      rw [Real.cosh_eq]
      have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
      linarith
    calc (Real.cosh x) ^ 2
        ≤ (Real.exp x) ^ 2 := pow_le_pow_left₀ (Real.cosh_pos x).le hce 2
      _ = Real.exp (2 * x) := by rw [sq, ← Real.exp_add]; congr 1; ring
      _ = Real.exp ((Δ : ℝ) * Real.log 2) * Real.exp (2 * β * H_max) := by
          rw [← Real.exp_add]; congr 1; dsimp only [x]; ring
      _ = (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) := by
          rw [mul_comm (Δ : ℝ), Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
  have hQ_nn : 0 ≤ degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
    unfold degreeFiltrationQ distSqDegree
    apply Finset.sum_nonneg; intro k _
    apply Real.sInf_nonneg; rintro _ ⟨g, _, rfl⟩
    apply Finset.sum_nonneg; intro σ _
    have hμ_nn : 0 ≤ isingGibbsMeasure β J hfield σ := by
      unfold isingGibbsMeasure
      exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    exact mul_nonneg hμ_nn (sq_nonneg _)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcosh_le hQ_nn)

end Araki1DIndependentRangeAndIsingActiveDegree

end KrylovChaos
