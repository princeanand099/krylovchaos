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
# Packaging Theorems for Eqs. (1.16), (1.17), and (1.20)

Provides clean end-to-end packaging wrappers for:
1. **Theorem 1.3(a), Eq. (1.20)** (`theorem_1_3a_high_temp_eq_1_20`): the exact two-sided
   high-temperature operator inequality
   `Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`.
2. **Theorem 1.2(c), Eq. (1.17)** (`theorem_1_2c_general_otoc_strip_three_way`,
   `theorem_1_2c_thermo_limit_otoc_strip_three_way`): thermodynamic-limit strip analyticity
   bundling all three Eq. (1.17) `liminf` upper bounds
   `min(C_V² liminf C_W(2iτ), C_W² liminf C_V(-2iτ), liminf T_{τ,N}(t))`.
3. **Theorem 1.2(b), Eq. (1.16)** (`theorem_1_2b_from_holoStripHalfWidth_ereal`,
   `theorem_1_2b_from_holoStripHalfWidth_finite`): `EReal` and finite-`r_W` packaging directly in
   terms of `r_W := holoStripHalfWidth μ`:
   `2 * liminf (b n / n) ≤ π / r_W ≤ 2π / (β + 2κ) < 2π / β`.
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

/-- Extended-real quotient `π / r` for `r : EReal` (`π / ⊤ = 0`, `π / (x : ℝ) = (π / x : ℝ)`). -/
noncomputable def piDivEReal (r : EReal) : EReal :=
  if r = ⊤ then (0 : EReal) else if r = ⊥ then ⊤ else ((Real.pi / r.toReal : ℝ) : EReal)

/-- **Theorem 1.2(b) — `EReal` Holomorphic Strip Half-Width Chain (Eq. 1.16)**:
Directly in terms of `r_W := holoStripHalfWidth μ` (handling both finite `r_W` and `r_W = ⊤`):
`((2 * liminf (b n / n) : ℝ) : EReal) ≤ piDivEReal r_W ≤ ((2π / (β + 2κ) : ℝ) : EReal) < ((2π / β : ℝ) : EReal)`. -/
theorem theorem_1_2b_from_holoStripHalfWidth_ereal (μ : Measure ℝ) (b : ℕ → ℝ)
    {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_lb : ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ)
    (hF_deriv_all : ∀ (R : ℝ) (F : ℂ → ℂ), 0 < R →
      DifferentiableOn ℂ F {z : ℂ | |z.im| < R} →
      (∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ) →
      ∀ n : ℕ, iteratedDeriv (2 * n) F 0 =
        ((-1 : ℂ) ^ n) * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ))
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
    have hbd := theorem_1_2b_from_holoStripHalfWidth μ b hR'_pos F hF_holo
      (hF_deriv_all R' F hR'_pos hF_holo hF_real) hb_pos hmom_eq
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

/-- **Theorem 1.2(b) — Finite `holoStripHalfWidth` Real-Valued Chain (Eq. 1.16)**:
When `holoStripHalfWidth μ = (r_W : EReal)` is finite, extracts the exact real-valued chain
`2 * liminf (b n / n) ≤ π / r_W ≤ 2π / (β + 2κ) < 2π / β`. -/
theorem theorem_1_2b_from_holoStripHalfWidth_finite (μ : Measure ℝ) (b : ℕ → ℝ)
    {β κ r_W : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_eq : holoStripHalfWidth μ = (r_W : EReal))
    (hrW_lb : β / 2 + κ ≤ r_W)
    (hF_deriv_all : ∀ (R : ℝ) (F : ℂ → ℂ), 0 < R →
      DifferentiableOn ℂ F {z : ℂ | |z.im| < R} →
      (∀ t : ℝ, F (t : ℂ) = ∫ ω : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) ∂μ) →
      ∀ n : ℕ, iteratedDeriv (2 * n) F 0 =
        ((-1 : ℂ) ^ n) * ((∫ ω : ℝ, ω ^ (2 * n) ∂μ : ℝ) : ℂ))
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / r_W ∧
    Real.pi / r_W ≤ 2 * Real.pi / (β + 2 * κ) ∧
    2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
  have h := theorem_1_2b_from_holoStripHalfWidth_ereal μ b hβ hκ
    (by rw [hrW_eq]; exact EReal.coe_le_coe_iff.mpr hrW_lb) hF_deriv_all hb_pos hmom_eq
  rw [hrW_eq] at h
  simp only [piDivEReal, EReal.coe_ne_top, EReal.coe_ne_bot, EReal.toReal_coe, ↓reduceIte,
    EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff] at h
  exact h

end ERealHoloStripHalfWidth

end KrylovChaos
