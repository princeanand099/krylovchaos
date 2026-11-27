import KrylovChaos.HighTempPolymerZ
import KrylovChaos.Theorem12Concrete

/-!
# High-Temperature Trace Cumulant Bound (Lemma 6.3, Eq. 6.3)

Combines the polymer partition function identity, Kotecký–Preiss nonvanishing and ratio
bounds, site-slice telescoping, and the Cauchy order-2 Schwarz lemma from
`KrylovChaos.HighTempPolymerZ` to prove `lemma_6_3_combined_cumulant_bound`
(Lemma 6.3, Eq. (6.3)).
-/

namespace KrylovChaos

open scoped BigOperators Matrix ComplexOrder
open Complex Matrix

noncomputable section TraceCumulantMain

set_option maxHeartbeats 800000 in
/-- **Lemma 6.3 (Unconditional High-Temperature Combined-Exponential Trace Cumulant Bound)**:
For any `r`-local (`r ≥ 2`) Hermitian Hamiltonian `H = ∑ Z ∈ E, h Z` with `h Z ∈ supportedOn Z`,
`Z.Nonempty`, `Z.card ≤ r`, site strength `≤ Jsite` (`0 < Jsite`), any `k_X`-local (`1 ≤ k_X`)
Hermitian observable `X = ∑ Z ∈ E_X, x Z` with `x Z ∈ supportedOn Z`, `Z.Nonempty`,
`Z.card ≤ k_X`, site strength `≤ gX` (`0 < gX`), `β ∈ [0, (8 e² r Jsite)⁻¹]`, `k_r := max r k_X`,
`Λ₀' := (16 * k_r * exp(1 + k_r / r) * gX)⁻¹`, and centered observable
`X̃ := X - ((gibbsRho hH β * X).trace.re : ℂ) • 1`:
For EVERY real `lam` with `|lam| ≤ Λ₀' / 2`:
`Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) ≤ 8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2`,
where `K = (-β) • H + lam • X̃`. -/
theorem lemma_6_3_combined_cumulant_bound {N r k_X : ℕ}
    (hr : 2 ≤ r) (hkX : 1 ≤ k_X)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    (E_X : Finset (Finset (Fin N))) (hEX_ne : ∀ Z ∈ E_X, Z.Nonempty)
    (hEX_card : ∀ Z ∈ E_X, Z.card ≤ k_X)
    (xOp : Finset (Fin N) → QubitOp N) (hx_supp : ∀ Z, xOp Z ∈ supportedOn Z)
    (hX : (∑ Z ∈ E_X, xOp Z).IsHermitian)
    {gX : ℝ} (hgX : 0 < gX)
    (hX_site : ∀ x : Fin N, ∑ Z ∈ E_X.filter (fun Z ↦ x ∈ Z), opNorm (xOp Z) ≤ gX)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite))
    {lam : ℝ}
    (hlam : |lam| ≤ (1 / (16 * ((max r k_X : ℕ) : ℝ) *
      Real.exp (1 + ((max r k_X : ℕ) : ℝ) / (r : ℝ)) * gX)) / 2) :
    let H := ∑ Z ∈ E, h Z
    let X := ∑ Z ∈ E_X, xOp Z
    let μ := (gibbsRho hH β * X).trace.re
    let Xtilde : QubitOp N := X - (μ : ℂ) • 1
    let K : QubitOp N := ((-β : ℝ) : ℂ) • H + ((lam : ℝ) : ℂ) • Xtilde
    have hK : K.IsHermitian := by
      have hXt : Xtilde.IsHermitian := by
        simp only [Xtilde, X, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hX.eq]
      simp only [K, H, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Complex.star_def, Complex.conj_ofReal, hH.eq, hXt.eq]
    let kr := max r k_X
    let Λ₀' := 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * gX)
    Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) ≤
      8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := by
  classical
  intro H X μ Xtilde K hK kr Λ₀'
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hkr_ge_r : r ≤ kr := le_max_left r k_X
  have hkr_ge_kX : k_X ≤ kr := le_max_right r k_X
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by exact_mod_cast (by omega : 0 < kr)
  have hΛ_pos : 0 < Λ₀' := by dsimp only [Λ₀']; positivity
  -- Union hypergraph `E_tot = E ∪ E_X` with negated affine interaction `g_tot ζ`.
  let E_tot : Finset (Finset (Fin N)) := E ∪ E_X
  have hEtot_ne : ∀ Z ∈ E_tot, Z.Nonempty := by
    intro Z hZ; rcases Finset.mem_union.mp hZ with h1 | h2
    · exact hE_ne Z h1
    · exact hEX_ne Z h2
  let A_op : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E then (β : ℂ) • h Z else 0
  let B_op : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E_X then (-1 : ℂ) • xOp Z else 0
  let g_tot : ℂ → Finset (Fin N) → QubitOp N := fun ζ Z ↦ A_op Z + ζ • B_op Z
  have hg_supp : ∀ ζ Z, g_tot ζ Z ∈ supportedOn Z := by
    intro ζ Z; dsimp only [g_tot, A_op, B_op]
    refine (supportedOn Z).add_mem ?_ ((supportedOn Z).smul_mem _ ?_)
    · split_ifs
      · exact (supportedOn Z).smul_mem _ (hh_supp Z)
      · exact (supportedOn Z).zero_mem
    · split_ifs
      · exact (supportedOn Z).smul_mem _ (hx_supp Z)
      · exact (supportedOn Z).zero_mem
  have hg_sum : ∀ ζ : ℂ, ∑ Z ∈ E_tot, g_tot ζ Z = (β : ℂ) • H - ζ • X := by
    intro ζ
    dsimp only [g_tot, A_op, B_op, H, X]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ Z ∈ E_tot, (if Z ∈ E then (β : ℂ) • h Z else 0) = (β : ℂ) • ∑ Z ∈ E, h Z := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Finset.subset_union_left,
        Finset.smul_sum]
    have h2 : ∑ Z ∈ E_tot, ζ • (if Z ∈ E_X then (-1 : ℂ) • xOp Z else 0) = -(ζ • ∑ Z ∈ E_X, xOp Z) := by
      have hrew : ∀ Z, ζ • (if Z ∈ E_X then (-1 : ℂ) • xOp Z else 0) =
          if Z ∈ E_X then (-ζ) • xOp Z else 0 := by
        intro Z; split_ifs <;> simp [smul_smul]
      simp_rw [hrew]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Finset.subset_union_right,
        ← Finset.smul_sum, neg_smul]
    rw [h1, h2, sub_eq_add_neg]
  -- Parameter `c = 1 / (2 * r)` and KP pinning verification on `closedBall 0 Λ₀'`.
  set c : ℝ := 1 / (2 * (r : ℝ))
  have hc_pos : 0 < c := by positivity
  have hc_le : c ≤ 1 / 4 := by
    dsimp only [c]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  let Γ := connectedPolymers E_tot
  let a : Polymer N → ℝ := fun γ ↦ c * (polySupp γ).card
  have ha_nn : ∀ γ, 0 ≤ a γ := fun γ ↦ by dsimp only [a]; positivity
  -- Key two-scale site-sum bound for all `‖ζ‖ ≤ Λ₀'`:
  have hsite_pin : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ x : Fin N,
      ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ) ≤ c / 2 := by
    intro ζ hζ x
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    let η : Finset (Fin N) → ℝ := fun Z ↦ (Real.exp (opNorm (g_tot ζ Z)) - 1) * Real.exp (c * (Z.card : ℝ))
    have hη_nn : ∀ Z ∈ E_tot, 0 ≤ η Z := fun Z _ ↦ by
      dsimp only [η]
      exact mul_nonneg (by linarith [Real.one_le_exp (opNorm_nonneg (g_tot ζ Z))]) (Real.exp_pos _).le
    have hβJ_lt : β * Jsite < 1 / 8 := by
      have h1 : β * Jsite ≤ 1 / (8 * Real.exp 2 * (r : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hβ hJ.le
        have heq : 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) * Jsite = 1 / (8 * Real.exp 2 * (r : ℝ)) := by
          field_simp [hJ.ne', (Real.exp_pos 2).ne', hr_pos.ne']
        linarith
      have he2 : (2 : ℝ) < Real.exp 2 := by
        have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0); linarith
      have hden : (8 : ℝ) < 8 * Real.exp 2 * (r : ℝ) := by nlinarith
      have hlt : 1 / (8 * Real.exp 2 * (r : ℝ)) < 1 / 8 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hΛg_lt : Λ₀' * gX < 1 / 8 := by
      have heq : Λ₀' * gX = 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ))) := by
        dsimp only [Λ₀']
        field_simp [hgX.ne', hkr_pos.ne', (Real.exp_pos _).ne']
      rw [heq]
      have hkr2 : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (le_trans hr hkr_ge_r)
      have hexp1 : (1 : ℝ) < Real.exp (1 + (kr : ℝ) / (r : ℝ)) :=
        Real.one_lt_exp_iff.mpr (by positivity)
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hsite_w : ∀ y : Fin N,
        ∑ Z ∈ E_tot.filter (fun Z ↦ y ∈ Z), η Z * Real.exp (c * (Z.card : ℝ)) ≤ c / 2 := by
      intro y
      have hterm_le : ∀ Z ∈ E_tot.filter (fun Z ↦ y ∈ Z),
          η Z * Real.exp (c * (Z.card : ℝ)) ≤
            (if Z ∈ E then β * opNorm (h Z) * Real.exp 2 else 0) +
            (if Z ∈ E_X then Λ₀' * opNorm (xOp Z) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) else 0) := by
        intro Z hZ
        have hZy : y ∈ Z := (Finset.mem_filter.mp hZ).2
        set u1 : ℝ := if Z ∈ E then β * opNorm (h Z) else 0
        set u2 : ℝ := if Z ∈ E_X then Λ₀' * opNorm (xOp Z) else 0
        have hu1_nn : 0 ≤ u1 := by
          dsimp only [u1]; split_ifs
          · exact mul_nonneg hβ0 (opNorm_nonneg _)
          · exact le_rfl
        have hu2_nn : 0 ≤ u2 := by
          dsimp only [u2]; split_ifs
          · exact mul_nonneg hΛ_pos.le (opNorm_nonneg _)
          · exact le_rfl
        have hop_le : opNorm (g_tot ζ Z) ≤ u1 + u2 := by
          dsimp only [g_tot, A_op, B_op, u1, u2]
          refine le_trans (opNorm_add_le _ _) (add_le_add ?_ ?_)
          · split_ifs
            · rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
            · simp [opNorm, opToCLM]
          · split_ifs
            · rw [smul_smul, opNorm_smul, norm_mul, norm_neg, norm_one, mul_one]
              exact mul_le_mul_of_nonneg_right hζ (opNorm_nonneg _)
            · simp [opNorm, opToCLM]
        have hu1_le : u1 ≤ β * Jsite := by
          dsimp only [u1]; split_ifs with hZE
          · have h1 : opNorm (h Z) ≤ ∑ W ∈ E.filter (fun W ↦ y ∈ W), opNorm (h W) :=
              Finset.single_le_sum (fun W _ ↦ opNorm_nonneg (h W)) (Finset.mem_filter.mpr ⟨hZE, hZy⟩)
            exact mul_le_mul_of_nonneg_left (le_trans h1 (hH_site y)) hβ0
          · positivity
        have hu2_le : u2 ≤ Λ₀' * gX := by
          dsimp only [u2]; split_ifs with hZEX
          · have h1 : opNorm (xOp Z) ≤ ∑ W ∈ E_X.filter (fun W ↦ y ∈ W), opNorm (xOp W) :=
              Finset.single_le_sum (fun W _ ↦ opNorm_nonneg (xOp W)) (Finset.mem_filter.mpr ⟨hZEX, hZy⟩)
            exact mul_le_mul_of_nonneg_left (le_trans h1 (hX_site y)) hΛ_pos.le
          · positivity
        have hsum_u_lt1 : u1 + u2 ≤ 1 := by linarith
        have hexp_sub : Real.exp (opNorm (g_tot ζ Z)) - 1 ≤ (u1 + u2) * Real.exp 1 := by
          have h1 : Real.exp (opNorm (g_tot ζ Z)) - 1 ≤ Real.exp (u1 + u2) - 1 := by
            linarith [Real.exp_le_exp.mpr hop_le]
          have h2 : Real.exp (u1 + u2) - 1 ≤ (u1 + u2) * Real.exp (u1 + u2) := by
            have := Real.add_one_le_exp (-(u1 + u2))
            have hpos := Real.exp_pos (u1 + u2)
            have hmul := mul_le_mul_of_nonneg_right this hpos.le
            rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
            linarith
          exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_u_lt1) (by linarith)))
        have hprod_eq : η Z * Real.exp (c * (Z.card : ℝ)) =
            (Real.exp (opNorm (g_tot ζ Z)) - 1) * Real.exp (2 * c * (Z.card : ℝ)) := by
          dsimp only [η]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        rw [hprod_eq]
        have h1 : (Real.exp (opNorm (g_tot ζ Z)) - 1) * Real.exp (2 * c * (Z.card : ℝ)) ≤
            u1 * (Real.exp 1 * Real.exp (2 * c * (Z.card : ℝ))) +
            u2 * (Real.exp 1 * Real.exp (2 * c * (Z.card : ℝ))) := by
          have := mul_le_mul_of_nonneg_right hexp_sub (Real.exp_pos (2 * c * (Z.card : ℝ))).le
          linarith
        refine le_trans h1 (add_le_add ?_ ?_)
        · dsimp only [u1]; split_ifs with hZE
          · have h2c : 2 * c * (Z.card : ℝ) ≤ 1 := by
              dsimp only [c]
              have hZle : (Z.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hE_card Z hZE
              calc 2 * (1 / (2 * (r : ℝ))) * (Z.card : ℝ) = (Z.card : ℝ) / (r : ℝ) := by
                    field_simp [hr_pos.ne']
                _ ≤ 1 := (div_le_one hr_pos).mpr hZle
            have hexp2 : Real.exp 1 * Real.exp (2 * c * (Z.card : ℝ)) ≤ Real.exp 2 := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
            have hnn : 0 ≤ β * opNorm (h Z) := mul_nonneg hβ0 (opNorm_nonneg _)
            exact mul_le_mul_of_nonneg_left hexp2 hnn
          · rw [zero_mul]
        · dsimp only [u2]; split_ifs with hZEX
          · have h2c : 2 * c * (Z.card : ℝ) ≤ (kr : ℝ) / (r : ℝ) := by
              dsimp only [c]
              have hZle : (Z.card : ℝ) ≤ (kr : ℝ) := by exact_mod_cast le_trans (hEX_card Z hZEX) hkr_ge_kX
              calc 2 * (1 / (2 * (r : ℝ))) * (Z.card : ℝ) = (Z.card : ℝ) / (r : ℝ) := by
                    field_simp [hr_pos.ne']
                _ ≤ (kr : ℝ) / (r : ℝ) := div_le_div_of_nonneg_right hZle hr_pos.le
            have hexp2 : Real.exp 1 * Real.exp (2 * c * (Z.card : ℝ)) ≤
                Real.exp (1 + (kr : ℝ) / (r : ℝ)) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
            have hnn : 0 ≤ Λ₀' * opNorm (xOp Z) := mul_nonneg hΛ_pos.le (opNorm_nonneg _)
            exact mul_le_mul_of_nonneg_left hexp2 hnn
          · rw [zero_mul]
      have hsum := Finset.sum_le_sum hterm_le
      rw [Finset.sum_add_distrib] at hsum
      have hsumE : ∑ Z ∈ E_tot.filter (fun Z ↦ y ∈ Z), (if Z ∈ E then β * opNorm (h Z) * Real.exp 2 else 0) ≤
          1 / (8 * (r : ℝ)) := by
        rw [← Finset.sum_filter]
        have hf : (E_tot.filter (fun Z ↦ y ∈ Z)).filter (fun Z ↦ Z ∈ E) = E.filter (fun Z ↦ y ∈ Z) := by
          ext Z; simp only [E_tot, Finset.mem_filter, Finset.mem_union]; tauto
        rw [hf]
        have hfac : ∑ Z ∈ E.filter (fun Z ↦ y ∈ Z), β * opNorm (h Z) * Real.exp 2 =
            β * Real.exp 2 * ∑ Z ∈ E.filter (fun Z ↦ y ∈ Z), opNorm (h Z) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Z _; ring
        rw [hfac]
        calc β * Real.exp 2 * ∑ Z ∈ E.filter (fun Z ↦ y ∈ Z), opNorm (h Z)
            ≤ β * Real.exp 2 * Jsite := mul_le_mul_of_nonneg_left (hH_site y) (by positivity)
          _ ≤ (1 / (8 * Real.exp 2 * (r : ℝ) * Jsite)) * Real.exp 2 * Jsite := by
              apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ (Real.exp_pos 2).le) hJ.le
          _ = 1 / (8 * (r : ℝ)) := by field_simp [hJ.ne', (Real.exp_pos 2).ne', hr_pos.ne']
      have hsumEX : ∑ Z ∈ E_tot.filter (fun Z ↦ y ∈ Z),
          (if Z ∈ E_X then Λ₀' * opNorm (xOp Z) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) else 0) ≤
          1 / (8 * (r : ℝ)) := by
        rw [← Finset.sum_filter]
        have hf : (E_tot.filter (fun Z ↦ y ∈ Z)).filter (fun Z ↦ Z ∈ E_X) = E_X.filter (fun Z ↦ y ∈ Z) := by
          ext Z; simp only [E_tot, Finset.mem_filter, Finset.mem_union]; tauto
        rw [hf]
        have hfac : ∑ Z ∈ E_X.filter (fun Z ↦ y ∈ Z), Λ₀' * opNorm (xOp Z) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) =
            Λ₀' * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * ∑ Z ∈ E_X.filter (fun Z ↦ y ∈ Z), opNorm (xOp Z) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Z _; ring
        rw [hfac]
        calc Λ₀' * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * ∑ Z ∈ E_X.filter (fun Z ↦ y ∈ Z), opNorm (xOp Z)
            ≤ Λ₀' * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * gX :=
              mul_le_mul_of_nonneg_left (hX_site y) (by positivity)
          _ = 1 / (16 * (kr : ℝ)) := by
              dsimp only [Λ₀']
              field_simp [hkr_pos.ne', (Real.exp_pos _).ne', hgX.ne']
          _ ≤ 1 / (8 * (r : ℝ)) := by
              have hkr_ge : (r : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr_ge_r
              rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hc2 : 1 / (8 * (r : ℝ)) + 1 / (8 * (r : ℝ)) = c / 2 := by
        dsimp only [c]; field_simp [hr_pos.ne']; ring
      linarith
    -- Now bound `∑_{γ ∋ x} ‖w γ‖ exp(a γ)` by `∑_{Z ∋ x} unorderedTreeSum ≤ c / 2`!
    have hpoly_le : ∀ γ ∈ Γ, ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ) ≤ ∏ Z ∈ γ, η Z := by
      intro γ hγ
      have hcard_bi : (polySupp γ).card ≤ ∑ Z ∈ γ, Z.card := Finset.card_biUnion_le
      have hexp_le : Real.exp (a γ) ≤ ∏ Z ∈ γ, Real.exp (c * (Z.card : ℝ)) := by
        rw [← Real.exp_sum]
        apply Real.exp_le_exp.mpr
        have hcast : ((polySupp γ).card : ℝ) ≤ ∑ Z ∈ γ, (Z.card : ℝ) := by exact_mod_cast hcard_bi
        calc c * ((polySupp γ).card : ℝ) ≤ c * ∑ Z ∈ γ, (Z.card : ℝ) :=
              mul_le_mul_of_nonneg_left hcast hc_pos.le
          _ = ∑ Z ∈ γ, c * (Z.card : ℝ) := Finset.mul_sum _ _ _
      calc ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ)
          ≤ (∏ Z ∈ γ, (Real.exp (opNorm (g_tot ζ Z)) - 1)) *
              (∏ Z ∈ γ, Real.exp (c * (Z.card : ℝ))) := by
            have hw := norm_tracePolyWeight_le (g_tot ζ) (by norm_num : (0 : ℝ) ≤ 1) γ
            simp only [one_mul] at hw
            exact mul_le_mul hw hexp_le (Real.exp_pos _).le
              (Finset.prod_nonneg fun Z _ ↦ by linarith [Real.one_le_exp (opNorm_nonneg (g_tot ζ Z))])
        _ = ∏ Z ∈ γ, η Z := by rw [← Finset.prod_mul_distrib]
    have hpin : Γ.filter (fun γ ↦ x ∈ polySupp γ) ⊆
        (E_tot.filter (fun Z ↦ x ∈ Z)).biUnion
          (fun Z₀ ↦ Γ.filter (fun γ ↦ Z₀ ∈ γ ∧ γ.card ≤ E_tot.card + 1)) := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγΓ, hxγ⟩
      have hsub : γ ⊆ E_tot := (mem_connectedPolymers.mp hγΓ).1
      rcases Finset.mem_biUnion.mp hxγ with ⟨Z₀, hZ₀γ, hxZ₀⟩
      exact Finset.mem_biUnion.mpr ⟨Z₀, Finset.mem_filter.mpr ⟨hsub hZ₀γ, hxZ₀⟩,
        Finset.mem_filter.mpr ⟨hγΓ, hZ₀γ, le_trans (Finset.card_le_card hsub) (Nat.le_succ _)⟩⟩
    have htree := unorderedTreeSum_le_weighted E_tot η hη_nn hc_pos.le
      (fun y ↦ le_trans (hsite_w y) (by linarith))
    calc ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ)
        ≤ ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ∏ Z ∈ γ, η Z :=
          Finset.sum_le_sum fun γ hγ ↦ hpoly_le γ (Finset.mem_filter.mp hγ).1
      _ ≤ ∑ γ ∈ (E_tot.filter (fun Z ↦ x ∈ Z)).biUnion
            (fun Z₀ ↦ Γ.filter (fun γ ↦ Z₀ ∈ γ ∧ γ.card ≤ E_tot.card + 1)), ∏ Z ∈ γ, η Z :=
          Finset.sum_le_sum_of_subset_of_nonneg hpin fun γ hγ _ ↦ by
            rcases Finset.mem_biUnion.mp hγ with ⟨_, _, hγ'⟩
            exact Finset.prod_nonneg fun Z hZ ↦
              hη_nn Z ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ').1).1 hZ)
      _ ≤ ∑ Z₀ ∈ E_tot.filter (fun Z ↦ x ∈ Z),
            ∑ γ ∈ Γ.filter (fun γ ↦ Z₀ ∈ γ ∧ γ.card ≤ E_tot.card + 1), ∏ Z ∈ γ, η Z :=
          real_sum_biUnion_le _ _ _ fun γ hγ ↦ by
            rcases Finset.mem_biUnion.mp hγ with ⟨_, _, hγ'⟩
            exact Finset.prod_nonneg fun Z hZ ↦
              hη_nn Z ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ').1).1 hZ)
      _ ≤ ∑ Z₀ ∈ E_tot.filter (fun Z ↦ x ∈ Z), unorderedTreeSum E_tot η E_tot.card Z₀ :=
          Finset.sum_le_sum fun Z₀ hZ₀ ↦
            sum_connectedPolymers_le_unorderedTreeSum E_tot hEtot_ne η hη_nn E_tot.card Z₀
              (Finset.mem_filter.mp hZ₀).1
      _ ≤ ∑ Z₀ ∈ E_tot.filter (fun Z ↦ x ∈ Z), η Z₀ * Real.exp (c * (Z₀.card : ℝ)) :=
          Finset.sum_le_sum fun Z₀ hZ₀ ↦ htree E_tot.card Z₀ (Finset.mem_filter.mp hZ₀).1
      _ ≤ c / 2 := hsite_w x
  -- Derive KP half-budget & per-polymer smallness on `closedBall 0 Λ₀'`.
  have hkp_disk : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀',
      (∀ γ ∈ Γ, ∑ δ ∈ Γ.filter (fun δ ↦ polyIncompat γ δ),
          ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ) ≤ a γ / 2) ∧
      (∀ δ ∈ Γ, ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ) ≤ 1 / 2) := by
    intro ζ hζ
    constructor
    · intro γ _
      have hbi : Γ.filter (fun δ ↦ polyIncompat γ δ) ⊆
          (polySupp γ).biUnion (fun x ↦ Γ.filter (fun δ ↦ x ∈ polySupp δ)) := by
        intro δ hδ; rcases Finset.mem_filter.mp hδ with ⟨hδΓ, hinc⟩
        rcases Finset.not_disjoint_iff.mp hinc with ⟨x, hx1, hx2⟩
        exact Finset.mem_biUnion.mpr ⟨x, hx1, Finset.mem_filter.mpr ⟨hδΓ, hx2⟩⟩
      calc ∑ δ ∈ Γ.filter (fun δ ↦ polyIncompat γ δ), ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ)
          ≤ ∑ δ ∈ (polySupp γ).biUnion (fun x ↦ Γ.filter (fun δ ↦ x ∈ polySupp δ)),
              ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hbi fun _ _ _ ↦ by positivity
        _ ≤ ∑ x ∈ polySupp γ, ∑ δ ∈ Γ.filter (fun δ ↦ x ∈ polySupp δ),
              ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ) :=
            real_sum_biUnion_le _ _ _ fun _ _ ↦ by positivity
        _ ≤ ∑ _x ∈ polySupp γ, (c / 2) := Finset.sum_le_sum fun x _ ↦ hsite_pin ζ hζ x
        _ = a γ / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp only [a]; ring
    · intro δ hδ
      rcases (mem_connectedPolymers.mp hδ).2.1 with ⟨Z, hZδ⟩
      rcases hEtot_ne Z ((mem_connectedPolymers.mp hδ).1 hZδ) with ⟨x, hxZ⟩
      have hxδ : x ∈ polySupp δ := Finset.mem_biUnion.mpr ⟨Z, hZδ, hxZ⟩
      have h1 : ‖tracePolyWeight (g_tot ζ) 1 δ‖ * Real.exp (a δ) ≤
          ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ) :=
        Finset.single_le_sum (f := fun γ ↦ ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ))
          (fun _ _ ↦ by positivity) (Finset.mem_filter.mpr ⟨hδ, hxδ⟩)
      linarith [hsite_pin ζ hζ x, hc_le]
  -- Site-by-site ratio and telescoping logarithm `L(ζ)`.
  let Zslice : ℕ → ℂ → ℂ := fun k ζ ↦ polymerZ polyIncompat (tracePolyWeight (g_tot ζ) 1) (siteSlice Γ k)
  let siteRatio : ℕ → ℂ → ℂ := fun k ζ ↦ Zslice (k + 1) ζ / Zslice k ζ
  let L : ℂ → ℂ := fun ζ ↦ ∑ k ∈ Finset.range N, Complex.log (siteRatio k ζ)
  have hZslice_ne : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ k : ℕ, Zslice k ζ ≠ 0 := by
    intro ζ hζ k
    rcases hkp_disk ζ hζ with ⟨hkp_h, hsm⟩
    exact (polymerZ_nonvanishing_and_ratio polyIncompat polyIncompat_symm
      (tracePolyWeight (g_tot ζ) 1) a ha_nn Γ hkp_h hsm (siteSlice Γ k).card
      (siteSlice Γ k) le_rfl (Finset.filter_subset _ _)).1
  have hratio_close : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ k ∈ Finset.range N,
      ‖siteRatio k ζ - 1‖ ≤ 1 / 4 := by
    intro ζ hζ k hk
    have hkN : k < N := Finset.mem_range.mp hk
    rcases hkp_disk ζ hζ with ⟨hkp_h, hsm⟩
    have hZne := hZslice_ne ζ hζ k
    have hstep := polymerZ_siteSlice_step (tracePolyWeight (g_tot ζ) 1) Γ hkN
    have hsub_eq : siteRatio k ζ - 1 =
        ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
          tracePolyWeight (g_tot ζ) 1 γ *
            (polymerZ polyIncompat (tracePolyWeight (g_tot ζ) 1)
              ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ) := by
      dsimp only [siteRatio, Zslice]
      rw [hstep, add_div, div_self hZne, add_sub_cancel_left, Finset.sum_div]
      apply Finset.sum_congr rfl; intro γ _; rw [mul_div_assoc]
    rw [hsub_eq]
    have hkp_rat := (polymerZ_nonvanishing_and_ratio polyIncompat polyIncompat_symm
      (tracePolyWeight (g_tot ζ) 1) a ha_nn Γ hkp_h hsm (siteSlice Γ k).card
      (siteSlice Γ k) le_rfl (Finset.filter_subset _ _)).2
    have hsub_pin : siteSlice Γ (k + 1) \ siteSlice Γ k ⊆ Γ.filter (fun γ ↦ (⟨k, hkN⟩ : Fin N) ∈ polySupp γ) := by
      intro γ hγ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hγ).1).1,
        mem_siteSlice_sdiff_mem_polySupp Γ hkN hγ⟩
    calc ‖∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            tracePolyWeight (g_tot ζ) 1 γ *
              (polymerZ polyIncompat (tracePolyWeight (g_tot ζ) 1)
                ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ)‖
        ≤ ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            ‖tracePolyWeight (g_tot ζ) 1 γ‖ *
              ‖polymerZ polyIncompat (tracePolyWeight (g_tot ζ) 1)
                ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ‖ := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun γ _ ↦ ?_); rw [norm_mul]
      _ ≤ ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ) :=
          Finset.sum_le_sum fun γ hγ ↦ mul_le_mul_of_nonneg_left
            (hkp_rat γ (Finset.mem_filter.mp (Finset.mem_sdiff.mp hγ).1).1) (norm_nonneg _)
      _ ≤ ∑ γ ∈ Γ.filter (fun γ ↦ (⟨k, hkN⟩ : Fin N) ∈ polySupp γ),
            ‖tracePolyWeight (g_tot ζ) 1 γ‖ * Real.exp (a γ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_pin fun _ _ _ ↦ by positivity
      _ ≤ c / 2 := hsite_pin ζ hζ ⟨k, hkN⟩
      _ ≤ 1 / 4 := by linarith [hc_le]
  -- Telescoping exponential identity: `Complex.exp (L ζ) = Z(ζ)`.
  let Zfn : ℂ → ℂ := fun ζ ↦ ∑' m : ℕ, ((m.factorial : ℂ)⁻¹ * normalizedTrace (((-β : ℂ) • H + ζ • X) ^ m))
  have hZfn_eq : ∀ ζ : ℂ, Zfn ζ = Zslice N ζ := by
    intro ζ
    have hpoly := normalizedTrace_tsum_exp_eq_polymerZ E_tot hEtot_ne (g_tot ζ) (hg_supp ζ)
    dsimp only [Zslice]
    rw [siteSlice_full, ← hpoly]
    dsimp only [Zfn]
    apply tsum_congr; intro m
    have hpow : ((-β : ℂ) • H + ζ • X) ^ m = (-(1 : ℝ) : ℂ) ^ m • (∑ Z ∈ E_tot, g_tot ζ Z) ^ m := by
      rw [hg_sum ζ]
      have hneg : (-β : ℂ) • H + ζ • X = (-(1 : ℝ) : ℂ) • ((β : ℂ) • H - ζ • X) := by
        ext i j; simp; ring
      rw [hneg, smul_pow]
    rw [hpow, normalizedTrace_smul]
    ring
  have hexp_L : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', Complex.exp (L ζ) = Zfn ζ := by
    intro ζ hζ
    rw [hZfn_eq ζ]
    dsimp only [L]
    rw [Complex.exp_sum]
    have hlog : ∀ k ∈ Finset.range N, Complex.exp (Complex.log (siteRatio k ζ)) = siteRatio k ζ := by
      intro k hk
      have hslit := (complex_log_bound_of_norm_sub_one_le (hratio_close ζ hζ k hk)).1
      exact Complex.exp_log (Complex.slitPlane_ne_zero hslit)
    rw [Finset.prod_congr rfl hlog]
    -- Telescope `∏ k < N, Zslice (k + 1) ζ / Zslice k ζ = Zslice N ζ / Zslice 0 ζ = Zslice N ζ`.
    have htel : ∀ M : ℕ, M ≤ N →
        ∏ k ∈ Finset.range M, siteRatio k ζ = Zslice M ζ / Zslice 0 ζ := by
      intro M
      induction M with
      | zero => intro _; simp [div_self (hZslice_ne ζ hζ 0)]
      | succ M ih =>
        intro hM
        rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hM)]
        dsimp only [siteRatio]
        rw [div_mul_div_comm, mul_comm (Zslice M ζ), ← div_mul_div_comm, div_self (hZslice_ne ζ hζ M), mul_one]
    have hZ0 : Zslice 0 ζ = 1 := by
      dsimp only [Zslice]; rw [siteSlice_zero hEtot_ne]
      unfold polymerZ
      rw [Finset.sum_eq_single (∅ : Finset (Polymer N))]
      · exact Finset.prod_empty
      · intro I hI hne
        exfalso; apply hne
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty] at hI
        exact hI.1
      · intro hnot; exfalso; apply hnot
        simp [isCompatPolymer]
    rw [htel N le_rfl, hZ0, div_one]
  -- Differentiability of `Zslice k` and `L` on `closedBall 0 Λ₀'`.
  have hZslice_diff : ∀ k : ℕ, Differentiable ℂ (Zslice k) := by
    intro k
    dsimp only [Zslice]
    unfold polymerZ
    refine Differentiable.fun_sum fun I _ ↦ Differentiable.fun_finset_prod fun γ _ ↦ ?_
    exact differentiable_tracePolyWeight_affine A_op B_op γ
  have hL_diffAt : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', DifferentiableAt ℂ L ζ := by
    intro ζ hζ
    dsimp only [L]
    refine DifferentiableAt.fun_sum fun k hk ↦ ?_
    have hrat_d : DifferentiableAt ℂ (siteRatio k) ζ :=
      (hZslice_diff (k + 1) ζ).div (hZslice_diff k ζ) (hZslice_ne ζ hζ k)
    exact hrat_d.clog (complex_log_bound_of_norm_sub_one_le (hratio_close ζ hζ k hk)).1
  -- Define centered holomorphic function `g(ζ) := L(ζ) - L(0) - (μ : ℂ) * ζ`.
  let g : ℂ → ℂ := fun ζ ↦ L ζ - L 0 - (μ : ℂ) * ζ
  have hg_cont : ContinuousOn g (Metric.closedBall 0 Λ₀') := by
    intro ζ hζ
    exact ((hL_diffAt ζ hζ).continuousAt.sub continuousAt_const).sub
      (continuousAt_const.mul continuousAt_id) |>.continuousWithinAt
  have hg_diff : ∀ ζ ∈ Metric.ball (0 : ℂ) Λ₀', DifferentiableAt ℂ g ζ := by
    intro ζ hζ
    have hcl := Metric.ball_subset_closedBall hζ
    exact ((hL_diffAt ζ hcl).sub (differentiableAt_const _)).sub
      ((differentiableAt_const _).mul differentiableAt_id)
  have hg0 : g 0 = 0 := by simp [g]
  -- Compute `deriv L 0 = (μ : ℂ)` via `Complex.exp (L ζ) = Zfn ζ`.
  have hZ0_eq : Zfn 0 = normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ)))) := by
    rw [trace_hermFunc_exp_eq_tsum hH (-(β : ℂ))]
    dsimp only [Zfn]
    apply tsum_congr; intro m
    rw [zero_smul, add_zero, smul_pow, normalizedTrace_smul]
    change (m.factorial : ℂ)⁻¹ * ((-(β : ℂ)) ^ m * normalizedTrace ((∑ Z ∈ E, h Z) ^ m)) = _
    ring
  have hZ0_re : Zfn 0 = (((2 : ℝ) ^ N : ℂ)⁻¹) * (gibbsPartitionFn hH β : ℂ) := by
    rw [hZ0_eq]; unfold normalizedTrace gibbsPartitionFn hermFunc
    congr 1
    have htr : Matrix.trace ((hH.eigenvectorUnitary : QubitOp N) *
        Matrix.diagonal (fun i ↦ Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ))) *
        (hH.eigenvectorUnitary : QubitOp N)ᴴ) =
        ∑ i : QubitIdx N, Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ)) := by
      have hU : (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.prop
      calc Matrix.trace ((hH.eigenvectorUnitary : QubitOp N) *
              Matrix.diagonal (fun i ↦ Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ))) *
              (hH.eigenvectorUnitary : QubitOp N)ᴴ)
          = Matrix.trace ((hH.eigenvectorUnitary : QubitOp N)ᴴ *
              ((hH.eigenvectorUnitary : QubitOp N) *
                Matrix.diagonal (fun i ↦ Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ))))) :=
            Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Matrix.diagonal (fun i ↦ Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ)))) := by
            rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
        _ = ∑ i : QubitIdx N, Complex.exp (-(β : ℂ) * (hH.eigenvalues i : ℂ)) := Matrix.trace_diagonal _
    rw [htr]; push_cast; rfl
  have hZ'0 : HasDerivAt Zfn (normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) * X)) 0 := by
    have hd := hasDerivAt_normalizedTrace_exp_affine ((-β : ℂ) • H) X
    refine hd.congr_deriv ?_
    have hsum := hasSum_hermFunc_exp hH (-(β : ℂ))
    let Ψ : QubitOp N →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M ↦ normalizedTrace (M * X)
          map_add' := fun M₁ M₂ ↦ by rw [Matrix.add_mul, normalizedTrace_add]
          map_smul' := fun α M ↦ by simp [Matrix.smul_mul, normalizedTrace_smul] }
    have hΨ := hsum.map Ψ Ψ.continuous
    have hrew : (⇑Ψ ∘ fun m : ℕ ↦ ((-(β : ℂ)) ^ m / (m.factorial : ℂ)) • (∑ Z ∈ E, h Z) ^ m) =
        fun m : ℕ ↦ (m.factorial : ℂ)⁻¹ * normalizedTrace (((-β : ℂ) • H) ^ m * X) := by
      funext m
      change normalizedTrace ((((-(β : ℂ)) ^ m / (m.factorial : ℂ)) • H ^ m) * X) = _
      rw [smul_pow, Matrix.smul_mul, Matrix.smul_mul, normalizedTrace_smul, normalizedTrace_smul]
      ring
    rw [hrew] at hΨ
    exact hΨ.tsum_eq
  have hμ_complex : (gibbsRho hH β * X).trace = (μ : ℂ) := by
    have hρ_herm : (gibbsRho hH β)ᴴ = gibbsRho hH β := by
      unfold gibbsRho
      rw [Matrix.conjTranspose_smul, hermFunc_conjTranspose]
      congr 1
      · simp [Complex.star_def, Complex.conj_ofReal]
      · congr 1; funext e; rw [Complex.star_def, Complex.conj_ofReal]
    have htr_re : (gibbsRho hH β * X).trace.im = 0 := by
      have hconj : star (gibbsRho hH β * X).trace = (gibbsRho hH β * X).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq,
          hρ_herm, Matrix.trace_mul_comm]
      exact Complex.conj_eq_iff_im.mp hconj
    exact Complex.ext rfl (by simp [htr_re])
  have hg'0 : deriv g 0 = 0 := by
    have hL0 : HasDerivAt L (deriv L 0) 0 := (hL_diffAt 0 (Metric.mem_closedBall_self hΛ_pos.le)).hasDerivAt
    have hexp_d : HasDerivAt (fun ζ : ℂ ↦ Complex.exp (L ζ)) (Complex.exp (L 0) * deriv L 0) 0 := by
      simpa [mul_comm] using hL0.cexp
    have hagree : (fun ζ : ℂ ↦ Complex.exp (L ζ)) =ᶠ[nhds 0] Zfn := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hΛ_pos] with ζ hζ
      exact hexp_L ζ hζ
    have hZ_d2 : HasDerivAt Zfn (Complex.exp (L 0) * deriv L 0) 0 := hexp_d.congr_of_eventuallyEq hagree.symm
    have heq_d : Complex.exp (L 0) * deriv L 0 =
        normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) * X) :=
      hZ_d2.unique hZ'0
    rw [hexp_L 0 (Metric.mem_closedBall_self hΛ_pos.le), hZ0_re] at heq_d
    have hZpart_pos : 0 < gibbsPartitionFn hH β := gibbsPartitionFn_pos hH β
    have hZ0_ne : (((2 : ℝ) ^ N : ℂ)⁻¹ * (gibbsPartitionFn hH β : ℂ)) ≠ 0 := by
      apply mul_ne_zero (inv_ne_zero (by positivity))
      exact Complex.ofReal_ne_zero.mpr hZpart_pos.ne'
    have hL'_eq : deriv L 0 = (μ : ℂ) := by
      rw [← hμ_complex]
      have hgibbs : gibbsRho hH β = ((gibbsPartitionFn hH β : ℂ)⁻¹) •
          hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) := by
        unfold gibbsRho; congr 1; congr 1; funext e; rw [Complex.ofReal_exp]; push_cast; rfl
      rw [hgibbs, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      apply mul_left_cancel₀ hZ0_ne
      rw [heq_d]
      unfold normalizedTrace
      have hneZ : (gibbsPartitionFn hH β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpart_pos.ne'
      field_simp [hneZ]
    have hg_d : HasDerivAt g (deriv L 0 - (μ : ℂ)) 0 := by
      have h1 : HasDerivAt (fun ζ : ℂ ↦ L ζ - L 0 - (μ : ℂ) * ζ) (deriv L 0 - 0 - (μ : ℂ) * 1) 0 :=
        (hL0.sub (hasDerivAt_const (0 : ℂ) (L 0))).sub ((hasDerivAt_id (0 : ℂ)).const_mul (μ : ℂ))
      simpa [g] using h1
    rw [hg_d.deriv, hL'_eq, sub_self]
  -- Bound `‖g ζ‖ ≤ 2 * N` on `sphere 0 Λ₀'`.
  have hμ_le : |μ| ≤ (N : ℝ) * gX := by
    have h1 : ‖(gibbsRho hH β * X).trace‖ ≤ opNorm X := norm_trace_gibbsRho_mul_le_opNorm hH β X
    have h2 : |μ| ≤ ‖(gibbsRho hH β * X).trace‖ := Complex.abs_re_le_norm _
    have h3 : opNorm X ≤ (N : ℝ) * gX := by
      dsimp only [X]
      calc opNorm (∑ Z ∈ E_X, xOp Z) ≤ ∑ Z ∈ E_X, opNorm (xOp Z) := opNorm_sum_le E_X xOp
        _ ≤ ∑ x : Fin N, ∑ Z ∈ E_X.filter (fun Z ↦ x ∈ Z), opNorm (xOp Z) := by
            have hsub : E_X ⊆ Finset.univ.biUnion (fun x : Fin N ↦ E_X.filter (fun Z ↦ x ∈ Z)) := by
              intro Z hZ; rcases hEX_ne Z hZ with ⟨x, hxZ⟩
              exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, Finset.mem_filter.mpr ⟨hZ, hxZ⟩⟩
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ opNorm_nonneg _)
              (real_sum_biUnion_le _ _ _ fun _ _ ↦ opNorm_nonneg _)
        _ ≤ ∑ _x : Fin N, gX := Finset.sum_le_sum fun x _ ↦ hX_site x
        _ = (N : ℝ) * gX := by simp
    exact le_trans h2 (le_trans h1 h3)
  have hL_norm : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ‖L ζ‖ ≤ (2 / 3) * (N : ℝ) := by
    intro ζ hζ
    dsimp only [L]
    calc ‖∑ k ∈ Finset.range N, Complex.log (siteRatio k ζ)‖
        ≤ ∑ k ∈ Finset.range N, ‖Complex.log (siteRatio k ζ)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (2 / 3 : ℝ) :=
          Finset.sum_le_sum fun k hk ↦ (complex_log_bound_of_norm_sub_one_le (hratio_close ζ hζ k hk)).2
      _ = (2 / 3) * (N : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hg_bdd : ∀ ζ ∈ Metric.sphere (0 : ℂ) Λ₀', ‖g ζ‖ ≤ 2 * (N : ℝ) := by
    intro ζ hζ
    have hcl := Metric.sphere_subset_closedBall hζ
    rw [Metric.mem_sphere, dist_zero_right] at hζ
    have hμΛ : |μ| * Λ₀' ≤ (N : ℝ) / 16 := by
      have h1 : gX * Λ₀' ≤ 1 / 16 := by
        have heq : gX * Λ₀' = 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ))) := by
          dsimp only [Λ₀']; field_simp [hgX.ne', hkr_pos.ne', (Real.exp_pos _).ne']
        rw [heq, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hkr1 : (1 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (by omega : 1 ≤ kr)
        have hexp1 : (1 : ℝ) ≤ Real.exp (1 + (kr : ℝ) / (r : ℝ)) := Real.one_le_exp (by positivity)
        nlinarith
      calc |μ| * Λ₀' ≤ ((N : ℝ) * gX) * Λ₀' := mul_le_mul_of_nonneg_right hμ_le hΛ_pos.le
        _ = (N : ℝ) * (gX * Λ₀') := by ring
        _ ≤ (N : ℝ) * (1 / 16) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)
        _ = (N : ℝ) / 16 := by ring
    dsimp only [g]
    calc ‖L ζ - L 0 - (μ : ℂ) * ζ‖
        ≤ ‖L ζ - L 0‖ + ‖(μ : ℂ) * ζ‖ := norm_sub_le _ _
      _ ≤ (‖L ζ‖ + ‖L 0‖) + ‖(μ : ℂ)‖ * ‖ζ‖ := by
          rw [norm_mul]; exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ((2 / 3) * (N : ℝ) + (2 / 3) * (N : ℝ)) + |μ| * Λ₀' := by
          rw [Complex.norm_real, Real.norm_eq_abs, hζ]
          exact add_le_add (add_le_add (hL_norm ζ hcl) (hL_norm 0 (Metric.mem_closedBall_self hΛ_pos.le))) le_rfl
      _ ≤ 2 * (N : ℝ) := by linarith
  -- Apply `cauchy_order2_schwarz_bound` at `w = (lam : ℂ)`!
  have hschwarz := cauchy_order2_schwarz_bound hΛ_pos (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
    g hg_cont hg_diff hg0 hg'0 hg_bdd (lam : ℂ)
    (by rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hlam)
  -- Connect `(g (lam : ℂ)).re` to `Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β)`.
  let K₀ : QubitOp N := ((-β : ℝ) : ℂ) • H + ((lam : ℝ) : ℂ) • X
  have hK₀ : K₀.IsHermitian := by
    simp only [K₀, H, X, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, hH.eq, hX.eq]
  have hZlam_re : Zfn (lam : ℂ) = (((2 : ℝ) ^ N : ℂ)⁻¹) * (gibbsPartitionFn hK₀ (-1) : ℂ) := by
    have h1 := trace_hermFunc_exp_eq_tsum hK₀ (1 : ℂ)
    have h2 : Zfn (lam : ℂ) = normalizedTrace (hermFunc hK₀ (fun e ↦ Complex.exp ((1 : ℂ) * (e : ℂ)))) := by
      rw [h1]; dsimp only [Zfn, K₀]
      apply tsum_congr; intro m; simp
    rw [h2]; unfold normalizedTrace gibbsPartitionFn hermFunc
    congr 1
    have hU : (hK₀.eigenvectorUnitary : QubitOp N)ᴴ * (hK₀.eigenvectorUnitary : QubitOp N) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hK₀.eigenvectorUnitary.prop
    calc Matrix.trace ((hK₀.eigenvectorUnitary : QubitOp N) *
            Matrix.diagonal (fun i ↦ Complex.exp ((1 : ℂ) * (hK₀.eigenvalues i : ℂ))) *
            (hK₀.eigenvectorUnitary : QubitOp N)ᴴ)
        = Matrix.trace ((hK₀.eigenvectorUnitary : QubitOp N)ᴴ *
            ((hK₀.eigenvectorUnitary : QubitOp N) *
              Matrix.diagonal (fun i ↦ Complex.exp ((1 : ℂ) * (hK₀.eigenvalues i : ℂ))))) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Matrix.diagonal (fun i ↦ Complex.exp ((1 : ℂ) * (hK₀.eigenvalues i : ℂ)))) := by
          rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
      _ = ∑ i : QubitIdx N, Complex.exp ((1 : ℂ) * (hK₀.eigenvalues i : ℂ)) := Matrix.trace_diagonal _
      _ = ((∑ i : QubitIdx N, Real.exp (-(-1 : ℝ) * hK₀.eigenvalues i) : ℝ) : ℂ) := by
          push_cast; apply Finset.sum_congr rfl; intro i _; congr 1; simp
  have hK_part : gibbsPartitionFn hK (-1) = Real.exp (-lam * μ) * gibbsPartitionFn hK₀ (-1) := by
    -- `exp(K) = exp(-lam * μ) • exp(K₀)` since `K = K₀ + (-lam * μ) • 1`.
    have hK_eq : K = K₀ + ((-lam * μ : ℝ) : ℂ) • (1 : QubitOp N) := by
      dsimp only [K, K₀, Xtilde]
      rw [smul_sub, smul_smul]; push_cast; rw [sub_eq_add_neg, neg_smul, ← add_assoc]
      congr 2; ext i j; simp
    have hexp_shift : hermFunc hK (fun e ↦ Complex.exp (e : ℂ)) =
        (Complex.exp ((-lam * μ : ℝ) : ℂ)) • hermFunc hK₀ (fun e ↦ Complex.exp (e : ℂ)) := by
      have h1 := hasSum_hermFunc_exp hK (1 : ℂ)
      have h2 := hasSum_hermFunc_exp hK₀ (1 : ℂ)
      -- Compare traces via `Matrix.exp` / Cauchy product of `exp(K₀)` and `exp((-lam * μ) • 1)`.
      -- Direct eigenspace proof: `hK₀` eigenvectors are eigenvectors of `K = K₀ + c • 1` with eigenvalue `e_i + c`!
      set U := (hK₀.eigenvectorUnitary : QubitOp N)
      have hUUH : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hK₀.eigenvectorUnitary.prop
      have hUHU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hK₀.eigenvectorUnitary.prop
      have hK_diag : K = U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) * Uᴴ := by
        have h1_eq : (1 : QubitOp N) = U * (1 : QubitOp N) * Uᴴ := by rw [Matrix.mul_one, hUUH]
        have hK₀_eq : K₀ = U * Matrix.diagonal (fun i ↦ (hK₀.eigenvalues i : ℂ)) * Uᴴ :=
          (hermFunc_id hK₀).symm
        have hD : Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) =
            Matrix.diagonal (fun i ↦ (hK₀.eigenvalues i : ℂ)) + ((-lam * μ : ℝ) : ℂ) • (1 : QubitOp N) := by
          ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;> simp
        rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← hK₀_eq, ← h1_eq, ← hK_eq]
      have hpow_K : ∀ m : ℕ, K ^ m = U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) * Uᴴ := by
        intro m
        induction m with
        | zero => simp [hUUH]
        | succ m ih =>
          rw [pow_succ, ih, hK_diag]
          calc U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) * Uᴴ *
                (U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) * Uᴴ)
              = U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) *
                  (Uᴴ * U) * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) * Uᴴ := by
                simp only [Matrix.mul_assoc]
            _ = U * (Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) *
                  Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ))) * Uᴴ := by
                rw [hUHU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ (m + 1)) * Uᴴ := by
                rw [Matrix.diagonal_mul_diagonal]
                simp_rw [← pow_succ]
      have hsum_K : HasSum (fun m : ℕ ↦ ((1 : ℂ) ^ m / (m.factorial : ℂ)) • K ^ m)
          (U * Matrix.diagonal (fun i ↦ Complex.exp ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) * Uᴴ) := by
        have hdiag_sum : HasSum
            (fun m : ℕ ↦ Matrix.diagonal (fun i : QubitIdx N ↦
              ((1 : ℂ) ^ m / (m.factorial : ℂ)) * ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m))
            (Matrix.diagonal (fun i : QubitIdx N ↦ Complex.exp ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ))) := by
          have hvec : HasSum
              (fun m : ℕ ↦ (fun i : QubitIdx N ↦
                ((1 : ℂ) ^ m / (m.factorial : ℂ)) * ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m))
              (fun i : QubitIdx N ↦ Complex.exp ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) := by
            rw [Pi.hasSum]; intro a
            simp only [one_pow, one_div]
            have hce := NormedSpace.expSeries_div_hasSum_exp (((hK₀.eigenvalues a + (-lam * μ) : ℝ) : ℂ))
            rw [← Complex.exp_eq_exp_ℂ] at hce
            simpa [div_eq_inv_mul, mul_comm] using hce
          let Dmap : (QubitIdx N → ℂ) →L[ℂ] QubitOp N :=
            LinearMap.toContinuousLinearMap
              { toFun := Matrix.diagonal
                map_add' := fun v w ↦ by ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
                map_smul' := fun c v ↦ by ext i j; simp [Matrix.diagonal_apply] }
          exact hvec.map Dmap Dmap.continuous
        let Lmul : QubitOp N →L[ℂ] QubitOp N :=
          LinearMap.toContinuousLinearMap
            { toFun := fun M ↦ U * M * Uᴴ
              map_add' := fun M₁ M₂ ↦ by rw [Matrix.mul_add, Matrix.add_mul]
              map_smul' := fun c M ↦ by simp [Matrix.mul_smul, Matrix.smul_mul] }
        have hL := hdiag_sum.map Lmul Lmul.continuous
        convert hL using 1
        · funext m; rw [hpow_K m]
          change ((1 : ℂ) ^ m / (m.factorial : ℂ)) • (U * Matrix.diagonal (fun i ↦ ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) * Uᴴ) =
            U * Matrix.diagonal (fun i ↦ ((1 : ℂ) ^ m / (m.factorial : ℂ)) * ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ) ^ m) * Uᴴ
          ext a b
          simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
            Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro k _
          split_ifs <;> ring
        · rfl
      have heq_mat : hermFunc hK (fun e ↦ Complex.exp ((1 : ℂ) * (e : ℂ))) =
          U * Matrix.diagonal (fun i ↦ Complex.exp ((hK₀.eigenvalues i + (-lam * μ) : ℝ) : ℂ)) * Uᴴ :=
        h1.unique hsum_K
      have heq_f : (fun e : ℝ ↦ Complex.exp (e : ℂ)) = fun e : ℝ ↦ Complex.exp ((1 : ℂ) * (e : ℂ)) := by
        funext e; simp
      rw [heq_f, heq_mat]
      unfold hermFunc
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro k _
      split_ifs
      · push_cast; rw [Complex.exp_add]; simp only [one_mul]; ring
      · ring
    have htrK : (hermFunc hK (fun e ↦ Complex.exp (e : ℂ))).trace = (gibbsPartitionFn hK (-1) : ℂ) := by
      unfold gibbsPartitionFn hermFunc
      have hU : (hK.eigenvectorUnitary : QubitOp N)ᴴ * (hK.eigenvectorUnitary : QubitOp N) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hK.eigenvectorUnitary.prop
      calc Matrix.trace ((hK.eigenvectorUnitary : QubitOp N) *
              Matrix.diagonal (fun i ↦ Complex.exp (hK.eigenvalues i : ℂ)) *
              (hK.eigenvectorUnitary : QubitOp N)ᴴ)
          = Matrix.trace ((hK.eigenvectorUnitary : QubitOp N)ᴴ *
              ((hK.eigenvectorUnitary : QubitOp N) *
                Matrix.diagonal (fun i ↦ Complex.exp (hK.eigenvalues i : ℂ)))) :=
            Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Matrix.diagonal (fun i ↦ Complex.exp (hK.eigenvalues i : ℂ))) := by
            rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
        _ = ∑ i : QubitIdx N, Complex.exp (hK.eigenvalues i : ℂ) := Matrix.trace_diagonal _
        _ = ((∑ i : QubitIdx N, Real.exp (-(-1 : ℝ) * hK.eigenvalues i) : ℝ) : ℂ) := by
            push_cast; apply Finset.sum_congr rfl; intro i _; congr 1; simp
    have htrK₀ : (hermFunc hK₀ (fun e ↦ Complex.exp (e : ℂ))).trace = (gibbsPartitionFn hK₀ (-1) : ℂ) := by
      unfold gibbsPartitionFn hermFunc
      have hU : (hK₀.eigenvectorUnitary : QubitOp N)ᴴ * (hK₀.eigenvectorUnitary : QubitOp N) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hK₀.eigenvectorUnitary.prop
      calc Matrix.trace ((hK₀.eigenvectorUnitary : QubitOp N) *
              Matrix.diagonal (fun i ↦ Complex.exp (hK₀.eigenvalues i : ℂ)) *
              (hK₀.eigenvectorUnitary : QubitOp N)ᴴ)
          = Matrix.trace ((hK₀.eigenvectorUnitary : QubitOp N)ᴴ *
              ((hK₀.eigenvectorUnitary : QubitOp N) *
                Matrix.diagonal (fun i ↦ Complex.exp (hK₀.eigenvalues i : ℂ)))) :=
            Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Matrix.diagonal (fun i ↦ Complex.exp (hK₀.eigenvalues i : ℂ))) := by
            rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
        _ = ∑ i : QubitIdx N, Complex.exp (hK₀.eigenvalues i : ℂ) := Matrix.trace_diagonal _
        _ = ((∑ i : QubitIdx N, Real.exp (-(-1 : ℝ) * hK₀.eigenvalues i) : ℝ) : ℂ) := by
            push_cast; apply Finset.sum_congr rfl; intro i _; congr 1; simp
    have htr_eq := congrArg Matrix.trace hexp_shift
    rw [Matrix.trace_smul, smul_eq_mul, htrK, htrK₀, ← Complex.ofReal_exp] at htr_eq
    have hre := congrArg Complex.re htr_eq
    simpa [← Complex.ofReal_exp] using hre
  -- Now relate `Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β)` to `(g (lam : ℂ)).re`!
  have hlam_mem : (lam : ℂ) ∈ Metric.closedBall (0 : ℂ) Λ₀' := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hexp_diff : Complex.exp (L (lam : ℂ) - L 0) =
      ((gibbsPartitionFn hK₀ (-1) / gibbsPartitionFn hH β : ℝ) : ℂ) := by
    rw [Complex.exp_sub, hexp_L (lam : ℂ) hlam_mem, hexp_L 0 (Metric.mem_closedBall_self hΛ_pos.le),
      hZlam_re, hZ0_re]
    have h2ne : (((2 : ℝ) ^ N : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by positivity)
    rw [mul_div_mul_left _ _ h2ne]; push_cast; rfl
  have hnorm_exp : Real.exp (L (lam : ℂ) - L 0).re = gibbsPartitionFn hK₀ (-1) / gibbsPartitionFn hH β := by
    have h1 := congrArg (fun z : ℂ ↦ ‖z‖) hexp_diff
    rw [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (gibbsPartitionFn_pos hK₀ (-1)) (gibbsPartitionFn_pos hH β))] at h1
    exact h1
  have hlog_eq : Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) = (g (lam : ℂ)).re := by
    rw [hK_part, mul_div_assoc, Real.log_mul (Real.exp_pos _).ne'
      (div_pos (gibbsPartitionFn_pos hK₀ (-1)) (gibbsPartitionFn_pos hH β)).ne',
      Real.log_exp, ← hnorm_exp, Real.log_exp]
    dsimp only [g]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hlog_eq]
  have hre_le : (g (lam : ℂ)).re ≤ ‖g (lam : ℂ)‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  refine le_trans hre_le (le_trans hschwarz ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  have hnn : 0 ≤ (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := by positivity
  calc 2 * (2 * (N : ℝ)) * (lam ^ 2 / (Λ₀') ^ 2)
      = 4 * ((N : ℝ) * lam ^ 2 / (Λ₀') ^ 2) := by ring
    _ ≤ 8 * ((N : ℝ) * lam ^ 2 / (Λ₀') ^ 2) := by linarith
    _ = 8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := by ring

end TraceCumulantMain

end KrylovChaos
