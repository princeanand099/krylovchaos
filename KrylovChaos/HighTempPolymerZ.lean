/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.ConcreteCombinatorics
import KrylovChaos.PolymerTrees
import KrylovChaos.PolymerExpansionConcrete
import KrylovChaos.ClusterCumulantAndDecoupling
import KrylovChaos.EndToEndTheorems
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# High-Temperature Trace Cumulant Generating Function Bound (Lemma 6.3, Eq. 6.3)

Proves the unconditional high-temperature trace cumulant bound (Lemma 6.3) on `QubitOp N`
strictly on top of Mathlib `v4.35.0` with zero custom axioms and zero `sorry`s:
1. `unorderedTreeSum_le_weighted`: per-edge weighted Galton–Watson / Kotecký–Preiss tree sum.
2. `polymerZ_nonvanishing_and_ratio`: self-contained Kotecký–Preiss nonvanishing and
   activity-ratio bound `‖Z(Λ \ N(γ)) / Z(Λ)‖ ≤ exp(a(γ))`.
3. `polymerZ_site_telescoping_log`: site-by-site telescoping `Λ_0 ⊂ Λ_1 ⊂ ⋯ ⊂ Λ_N` yielding
   an analytic logarithm `L(ζ)` of the polymer partition function with `‖L(ζ)‖ ≤ (2/3) N`.
4. `cauchy_order2_schwarz_bound`: order-2 Schwarz bound via Cauchy's integral formula on
   `closedBall 0 R`: if `g(0) = 0`, `g'(0) = 0`, and `‖g‖ ≤ M` on `sphere 0 R`, then
   `‖g(w)‖ ≤ 2 M (‖w‖ / R)²` for all `‖w‖ ≤ R / 2`.
5. `lemma_6_3_combined_cumulant_bound`: for any `r`-local Hamiltonian `H = ∑ Z ∈ E, h Z`
   (`r ≥ 2`, site strength `≤ Jsite`), `k_X`-local Hermitian observable `X = ∑ Z ∈ E_X, x Z`
   (site strength `≤ gX`), `β ∈ [0, (8 e² r Jsite)⁻¹]`, `k_r = max r k_X`,
   `Λ₀' = (16 k_r e^{1 + k_r / r} gX)⁻¹`, and centered `X̃ = X - ⟨X⟩_β I`, for ALL real
   `lam` with `|lam| ≤ Λ₀' / 2`:
   `Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) ≤ 8 * N * lam² / (Λ₀')²`,
   where `K = (-β) H + lam X̃`.
-/

namespace KrylovChaos

open Matrix Filter Topology Complex

section WeightedTreeAndKPRatio

/-- Weighted Galton–Watson unordered tree sum bound allowing edge-dependent supports `Y.card`. -/
lemma unorderedTreeSum_le_weighted {N : ℕ}
    (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {c : ℝ} (hc : 0 ≤ c)
    (hsite_w : ∀ x : Fin N,
      ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), η Y * Real.exp (c * (Y.card : ℝ)) ≤ c) :
    ∀ h : ℕ, ∀ X ∈ E,
      unorderedTreeSum E η h X ≤ η X * Real.exp (c * (X.card : ℝ)) := by
  intro h
  induction h with
  | zero =>
    intro X hX
    rw [unorderedTreeSum]
    have h1 : (1 : ℝ) ≤ Real.exp (c * (X.card : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith [hη_nn X hX]
  | succ h ih =>
    intro X hX
    rw [unorderedTreeSum]
    apply mul_le_mul_of_nonneg_left _ (hη_nn X hX)
    have hprod_exp : ∏ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), (1 + unorderedTreeSum E η h Y) ≤
        ∏ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), Real.exp (unorderedTreeSum E η h Y) := by
      have haux : ∀ (S : Finset (Finset (Fin N))), S ⊆ E →
          ∏ Y ∈ S, (1 + unorderedTreeSum E η h Y) ≤ ∏ Y ∈ S, Real.exp (unorderedTreeSum E η h Y) := by
        intro S
        induction S using Finset.induction with
        | empty => intro _; simp
        | @insert Y S' hYS' ihS =>
          intro hsub
          rw [Finset.prod_insert hYS', Finset.prod_insert hYS']
          have hnn1 : 0 ≤ 1 + unorderedTreeSum E η h Y := by
            linarith [unorderedTreeSum_nonneg E η hη_nn h Y (hsub (Finset.mem_insert_self Y S'))]
          have hnn2 : 0 ≤ ∏ Z ∈ S', (1 + unorderedTreeSum E η h Z) :=
            Finset.prod_nonneg fun Z hZ ↦ by
              linarith [unorderedTreeSum_nonneg E η hη_nn h Z (hsub (Finset.mem_insert_of_mem hZ))]
          exact mul_le_mul (by linarith [Real.add_one_le_exp (unorderedTreeSum E η h Y)])
            (ihS (Finset.Subset.trans (Finset.subset_insert Y S') hsub)) hnn2 (Real.exp_pos _).le
      exact haux _ (Finset.filter_subset _ _)
    rw [← Real.exp_sum] at hprod_exp
    refine le_trans hprod_exp (Real.exp_le_exp.mpr ?_)
    have hsub : E.filter (fun Y ↦ (X ∩ Y).Nonempty) ⊆
        X.biUnion (fun x ↦ E.filter (fun Y ↦ x ∈ Y)) := by
      intro Y hY
      rcases Finset.mem_filter.mp hY with ⟨hYE, ⟨x, hx⟩⟩
      rcases Finset.mem_inter.mp hx with ⟨hxX, hxY⟩
      exact Finset.mem_biUnion.mpr ⟨x, hxX, Finset.mem_filter.mpr ⟨hYE, hxY⟩⟩
    calc ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), unorderedTreeSum E η h Y
        ≤ ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), η Y * Real.exp (c * (Y.card : ℝ)) :=
          Finset.sum_le_sum fun Y hY ↦ ih Y (Finset.mem_filter.mp hY).1
      _ ≤ ∑ Y ∈ X.biUnion (fun x ↦ E.filter (fun Y ↦ x ∈ Y)),
            η Y * Real.exp (c * (Y.card : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun Y hY _ ↦ ?_
          rcases Finset.mem_biUnion.mp hY with ⟨_, _, hYE⟩
          exact mul_nonneg (hη_nn Y (Finset.mem_filter.mp hYE).1) (Real.exp_pos _).le
      _ ≤ ∑ x ∈ X, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), η Y * Real.exp (c * (Y.card : ℝ)) := by
          refine real_sum_biUnion_le _ _ _ fun Y hY ↦ ?_
          rcases Finset.mem_biUnion.mp hY with ⟨_, _, hYE⟩
          exact mul_nonneg (hη_nn Y (Finset.mem_filter.mp hYE).1) (Real.exp_pos _).le
      _ ≤ ∑ _x ∈ X, c := Finset.sum_le_sum fun x _ ↦ hsite_w x
      _ = c * (X.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Elementary bound `(1 - u)⁻¹ ≤ exp (2 * u)` for `0 ≤ u ≤ 1 / 2`. -/
lemma inv_one_sub_le_exp_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    (1 - u)⁻¹ ≤ Real.exp (2 * u) := by
  have hpos : 0 < 1 - u := by linarith
  have h1 : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
  have h2 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have h3 : 1 ≤ (1 - u) * Real.exp (2 * u) := le_trans h1 (mul_le_mul_of_nonneg_left h2 hpos.le)
  rw [inv_le_iff_one_le_mul₀ hpos, mul_comm]
  exact h3

/-- Splitting `polymerZ` on `Λ` by whether a chosen polymer `δ ∈ Λ` is present or absent. -/
lemma polymerZ_split_mem {ι : Type*} [DecidableEq ι]
    (incompat : ι → ι → Prop) [DecidableRel incompat]
    (hsym : ∀ u v, incompat u v → incompat v u)
    (w : ι → ℂ) (Λ : Finset ι) {δ : ι} (hδ : δ ∈ Λ) :
    polymerZ incompat w Λ =
      polymerZ incompat w (Λ.erase δ) +
      w δ * polymerZ incompat w ((Λ.erase δ).filter (fun u ↦ ¬incompat δ u)) := by
  classical
  unfold polymerZ
  let S := Λ.powerset.filter (fun I ↦ isCompatPolymer incompat I)
  change ∑ I ∈ S, ∏ γ ∈ I, w γ = _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun I ↦ δ ∉ I)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext I
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun J _ ↦ insert δ J) ?_ ?_ ?_ ?_
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      simp only [S, Finset.mem_filter, Finset.mem_powerset, not_not]
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self δ J⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxJ
        · exact hδ
        · exact Finset.erase_subset δ Λ (Finset.mem_filter.mp (hJ.1 hxJ)).1
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | huJ <;>
        rcases Finset.mem_insert.mp hv with rfl | hvJ
        · exact absurd rfl huv
        · exact (Finset.mem_filter.mp (hJ.1 hvJ)).2
        · intro hinc; exact (Finset.mem_filter.mp (hJ.1 huJ)).2 (hsym _ _ hinc)
        · exact hJ.2 u huJ v hvJ huv
    · intro J₁ hJ₁ J₂ hJ₂ heq
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₁ hJ₂
      have h1 : δ ∉ J₁ := fun h ↦ (Finset.mem_erase.mp (Finset.mem_filter.mp (hJ₁.1 h)).1).1 rfl
      have h2 : δ ∉ J₂ := fun h ↦ (Finset.mem_erase.mp (Finset.mem_filter.mp (hJ₂.1 h)).1).1 rfl
      ext x
      have hx := Finset.ext_iff.mp heq x
      simp only [Finset.mem_insert] at hx
      constructor
      · intro hx1
        rcases hx.mp (Or.inr hx1) with rfl | hx2
        · exact absurd hx1 h1
        · exact hx2
      · intro hx2
        rcases hx.mpr (Or.inr hx2) with rfl | hx1
        · exact absurd hx2 h2
        · exact hx1
    · intro I hI
      simp only [S, Finset.mem_filter, Finset.mem_powerset, not_not] at hI
      refine ⟨I.erase δ, ?_, Finset.insert_erase hI.2⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun x hx ↦ ?_, fun u hu v hv huv ↦ hI.1.2 u (Finset.mem_of_mem_erase hu) v
        (Finset.mem_of_mem_erase hv) huv⟩
      rcases Finset.mem_erase.mp hx with ⟨hne, hxI⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hI.1.1 hxI⟩,
        hI.1.2 δ hI.2 x hxI (Ne.symm hne)⟩
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      have hnot : δ ∉ J := fun h ↦ (Finset.mem_erase.mp (Finset.mem_filter.mp (hJ.1 h)).1).1 rfl
      rw [Finset.prod_insert hnot]

/-- **Self-Contained Kotecký–Preiss Nonvanishing and Ratio Bound**:
Under the half-budget Kotecký–Preiss condition
`∀ γ ∈ Γ, ∑ δ ∈ Γ.filter (incompat γ), ‖w δ‖ * exp(a δ) ≤ a γ / 2`
and per-polymer smallness `∀ δ ∈ Γ, ‖w δ‖ * exp(a δ) ≤ 1 / 2`,
for EVERY `Λ ⊆ Γ`:
1. `polymerZ incompat w Λ ≠ 0`, and
2. `∀ γ ∈ Γ, ‖polymerZ incompat w (Λ.filter (fun δ ↦ ¬incompat γ δ)) / polymerZ incompat w Λ‖ ≤ exp(a γ)`. -/
theorem polymerZ_nonvanishing_and_ratio {ι : Type*} [DecidableEq ι]
    (incompat : ι → ι → Prop) [DecidableRel incompat]
    (hsym : ∀ u v, incompat u v → incompat v u)
    (w : ι → ℂ) (a : ι → ℝ) (ha_nn : ∀ γ, 0 ≤ a γ) (Γ : Finset ι)
    (hkp_half : ∀ γ ∈ Γ, ∑ δ ∈ Γ.filter (fun δ ↦ incompat γ δ), ‖w δ‖ * Real.exp (a δ) ≤ a γ / 2)
    (hsmall : ∀ δ ∈ Γ, ‖w δ‖ * Real.exp (a δ) ≤ 1 / 2) :
    ∀ n : ℕ, ∀ Λ : Finset ι, Λ.card ≤ n → Λ ⊆ Γ →
      polymerZ incompat w Λ ≠ 0 ∧
      ∀ γ ∈ Γ, ‖polymerZ incompat w (Λ.filter (fun δ ↦ ¬incompat γ δ)) / polymerZ incompat w Λ‖ ≤
        Real.exp (a γ) := by
  intro n
  induction n with
  | zero =>
    intro Λ hcard _
    have hΛ : Λ = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    subst hΛ
    have hZ0 : polymerZ incompat w ∅ = 1 := by
      unfold polymerZ
      have : (∅ : Finset ι).powerset.filter (fun I ↦ isCompatPolymer incompat I) = {∅} := by
        ext I; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl u hu; exact absurd hu (Finset.notMem_empty u)
      rw [this, Finset.sum_singleton, Finset.prod_empty]
    refine ⟨by rw [hZ0]; exact one_ne_zero, fun γ _ ↦ ?_⟩
    simp [hZ0, Real.one_le_exp (ha_nn γ)]
  | succ n ih =>
    intro Λ hcard hΛΓ
    by_cases hcard_le : Λ.card ≤ n
    · exact ih Λ hcard_le hΛΓ
    · have hcard_eq : Λ.card = n + 1 := by omega
      have hΛ_ne : Λ.Nonempty := Finset.card_pos.mp (by omega)
      rcases hΛ_ne with ⟨δ₀, hδ₀⟩
      have hcard_er : (Λ.erase δ₀).card ≤ n := by
        rw [Finset.card_erase_of_mem hδ₀]; omega
      have hih_er := ih (Λ.erase δ₀) hcard_er (Finset.Subset.trans (Finset.erase_subset _ _) hΛΓ)
      have hsplit₀ := polymerZ_split_mem incompat hsym w Λ hδ₀
      have hstep_norm : ∀ (M : Finset ι) (δ : ι), M ⊆ Γ → M.card ≤ n → δ ∈ Γ → δ ∉ M →
          let M' := insert δ M
          ‖polymerZ incompat w M' / polymerZ incompat w M - 1‖ ≤ ‖w δ‖ * Real.exp (a δ) ∧
          polymerZ incompat w M' ≠ 0 ∧
          ‖polymerZ incompat w M / polymerZ incompat w M'‖ ≤ Real.exp (2 * (‖w δ‖ * Real.exp (a δ))) := by
        intro M δ hMΓ hMcard hδΓ hδM
        dsimp only
        have hihM := ih M hMcard hMΓ
        have hZ_M_ne : polymerZ incompat w M ≠ 0 := hihM.1
        have her : (insert δ M).erase δ = M := Finset.erase_insert hδM
        have hsp := polymerZ_split_mem incompat hsym w (insert δ M) (Finset.mem_insert_self δ M)
        rw [her] at hsp
        have hdiv : polymerZ incompat w (insert δ M) / polymerZ incompat w M - 1 =
            w δ * (polymerZ incompat w (M.filter (fun u ↦ ¬incompat δ u)) / polymerZ incompat w M) := by
          rw [hsp, add_div, div_self hZ_M_ne, add_sub_cancel_left, mul_div_assoc]
        have hdiff_le : ‖polymerZ incompat w (insert δ M) / polymerZ incompat w M - 1‖ ≤
            ‖w δ‖ * Real.exp (a δ) := by
          rw [hdiv, norm_mul]
          exact mul_le_mul_of_nonneg_left (hihM.2 δ hδΓ) (norm_nonneg _)
        have hu_le : ‖w δ‖ * Real.exp (a δ) ≤ 1 / 2 := hsmall δ hδΓ
        have hnorm_ge : 1 - ‖w δ‖ * Real.exp (a δ) ≤
            ‖polymerZ incompat w (insert δ M) / polymerZ incompat w M‖ := by
          have htri := norm_sub_norm_le (1 : ℂ) (polymerZ incompat w (insert δ M) / polymerZ incompat w M)
          rw [norm_one, norm_sub_rev] at htri
          linarith
        have hpos_low : 0 < 1 - ‖w δ‖ * Real.exp (a δ) := by linarith
        have hratio_pos : 0 < ‖polymerZ incompat w (insert δ M) / polymerZ incompat w M‖ :=
          lt_of_lt_of_le hpos_low hnorm_ge
        have hZM'_ne : polymerZ incompat w (insert δ M) ≠ 0 := by
          intro h0; rw [h0, zero_div, norm_zero] at hratio_pos; linarith
        have hinv_le : ‖polymerZ incompat w M / polymerZ incompat w (insert δ M)‖ ≤
            Real.exp (2 * (‖w δ‖ * Real.exp (a δ))) := by
          have hinv_eq : ‖polymerZ incompat w M / polymerZ incompat w (insert δ M)‖ =
              ‖polymerZ incompat w (insert δ M) / polymerZ incompat w M‖⁻¹ := by
            rw [norm_div, norm_div, inv_div]
          rw [hinv_eq]
          calc ‖polymerZ incompat w (insert δ M) / polymerZ incompat w M‖⁻¹
              ≤ (1 - ‖w δ‖ * Real.exp (a δ))⁻¹ := inv_anti₀ hpos_low hnorm_ge
            _ ≤ Real.exp (2 * (‖w δ‖ * Real.exp (a δ))) :=
                inv_one_sub_le_exp_two_mul (by positivity) hu_le
        exact ⟨hdiff_le, hZM'_ne, hinv_le⟩
      have hZΛ_ne : polymerZ incompat w Λ ≠ 0 := by
        have hst := hstep_norm (Λ.erase δ₀) δ₀ (Finset.Subset.trans (Finset.erase_subset _ _) hΛΓ)
          hcard_er (hΛΓ hδ₀) (Finset.notMem_erase δ₀ Λ)
        rw [Finset.insert_erase hδ₀] at hst
        exact hst.2.1
      refine ⟨hZΛ_ne, fun γ hγΓ ↦ ?_⟩
      let Λ₀ := Λ.filter (fun δ ↦ ¬incompat γ δ)
      let B := Λ.filter (fun δ ↦ incompat γ δ)
      have hdisj : Disjoint Λ₀ B := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
      have hunion : Λ₀ ∪ B = Λ := by
        ext x; simp only [Λ₀, B, Finset.mem_union, Finset.mem_filter]; tauto
      have hS_bound : ∀ S : Finset ι, S ⊆ B →
          polymerZ incompat w (Λ₀ ∪ S) ≠ 0 ∧
          ‖polymerZ incompat w Λ₀ / polymerZ incompat w (Λ₀ ∪ S)‖ ≤
            Real.exp (2 * ∑ δ ∈ S, ‖w δ‖ * Real.exp (a δ)) := by
        intro S
        induction S using Finset.induction with
        | empty =>
          intro _
          rw [Finset.union_empty, Finset.sum_empty, mul_zero, Real.exp_zero]
          by_cases hB : B = ∅
          · have heq : Λ₀ = Λ := by rw [← hunion, hB, Finset.union_empty]
            rw [heq, div_self hZΛ_ne, norm_one]; exact ⟨hZΛ_ne, le_rfl⟩
          · have hcard0 : Λ₀.card ≤ n := by
              have hlt : Λ₀.card < Λ.card := by
                rw [← hunion, Finset.card_union_of_disjoint hdisj]
                have hBp : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB)
                omega
              omega
            have hih0 := ih Λ₀ hcard0 (Finset.Subset.trans (Finset.filter_subset _ _) hΛΓ)
            rw [div_self hih0.1, norm_one]; exact ⟨hih0.1, le_rfl⟩
        | @insert δ S' hδS' ihS =>
          intro hsub
          have hS'sub : S' ⊆ B := Finset.Subset.trans (Finset.subset_insert δ S') hsub
          have hδB : δ ∈ B := hsub (Finset.mem_insert_self δ S')
          have hδΛ₀ : δ ∉ Λ₀ := Finset.disjoint_right.mp hdisj hδB
          have hδM : δ ∉ Λ₀ ∪ S' := by
            simp only [Finset.mem_union, not_or]; exact ⟨hδΛ₀, hδS'⟩
          have hMsub : Λ₀ ∪ S' ⊆ Λ := by
            rw [← hunion]; exact Finset.union_subset_union_right hS'sub
          have hMcard : (Λ₀ ∪ S').card ≤ n := by
            have hss : Λ₀ ∪ S' ⊂ Λ := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨hMsub, fun heq ↦ hδM (heq ▸ (Finset.mem_filter.mp hδB).1)⟩
            have hlt := Finset.card_lt_card hss
            omega
          have hprev := ihS hS'sub
          have hst := hstep_norm (Λ₀ ∪ S') δ (Finset.Subset.trans hMsub hΛΓ) hMcard
            (hΛΓ (Finset.mem_filter.mp hδB).1) hδM
          have hins_eq : Λ₀ ∪ insert δ S' = insert δ (Λ₀ ∪ S') := by ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
          rw [hins_eq]
          refine ⟨hst.2.1, ?_⟩
          have hmul : polymerZ incompat w Λ₀ / polymerZ incompat w (insert δ (Λ₀ ∪ S')) =
              (polymerZ incompat w Λ₀ / polymerZ incompat w (Λ₀ ∪ S')) *
              (polymerZ incompat w (Λ₀ ∪ S') / polymerZ incompat w (insert δ (Λ₀ ∪ S'))) := by
            rw [div_mul_div_cancel₀ hprev.1]
          rw [hmul, norm_mul, Finset.sum_insert hδS', mul_add, Real.exp_add]
          calc ‖polymerZ incompat w Λ₀ / polymerZ incompat w (Λ₀ ∪ S')‖ *
                ‖polymerZ incompat w (Λ₀ ∪ S') / polymerZ incompat w (insert δ (Λ₀ ∪ S'))‖
              ≤ Real.exp (2 * ∑ x ∈ S', ‖w x‖ * Real.exp (a x)) *
                Real.exp (2 * (‖w δ‖ * Real.exp (a δ))) :=
                mul_le_mul hprev.2 hst.2.2 (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp (2 * (‖w δ‖ * Real.exp (a δ))) *
                Real.exp (2 * ∑ x ∈ S', ‖w x‖ * Real.exp (a x)) := mul_comm _ _
      have hfinal := (hS_bound B Finset.Subset.rfl).2
      rw [hunion] at hfinal
      refine le_trans hfinal (Real.exp_le_exp.mpr ?_)
      have hBsub : B ⊆ Γ.filter (fun δ ↦ incompat γ δ) := by
        intro δ hδ; rcases Finset.mem_filter.mp hδ with ⟨h1, h2⟩
        exact Finset.mem_filter.mpr ⟨hΛΓ h1, h2⟩
      have hsum_le : ∑ δ ∈ B, ‖w δ‖ * Real.exp (a δ) ≤
          ∑ δ ∈ Γ.filter (fun δ ↦ incompat γ δ), ‖w δ‖ * Real.exp (a δ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hBsub fun _ _ _ ↦ by positivity
      linarith [hkp_half γ hγΓ]

end WeightedTreeAndKPRatio

section SiteTelescopingLog

/-- Site-prefix slice `Λ_k`: polymers in `Γ` whose support lies in `{y : Fin N | y.val < k}`. -/
def siteSlice {N : ℕ} (Γ : Finset (Polymer N)) (k : ℕ) : Finset (Polymer N) :=
  Γ.filter (fun γ ↦ ∀ y ∈ polySupp γ, y.val < k)

lemma siteSlice_zero {N : ℕ} {E : Finset (Finset (Fin N))} (hne : ∀ X ∈ E, X.Nonempty) :
    siteSlice (connectedPolymers E) 0 = ∅ := by
  ext γ
  simp only [siteSlice, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro hγ hall
  rcases (mem_connectedPolymers.mp hγ).2.1 with ⟨X, hXγ⟩
  rcases hne X ((mem_connectedPolymers.mp hγ).1 hXγ) with ⟨y, hyX⟩
  have := hall y (Finset.mem_biUnion.mpr ⟨X, hXγ, hyX⟩)
  omega

lemma siteSlice_full {N : ℕ} (Γ : Finset (Polymer N)) :
    siteSlice Γ N = Γ := by
  ext γ; simp only [siteSlice, Finset.mem_filter, and_iff_left_iff_imp]
  intro _ y _; exact y.isLt

lemma siteSlice_subset_succ {N : ℕ} (Γ : Finset (Polymer N)) (k : ℕ) :
    siteSlice Γ k ⊆ siteSlice Γ (k + 1) := by
  intro γ hγ
  rcases Finset.mem_filter.mp hγ with ⟨h1, h2⟩
  exact Finset.mem_filter.mpr ⟨h1, fun y hy ↦ Nat.lt_succ_of_lt (h2 y hy)⟩

/-- Every polymer in `siteSlice Γ (k + 1) \ siteSlice Γ k` contains site `⟨k, hk⟩`. -/
lemma mem_siteSlice_sdiff_mem_polySupp {N : ℕ} (Γ : Finset (Polymer N)) {k : ℕ} (hk : k < N)
    {γ : Polymer N} (hγ : γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k) :
    (⟨k, hk⟩ : Fin N) ∈ polySupp γ := by
  rw [Finset.mem_sdiff, siteSlice, siteSlice, Finset.mem_filter, Finset.mem_filter] at hγ
  have hnot : ¬∀ y ∈ polySupp γ, y.val < k := fun h ↦ hγ.2 ⟨hγ.1.1, h⟩
  push Not at hnot
  rcases hnot with ⟨y, hy, hyk⟩
  have hlt := hγ.1.2 y hy
  have heq : y = ⟨k, hk⟩ := Fin.ext (by dsimp; omega)
  exact heq ▸ hy

/-- Exact site-by-site partition function step:
`Z(Λ_{k+1}) = Z(Λ_k) + ∑ γ ∈ Λ_{k+1} \ Λ_k, w γ * Z(Λ_k.filter (¬polyIncompat γ ·))`. -/
lemma polymerZ_siteSlice_step {N : ℕ} (w : Polymer N → ℂ) (Γ : Finset (Polymer N))
    {k : ℕ} (hk : k < N) :
    polymerZ polyIncompat w (siteSlice Γ (k + 1)) =
      polymerZ polyIncompat w (siteSlice Γ k) +
      ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
        w γ * polymerZ polyIncompat w ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) := by
  classical
  let Λk := siteSlice Γ k
  let Λk1 := siteSlice Γ (k + 1)
  let Δ := Λk1 \ Λk
  have hsub : Λk ⊆ Λk1 := siteSlice_subset_succ Γ k
  have hpair_inc : ∀ γ₁ ∈ Δ, ∀ γ₂ ∈ Δ, polyIncompat γ₁ γ₂ := by
    intro γ₁ h₁ γ₂ h₂
    unfold polyIncompat
    rw [Finset.not_disjoint_iff]
    exact ⟨⟨k, hk⟩, mem_siteSlice_sdiff_mem_polySupp Γ hk h₁,
      mem_siteSlice_sdiff_mem_polySupp Γ hk h₂⟩
  have hstep : ∀ S : Finset (Polymer N), S ⊆ Δ →
      polymerZ polyIncompat w (Λk ∪ S) =
        polymerZ polyIncompat w Λk +
        ∑ γ ∈ S, w γ * polymerZ polyIncompat w (Λk.filter (fun δ ↦ ¬polyIncompat γ δ)) := by
    intro S
    induction S using Finset.induction with
    | empty => intro _; simp
    | @insert γ S' hγS' ih =>
      intro hSsub
      have hγΔ : γ ∈ Δ := hSsub (Finset.mem_insert_self γ S')
      have hS'sub : S' ⊆ Δ := Finset.Subset.trans (Finset.subset_insert γ S') hSsub
      have hγΛk : γ ∉ Λk := (Finset.mem_sdiff.mp hγΔ).2
      have hγnot : γ ∉ Λk ∪ S' := by
        simp only [Finset.mem_union, not_or]; exact ⟨hγΛk, hγS'⟩
      rw [Finset.union_insert]
      have hsp := polymerZ_split_mem polyIncompat polyIncompat_symm w
        (insert γ (Λk ∪ S')) (Finset.mem_insert_self γ (Λk ∪ S'))
      rw [Finset.erase_insert hγnot] at hsp
      have hfilt : (Λk ∪ S').filter (fun δ ↦ ¬polyIncompat γ δ) =
          Λk.filter (fun δ ↦ ¬polyIncompat γ δ) := by
        ext δ; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h2, hni⟩
          · exact ⟨h1, hni⟩
          · exact absurd (hpair_inc γ hγΔ δ (hS'sub h2)) hni
        · rintro ⟨h1, hni⟩; exact ⟨Or.inl h1, hni⟩
      rw [hsp, hfilt, ih hS'sub, Finset.sum_insert hγS']
      ring
  have hunion : Λk ∪ Δ = Λk1 := Finset.union_sdiff_of_subset hsub
  have hres := hstep Δ Finset.Subset.rfl
  rw [hunion] at hres
  exact hres

/-- For `z : ℂ` with `‖z - 1‖ ≤ 1 / 4`, `z ∈ Complex.slitPlane` and `‖Complex.log z‖ ≤ 2 / 3`. -/
lemma complex_log_bound_of_norm_sub_one_le {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 4) :
    z ∈ Complex.slitPlane ∧ ‖Complex.log z‖ ≤ 2 / 3 := by
  have hre_sub : |z.re - 1| ≤ 1 / 4 := by
    have h1 : |z.re - 1| = |(z - 1).re| := by simp
    rw [h1]; exact le_trans (Complex.abs_re_le_norm (z - 1)) hz
  have him : |z.im| ≤ 1 / 4 := by
    have h1 : |z.im| = |(z - 1).im| := by simp
    rw [h1]; exact le_trans (Complex.abs_im_le_norm (z - 1)) hz
  have hre_ge : 3 / 4 ≤ z.re := by linarith [(abs_le.mp hre_sub).1]
  have hre_pos : 0 < z.re := by linarith
  have hslit : z ∈ Complex.slitPlane := Or.inl hre_pos
  have hnorm_ge : 3 / 4 ≤ ‖z‖ := le_trans hre_ge (le_trans (le_abs_self z.re) (Complex.abs_re_le_norm z))
  have hnorm_le : ‖z‖ ≤ 5 / 4 := by
    have h1 := norm_sub_norm_le z 1
    rw [norm_one] at h1; linarith
  have hlog_abs : |Real.log ‖z‖| ≤ 1 / 3 := by
    rw [abs_le]; constructor
    · have hinv : Real.log (‖z‖⁻¹) ≤ ‖z‖⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith))
      rw [Real.log_inv] at hinv
      have hinv_le : ‖z‖⁻¹ ≤ 4 / 3 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    · have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖z‖)
      linarith
  have harg_abs : |Complex.arg z| ≤ 1 / 3 := by
    have hθ_lt : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    have htan_eq : Real.tan (Complex.arg z) = z.im / z.re := by
      rw [Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg (Complex.slitPlane_ne_zero hslit)]
      field_simp [(by linarith : ‖z‖ ≠ 0), hre_pos.ne']
    have hle_tan : ∀ t : ℝ, 0 ≤ t → t < Real.pi / 2 → t ≤ Real.tan t := by
      intro t ht0 htpi
      by_cases h0 : t = 0
      · subst h0; simp
      · have hpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
        have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun u ↦ Real.tan u - u) (1 / Real.cos x ^ 2 - 1) x := by
          intro x hx
          have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
          exact (Real.hasDerivAt_tan hcos_pos.ne').sub (hasDerivAt_id x)
        have hcont : ContinuousOn (fun u ↦ Real.tan u - u) (Set.Icc 0 t) := by
          intro x hx
          have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
          exact ((Real.continuousAt_tan.mpr hcos_pos.ne').sub continuousAt_id).continuousWithinAt
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u ↦ Real.tan u - u)
          (fun x ↦ 1 / Real.cos x ^ 2 - 1) hpos hcont hderiv
        have hcos_pos : 0 < Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1, Real.pi_pos], by linarith [hc.2]⟩
        have hcos_sq : Real.cos c ^ 2 ≤ 1 := by nlinarith [Real.cos_le_one c, Real.neg_one_le_cos c]
        have hinv_ge : 1 ≤ 1 / Real.cos c ^ 2 := (one_le_div (sq_pos_of_pos hcos_pos)).mpr hcos_sq
        simp only [Real.tan_zero, sub_zero] at hslope
        have hnn : 0 ≤ (Real.tan t - t) / t := by rw [← hslope]; linarith
        have hmul := mul_nonneg hnn hpos.le
        rw [div_mul_cancel₀ _ hpos.ne'] at hmul
        linarith
    have habs_le : |Complex.arg z| ≤ |Real.tan (Complex.arg z)| := by
      rcases le_or_gt 0 (Complex.arg z) with hge | hlt
      · rw [abs_of_nonneg hge] at hθ_lt ⊢
        exact le_trans (hle_tan _ hge hθ_lt) (le_abs_self _)
      · have hneg : 0 ≤ -Complex.arg z := by linarith
        have hneg_lt : -Complex.arg z < Real.pi / 2 := by rw [abs_of_neg hlt] at hθ_lt; exact hθ_lt
        rw [abs_of_neg hlt]
        have h1 := hle_tan (-Complex.arg z) hneg hneg_lt
        rw [Real.tan_neg] at h1
        exact le_trans h1 (neg_le_abs _)
    calc |Complex.arg z| ≤ |Real.tan (Complex.arg z)| := habs_le
      _ = |z.im / z.re| := by rw [htan_eq]
      _ = |z.im| / z.re := by rw [abs_div, abs_of_pos hre_pos]
      _ ≤ (1 / 4) / (3 / 4) := div_le_div₀ (by norm_num) him (by norm_num) hre_ge
      _ = 1 / 3 := by norm_num
  have hlog_norm : ‖Complex.log z‖ ≤ 2 / 3 := by
    have hdef : Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I := rfl
    rw [hdef]
    calc ‖(Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I‖
        ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(Complex.arg z : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |Real.log ‖z‖| + |Complex.arg z| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 / 3 + 1 / 3 := add_le_add hlog_abs harg_abs
      _ = 2 / 3 := by norm_num
  exact ⟨hslit, hlog_norm⟩

end SiteTelescopingLog

section CauchyOrder2Schwarz

/-- **Order-2 Cauchy–Schwarz Lemma on a Disk**:
If `g : ℂ → ℂ` is continuous on `Metric.closedBall 0 R`, differentiable on `Metric.ball 0 R`,
satisfies `g 0 = 0`, `deriv g 0 = 0`, and `∀ z ∈ Metric.sphere 0 R, ‖g z‖ ≤ M` (`0 < R`, `0 ≤ M`),
then for every `w ∈ Metric.closedBall 0 (R / 2)`:
`‖g w‖ ≤ 2 * M * (‖w‖ / R) ^ 2`. -/
theorem cauchy_order2_schwarz_bound {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (g : ℂ → ℂ)
    (hcont : ContinuousOn g (Metric.closedBall 0 R))
    (hdiff : ∀ z ∈ Metric.ball (0 : ℂ) R, DifferentiableAt ℂ g z)
    (hg0 : g 0 = 0) (hg'0 : deriv g 0 = 0)
    (hbdd : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) (R / 2),
      ‖g w‖ ≤ 2 * M * (‖w‖ / R) ^ 2 := by
  intro w hw
  by_cases hw0 : w = 0
  · subst hw0; simp [hg0]
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then 0 else g z / z
  have hh₁_cont : ContinuousOn h₁ (Metric.closedBall 0 R) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have hd0 : HasDerivAt g 0 0 := by
        have h := (hdiff 0 (Metric.mem_ball_self hR)).hasDerivAt; rwa [hg'0] at h
      have hslope := hd0.tendsto_slope_zero
      have hlim : Tendsto h₁ (nhds (0 : ℂ)) (nhds 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have h1 := (Metric.tendsto_nhds.mp hslope) ε hε
        rw [eventually_nhdsWithin_iff] at h1
        refine h1.mono fun u hu ↦ ?_
        by_cases hu0 : u = 0
        · subst hu0; simp [h₁, hε]
        · have := hu hu0
          simpa [h₁, hu0, slope_def_field, hg0, div_eq_inv_mul, dist_eq_norm] using this
      have hca : ContinuousAt h₁ 0 := by
        rw [ContinuousAt, show h₁ 0 = 0 by simp [h₁]]; exact hlim
      exact hca.continuousWithinAt
    · have hdiv_c : ContinuousWithinAt (fun u : ℂ ↦ g u / u) (Metric.closedBall 0 R) z :=
        (hcont z hz).div continuousWithinAt_id hz0
      refine hdiv_c.congr_of_eventuallyEq ?_ (by simp [h₁, hz0])
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_ne.mem_nhds hz0)] with u hu
      simp [h₁, hu]
  have hh₁_diff : ∀ z ∈ Metric.ball (0 : ℂ) R \ ({0} : Set ℂ), DifferentiableAt ℂ h₁ z := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hdiv_d : DifferentiableAt ℂ (fun u : ℂ ↦ g u / u) z :=
      (hdiff z hz.1).div differentiableAt_id hz0
    refine hdiv_d.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz0] with u hu
    simp [h₁, hu]
  have hw_ball : w ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR
  have hc_w := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (Set.countable_singleton (0 : ℂ)) hw_ball hh₁_cont hh₁_diff
  have hc_0 := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (Set.countable_singleton (0 : ℂ)) h0_ball hh₁_cont hh₁_diff
  have hci_w : CircleIntegrable (fun z ↦ (z - w)⁻¹ • h₁ z) 0 R := by
    have hco : ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹ • h₁ z) (Metric.sphere 0 R) := by
      change ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹ * h₁ z) (Metric.sphere 0 R)
      refine ContinuousOn.mul ?_ (hh₁_cont.mono Metric.sphere_subset_closedBall)
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz ↦ ?_
      rw [sub_ne_zero]; intro heq; subst heq
      rw [Metric.mem_sphere, dist_zero_right] at hz
      rw [Metric.mem_closedBall, dist_zero_right] at hw; linarith
    exact hco.circleIntegrable hR.le
  have hci_0 : CircleIntegrable (fun z ↦ (z - 0)⁻¹ • h₁ z) 0 R := by
    have hco : ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹ • h₁ z) (Metric.sphere 0 R) := by
      change ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹ * h₁ z) (Metric.sphere 0 R)
      refine ContinuousOn.mul ?_ (hh₁_cont.mono Metric.sphere_subset_closedBall)
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz ↦ ?_
      rw [sub_zero]; intro heq; subst heq
      rw [Metric.mem_sphere, dist_zero_right, norm_zero] at hz; linarith
    exact hco.circleIntegrable hR.le
  have hh₁_w_eq : h₁ w = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C((0 : ℂ), R), ((z - w)⁻¹ • h₁ z - (z - 0)⁻¹ • h₁ z) := by
    have hsub : h₁ w - h₁ 0 =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C((0 : ℂ), R), ((z - w)⁻¹ • h₁ z - (z - 0)⁻¹ • h₁ z) := by
      rw [circleIntegral.integral_sub hci_w hci_0, smul_sub, hc_w, hc_0]
    simpa [h₁] using hsub
  have hg_w_eq : g w = w * h₁ w := by
    simp [h₁, hw0, mul_div_cancel₀ _ hw0]
  have hbound_int : ‖∮ z in C((0 : ℂ), R), ((z - w)⁻¹ • h₁ z - (z - 0)⁻¹ • h₁ z)‖ ≤
      2 * Real.pi * R * (2 * ‖w‖ * M / R ^ 3) := by
    have hle := circleIntegral.norm_integral_le_of_norm_le_const (c := (0 : ℂ)) (R := R)
      (C := 2 * ‖w‖ * M / R ^ 3) hR.le (fun z hz ↦ ?_)
    · simpa [abs_of_pos hR] using hle
    · rw [Metric.mem_sphere, dist_zero_right] at hz
      have hz_ne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; linarith
      have hzw_ge : R / 2 ≤ ‖z - w‖ := by
        have htri := norm_sub_norm_le z w
        rw [hz] at htri
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        linarith
      have hzw_ne : z - w ≠ 0 := by intro h0; rw [h0, norm_zero] at hzw_ge; linarith
      have halg : (z - w)⁻¹ • h₁ z - (z - 0)⁻¹ • h₁ z = (w / (z ^ 2 * (z - w))) * g z := by
        simp only [h₁, if_neg hz_ne, sub_zero, smul_eq_mul]
        field_simp [hz_ne, hzw_ne]; ring
      rw [halg, norm_mul, norm_div, norm_mul, norm_pow, hz]
      have hg_le : ‖g z‖ ≤ M := hbdd z (by rw [Metric.mem_sphere, dist_zero_right]; exact hz)
      have hdenom : R ^ 2 * (R / 2) ≤ R ^ 2 * ‖z - w‖ :=
        mul_le_mul_of_nonneg_left hzw_ge (sq_nonneg R)
      calc ‖w‖ / (R ^ 2 * ‖z - w‖) * ‖g z‖
          ≤ ‖w‖ / (R ^ 2 * (R / 2)) * M := by
            apply mul_le_mul _ hg_le (norm_nonneg _) (by positivity)
            exact div_le_div_of_nonneg_left (norm_nonneg w) (by positivity) hdenom
        _ = 2 * ‖w‖ * M / R ^ 3 := by field_simp [hR.ne']
  rw [hg_w_eq, hh₁_w_eq, norm_mul, norm_smul, norm_inv, norm_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one]
  calc ‖w‖ * ((2 * Real.pi)⁻¹ * ‖∮ z in C((0 : ℂ), R), ((z - w)⁻¹ • h₁ z - (z - 0)⁻¹ • h₁ z)‖)
      ≤ ‖w‖ * ((2 * Real.pi)⁻¹ * (2 * Real.pi * R * (2 * ‖w‖ * M / R ^ 3))) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
        exact mul_le_mul_of_nonneg_left hbound_int (by positivity)
    _ = 2 * M * (‖w‖ / R) ^ 2 := by
        field_simp [Real.pi_pos.ne', hR.ne']

end CauchyOrder2Schwarz

section TracePolymerIdentityAndCumulant

/-- Matrix exponential via `NormedSpace.exp` on `QubitOpCLM N` equals `hermFunc` for Hermitian `A`. -/
lemma trace_hermFunc_exp_eq_tsum {N : ℕ} {A : QubitOp N} (hA : A.IsHermitian) (c : ℂ) :
    normalizedTrace (hermFunc hA (fun e ↦ Complex.exp (c * (e : ℂ)))) =
      ∑' k : ℕ, (c ^ k / (k.factorial : ℂ)) * normalizedTrace (A ^ k) := by
  have hsum := hasSum_hermFunc_exp hA c
  let Φ : QubitOp N →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := normalizedTrace
        map_add' := normalizedTrace_add
        map_smul' := fun α X ↦ by simp [normalizedTrace_smul] }
  have hΦ : HasSum (fun k : ℕ ↦ Φ ((c ^ k / (k.factorial : ℂ)) • A ^ k))
      (Φ (hermFunc hA (fun e ↦ Complex.exp (c * (e : ℂ))))) := hsum.map Φ Φ.continuous
  have hrew : (fun k : ℕ ↦ Φ ((c ^ k / (k.factorial : ℂ)) • A ^ k)) =
      fun k : ℕ ↦ (c ^ k / (k.factorial : ℂ)) * normalizedTrace (A ^ k) := by
    funext k; exact normalizedTrace_smul _ _
  rw [hrew] at hΦ
  exact hΦ.tsum_eq.symm

/-- Disjoint-support multiplicative factorization of `normalizedTrace (polyOp g 1 (I.biUnion id))`. -/
lemma normalizedTrace_polyOp_biUnion {N : ℕ}
    (g : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, g X ∈ supportedOn X)
    (I : Finset (Polymer N))
    (hcomp : ∀ γ₁ ∈ I, ∀ γ₂ ∈ I, γ₁ ≠ γ₂ → ¬polyIncompat γ₁ γ₂)
    (hne : ∀ γ ∈ I, ∀ X ∈ γ, X.Nonempty) :
    normalizedTrace (polyOp g 1 (I.biUnion id)) = ∏ γ ∈ I, tracePolyWeight g 1 γ := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty]
    have h1 : polyOp g 1 ∅ = 1 := by
      unfold polyOp
      have h0 : ∀ n : ℕ, ((1 : ℂ) ^ n / (n.factorial : ℂ)) • polyTermSum g ∅ n =
          if n = 0 then (1 : QubitOp N) else 0 := by
        intro n
        cases n with
        | zero =>
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul, ↓reduceIte]
          unfold polyTermSum
          have hsing : (Fintype.piFinset (fun _ : Fin 0 ↦ (∅ : Finset (Finset (Fin N))))).filter
              (fun f ↦ Finset.univ.image f = ∅) = {Fin.elim0} := by
            ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
            constructor
            · intro _; funext j; exact Fin.elim0 j
            · rintro rfl; refine ⟨fun j ↦ Fin.elim0 j, ?_⟩; ext X; simp
          rw [hsing, Finset.sum_singleton]; simp
        | succ m =>
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          unfold polyTermSum
          have hemp : (Fintype.piFinset (fun _ : Fin (m + 1) ↦ (∅ : Finset (Finset (Fin N))))).filter
              (fun f ↦ Finset.univ.image f = ∅) = ∅ := by
            ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.notMem_empty, iff_false]
            intro h; exact h.1 0
          rw [hemp, Finset.sum_empty, smul_zero]
      have hneg1 : ∀ n : ℕ, ((-(1 : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) • polyTermSum g ∅ n =
          if n = 0 then (1 : QubitOp N) else 0 := by
        intro n; cases n with
        | zero => simpa using h0 0
        | succ m =>
          have := h0 (m + 1)
          simp only [Nat.succ_ne_zero, ↓reduceIte] at this ⊢
          unfold polyTermSum
          have hemp : (Fintype.piFinset (fun _ : Fin (m + 1) ↦ (∅ : Finset (Finset (Fin N))))).filter
              (fun f ↦ Finset.univ.image f = ∅) = ∅ := by
            ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.notMem_empty, iff_false]
            intro h; exact h.1 0
          rw [hemp, Finset.sum_empty, smul_zero]
      simp_rw [hneg1]
      rw [tsum_ite_eq]
    rw [h1, normalizedTrace_one]
  | @insert γ I' hγ ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hγ]
    have hcomp' : ∀ γ₁ ∈ I', ∀ γ₂ ∈ I', γ₁ ≠ γ₂ → ¬polyIncompat γ₁ γ₂ :=
      fun γ₁ h₁ γ₂ h₂ hne' ↦ hcomp γ₁ (Finset.mem_insert_of_mem h₁) γ₂ (Finset.mem_insert_of_mem h₂) hne'
    have hdisj_supp : Disjoint (polySupp γ) (polySupp (I'.biUnion id)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_biUnion.mp hx2 with ⟨X, hX, hxX⟩
      rcases Finset.mem_biUnion.mp hX with ⟨γ', hγ', hXγ'⟩
      have hne' : γ ≠ γ' := fun h ↦ hγ (h ▸ hγ')
      have hni := hcomp γ (Finset.mem_insert_self _ _) γ' (Finset.mem_insert_of_mem hγ') hne'
      unfold polyIncompat at hni; push Not at hni
      exact Finset.disjoint_left.mp hni hx1 (Finset.mem_biUnion.mpr ⟨X, hXγ', hxX⟩)
    have hdisj_set : Disjoint γ (I'.biUnion id) := by
      rw [Finset.disjoint_left]; intro X hXγ hXI'
      rcases hne γ (Finset.mem_insert_self _ _) X hXγ with ⟨x, hxX⟩
      exact Finset.disjoint_left.mp hdisj_supp
        (Finset.mem_biUnion.mpr ⟨X, hXγ, hxX⟩)
        (Finset.mem_biUnion.mpr ⟨X, hXI', hxX⟩)
    dsimp only [id]
    rw [polyOp_union_of_disjoint g hsupp 1 hdisj_supp hdisj_set,
      normalizedTrace_mul_of_disjoint hdisj_supp
        (polyOp_mem_supportedOn g hsupp 1 γ) (polyOp_mem_supportedOn g hsupp 1 (I'.biUnion id)),
      ih hcomp' (fun δ hδ ↦ hne δ (Finset.mem_insert_of_mem hδ))]
    rfl

/-- **Exact Normalized-Trace Polymer Partition Function Identity (General Complex Interaction)**:
For ANY `g : Finset (Fin N) → QubitOp N` with `g X ∈ supportedOn X` and `∀ X ∈ E, X.Nonempty`:
`∑' n, (n!⁻¹ : ℂ) * normalizedTrace ((∑ X ∈ E, -g X) ^ n) = polymerZ polyIncompat (tracePolyWeight g 1) (connectedPolymers E)`.
In particular, substituting `g' X := -g X` gives the exact polymer expansion of
`τ(exp(∑ X ∈ E, g' X))` for ANY complex-weighted local interaction! -/
theorem normalizedTrace_tsum_exp_eq_polymerZ {N : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (g : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, g X ∈ supportedOn X) :
    (∑' m : ℕ, (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) *
      normalizedTrace ((∑ X ∈ E, g X) ^ m))) =
      polymerZ polyIncompat (tracePolyWeight g 1) (connectedPolymers E) := by
  classical
  have hpow_expand : ∀ m : ℕ, (∑ X ∈ E, g X) ^ m = ∑ S ∈ E.powerset, polyTermSum g S m := by
    intro m
    have hpi : (∑ X ∈ E, g X) ^ m =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin m ↦ E), (List.ofFn (fun j : Fin m ↦ g (f j))).prod := by
      induction m with
      | zero =>
        simp only [pow_zero]
        have hsing : Fintype.piFinset (fun _ : Fin 0 ↦ E) = {Fin.elim0} := by
          ext f; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
          constructor
          · intro _; funext j; exact Fin.elim0 j
          · rintro rfl j; exact Fin.elim0 j
        rw [hsing, Finset.sum_singleton]; simp
      | succ m ih =>
        rw [pow_succ', ih, Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_bij (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
          rw [Fintype.mem_piFinset]
          intro j; refine Fin.cases hp1 (fun k ↦ Fintype.mem_piFinset.mp hp2 k) j
        · intro p₁ _ p₂ _ heq
          apply Prod.ext
          · have := congrFun heq 0; simpa using this
          · funext k; have := congrFun heq k.succ; simpa using this
        · intro f hf
          refine ⟨(f 0, Fin.tail f), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hf 0,
            Fintype.mem_piFinset.mpr fun k ↦ Fintype.mem_piFinset.mp hf k.succ⟩, ?_⟩
          funext j; refine Fin.cases rfl (fun k ↦ rfl) j
        · intro p _; simp [List.ofFn_succ]
    rw [hpi]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin m → Finset (Fin N) ↦ Finset.univ.image f)
      (t := E.powerset)]
    · apply Finset.sum_congr rfl; intro S hS
      unfold polyTermSum
      apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨_, him⟩
        exact ⟨fun j ↦ him ▸ Finset.mem_image_of_mem f (Finset.mem_univ j), him⟩
      · rintro ⟨hfS, him⟩
        exact ⟨fun j ↦ (Finset.mem_powerset.mp hS) (hfS j), him⟩
    · intro f hf
      rw [Finset.mem_powerset]
      intro X hX; rcases Finset.mem_image.mp hX with ⟨j, _, rfl⟩
      exact Fintype.mem_piFinset.mp hf j
  let Φ : QubitOp N →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := normalizedTrace
        map_add' := normalizedTrace_add
        map_smul' := fun α X ↦ by simp [normalizedTrace_smul] }
  have hterm_S : ∀ S ∈ E.powerset,
      HasSum (fun m : ℕ ↦ ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) *
        normalizedTrace (polyTermSum g S m))
        (normalizedTrace (polyOp g 1 S)) := by
    intro S _
    have hs : HasSum (fun m : ℕ ↦ Φ (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • polyTermSum g S m))
        (Φ (polyOp g 1 S)) := (hasSum_polyOp g 1 S).map Φ Φ.continuous
    have hrew : (fun m : ℕ ↦ Φ (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • polyTermSum g S m)) =
        fun m : ℕ ↦ ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) * normalizedTrace (polyTermSum g S m) := by
      funext m; exact normalizedTrace_smul _ _
    rw [hrew] at hs
    exact hs
  have hsum_all := hasSum_sum (s := E.powerset) hterm_S
  have hlhs_eq : (fun m : ℕ ↦ ∑ S ∈ E.powerset,
      ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) * normalizedTrace (polyTermSum g S m)) =
      fun m : ℕ ↦ ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) *
        normalizedTrace ((∑ X ∈ E, g X) ^ m) := by
    funext m
    rw [hpow_expand m, normalizedTrace_sum, Finset.mul_sum]
  rw [hlhs_eq] at hsum_all
  rw [hsum_all.tsum_eq]
  rcases compatible_connectedPolymers_bijection E hne with ⟨hinj, hsurj⟩
  unfold polymerZ
  symm
  refine Finset.sum_bij (fun I _ ↦ I.biUnion id) ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_powerset]
    intro X hX
    rcases Finset.mem_biUnion.mp hX with ⟨γ, hγI, hXγ⟩
    exact (mem_connectedPolymers.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1) hγI)).1 hXγ
  · intro I₁ hI₁ I₂ hI₂ heq
    exact hinj I₁ (by simpa [Finset.mem_filter] using hI₁) I₂ (by simpa [Finset.mem_filter] using hI₂) heq
  · intro S hS
    rcases hsurj S hS with ⟨I, hI, hEq⟩
    exact ⟨I, by simpa [Finset.mem_filter] using hI, hEq⟩
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_powerset] at hI
    exact (normalizedTrace_polyOp_biUnion g hsupp I hI.2
      (fun γ hγ X hXγ ↦ hne X ((mem_connectedPolymers.mp (hI.1 hγ)).1 hXγ))).symm

/-- Holomorphy of `ζ ↦ tracePolyWeight (g_tot ζ) 1 γ` for any affine-in-`ζ` local interaction
`g_tot ζ Z = A Z + ζ • B Z`. -/
lemma differentiable_tracePolyWeight_affine {N : ℕ}
    (A B : Finset (Fin N) → QubitOp N) (γ : Polymer N) :
    Differentiable ℂ (fun ζ : ℂ ↦ tracePolyWeight (fun Z ↦ A Z + ζ • B Z) 1 γ) := by
  intro ζ₀
  set R : ℝ := ‖ζ₀‖ + 1
  have hR : 0 < R := by positivity
  let f : ℕ → ℂ → ℂ := fun m ζ ↦
    ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) * normalizedTrace (polyTermSum (fun Z ↦ A Z + ζ • B Z) γ m)
  have hf_diff : ∀ m : ℕ, Differentiable ℂ (f m) := by
    intro m
    dsimp only [f]
    refine Differentiable.const_mul ?_ _
    unfold normalizedTrace
    refine Differentiable.const_mul ?_ _
    unfold Matrix.trace Matrix.diag polyTermSum
    simp only [Matrix.sum_apply]
    refine Differentiable.fun_sum fun i _ ↦ Differentiable.fun_sum fun w _ ↦ ?_
    have hprod_diff : ∀ (k : ℕ) (M : Fin k → ℂ → QubitOp N),
        (∀ j a b, Differentiable ℂ (fun ζ ↦ M j ζ a b)) →
        ∀ a b, Differentiable ℂ (fun ζ ↦ (List.ofFn (fun j : Fin k ↦ M j ζ)).prod a b) := by
      intro k
      induction k with
      | zero =>
        intro M _ a b
        simp only [List.ofFn_zero, List.prod_nil]
        exact differentiable_const _
      | succ k ih =>
        intro M hM a b
        simp only [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
        refine Differentiable.fun_sum fun c _ ↦ ?_
        exact (hM 0 a c).mul (ih (fun j ↦ M j.succ) (fun j ↦ hM j.succ) c b)
    refine hprod_diff m (fun j ζ ↦ A (w j) + ζ • B (w j)) (fun j a b ↦ ?_) i i
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
  set C : ℝ := ∑ Z ∈ γ, (opNorm (A Z) + R * opNorm (B Z))
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun Z _ ↦ by
    have := opNorm_nonneg (A Z); have := opNorm_nonneg (B Z); positivity
  have hf_bound : ∀ m : ℕ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ‖f m ζ‖ ≤ C ^ m / (m.factorial : ℝ) := by
    intro m ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    dsimp only [f]
    rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_one, one_pow, Complex.norm_natCast]
    have htr := norm_normalizedTrace_le (polyTermSum (fun Z ↦ A Z + ζ • B Z) γ m)
    have hpt := opNorm_polyTermSum_le (fun Z ↦ A Z + ζ • B Z) γ m
    have hsum_le : ∑ Z ∈ γ, opNorm (A Z + ζ • B Z) ≤ C := by
      apply Finset.sum_le_sum; intro Z _
      calc opNorm (A Z + ζ • B Z) ≤ opNorm (A Z) + opNorm (ζ • B Z) := opNorm_add_le _ _
        _ = opNorm (A Z) + ‖ζ‖ * opNorm (B Z) := by rw [opNorm_smul]
        _ ≤ opNorm (A Z) + R * opNorm (B Z) := by gcongr
    have hpow_le : (∑ Z ∈ γ, opNorm (A Z + ζ • B Z)) ^ m ≤ C ^ m :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun Z _ ↦ opNorm_nonneg _) hsum_le m
    calc 1 / (m.factorial : ℝ) * ‖normalizedTrace (polyTermSum (fun Z ↦ A Z + ζ • B Z) γ m)‖
        ≤ 1 / (m.factorial : ℝ) * C ^ m :=
          mul_le_mul_of_nonneg_left (le_trans htr (le_trans hpt (le_trans (scalarWordSum_le_pow _ (fun _ _ ↦ opNorm_nonneg _) γ m) hpow_le))) (by positivity)
      _ = C ^ m / (m.factorial : ℝ) := by ring
  have hsumm_u : Summable (fun m : ℕ ↦ C ^ m / (m.factorial : ℝ)) :=
    Real.summable_pow_div_factorial C
  have htend : TendstoUniformlyOn (fun K : ℕ ↦ fun ζ : ℂ ↦ ∑ m ∈ Finset.range K, f m ζ)
      (fun ζ : ℂ ↦ tracePolyWeight (fun Z ↦ A Z + ζ • B Z) 1 γ) atTop (Metric.closedBall 0 R) := by
    have hweier := tendstoUniformlyOn_tsum_nat hsumm_u (fun m ζ hζ ↦ hf_bound m ζ hζ)
    refine hweier.congr_right fun ζ _ ↦ ?_
    let Φ : QubitOp N →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := normalizedTrace
          map_add' := normalizedTrace_add
          map_smul' := fun α X ↦ by simp [normalizedTrace_smul] }
    have hs : HasSum (fun m : ℕ ↦ Φ (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) •
        polyTermSum (fun Z ↦ A Z + ζ • B Z) γ m))
        (Φ (polyOp (fun Z ↦ A Z + ζ • B Z) 1 γ)) :=
      (hasSum_polyOp (fun Z ↦ A Z + ζ • B Z) 1 γ).map Φ Φ.continuous
    have hrew : (fun m : ℕ ↦ Φ (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) •
        polyTermSum (fun Z ↦ A Z + ζ • B Z) γ m)) = fun m ↦ f m ζ := by
      funext m; exact normalizedTrace_smul _ _
    rw [hrew] at hs
    exact hs.tsum_eq
  have hloc : TendstoLocallyUniformlyOn (fun K : ℕ ↦ fun ζ : ℂ ↦ ∑ m ∈ Finset.range K, f m ζ)
      (fun ζ : ℂ ↦ tracePolyWeight (fun Z ↦ A Z + ζ • B Z) 1 γ) atTop (Metric.ball 0 R) :=
    (htend.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff_ball : DifferentiableOn ℂ (fun ζ : ℂ ↦ tracePolyWeight (fun Z ↦ A Z + ζ • B Z) 1 γ)
      (Metric.ball 0 R) :=
    hloc.differentiableOn (Eventually.of_forall fun K ↦
      (Differentiable.fun_sum fun m _ ↦ hf_diff m).differentiableOn) Metric.isOpen_ball
  exact (hdiff_ball ζ₀ (by rw [Metric.mem_ball, dist_zero_right]; linarith)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; linarith))

/-- Derivative at `ζ = 0` of `ζ ↦ ∑' m, (m!⁻¹) * normalizedTrace ((A + ζ • B) ^ m)` is
`∑' m, (m!⁻¹) * normalizedTrace (A ^ m * B)`. -/
lemma hasDerivAt_normalizedTrace_exp_affine {N : ℕ} (A B : QubitOp N) :
    HasDerivAt
      (fun ζ : ℂ ↦ ∑' m : ℕ, ((m.factorial : ℂ)⁻¹ * normalizedTrace ((A + ζ • B) ^ m)))
      (∑' m : ℕ, ((m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B))) 0 := by
  have hderiv_pow : ∀ m : ℕ,
      HasDerivAt (fun ζ : ℂ ↦ normalizedTrace ((A + ζ • B) ^ m))
        ((m : ℂ) * normalizedTrace (A ^ (m - 1) * B)) 0 := by
    intro m
    have hmat_deriv : ∀ (k : ℕ) (a b : QubitIdx N),
        HasDerivAt (fun ζ : ℂ ↦ ((A + ζ • B) ^ k) a b)
          ((∑ j ∈ Finset.range k, A ^ j * B * A ^ (k - 1 - j)) a b) 0 := by
      intro k
      induction k with
      | zero =>
        intro a b; simp [hasDerivAt_const]
      | succ k ih =>
        intro a b
        have hpow : (fun ζ : ℂ ↦ ((A + ζ • B) ^ (k + 1)) a b) =
            fun ζ : ℂ ↦ ∑ c : QubitIdx N, ((A + ζ • B) ^ k) a c * (A + ζ • B) c b := by
          funext ζ; rw [pow_succ, Matrix.mul_apply]
        rw [hpow]
        have hterm : ∀ c : QubitIdx N,
            HasDerivAt (fun ζ : ℂ ↦ ((A + ζ • B) ^ k) a c * (A + ζ • B) c b)
              (((∑ j ∈ Finset.range k, A ^ j * B * A ^ (k - 1 - j)) a c) * A c b +
               (A ^ k) a c * B c b) 0 := by
          intro c
          have h1 := ih a c
          have h2 : HasDerivAt (fun ζ : ℂ ↦ (A + ζ • B) c b) (B c b) 0 := by
            have hlin : HasDerivAt (fun ζ : ℂ ↦ A c b + ζ * B c b) (0 + 1 * B c b) 0 :=
              (hasDerivAt_const (0 : ℂ) (A c b)).add ((hasDerivAt_id (0 : ℂ)).mul_const (B c b))
            rw [zero_add, one_mul] at hlin
            refine hlin.congr_of_eventuallyEq (Eventually.of_forall fun ζ ↦ by simp)
          have hmul : HasDerivAt (fun ζ : ℂ ↦ ((A + ζ • B) ^ k) a c * (A + ζ • B) c b)
              (((∑ j ∈ Finset.range k, A ^ j * B * A ^ (k - 1 - j)) a c) * (A + (0 : ℂ) • B) c b +
               ((A + (0 : ℂ) • B) ^ k) a c * B c b) 0 := h1.mul h2
          simpa using hmul
        have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun c _ ↦ hterm c
        refine hsum.congr_deriv ?_
        rw [Finset.sum_add_distrib]
        have h1 : ∑ c : QubitIdx N, (∑ j ∈ Finset.range k, A ^ j * B * A ^ (k - 1 - j)) a c * A c b =
            ((∑ j ∈ Finset.range k, A ^ j * B * A ^ (k - 1 - j)) * A) a b := by
          rw [Matrix.mul_apply]
        have h2 : ∑ c : QubitIdx N, (A ^ k) a c * B c b = (A ^ k * B) a b := by
          rw [Matrix.mul_apply]
        rw [h1, h2, Finset.sum_mul, Finset.sum_range_succ, Matrix.add_apply]
        congr 1
        · simp only [Matrix.sum_apply]
          apply Finset.sum_congr rfl; intro j hj
          have hjk : j < k := Finset.mem_range.mp hj
          have heq : k - j = (k - 1 - j) + 1 := by omega
          rw [Nat.add_sub_cancel, heq, pow_succ, Matrix.mul_assoc]
        · simp [Nat.sub_self]
    unfold normalizedTrace Matrix.trace Matrix.diag
    have htr := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hmat_deriv m i i).const_mul (((2 : ℝ) ^ N : ℂ)⁻¹)
    refine htr.congr_deriv ?_
    have hcyc : ∑ i : QubitIdx N, (∑ j ∈ Finset.range m, A ^ j * B * A ^ (m - 1 - j)) i i =
        (m : ℂ) * Matrix.trace (A ^ (m - 1) * B) := by
      have h1 : ∑ i : QubitIdx N, (∑ j ∈ Finset.range m, A ^ j * B * A ^ (m - 1 - j)) i i =
          ∑ j ∈ Finset.range m, Matrix.trace (A ^ j * B * A ^ (m - 1 - j)) := by
        simp only [Matrix.sum_apply, Matrix.trace, Matrix.diag]
        rw [Finset.sum_comm]
      rw [h1]
      have h2 : ∀ j ∈ Finset.range m, Matrix.trace (A ^ j * B * A ^ (m - 1 - j)) =
          Matrix.trace (A ^ (m - 1) * B) := by
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        calc Matrix.trace (A ^ j * B * A ^ (m - 1 - j))
            = Matrix.trace (A ^ (m - 1 - j) * (A ^ j * B)) := Matrix.trace_mul_comm _ _
          _ = Matrix.trace ((A ^ (m - 1 - j) * A ^ j) * B) := by simp only [Matrix.mul_assoc]
          _ = Matrix.trace (A ^ (m - 1) * B) := by
              rw [← pow_add, show m - 1 - j + j = m - 1 by omega]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcyc]; unfold Matrix.trace Matrix.diag; ring
  let f : ℕ → ℂ → ℂ := fun m ζ ↦ (m.factorial : ℂ)⁻¹ * normalizedTrace ((A + ζ • B) ^ m)
  set M : ℝ := opNorm A + opNorm B
  have hM_nn : 0 ≤ M := add_nonneg (opNorm_nonneg A) (opNorm_nonneg B)
  have hop_pow : ∀ (X : QubitOp N) (m : ℕ), opNorm (X ^ m) ≤ opNorm X ^ m := by
    intro X m
    induction m with
    | zero => simp [pow_zero, opNorm_one_le]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (opNorm_mul_le _ _) (mul_le_mul_of_nonneg_right ih (opNorm_nonneg X))
  have hf_bound : ∀ m : ℕ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖f m ζ‖ ≤ M ^ m / (m.factorial : ℝ) := by
    intro m ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    dsimp only [f]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have htr := norm_normalizedTrace_le ((A + ζ • B) ^ m)
    have hpow : opNorm ((A + ζ • B) ^ m) ≤ opNorm (A + ζ • B) ^ m := hop_pow _ m
    have hnorm : opNorm (A + ζ • B) ≤ M := by
      calc opNorm (A + ζ • B) ≤ opNorm A + opNorm (ζ • B) := opNorm_add_le _ _
        _ = opNorm A + ‖ζ‖ * opNorm B := by rw [opNorm_smul]
        _ ≤ opNorm A + 1 * opNorm B := by
            linarith [mul_le_mul_of_nonneg_right hζ (opNorm_nonneg B)]
        _ = M := by ring
    calc (m.factorial : ℝ)⁻¹ * ‖normalizedTrace ((A + ζ • B) ^ m)‖
        ≤ (m.factorial : ℝ)⁻¹ * M ^ m :=
          mul_le_mul_of_nonneg_left (le_trans htr (le_trans hpow (pow_le_pow_left₀ (opNorm_nonneg _) hnorm m)))
            (by positivity)
      _ = M ^ m / (m.factorial : ℝ) := by ring
  have hdiff_f : ∀ m : ℕ, Differentiable ℂ (f m) := by
    intro m; dsimp only [f]
    refine Differentiable.const_mul ?_ _
    unfold normalizedTrace Matrix.trace Matrix.diag
    refine Differentiable.const_mul (Differentiable.fun_sum fun i _ ↦ ?_) _
    have hpow_d : ∀ (k : ℕ) (a b : QubitIdx N), Differentiable ℂ (fun ζ : ℂ ↦ ((A + ζ • B) ^ k) a b) := by
      intro k
      induction k with
      | zero => intro a b; exact differentiable_const _
      | succ k ih =>
        intro a b
        have heq : (fun ζ : ℂ ↦ ((A + ζ • B) ^ (k + 1)) a b) =
            fun ζ ↦ ∑ c : QubitIdx N, ((A + ζ • B) ^ k) a c * (A c b + ζ * B c b) := by
          funext ζ; rw [pow_succ, Matrix.mul_apply]; apply Finset.sum_congr rfl; intro c _; simp
        rw [heq]
        exact Differentiable.fun_sum fun c _ ↦ (ih a c).mul
          ((differentiable_const _).add (differentiable_id.mul (differentiable_const _)))
    exact hpow_d m i i
  have htend : TendstoLocallyUniformlyOn (fun K : ℕ ↦ fun ζ : ℂ ↦ ∑ m ∈ Finset.range K, f m ζ)
      (fun ζ : ℂ ↦ ∑' m : ℕ, f m ζ) atTop (Metric.ball 0 1) :=
    ((tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial M) hf_bound).mono
      Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff_lim : DifferentiableAt ℂ (fun ζ : ℂ ↦ ∑' m : ℕ, f m ζ) 0 :=
    (htend.differentiableOn (Eventually.of_forall fun K ↦
      (Differentiable.fun_sum fun m _ ↦ hdiff_f m).differentiableOn) Metric.isOpen_ball
      0 (Metric.mem_ball_self one_pos)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
  have hderiv_lim := (htend.deriv (Eventually.of_forall fun K ↦
    (Differentiable.fun_sum fun m _ ↦ hdiff_f m).differentiableOn) Metric.isOpen_ball).tendsto_at
    (Metric.mem_ball_self one_pos)
  have hderiv_K : ∀ K : ℕ, deriv (fun ζ : ℂ ↦ ∑ m ∈ Finset.range (K + 1), f m ζ) 0 =
      ∑ m ∈ Finset.range K, (m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B) := by
    intro K
    have hhd : HasDerivAt (fun ζ : ℂ ↦ ∑ m ∈ Finset.range (K + 1), f m ζ)
        (∑ m ∈ Finset.range (K + 1), (m.factorial : ℂ)⁻¹ * ((m : ℂ) * normalizedTrace (A ^ (m - 1) * B))) 0 :=
      HasDerivAt.fun_sum (u := Finset.range (K + 1)) fun m _ ↦ (hderiv_pow m).const_mul _
    rw [hhd.deriv, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl; intro m _
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, mul_inv]
    have hm_ne : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    push_cast at hm_ne ⊢
    field_simp [hm_ne]
  have hsumm_d : Summable (fun m : ℕ ↦ (m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B)) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ ↦ (opNorm A ^ m / (m.factorial : ℝ)) * opNorm B)
      ((Real.summable_pow_div_factorial (opNorm A)).mul_right (opNorm B)) fun m ↦ ?_
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have htr := le_trans (norm_normalizedTrace_le (A ^ m * B))
      (le_trans (opNorm_mul_le (A ^ m) B) (mul_le_mul_of_nonneg_right (hop_pow A m) (opNorm_nonneg B)))
    calc (m.factorial : ℝ)⁻¹ * ‖normalizedTrace (A ^ m * B)‖
        ≤ (m.factorial : ℝ)⁻¹ * (opNorm A ^ m * opNorm B) :=
          mul_le_mul_of_nonneg_left htr (by positivity)
      _ = opNorm A ^ m / (m.factorial : ℝ) * opNorm B := by ring
  have hlim1 : Tendsto (fun K : ℕ ↦ deriv (fun ζ : ℂ ↦ ∑ m ∈ Finset.range (K + 1), f m ζ) 0)
      atTop (nhds (deriv (fun ζ : ℂ ↦ ∑' m : ℕ, f m ζ) 0)) :=
    hderiv_lim.comp (tendsto_add_atTop_nat 1)
  have hlim2 : Tendsto (fun K : ℕ ↦ ∑ m ∈ Finset.range K, (m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B))
      atTop (nhds (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B))) :=
    hsumm_d.hasSum.tendsto_sum_nat
  simp_rw [hderiv_K] at hlim1
  have heq_d : deriv (fun ζ : ℂ ↦ ∑' m : ℕ, f m ζ) 0 =
      ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * normalizedTrace (A ^ m * B) :=
    tendsto_nhds_unique hlim1 hlim2
  exact heq_d ▸ hdiff_lim.hasDerivAt

end TracePolymerIdentityAndCumulant

end KrylovChaos
