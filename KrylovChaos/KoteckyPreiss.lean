/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Ground-Up Proof of the Kotecký–Preiss Polymer Cluster-Expansion Convergence Theorem

Proves from scratch (using only Mathlib, zero external axioms or literature hypotheses)
the full Kotecký–Preiss (1986) / Dobrushin–Scott–Sokal convergence theorem for any finite
polymer system `(Γ, incompat, w)` satisfying the KP criterion:
`∑_{γ' ≁ γ} ‖w γ'‖ e^{a γ'} ≤ a γ`.

Specifically:
1. `polymerZ_eq_add_incompat`: Exact deletion-neighborhood recursion
   `Z(Λ) = Z(Λ \ {γ}) + w(γ) Z(Λ \ N[γ])`.
2. `kotecky_preiss_convergence`: Non-vanishing `Z(Λ) ≠ 0`, exact ratio deviation
   `‖Z(Λ) / Z(Λ \ {γ}) - 1‖ ≤ r(γ) / (1 + r(γ))`, and inverse ratio bound
   `‖Z(Λ \ {γ}) / Z(Λ)‖ ≤ 1 + r(γ)` where `r(γ) = ‖w γ‖ e^{a γ}`.
3. `kotecky_preiss_log_bound`: Exact two-sided exponential bound
   `exp(-∑_{γ ∈ Λ} ‖w γ‖ e^{a γ}) ≤ ‖Z(Λ)‖ ≤ exp(∑_{γ ∈ Λ} ‖w γ‖ e^{a γ})`.
-/

namespace KrylovChaos

private lemma kp_prod_le_prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

/-- Pairwise compatibility of a finite set of polymers `I` under incompatibility relation `incompat`. -/
abbrev isCompatPolymer {Γ : Type*} (incompat : Γ → Γ → Prop) (I : Finset Γ) : Prop :=
  ∀ γ₁ ∈ I, ∀ γ₂ ∈ I, γ₁ ≠ γ₂ → ¬ incompat γ₁ γ₂

/-- Finite-volume polymer partition function `Z(Λ) = ∑_{I ⊆ Λ, compat} ∏_{γ ∈ I} w(γ)`. -/
noncomputable def polymerZ {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (w : Γ → ℂ) (Λ : Finset Γ) : ℂ :=
  ∑ I ∈ Λ.powerset.filter (fun I ↦ isCompatPolymer incompat I), ∏ γ ∈ I, w γ

/-- Kotecký–Preiss effective activity `r(γ) = ‖w γ‖ e^{a γ}`. -/
noncomputable def kpActivity {Γ : Type*} (w : Γ → ℂ) (a : Γ → ℝ) (γ : Γ) : ℝ :=
  ‖w γ‖ * Real.exp (a γ)

lemma polymerZ_empty {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat] (w : Γ → ℂ) :
    polymerZ incompat w ∅ = 1 := by
  unfold polymerZ
  have h : (∅ : Finset Γ).powerset.filter (fun I ↦ isCompatPolymer incompat I) = {∅} := by
    ext I
    simp [isCompatPolymer]
  rw [h, Finset.sum_singleton, Finset.prod_empty]

/-- **Deletion–Neighborhood Recursion**: For any `γ ∈ Λ` and symmetric incompatibility `incompat`,
`Z(Λ) = Z(Λ \ {γ}) + w(γ) Z(Λ \ N[γ])`. -/
theorem polymerZ_eq_add_incompat {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (hrefl : ∀ γ, incompat γ γ)
    (hsym : ∀ γ₁ γ₂, incompat γ₁ γ₂ → incompat γ₂ γ₁)
    (w : Γ → ℂ) {Λ : Finset Γ} {γ : Γ} (hγ : γ ∈ Λ) :
    polymerZ incompat w Λ =
      polymerZ incompat w (Λ.erase γ) +
        w γ * polymerZ incompat w (Λ.filter (fun γ' ↦ ¬ incompat γ γ')) := by
  classical
  unfold polymerZ
  set S := Λ.powerset.filter (fun I ↦ isCompatPolymer incompat I)
  have hsplit : (∑ I ∈ S, ∏ x ∈ I, w x) =
      (∑ I ∈ S.filter (fun I ↦ γ ∉ I), ∏ x ∈ I, w x) +
      (∑ I ∈ S.filter (fun I ↦ γ ∈ I), ∏ x ∈ I, w x) := by
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  congr 1
  · congr 1
    ext I
    simp only [S, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hI, hc⟩, hnot⟩
      refine ⟨?_, hc⟩
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hEq ↦ hnot (hEq ▸ hx), hI hx⟩
    · rintro ⟨hI, hc⟩
      refine ⟨⟨fun x hx ↦ (Finset.mem_erase.mp (hI hx)).2, hc⟩, fun hmem ↦ ?_⟩
      exact (Finset.mem_erase.mp (hI hmem)).1 rfl
  · rw [Finset.mul_sum]
    refine Finset.sum_bij (fun I _ ↦ I.erase γ) ?_ ?_ ?_ ?_
    · intro I hI
      simp only [S, Finset.mem_filter, Finset.mem_powerset] at hI ⊢
      rcases hI with ⟨⟨hsub, hc⟩, hmem⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hne, hxI⟩
        exact Finset.mem_filter.mpr ⟨hsub hxI, fun hinc ↦ hc γ hmem x hxI (Ne.symm hne) hinc⟩
      · intro x hx y hy hxy
        exact hc x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
    · intro I₁ hI₁ I₂ hI₂ heq
      have h1 : γ ∈ I₁ := (Finset.mem_filter.mp hI₁).2
      have h2 : γ ∈ I₂ := (Finset.mem_filter.mp hI₂).2
      rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, heq]
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      rcases hJ with ⟨hsub, hc⟩
      have hnot : γ ∉ J := by
        intro hmem
        exact (Finset.mem_filter.mp (hsub hmem)).2 (hrefl γ)
      refine ⟨insert γ J, ?_, Finset.erase_insert hnot⟩
      simp only [S, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self γ J⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxJ
        · exact hγ
        · exact (Finset.mem_filter.mp (hsub hxJ)).1
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hxJ <;>
        rcases Finset.mem_insert.mp hy with rfl | hyJ
        · exact absurd rfl hxy
        · exact (Finset.mem_filter.mp (hsub hyJ)).2
        · intro hinc; exact (Finset.mem_filter.mp (hsub hxJ)).2 (hsym _ _ hinc)
        · exact hc x hxJ y hyJ hxy
    · intro I hI
      have hmem : γ ∈ I := (Finset.mem_filter.mp hI).2
      rw [← Finset.mul_prod_erase I w hmem]

/-- **Kotecký–Preiss (1986) Convergence Theorem (Ground-Up Proof)**:
For any finite polymer system `Λ₀` satisfying the Kotecký–Preiss criterion
`∀ γ ∈ Λ₀, ∑_{γ' ∈ Λ₀, γ' ≁ γ} ‖w γ'‖ e^{a γ'} ≤ a γ`,
every subset `Λ ⊆ Λ₀` has non-vanishing partition function `Z(Λ) ≠ 0` and satisfies
the exact ratio bounds `‖Z(Λ)/Z(Λ \ {γ}) - 1‖ ≤ r(γ)/(1 + r(γ))` and
`‖Z(Λ \ {γ})/Z(Λ)‖ ≤ 1 + r(γ)`. -/
theorem kotecky_preiss_convergence {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (hrefl : ∀ γ, incompat γ γ)
    (hsym : ∀ γ₁ γ₂, incompat γ₁ γ₂ → incompat γ₂ γ₁)
    (w : Γ → ℂ) (a : Γ → ℝ) (Λ₀ : Finset Γ)
    (hkp : ∀ γ ∈ Λ₀,
      ∑ γ' ∈ Λ₀.filter (fun γ' ↦ incompat γ γ'), kpActivity w a γ' ≤ a γ) :
    ∀ Λ ⊆ Λ₀,
      polymerZ incompat w Λ ≠ 0 ∧
      ∀ γ ∈ Λ,
        ‖polymerZ incompat w Λ / polymerZ incompat w (Λ.erase γ) - 1‖ ≤
          kpActivity w a γ / (1 + kpActivity w a γ) ∧
        ‖polymerZ incompat w (Λ.erase γ) / polymerZ incompat w Λ‖ ≤
          1 + kpActivity w a γ := by
  classical
  have hmain : ∀ n : ℕ, ∀ Λ ⊆ Λ₀, Λ.card = n →
      polymerZ incompat w Λ ≠ 0 ∧
      ∀ γ ∈ Λ,
        ‖polymerZ incompat w Λ / polymerZ incompat w (Λ.erase γ) - 1‖ ≤
          kpActivity w a γ / (1 + kpActivity w a γ) ∧
        ‖polymerZ incompat w (Λ.erase γ) / polymerZ incompat w Λ‖ ≤
          1 + kpActivity w a γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Λ hsub hcard
      by_cases hEmp : Λ = ∅
      · subst hEmp
        refine ⟨?_, fun γ hγ ↦ by simp at hγ⟩
        rw [polymerZ_empty]; exact one_ne_zero
      · have htele : ∀ B ⊆ Λ, B.card < n → ∀ A ⊆ B,
            polymerZ incompat w B ≠ 0 ∧
            ‖polymerZ incompat w A / polymerZ incompat w B‖ ≤
              ∏ x ∈ B \ A, (1 + kpActivity w a x) := by
          intro B hB hBlt
          have hBsub0 : B ⊆ Λ₀ := Finset.Subset.trans hB hsub
          have hBne : polymerZ incompat w B ≠ 0 :=
            (ih B.card hBlt B hBsub0 rfl).1
          suffices ∀ k : ℕ, ∀ A ⊆ B, (B \ A).card = k →
              ‖polymerZ incompat w A / polymerZ incompat w B‖ ≤
                ∏ x ∈ B \ A, (1 + kpActivity w a x) by
            intro A hAB; exact ⟨hBne, this (B \ A).card A hAB rfl⟩
          intro k
          induction k with
          | zero =>
            intro A hAB hk0
            have hEq : A = B := by
              have hdiff : B \ A = ∅ := Finset.card_eq_zero.mp hk0
              ext x
              constructor
              · exact fun hx ↦ hAB hx
              · intro hx
                by_contra hnot
                have : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hx, hnot⟩
                rw [hdiff] at this; simp at this
            subst hEq
            rw [div_self hBne, norm_one, Finset.sdiff_self, Finset.prod_empty]
          | succ k ihk =>
            intro A hAB hk
            have hne_diff : (B \ A).Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨x, hx⟩ := hne_diff
            rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxA⟩
            set A' := insert x A
            have hA'B : A' ⊆ B := Finset.insert_subset hxB hAB
            have hdiff_eq : B \ A = insert x (B \ A') := by
              ext y
              simp only [A', Finset.mem_sdiff, Finset.mem_insert]
              constructor
              · rintro ⟨hyB, hyA⟩
                by_cases hyx : y = x
                · exact Or.inl hyx
                · exact Or.inr ⟨hyB, fun h ↦ h.elim hyx hyA⟩
              · rintro (rfl | ⟨hyB, hnot⟩)
                · exact ⟨hxB, hxA⟩
                · exact ⟨hyB, fun hyA ↦ hnot (Or.inr hyA)⟩
            have hxnot : x ∉ B \ A' := by simp [A']
            have hcard' : (B \ A').card = k := by
              have h1 := congrArg Finset.card hdiff_eq
              rw [Finset.card_insert_of_notMem hxnot] at h1
              omega
            have hstep1 := ihk A' hA'B hcard'
            have hA'lt : A'.card < n := lt_of_le_of_lt (Finset.card_le_card hA'B) hBlt
            have hA'sub0 : A' ⊆ Λ₀ := Finset.Subset.trans hA'B hBsub0
            have hA'ne := (ih A'.card hA'lt A' hA'sub0 rfl).1
            have hstep2 := ((ih A'.card hA'lt A' hA'sub0 rfl).2 x
              (Finset.mem_insert_self x A)).2
            have herase : A'.erase x = A := Finset.erase_insert hxA
            rw [herase] at hstep2
            rw [hdiff_eq, Finset.prod_insert hxnot]
            have hdiv : polymerZ incompat w A / polymerZ incompat w B =
                (polymerZ incompat w A / polymerZ incompat w A') *
                  (polymerZ incompat w A' / polymerZ incompat w B) := by
              field_simp [hA'ne, hBne]
            rw [hdiv, norm_mul]
            exact mul_le_mul hstep2 hstep1 (norm_nonneg _) (by unfold kpActivity; positivity)
        have hratio : ∀ γ ∈ Λ,
            polymerZ incompat w Λ ≠ 0 ∧
            ‖polymerZ incompat w Λ / polymerZ incompat w (Λ.erase γ) - 1‖ ≤
              kpActivity w a γ / (1 + kpActivity w a γ) ∧
            ‖polymerZ incompat w (Λ.erase γ) / polymerZ incompat w Λ‖ ≤
              1 + kpActivity w a γ := by
          intro γ hγ
          set Λ' := Λ.erase γ
          set Λ'' := Λ.filter (fun γ' ↦ ¬ incompat γ γ')
          have hΛ'sub : Λ' ⊆ Λ := Finset.erase_subset γ Λ
          have hΛ'lt : Λ'.card < n := by
            rw [← hcard]; exact Finset.card_erase_lt_of_mem hγ
          have hΛ''sub : Λ'' ⊆ Λ' := by
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨hxΛ, hnot⟩
            exact Finset.mem_erase.mpr ⟨fun hEq ↦ hnot (hEq ▸ hrefl γ), hxΛ⟩
          obtain ⟨hΛ'ne, htele_bd⟩ := htele Λ' hΛ'sub hΛ'lt Λ'' hΛ''sub
          have hrec := polymerZ_eq_add_incompat incompat hrefl hsym w hγ
          have hquot : polymerZ incompat w Λ / polymerZ incompat w Λ' - 1 =
              w γ * (polymerZ incompat w Λ'' / polymerZ incompat w Λ') := by
            rw [hrec]; field_simp [hΛ'ne]; ring
          have hprod_le : (1 + kpActivity w a γ) * ∏ x ∈ Λ' \ Λ'', (1 + kpActivity w a x) ≤
              Real.exp (a γ) := by
            have hnot : γ ∉ Λ' \ Λ'' := by simp [Λ']
            have hins : (1 + kpActivity w a γ) * ∏ x ∈ Λ' \ Λ'', (1 + kpActivity w a x) =
                ∏ x ∈ insert γ (Λ' \ Λ''), (1 + kpActivity w a x) :=
              (Finset.prod_insert (f := fun x ↦ 1 + kpActivity w a x) hnot).symm
            rw [hins]
            have hexp_le : ∏ x ∈ insert γ (Λ' \ Λ''), (1 + kpActivity w a x) ≤
                ∏ x ∈ insert γ (Λ' \ Λ''), Real.exp (kpActivity w a x) := by
              apply kp_prod_le_prod
              · intro x _; unfold kpActivity; positivity
              · intro x _; linarith [Real.add_one_le_exp (kpActivity w a x)]
            rw [← Real.exp_sum] at hexp_le
            have hsub_inc : insert γ (Λ' \ Λ'') ⊆ Λ₀.filter (fun γ' ↦ incompat γ γ') := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact Finset.mem_filter.mpr ⟨hsub hγ, hrefl γ⟩
              · rcases Finset.mem_sdiff.mp hx' with ⟨hxΛ', hxnot⟩
                have hxΛ : x ∈ Λ := (Finset.mem_erase.mp hxΛ').2
                have hinc : incompat γ x := by
                  by_contra hni
                  exact hxnot (Finset.mem_filter.mpr ⟨hxΛ, hni⟩)
                exact Finset.mem_filter.mpr ⟨hsub hxΛ, hinc⟩
            have hsum_le : ∑ x ∈ insert γ (Λ' \ Λ''), kpActivity w a x ≤ a γ :=
              le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_inc
                (fun x _ _ ↦ by unfold kpActivity; positivity)) (hkp γ (hsub hγ))
            exact le_trans hexp_le (Real.exp_le_exp.mpr hsum_le)
          have hr_nn : 0 ≤ kpActivity w a γ := by unfold kpActivity; positivity
          have h1pr_pos : 0 < 1 + kpActivity w a γ := by linarith
          have hdev : ‖polymerZ incompat w Λ / polymerZ incompat w Λ' - 1‖ ≤
              kpActivity w a γ / (1 + kpActivity w a γ) := by
            rw [hquot, norm_mul]
            have h1 : ‖w γ‖ * ‖polymerZ incompat w Λ'' / polymerZ incompat w Λ'‖ ≤
                ‖w γ‖ * ∏ x ∈ Λ' \ Λ'', (1 + kpActivity w a x) :=
              mul_le_mul_of_nonneg_left htele_bd (norm_nonneg _)
            have h2 : ∏ x ∈ Λ' \ Λ'', (1 + kpActivity w a x) ≤
                Real.exp (a γ) / (1 + kpActivity w a γ) := by
              rw [le_div_iff₀ h1pr_pos]; linarith
            have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (w γ))
            have h4 : ‖w γ‖ * (Real.exp (a γ) / (1 + kpActivity w a γ)) =
                kpActivity w a γ / (1 + kpActivity w a γ) := by
              unfold kpActivity; ring
            linarith
          have hlow : 1 / (1 + kpActivity w a γ) ≤
              ‖polymerZ incompat w Λ / polymerZ incompat w Λ'‖ := by
            have htri : (1 : ℝ) - ‖polymerZ incompat w Λ / polymerZ incompat w Λ'‖ ≤
                ‖polymerZ incompat w Λ / polymerZ incompat w Λ' - 1‖ := by
              have := norm_sub_norm_le (1 : ℂ) (polymerZ incompat w Λ / polymerZ incompat w Λ')
              rw [norm_one, norm_sub_rev] at this
              exact this
            have hsub1 : (1 : ℝ) - kpActivity w a γ / (1 + kpActivity w a γ) =
                1 / (1 + kpActivity w a γ) := by
              field_simp [h1pr_pos.ne']; ring
            linarith
          have hΛne : polymerZ incompat w Λ ≠ 0 := by
            intro hzero
            rw [hzero, zero_div, norm_zero] at hlow
            linarith [div_pos one_pos h1pr_pos]
          have hinv : ‖polymerZ incompat w Λ' / polymerZ incompat w Λ‖ ≤
              1 + kpActivity w a γ := by
            rw [show polymerZ incompat w Λ' / polymerZ incompat w Λ =
              (polymerZ incompat w Λ / polymerZ incompat w Λ')⁻¹ by rw [inv_div], norm_inv]
            have := inv_anti₀ (div_pos one_pos h1pr_pos) hlow
            simpa [one_div] using this
          exact ⟨hΛne, hdev, hinv⟩
        obtain ⟨γ₀, hγ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
        exact ⟨(hratio γ₀ hγ₀).1, fun γ hγ ↦ ⟨(hratio γ hγ).2.1, (hratio γ hγ).2.2⟩⟩
  intro Λ hsub
  exact hmain Λ.card Λ hsub rfl

/-- **Kotecký–Preiss Two-Sided Partition-Function Bound**:
Under the Kotecký–Preiss criterion on `Λ₀`, for every `Λ ⊆ Λ₀`,
`exp(-∑_{γ ∈ Λ} ‖w γ‖ e^{a γ}) ≤ ‖Z(Λ)‖ ≤ exp(∑_{γ ∈ Λ} ‖w γ‖ e^{a γ})`. -/
theorem kotecky_preiss_log_bound {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (hrefl : ∀ γ, incompat γ γ)
    (hsym : ∀ γ₁ γ₂, incompat γ₁ γ₂ → incompat γ₂ γ₁)
    (w : Γ → ℂ) (a : Γ → ℝ) (Λ₀ : Finset Γ)
    (hkp : ∀ γ ∈ Λ₀,
      ∑ γ' ∈ Λ₀.filter (fun γ' ↦ incompat γ γ'), kpActivity w a γ' ≤ a γ) :
    ∀ Λ ⊆ Λ₀,
      Real.exp (-(∑ γ ∈ Λ, kpActivity w a γ)) ≤ ‖polymerZ incompat w Λ‖ ∧
      ‖polymerZ incompat w Λ‖ ≤ Real.exp (∑ γ ∈ Λ, kpActivity w a γ) := by
  classical
  have hconv := kotecky_preiss_convergence incompat hrefl hsym w a Λ₀ hkp
  intro Λ hsub
  induction Λ using Finset.induction_on with
  | empty =>
    rw [polymerZ_empty, norm_one, Finset.sum_empty, neg_zero, Real.exp_zero]
    exact ⟨le_rfl, le_rfl⟩
  | insert γ Λ hnot ih =>
    have hΛsub : Λ ⊆ Λ₀ := Finset.Subset.trans (Finset.subset_insert γ Λ) hsub
    obtain ⟨ih_lo, ih_hi⟩ := ih hΛsub
    obtain ⟨hZne, hrat⟩ := hconv (insert γ Λ) hsub
    obtain ⟨hdev, hinv⟩ := hrat γ (Finset.mem_insert_self γ Λ)
    rw [Finset.erase_insert hnot] at hdev hinv
    have hZΛne : polymerZ incompat w Λ ≠ 0 := (hconv Λ hΛsub).1
    have hr_nn : 0 ≤ kpActivity w a γ := by unfold kpActivity; positivity
    have h1pr_pos : 0 < 1 + kpActivity w a γ := by linarith
    have hup_step : ‖polymerZ incompat w (insert γ Λ)‖ ≤
        Real.exp (kpActivity w a γ) * ‖polymerZ incompat w Λ‖ := by
      have h1 : ‖polymerZ incompat w (insert γ Λ) / polymerZ incompat w Λ‖ ≤
          1 + kpActivity w a γ := by
        have htri : ‖polymerZ incompat w (insert γ Λ) / polymerZ incompat w Λ‖ - 1 ≤
            ‖polymerZ incompat w (insert γ Λ) / polymerZ incompat w Λ - 1‖ := by
          have := norm_sub_norm_le (polymerZ incompat w (insert γ Λ) / polymerZ incompat w Λ) 1
          rwa [norm_one] at this
        have hfrac : kpActivity w a γ / (1 + kpActivity w a γ) ≤ kpActivity w a γ := by
          rw [div_le_iff₀ h1pr_pos]; nlinarith
        linarith
      have h2 : 1 + kpActivity w a γ ≤ Real.exp (kpActivity w a γ) := by
        linarith [Real.add_one_le_exp (kpActivity w a γ)]
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hZΛne)] at h1
      have h3 := le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      linarith
    have hlo_step : Real.exp (-(kpActivity w a γ)) * ‖polymerZ incompat w Λ‖ ≤
        ‖polymerZ incompat w (insert γ Λ)‖ := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hZne)] at hinv
      have h2 : 1 + kpActivity w a γ ≤ Real.exp (kpActivity w a γ) := by
        linarith [Real.add_one_le_exp (kpActivity w a γ)]
      have h3 := le_trans hinv (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(kpActivity w a γ))).le
      have hcancel : Real.exp (-(kpActivity w a γ)) *
          (Real.exp (kpActivity w a γ) * ‖polymerZ incompat w (insert γ Λ)‖) =
          ‖polymerZ incompat w (insert γ Λ)‖ := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      linarith
    rw [Finset.sum_insert hnot]
    constructor
    · rw [neg_add, Real.exp_add]
      exact le_trans (mul_le_mul_of_nonneg_left ih_lo (Real.exp_pos _).le) hlo_step
    · rw [Real.exp_add]
      exact le_trans hup_step (mul_le_mul_of_nonneg_left ih_hi (Real.exp_pos _).le)

end KrylovChaos
