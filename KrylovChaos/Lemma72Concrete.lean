/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.PolymerExpansionConcrete
import Mathlib.Topology.Order.IntermediateValue

/-!
# Concrete Lemma 7.2 (Positive Depolarized Frame) & Unconditional Theorem 1.3(a)–(b) `C_W`
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section Lemma72AndUnconditionalThm13

private lemma finset_prod_sum_pi {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (F : α → Finset β) (w : β → ℝ) :
    ∏ a ∈ T, ∑ b ∈ F a, w b =
      ∑ g ∈ T.pi F, ∏ a ∈ T.attach, w (g a.1 a.2) := by
  rw [Finset.prod_sum]

/-- **Connected-Polymer Sum ≤ Unordered Rooted Tree Sum**:
For any `E` with nonempty hyperedges and nonnegative weights `η`, the sum of `∏_{X ∈ γ} η X`
over all connected polymers `γ ⊆ E` containing `X₀` of size `≤ h + 1` is bounded by
`unorderedTreeSum E η h X₀`. -/
lemma sum_connectedPolymers_le_unorderedTreeSum {N : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X) :
    ∀ h : ℕ, ∀ X₀ ∈ E,
      ∑ γ ∈ (connectedPolymers E).filter (fun γ ↦ X₀ ∈ γ ∧ γ.card ≤ h + 1), ∏ X ∈ γ, η X ≤
        unorderedTreeSum E η h X₀ := by
  classical
  intro h
  induction h with
  | zero =>
    intro X₀ hX₀
    rw [unorderedTreeSum]
    have hsub : (connectedPolymers E).filter (fun γ ↦ X₀ ∈ γ ∧ γ.card ≤ 1) ⊆ {{X₀}} := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨_, hX₀γ, hcard⟩
      rw [Finset.mem_singleton]
      have h1 : γ.card = 1 := le_antisymm hcard (Finset.card_pos.mpr ⟨X₀, hX₀γ⟩)
      rcases Finset.card_eq_one.mp h1 with ⟨Y, rfl⟩
      rw [Finset.mem_singleton.mp hX₀γ]
    calc ∑ γ ∈ (connectedPolymers E).filter (fun γ ↦ X₀ ∈ γ ∧ γ.card ≤ 1), ∏ X ∈ γ, η X
        ≤ ∑ γ ∈ ({ {X₀} } : Finset (Polymer N)), ∏ X ∈ γ, η X :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun γ hγ _ ↦ by
            rw [Finset.mem_singleton.mp hγ, Finset.prod_singleton]; exact hη_nn X₀ hX₀
      _ = η X₀ := by simp
  | succ h ih =>
    intro X₀ hX₀
    rw [unorderedTreeSum]
    let N₀ : Finset (Finset (Fin N)) := E.filter (fun Y ↦ (X₀ ∩ Y).Nonempty)
    let F : Finset (Fin N) → Finset (Polymer N) := fun Y ↦
      (connectedPolymers E).filter (fun C ↦ Y ∈ C ∧ C.card ≤ h + 1)
    let dom := (connectedPolymers E).filter (fun γ ↦ X₀ ∈ γ ∧ γ.card ≤ h + 2)
    let target := N₀.powerset.sigma (fun T ↦ T.pi F)
    -- For each `γ ∈ dom`, decompose `γ.erase X₀` into connected components `I`
    have hdecomp : ∀ γ ∈ dom,
        ∃ I ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
          I.biUnion id = γ.erase X₀ := by
      intro γ hγ
      have hγE : γ ⊆ E := (mem_connectedPolymers.mp (Finset.mem_filter.mp hγ).1).1
      exact (compatible_connectedPolymers_bijection E hne).2 (γ.erase X₀)
        (Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hγE))
    -- Canonical representative `rep C ∈ C ∩ N₀`
    let rep : Polymer N → Finset (Fin N) := fun C ↦
      if hneCN : (C ∩ N₀).Nonempty then hneCN.choose else X₀
    have hcomp_hits : ∀ γ ∈ dom,
        ∀ I ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
        I.biUnion id = γ.erase X₀ →
        ∀ C ∈ I, (C ∩ N₀).Nonempty ∧ C ∈ F (rep C) := by
      intro γ hγ I hI hIU C hCI
      rcases Finset.mem_filter.mp hγ with ⟨hγconn_mem, hX₀γ, hcardγ⟩
      have hγconn : isConnectedPolymer γ := (mem_connectedPolymers.mp hγconn_mem).2
      have hCconn_mem : C ∈ connectedPolymers E :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1 hCI
      have hCconn : isConnectedPolymer C := (mem_connectedPolymers.mp hCconn_mem).2
      have hCsub_erase : C ⊆ γ.erase X₀ := by
        intro Y hY; rw [← hIU]; exact Finset.mem_biUnion.mpr ⟨C, hCI, hY⟩
      have hCsub_γ : C ⊆ γ := Finset.Subset.trans hCsub_erase (Finset.erase_subset _ _)
      have hX₀notC : X₀ ∉ C := fun hX₀C ↦ (Finset.mem_erase.mp (hCsub_erase hX₀C)).1 rfl
      have hhits : (C ∩ N₀).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hdisj_X₀ : Disjoint (polySupp C) X₀ := by
          rw [Finset.disjoint_left]
          intro x hxC hxX₀
          rcases Finset.mem_biUnion.mp hxC with ⟨Y, hYC, hxY⟩
          have hYE : Y ∈ E := (mem_connectedPolymers.mp hCconn_mem).1 hYC
          have hYN₀ : Y ∈ N₀ := Finset.mem_filter.mpr ⟨hYE, ⟨x, Finset.mem_inter.mpr ⟨hxX₀, hxY⟩⟩⟩
          have hYint : Y ∈ C ∩ N₀ := Finset.mem_inter.mpr ⟨hYC, hYN₀⟩
          rw [hempty] at hYint; simp at hYint
        have hdisj_rest : Disjoint (polySupp C) (polySupp (γ \ C)) := by
          rw [Finset.disjoint_left]
          intro x hxC hxR
          rcases Finset.mem_biUnion.mp hxR with ⟨Z, hZR, hxZ⟩
          rcases Finset.mem_sdiff.mp hZR with ⟨hZγ, hZnotC⟩
          by_cases hZX₀ : Z = X₀
          · subst hZX₀; exact Finset.disjoint_left.mp hdisj_X₀ hxC hxZ
          · have hZerase : Z ∈ γ.erase X₀ := Finset.mem_erase.mpr ⟨hZX₀, hZγ⟩
            rw [← hIU] at hZerase
            rcases Finset.mem_biUnion.mp hZerase with ⟨D, hDI, hZD⟩
            have hCD : C ≠ D := fun h ↦ hZnotC (h ▸ hZD)
            have hcomp := (Finset.mem_filter.mp hI).2 C hCI D hDI hCD
            unfold polyIncompat at hcomp; push Not at hcomp
            exact Finset.disjoint_left.mp hcomp hxC (Finset.mem_biUnion.mpr ⟨Z, hZD, hxZ⟩)
        exact hγconn.2 C (γ \ C) hCconn.1 ⟨X₀, Finset.mem_sdiff.mpr ⟨hX₀γ, hX₀notC⟩⟩
          (Finset.union_sdiff_of_subset hCsub_γ) Finset.disjoint_sdiff hdisj_rest
      refine ⟨hhits, ?_⟩
      have hrep_mem : rep C ∈ C ∩ N₀ := by simp only [rep, hhits, ↓reduceDIte]; exact hhits.choose_spec
      refine Finset.mem_filter.mpr ⟨hCconn_mem, (Finset.mem_inter.mp hrep_mem).1, ?_⟩
      have hcard_erase : (γ.erase X₀).card = γ.card - 1 := Finset.card_erase_of_mem hX₀γ
      have hle := Finset.card_le_card hCsub_erase
      omega
    -- Map `γ ∈ dom` into `target`
    let toTarget : Polymer N → Σ T : Finset (Finset (Fin N)), (∀ Y ∈ T, Polymer N) := fun γ ↦
      if hγ : γ ∈ dom then
        let I := (hdecomp γ hγ).choose
        let T := I.image rep
        ⟨T, fun Y hY ↦
          let hC : ∃ C ∈ I, rep C = Y := Finset.mem_image.mp hY
          hC.choose⟩
      else ⟨∅, fun _ h ↦ by simp at h⟩
    have hmap_mem : ∀ γ ∈ dom, toTarget γ ∈ target := by
      intro γ hγ
      simp only [toTarget, hγ, ↓reduceDIte, target, Finset.mem_sigma, Finset.mem_powerset,
        Finset.mem_pi]
      set I := (hdecomp γ hγ).choose
      have hI := (hdecomp γ hγ).choose_spec.1
      have hIU := (hdecomp γ hγ).choose_spec.2
      refine ⟨?_, ?_⟩
      · intro Y hY
        rcases Finset.mem_image.mp hY with ⟨C, hCI, rfl⟩
        have hhits := (hcomp_hits γ hγ I hI hIU C hCI).1
        have hrep_mem : rep C ∈ C ∩ N₀ := by simp only [rep, hhits, ↓reduceDIte]; exact hhits.choose_spec
        exact (Finset.mem_inter.mp hrep_mem).2
      · intro Y hY
        let hC : ∃ C ∈ I, rep C = Y := Finset.mem_image.mp hY
        have hCI : hC.choose ∈ I := hC.choose_spec.1
        have hrepC : rep hC.choose = Y := hC.choose_spec.2
        have htmp := (hcomp_hits γ hγ I hI hIU hC.choose hCI).2
        rwa [hrepC] at htmp
    have hrep_inj : ∀ (γ : Polymer N) (hγ : γ ∈ dom),
        let I := (hdecomp γ hγ).choose
        ∀ C₁ ∈ I, ∀ C₂ ∈ I, rep C₁ = rep C₂ → C₁ = C₂ := by
      intro γ hγ I C₁ hC₁ C₂ hC₂ heq
      have hI := (hdecomp γ hγ).choose_spec.1
      have hIU := (hdecomp γ hγ).choose_spec.2
      by_contra hne12
      have h1 := (hcomp_hits γ hγ I hI hIU C₁ hC₁).1
      have h2 := (hcomp_hits γ hγ I hI hIU C₂ hC₂).1
      have hr1 : rep C₁ ∈ C₁ ∩ N₀ := by simp only [rep, h1, ↓reduceDIte]; exact h1.choose_spec
      have hr2 : rep C₂ ∈ C₂ ∩ N₀ := by simp only [rep, h2, ↓reduceDIte]; exact h2.choose_spec
      have hY1 : rep C₁ ∈ C₁ := (Finset.mem_inter.mp hr1).1
      have hY2 : rep C₁ ∈ C₂ := heq ▸ (Finset.mem_inter.mp hr2).1
      have hYE : rep C₁ ∈ E := (Finset.mem_filter.mp (Finset.mem_inter.mp hr1).2).1
      rcases hne (rep C₁) hYE with ⟨x, hx⟩
      have hcomp := (Finset.mem_filter.mp hI).2 C₁ hC₁ C₂ hC₂ hne12
      unfold polyIncompat at hcomp; push Not at hcomp
      exact Finset.disjoint_left.mp hcomp
        (Finset.mem_biUnion.mpr ⟨rep C₁, hY1, hx⟩)
        (Finset.mem_biUnion.mpr ⟨rep C₁, hY2, hx⟩)
    have hrecover : ∀ γ ∈ dom,
        insert X₀ ((toTarget γ).1.attach.biUnion (fun Y ↦ (toTarget γ).2 Y.1 Y.2)) = γ := by
      intro γ hγ
      have hto : toTarget γ = ⟨(hdecomp γ hγ).choose.image rep,
          fun Y hY ↦ (Finset.mem_image.mp hY).choose⟩ := dif_pos hγ
      rw [hto]
      set I := (hdecomp γ hγ).choose
      have hIU := (hdecomp γ hγ).choose_spec.2
      have hbi : (I.image rep).attach.biUnion
          (fun Y ↦ (Finset.mem_image.mp Y.2).choose) = I.biUnion id := by
        ext Z
        simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, id_eq]
        constructor
        · rintro ⟨Y, hY, hZ⟩
          exact ⟨(Finset.mem_image.mp hY).choose, (Finset.mem_image.mp hY).choose_spec.1, hZ⟩
        · rintro ⟨C, hCI, hZC⟩
          have hY : rep C ∈ I.image rep := Finset.mem_image_of_mem rep hCI
          have hchoose_eq : (Finset.mem_image.mp hY).choose = C :=
            hrep_inj γ hγ _ (Finset.mem_image.mp hY).choose_spec.1 C hCI
              (Finset.mem_image.mp hY).choose_spec.2
          exact ⟨rep C, hY, hchoose_eq.symm ▸ hZC⟩
      rw [hbi, hIU, Finset.insert_erase (Finset.mem_filter.mp hγ).2.1]
    have htoTarget_inj : Set.InjOn toTarget (dom : Set (Polymer N)) := by
      intro γ₁ hγ₁ γ₂ hγ₂ heq
      rw [← hrecover γ₁ hγ₁, ← hrecover γ₂ hγ₂, heq]
    have hweight_eq : ∀ γ ∈ dom,
        ∏ X ∈ γ, η X = η X₀ * ∏ Y ∈ (toTarget γ).1.attach, ∏ X ∈ (toTarget γ).2 Y.1 Y.2, η X := by
      intro γ hγ
      have hX₀γ : X₀ ∈ γ := (Finset.mem_filter.mp hγ).2.1
      rw [← Finset.mul_prod_erase γ η hX₀γ]
      congr 1
      have hto : toTarget γ = ⟨(hdecomp γ hγ).choose.image rep,
          fun Y hY ↦ (Finset.mem_image.mp hY).choose⟩ := dif_pos hγ
      rw [hto]
      set I := (hdecomp γ hγ).choose
      have hI := (hdecomp γ hγ).choose_spec.1
      have hIU := (hdecomp γ hγ).choose_spec.2
      conv_lhs => rw [← hIU]
      have hpair_disj : (I : Set (Polymer N)).PairwiseDisjoint id := by
        intro C₁ hC₁ C₂ hC₂ hne12
        change Disjoint C₁ C₂
        rw [Finset.disjoint_left]
        intro X hX1 hX2
        have hXE : X ∈ E :=
          (mem_connectedPolymers.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1 hC₁)).1 hX1
        rcases hne X hXE with ⟨x, hx⟩
        have hcomp := (Finset.mem_filter.mp hI).2 C₁ hC₁ C₂ hC₂ hne12
        unfold polyIncompat at hcomp; push Not at hcomp
        exact Finset.disjoint_left.mp hcomp
          (Finset.mem_biUnion.mpr ⟨X, hX1, hx⟩)
          (Finset.mem_biUnion.mpr ⟨X, hX2, hx⟩)
      rw [Finset.prod_biUnion hpair_disj]
      refine Finset.prod_bij (fun C hC ↦ ⟨rep C, Finset.mem_image_of_mem rep hC⟩) ?_ ?_ ?_ ?_
      · intro C _; exact Finset.mem_attach _ _
      · intro C₁ hC₁ C₂ hC₂ heq
        exact hrep_inj γ hγ C₁ hC₁ C₂ hC₂ (congrArg Subtype.val heq)
      · intro ⟨Y, hY⟩ _
        rcases Finset.mem_image.mp hY with ⟨C, hCI, rfl⟩
        exact ⟨C, hCI, rfl⟩
      · intro C hC
        have hY : rep C ∈ I.image rep := Finset.mem_image_of_mem rep hC
        have hchoose_eq : (Finset.mem_image.mp hY).choose = C :=
          hrep_inj γ hγ _ (Finset.mem_image.mp hY).choose_spec.1 C hC
            (Finset.mem_image.mp hY).choose_spec.2
        simp only [id_eq, hchoose_eq]
    have hsum_le : ∑ γ ∈ dom, ∏ X ∈ γ, η X ≤
        ∑ p ∈ target, η X₀ * ∏ Y ∈ p.1.attach, ∏ X ∈ p.2 Y.1 Y.2, η X := by
      calc ∑ γ ∈ dom, ∏ X ∈ γ, η X
          = ∑ γ ∈ dom, η X₀ * ∏ Y ∈ (toTarget γ).1.attach, ∏ X ∈ (toTarget γ).2 Y.1 Y.2, η X :=
            Finset.sum_congr rfl hweight_eq
        _ = ∑ p ∈ dom.image toTarget, η X₀ * ∏ Y ∈ p.1.attach, ∏ X ∈ p.2 Y.1 Y.2, η X := by
            rw [Finset.sum_image htoTarget_inj]
        _ ≤ ∑ p ∈ target, η X₀ * ∏ Y ∈ p.1.attach, ∏ X ∈ p.2 Y.1 Y.2, η X := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmap_mem) ?_
            intro p hp _
            refine mul_nonneg (hη_nn X₀ hX₀) (Finset.prod_nonneg fun Y _ ↦ ?_)
            have hCmem := (Finset.mem_pi.mp (Finset.mem_sigma.mp hp).2) Y.1 Y.2
            have hCE : p.2 Y.1 Y.2 ⊆ E := (mem_connectedPolymers.mp (Finset.mem_filter.mp hCmem).1).1
            exact Finset.prod_nonneg fun X hX ↦ hη_nn X (hCE hX)
    have htarget_eq : ∑ p ∈ target, η X₀ * ∏ Y ∈ p.1.attach, ∏ X ∈ p.2 Y.1 Y.2, η X =
        η X₀ * ∏ Y ∈ N₀, (1 + ∑ C ∈ F Y, ∏ X ∈ C, η X) := by
      dsimp only [target]
      rw [Finset.sum_sigma]
      simp_rw [← Finset.mul_sum]
      congr 1
      have hinner : ∀ T ∈ N₀.powerset,
          (∑ g ∈ T.pi F, ∏ Y ∈ T.attach, ∏ X ∈ g Y.1 Y.2, η X) =
            ∏ Y ∈ T, ∑ C ∈ F Y, ∏ X ∈ C, η X := fun T _ ↦
        (finset_prod_sum_pi T F (fun C ↦ ∏ X ∈ C, η X)).symm
      rw [Finset.sum_congr rfl hinner, Finset.prod_one_add]
    calc ∑ γ ∈ dom, ∏ X ∈ γ, η X
        ≤ η X₀ * ∏ Y ∈ N₀, (1 + ∑ C ∈ F Y, ∏ X ∈ C, η X) := htarget_eq ▸ hsum_le
      _ ≤ η X₀ * ∏ Y ∈ N₀, (1 + unorderedTreeSum E η h Y) := by
          apply mul_le_mul_of_nonneg_left _ (hη_nn X₀ hX₀)
          apply real_prod_le_prod
          · intro Y hY
            have hnn : 0 ≤ ∑ C ∈ F Y, ∏ X ∈ C, η X := Finset.sum_nonneg fun C hC ↦
              Finset.prod_nonneg fun X hX ↦
                hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hC).1).1 hX)
            linarith
          · intro Y hY
            linarith [ih Y (Finset.mem_filter.mp hY).1]

private lemma hermFunc_exp_real_isHermitian {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (c : ℝ) :
    (hermFunc hH (fun e ↦ Complex.exp (-(c : ℂ) * (e : ℂ)))).IsHermitian := by
  have hfn : (fun e : ℝ ↦ Complex.exp (-(c : ℂ) * (e : ℂ))) =
      fun e ↦ ((Real.exp (-c * e) : ℝ) : ℂ) := by
    funext e; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hfn]
  unfold hermFunc Matrix.IsHermitian
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  congr 2; ext i j
  simp only [Matrix.diagonal_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  split_ifs <;> rfl

private lemma depolDualWeight_exp_re_pos_of_nonzero {N : ℕ}
    {H : QubitOp N} (hH : H.IsHermitian) (s : Fin N → Fin 6) (β : ℝ)
    (hnonzero : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) ≠ 0) :
    0 < (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re := by
  let f : ℝ → ℝ := fun t ↦
    (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ))))).re
  have hf_cont : Continuous f := by
    let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
    have hherm_cont : Continuous (fun t : ℝ ↦
        hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      have hentry : (fun t : ℝ ↦
          (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) i j) =
          fun t : ℝ ↦ ∑ k : QubitIdx N, U i k *
            Complex.exp (-((t : ℂ) * ((β / 2 : ℝ) : ℂ)) * (hH.eigenvalues k : ℂ)) * Uᴴ k j := by
        funext t
        unfold hermFunc
        simp only [U, Matrix.mul_apply, Matrix.diagonal_apply]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hyx; simp [hyx]
        · intro hx; exact absurd (Finset.mem_univ x) hx
      rw [hentry]
      fun_prop
    exact Complex.continuous_re.comp ((depolDualWeight_continuous s).comp hherm_cont)
  have hf0 : f 0 = 1 := by
    dsimp only [f]
    have h1 : (fun e : ℝ ↦ Complex.exp (-((0 : ℝ) * (β / 2) : ℂ) * (e : ℂ))) = fun _ ↦ 1 := by
      funext e; simp
    rw [h1, hermFunc_one, depolDualWeight_one]; simp
  have hf_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht hft0
    have him : (depolDualWeight s
        (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ))))).im = 0 := by
      apply depolDualWeight_im_eq_zero_of_herm s
      convert hermFunc_exp_real_isHermitian hH (t * (β / 2)) using 2
      funext e; push_cast; ring
    have hz : depolDualWeight s
        (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) = 0 :=
      Complex.ext hft0 him
    exact hnonzero t ht hz
  by_contra hle
  push Not at hle
  have h1_val : f 1 = (depolDualWeight s
      (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re := by
    dsimp only [f]; congr 3; funext e; simp
  have h0mem' : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by linarith [h1_val], by linarith⟩
  rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf_cont.continuousOn h0mem' with
    ⟨t, ht, hft⟩
  exact hf_ne t ht hft

/-- **Lemma 7.2 (Concrete Positive Depolarized Frame Representation — Open Sub-Gap 1)**:
For ANY local Hamiltonian `H = ∑ X ∈ E, h X` with `∀ X ∈ E, X.Nonempty ∧ X.card ≤ r`,
`∀ X, h X ∈ supportedOn X`, `hH : H.IsHermitian`, inverse temperature `β ≥ 0`, and
high-temperature Kotecký–Preiss parameters `η₀, c > 0` satisfying:
- `∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), 6 ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀`
- `η₀ * Real.exp (2 * c * r) ≤ c`

there exists a STRICTLY POSITIVE weight function `π : (Fin N → Fin 6) → ℝ` (`∀ s, 0 < π s`)
such that:
`gibbsRhoHalf hH β = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s`. -/
theorem lemma_7_2_concrete_positive_frame {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    (hsite : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c) :
    ∃ π : (Fin N → Fin 6) → ℝ, (∀ s, 0 < π s) ∧
      gibbsRhoHalf hH β = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s := by
  let Λ₀ : Finset (Polymer N) := connectedPolymers E
  let a : Polymer N → ℝ := fun γ ↦ c * (∑ X ∈ γ, (X.card : ℝ))
  let η : Finset (Fin N) → ℝ := fun X ↦
    (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1)
  let ηTilde : Finset (Fin N) → ℝ := fun X ↦ η X * Real.exp (c * (X.card : ℝ))
  have hη_nn : ∀ X ∈ E, 0 ≤ η X := fun X _ ↦ by
    apply mul_nonneg (pow_nonneg (by norm_num) _)
    have : (1 : ℝ) ≤ Real.exp ((β / 2) * opNorm (h X)) :=
      Real.one_le_exp (mul_nonneg (by linarith) (opNorm_nonneg _))
    linarith
  have hηTilde_nn : ∀ X ∈ E, 0 ≤ ηTilde X := fun X hX ↦
    mul_nonneg (hη_nn X hX) (Real.exp_pos _).le
  have hηTilde_site : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X), ηTilde X ≤ η₀ * Real.exp (c * (r : ℝ)) := by
    intro x
    calc ∑ X ∈ E.filter (fun X ↦ x ∈ X), ηTilde X
        ≤ ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X * Real.exp (c * (r : ℝ)) := by
          apply Finset.sum_le_sum; intro X hX
          apply mul_le_mul_of_nonneg_left _ (hη_nn X (Finset.mem_filter.mp hX).1)
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ hc.le
          exact_mod_cast hcard X (Finset.mem_filter.mp hX).1
      _ = (∑ X ∈ E.filter (fun X ↦ x ∈ X), η X) * Real.exp (c * (r : ℝ)) := by rw [← Finset.sum_mul]
      _ ≤ η₀ * Real.exp (c * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right (hsite x) (Real.exp_pos _).le
  have hcond_tilde : (η₀ * Real.exp (c * (r : ℝ))) * Real.exp (c * (r : ℝ)) ≤ c := by
    rw [mul_assoc, ← Real.exp_add]
    have : c * (r : ℝ) + c * (r : ℝ) = 2 * c * (r : ℝ) := by ring
    rw [this]; exact hkp_param
  -- Show `depolDualWeight s (exp(-(t * β/2) H)) ≠ 0` for every `t ∈ [0, 1]` and `s`
  have hnonzero : ∀ s : Fin N → Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) ≠ 0 := by
    intro s t ht
    have ht_nn : 0 ≤ t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have hβ'_abs : |t * (β / 2)| ≤ β / 2 := by
      rw [abs_of_nonneg (mul_nonneg ht_nn (by linarith))]
      nlinarith
    have hkp : ∀ γ ∈ Λ₀,
        ∑ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'),
          kpActivity (polyWeight h s (t * (β / 2))) a γ' ≤ a γ := by
      intro γ hγ
      have hact_le : ∀ γ' ∈ Λ₀,
          kpActivity (polyWeight h s (t * (β / 2))) a γ' ≤ ∏ X ∈ γ', ηTilde X := by
        intro γ' hγ'
        unfold kpActivity a
        have hw := norm_polyWeight_le h hsupp s (t * (β / 2)) γ'
        have hstep : ∏ X ∈ γ', (6 : ℝ) ^ X.card * (Real.exp (|t * (β / 2)| * opNorm (h X)) - 1) ≤
            ∏ X ∈ γ', η X := by
          apply real_prod_le_prod
          · intro X _; apply mul_nonneg (pow_nonneg (by norm_num) _)
            have : (1 : ℝ) ≤ Real.exp (|t * (β / 2)| * opNorm (h X)) :=
              Real.one_le_exp (mul_nonneg (abs_nonneg _) (opNorm_nonneg _))
            linarith
          · intro X _
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            have : Real.exp (|t * (β / 2)| * opNorm (h X)) ≤ Real.exp ((β / 2) * opNorm (h X)) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ'_abs (opNorm_nonneg _))
            linarith
        calc ‖polyWeight h s (t * (β / 2)) γ'‖ * Real.exp (c * ∑ X ∈ γ', (X.card : ℝ))
            ≤ (∏ X ∈ γ', η X) * Real.exp (∑ X ∈ γ', c * (X.card : ℝ)) := by
              rw [← Finset.mul_sum]
              exact mul_le_mul_of_nonneg_right (le_trans hw hstep) (Real.exp_pos _).le
          _ = (∏ X ∈ γ', η X) * ∏ X ∈ γ', Real.exp (c * (X.card : ℝ)) := by rw [Real.exp_sum]
          _ = ∏ X ∈ γ', ηTilde X := by rw [← Finset.prod_mul_distrib]
      have htree_bound : ∀ Y ∈ E,
          ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X ≤
            ηTilde Y * Real.exp (c * (Y.card : ℝ)) := by
        intro Y hY
        have hsub_card : Λ₀.filter (fun γ' ↦ Y ∈ γ') ⊆
            (connectedPolymers E).filter (fun γ' ↦ Y ∈ γ' ∧ γ'.card ≤ E.card + 1) := by
          intro γ' hγ'
          rcases Finset.mem_filter.mp hγ' with ⟨hγ'Λ, hYγ'⟩
          refine Finset.mem_filter.mpr ⟨hγ'Λ, hYγ', ?_⟩
          have hle := Finset.card_le_card (mem_connectedPolymers.mp hγ'Λ).1
          omega
        calc ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X
            ≤ ∑ γ' ∈ (connectedPolymers E).filter (fun γ' ↦ Y ∈ γ' ∧ γ'.card ≤ E.card + 1),
                ∏ X ∈ γ', ηTilde X :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_card fun γ' hγ' _ ↦
                Finset.prod_nonneg fun X hX ↦
                  hηTilde_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ').1).1 hX)
          _ ≤ unorderedTreeSum E ηTilde E.card Y :=
              sum_connectedPolymers_le_unorderedTreeSum E hne ηTilde hηTilde_nn E.card Y hY
          _ ≤ ηTilde Y * Real.exp (c * (Y.card : ℝ)) :=
              lemma_A_3_concrete_unordered_tree_sum E hcard ηTilde hηTilde_nn hc.le
                hηTilde_site hcond_tilde E.card Y hY
      -- Cover `{γ' ∈ Λ₀ | polyIncompat γ γ'}` by `x ∈ polySupp γ` and `Y ∈ E` with `x ∈ Y`
      have hcover : ∑ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'), ∏ X ∈ γ', ηTilde X ≤
          ∑ x ∈ polySupp γ, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
            ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X := by
        have h1 : ∀ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'),
            ∃ x ∈ polySupp γ, ∃ Y ∈ E.filter (fun Y ↦ x ∈ Y), γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ') := by
          intro γ' hγ'
          rcases Finset.mem_filter.mp hγ' with ⟨hγ'Λ, hinc⟩
          unfold polyIncompat at hinc
          rw [Finset.not_disjoint_iff] at hinc
          rcases hinc with ⟨x, hxγ, hxγ'⟩
          rcases Finset.mem_biUnion.mp hxγ' with ⟨Y, hYγ', hxY⟩
          have hYE : Y ∈ E := (mem_connectedPolymers.mp hγ'Λ).1 hYγ'
          exact ⟨x, hxγ, Y, Finset.mem_filter.mpr ⟨hYE, hxY⟩, Finset.mem_filter.mpr ⟨hγ'Λ, hYγ'⟩⟩
        have hsub_u : Λ₀.filter (fun γ' ↦ polyIncompat γ γ') ⊆
            (polySupp γ).biUnion (fun x ↦
              (E.filter (fun Y ↦ x ∈ Y)).biUnion (fun Y ↦ Λ₀.filter (fun γ' ↦ Y ∈ γ'))) := by
          intro γ' hγ'
          rcases h1 γ' hγ' with ⟨x, hx, Y, hY, hγ'Y⟩
          exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr ⟨Y, hY, hγ'Y⟩⟩
        have hnn : ∀ γ' ∈ (polySupp γ).biUnion (fun x ↦
            (E.filter (fun Y ↦ x ∈ Y)).biUnion (fun Y ↦ Λ₀.filter (fun γ' ↦ Y ∈ γ'))),
            0 ≤ ∏ X ∈ γ', ηTilde X := by
          intro γ' hγ'
          rcases Finset.mem_biUnion.mp hγ' with ⟨_, _, h2⟩
          rcases Finset.mem_biUnion.mp h2 with ⟨_, _, h3⟩
          have hγ'E := (mem_connectedPolymers.mp (Finset.mem_filter.mp h3).1).1
          exact Finset.prod_nonneg fun X hX ↦ hηTilde_nn X (hγ'E hX)
        calc ∑ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'), ∏ X ∈ γ', ηTilde X
            ≤ ∑ γ' ∈ (polySupp γ).biUnion (fun x ↦
                (E.filter (fun Y ↦ x ∈ Y)).biUnion (fun Y ↦ Λ₀.filter (fun γ' ↦ Y ∈ γ'))),
                ∏ X ∈ γ', ηTilde X :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_u fun γ' hγ' _ ↦ hnn γ' hγ'
          _ ≤ ∑ x ∈ polySupp γ,
                ∑ γ' ∈ (E.filter (fun Y ↦ x ∈ Y)).biUnion (fun Y ↦ Λ₀.filter (fun γ' ↦ Y ∈ γ')),
                  ∏ X ∈ γ', ηTilde X := by
              refine real_sum_biUnion_le _ _ _ fun γ' hγ' ↦ ?_
              rcases Finset.mem_biUnion.mp hγ' with ⟨_, _, h3⟩
              rcases Finset.mem_biUnion.mp h3 with ⟨_, _, h4⟩
              have hγ'E := (mem_connectedPolymers.mp (Finset.mem_filter.mp h4).1).1
              exact Finset.prod_nonneg fun X hX ↦ hηTilde_nn X (hγ'E hX)
          _ ≤ ∑ x ∈ polySupp γ, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
                ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X := by
              apply Finset.sum_le_sum; intro x _
              refine real_sum_biUnion_le _ _ _ fun γ' hγ' ↦ ?_
              rcases Finset.mem_biUnion.mp hγ' with ⟨_, _, h4⟩
              have hγ'E := (mem_connectedPolymers.mp (Finset.mem_filter.mp h4).1).1
              exact Finset.prod_nonneg fun X hX ↦ hηTilde_nn X (hγ'E hX)
      have hsite_c : ∀ x : Fin N,
          ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
            ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X ≤ c := by
        intro x
        calc ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
                ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X
            ≤ ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), ηTilde Y * Real.exp (c * (Y.card : ℝ)) :=
              Finset.sum_le_sum fun Y hY ↦ htree_bound Y (Finset.mem_filter.mp hY).1
          _ ≤ ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), ηTilde Y * Real.exp (c * (r : ℝ)) := by
              apply Finset.sum_le_sum; intro Y hY
              apply mul_le_mul_of_nonneg_left _ (hηTilde_nn Y (Finset.mem_filter.mp hY).1)
              apply Real.exp_le_exp.mpr
              apply mul_le_mul_of_nonneg_left _ hc.le
              exact_mod_cast hcard Y (Finset.mem_filter.mp hY).1
          _ = (∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), ηTilde Y) * Real.exp (c * (r : ℝ)) := by
              rw [← Finset.sum_mul]
          _ ≤ (η₀ * Real.exp (c * (r : ℝ))) * Real.exp (c * (r : ℝ)) :=
              mul_le_mul_of_nonneg_right (hηTilde_site x) (Real.exp_pos _).le
          _ ≤ c := hcond_tilde
      have hcard_supp : ((polySupp γ).card : ℝ) ≤ ∑ X ∈ γ, (X.card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      calc ∑ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'),
              kpActivity (polyWeight h s (t * (β / 2))) a γ'
          ≤ ∑ γ' ∈ Λ₀.filter (fun γ' ↦ polyIncompat γ γ'), ∏ X ∈ γ', ηTilde X :=
            Finset.sum_le_sum fun γ' hγ' ↦ hact_le γ' (Finset.mem_filter.mp hγ').1
        _ ≤ ∑ x ∈ polySupp γ, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
              ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X := hcover
        _ ≤ ∑ _x ∈ polySupp γ, c := Finset.sum_le_sum fun x _ ↦ hsite_c x
        _ = ((polySupp γ).card : ℝ) * c := by simp
        _ ≤ (∑ X ∈ γ, (X.card : ℝ)) * c := mul_le_mul_of_nonneg_right hcard_supp hc.le
        _ = a γ := by dsimp only [a]; ring
    -- Apply Kotecký–Preiss on `Λ₀` (noting `polyIncompat` is reflexive on `Λ₀` since every `γ ∈ Λ₀` has nonempty support)
    let incompatRefl : Polymer N → Polymer N → Prop := fun γ₁ γ₂ ↦ γ₁ = γ₂ ∨ polyIncompat γ₁ γ₂
    have hrefl : ∀ γ, incompatRefl γ γ := fun _ ↦ Or.inl rfl
    have hsym : ∀ γ₁ γ₂, incompatRefl γ₁ γ₂ → incompatRefl γ₂ γ₁ := by
      rintro γ₁ γ₂ (rfl | hinc)
      · exact Or.inl rfl
      · exact Or.inr (polyIncompat_symm _ _ hinc)
    have hinc_eq : ∀ γ ∈ Λ₀, ∀ γ' ∈ Λ₀, incompatRefl γ γ' ↔ polyIncompat γ γ' := by
      intro γ hγ γ' _
      constructor
      · rintro (rfl | hinc)
        · unfold polyIncompat
          rcases (mem_connectedPolymers.mp hγ).2.1 with ⟨X, hXγ⟩
          rcases hne X ((mem_connectedPolymers.mp hγ).1 hXγ) with ⟨x, hxX⟩
          intro hd
          exact Finset.disjoint_left.mp hd
            (Finset.mem_biUnion.mpr ⟨X, hXγ, hxX⟩)
            (Finset.mem_biUnion.mpr ⟨X, hXγ, hxX⟩)
        · exact hinc
      · exact Or.inr
    have hkp' : ∀ γ ∈ Λ₀,
        ∑ γ' ∈ Λ₀.filter (fun γ' ↦ incompatRefl γ γ'),
          kpActivity (polyWeight h s (t * (β / 2))) a γ' ≤ a γ := by
      intro γ hγ
      have hfeq : Λ₀.filter (fun γ' ↦ incompatRefl γ γ') = Λ₀.filter (fun γ' ↦ polyIncompat γ γ') := by
        ext γ'; simp only [Finset.mem_filter]
        exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (hinc_eq γ hγ γ' h1).mp h2⟩,
               fun ⟨h1, h2⟩ ↦ ⟨h1, (hinc_eq γ hγ γ' h1).mpr h2⟩⟩
      rw [hfeq]; exact hkp γ hγ
    have hZ_ne := (kotecky_preiss_convergence incompatRefl hrefl hsym
      (polyWeight h s (t * (β / 2))) a Λ₀ hkp' Λ₀ Finset.Subset.rfl).1
    have hZ_eq : polymerZ incompatRefl (polyWeight h s (t * (β / 2))) Λ₀ =
        polymerZ polyIncompat (polyWeight h s (t * (β / 2))) Λ₀ := by
      unfold polymerZ
      apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext I; simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hsub, hc⟩; refine ⟨hsub, fun a ha b hb hab ↦ ?_⟩
        rw [← hinc_eq a (hsub ha) b (hsub hb)]; exact hc a ha b hb hab
      · rintro ⟨hsub, hc⟩; refine ⟨hsub, fun a ha b hb hab ↦ ?_⟩
        rw [hinc_eq a (hsub ha) b (hsub hb)]; exact hc a ha b hb hab
    rw [hZ_eq] at hZ_ne
    have heq := depolDualWeight_exp_eq_polymerZ E hne h hsupp hH s (t * (β / 2))
    rw [← heq] at hZ_ne
    convert hZ_ne using 2
    congr 1; funext e; push_cast; ring
  -- By Intermediate Value Theorem on `t ∈ [0, 1]`, `0 < (depolDualWeight s (exp(-(β/2) H))).re`
  have hpos : ∀ s : Fin N → Fin 6,
      0 < (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re :=
    fun s ↦ depolDualWeight_exp_re_pos_of_nonzero hH s β (hnonzero s)
  -- Assemble strictly positive `π s` for `gibbsRhoHalf hH β`
  let Zhalf : ℝ := Real.sqrt (gibbsPartitionFn hH β)
  have hZhalf_pos : 0 < Zhalf := Real.sqrt_pos.mpr (gibbsPartitionFn_pos hH β)
  let π : (Fin N → Fin 6) → ℝ := fun s ↦
    Zhalf⁻¹ * ((1 / 3 : ℝ) ^ N) *
      (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re
  refine ⟨π, fun s ↦ mul_pos (mul_pos (inv_pos.mpr hZhalf_pos) (pow_pos (by norm_num) N)) (hpos s), ?_⟩
  have hM_eq : gibbsRhoHalf hH β =
      ((Zhalf⁻¹ : ℝ) : ℂ) • hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))) := by
    unfold gibbsRhoHalf
    congr 1
    · simp only [Zhalf, Complex.ofReal_inv]
    · congr 1; funext e
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hM_eq]
  conv_lhs => rw [depol_global_reconstruct (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))]
  rw [smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [smul_smul]
  congr 1
  have him : (depolDualWeight s
      (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).im = 0 := by
    apply depolDualWeight_im_eq_zero_of_herm s
    convert hermFunc_exp_real_isHermitian hH (β / 2) using 2
    funext e; push_cast; ring
  have hre : depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ)))) =
      ((depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re : ℂ) :=
    Complex.ext rfl (by simp [him])
  rw [hre]
  dsimp only [π]
  push_cast; ring

/-- **Unconditional Theorem 1.3(a) (Zero `hρHalf` Hypothesis)**:
Directly from any `r`-local Hamiltonian `H = ∑ X ∈ E, h X` in the high-temperature
Kotecký–Preiss regime, for `G := concreteGibbsData hH β` and EVERY `A : QubitOp N`:
`(A | 𝒬̃^{(β)} A)_β^W ≤ ∑_x ‖𝒮_x(A)‖_{β,W}² ≤ 9 (A | 𝒬^{(β)} A)_β^W`. -/
theorem theorem_1_3a_unconditional {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    (hsite : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c)
    (A : QubitOp N) :
    (gibbsWightmanInner (concreteGibbsData hH β) A
        (quantumGlauberGen (concreteGibbsData hH β) A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq (concreteGibbsData hH β) (siteSizeOp x A) ∧
    ∑ x : Fin N, gibbsWightmanNormSq (concreteGibbsData hH β) (siteSizeOp x A) ≤
      9 * (gibbsWightmanInner (concreteGibbsData hH β) A
        (wightmanQ (concreteGibbsData hH β) A)).re := by
  rcases lemma_7_2_concrete_positive_frame E hne hcard h hsupp hH hβ hc hsite hkp_param with
    ⟨π, hπ_pos, hρHalf⟩
  exact theorem_1_3a_concrete_operator (concreteGibbsData hH β) π
    (fun s ↦ (hπ_pos s).le) hρHalf A

/-- **Unconditional Theorem 1.3(b) Part 1 — Equal-Time Commutator Bound (Zero `hρHalf` Hypothesis)**:
Directly from any `r`-local Hamiltonian `H = ∑ X ∈ E, h X` in the high-temperature
Kotecký–Preiss regime, for `G := concreteGibbsData hH β` and EVERY `A : QubitOp N`:
`otocCW G A ≤ 54 * Re (A | 𝒬^{(β)} A)_β^W`. -/
theorem theorem_1_3b_CW_unconditional {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    (hsite : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c)
    (A : QubitOp N) :
    otocCW (concreteGibbsData hH β) A ≤
      54 * (gibbsWightmanInner (concreteGibbsData hH β) A
        (wightmanQ (concreteGibbsData hH β) A)).re := by
  rcases lemma_7_2_concrete_positive_frame E hne hcard h hsupp hH hβ hc hsite hkp_param with
    ⟨π, hπ_pos, hρHalf⟩
  exact theorem_1_3b_concrete_CW (concreteGibbsData hH β) π
    (fun s ↦ (hπ_pos s).le) hρHalf A

end Lemma72AndUnconditionalThm13

end KrylovChaos
