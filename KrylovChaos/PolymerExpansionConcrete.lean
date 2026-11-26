/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.SupportAndDualFrame
import KrylovChaos.ConcreteCombinatorics
import KrylovChaos.KoteckyPreiss
import Mathlib.Topology.Order.IntermediateValue

/-!
# Concrete Non-Commutative Polymer Expansion for Lemma 7.2 & Unconditional Theorem 1.3(a)–(b)
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section PolymerExpansion

/-- A polymer is a finite set of hyperedges (supports of local Hamiltonian terms). -/
abbrev Polymer (N : ℕ) := Finset (Finset (Fin N))

/-- Total lattice support of a polymer `γ`. -/
def polySupp {N : ℕ} (γ : Polymer N) : Finset (Fin N) := γ.biUnion id

/-- Two polymers are incompatible iff their supports intersect. -/
def polyIncompat {N : ℕ} (γ₁ γ₂ : Polymer N) : Prop :=
  ¬ Disjoint (polySupp γ₁) (polySupp γ₂)

instance {N : ℕ} : DecidableRel (polyIncompat (N := N)) :=
  fun γ₁ γ₂ ↦ by unfold polyIncompat; infer_instance

lemma polyIncompat_symm {N : ℕ} (γ₁ γ₂ : Polymer N) :
    polyIncompat γ₁ γ₂ → polyIncompat γ₂ γ₁ := by
  unfold polyIncompat; intro h hd; exact h hd.symm

/-- A polymer `γ` is connected if it is nonempty and cannot be partitioned into two
nonempty sub-polymers with disjoint supports. -/
def isConnectedPolymer {N : ℕ} (γ : Polymer N) : Prop :=
  γ.Nonempty ∧ ∀ γ₁ γ₂ : Polymer N, γ₁.Nonempty → γ₂.Nonempty →
    γ₁ ∪ γ₂ = γ → Disjoint γ₁ γ₂ → ¬ Disjoint (polySupp γ₁) (polySupp γ₂)

/-- The finite set of all connected polymers contained in `E`. -/
noncomputable def connectedPolymers {N : ℕ} (E : Finset (Finset (Fin N))) : Finset (Polymer N) :=
  letI := Classical.decPred (isConnectedPolymer (N := N))
  E.powerset.filter (fun γ ↦ isConnectedPolymer γ)

lemma mem_connectedPolymers {N : ℕ} {E : Finset (Finset (Fin N))} {γ : Polymer N} :
    γ ∈ connectedPolymers E ↔ γ ⊆ E ∧ isConnectedPolymer γ := by
  classical
  simp [connectedPolymers]

/-- One step of BFS reachability inside `S` under support overlap. -/
def overlapStep {N : ℕ} (S T : Polymer N) : Polymer N :=
  S.filter (fun Y ↦ ∃ Z ∈ T, ¬ Disjoint Y Z)

/-- Connected component of `X` inside `S`. -/
def reachComponent {N : ℕ} (S : Polymer N) (X : Finset (Fin N)) : Polymer N :=
  (overlapStep S)^[S.card] {X}

lemma overlapStep_subset {N : ℕ} (S T : Polymer N) : overlapStep S T ⊆ S :=
  Finset.filter_subset _ _

lemma overlapStep_mono {N : ℕ} (S : Polymer N) {T₁ T₂ : Polymer N} (h : T₁ ⊆ T₂) :
    overlapStep S T₁ ⊆ overlapStep S T₂ := by
  intro Y hY
  rcases Finset.mem_filter.mp hY with ⟨hYS, Z, hZT₁, hnd⟩
  exact Finset.mem_filter.mpr ⟨hYS, Z, h hZT₁, hnd⟩

lemma subset_overlapStep {N : ℕ} {S T : Polymer N} (hTS : T ⊆ S)
    (hne : ∀ Y ∈ T, Y.Nonempty) : T ⊆ overlapStep S T := by
  intro Y hY
  refine Finset.mem_filter.mpr ⟨hTS hY, Y, hY, ?_⟩
  intro hd; rcases hne Y hY with ⟨x, hx⟩; exact Finset.disjoint_left.mp hd hx hx

lemma reachComponent_subset {N : ℕ} {S : Polymer N} {X : Finset (Fin N)} (hX : X ∈ S) :
    reachComponent S X ⊆ S := by
  unfold reachComponent
  cases h : S.card with
  | zero => exact absurd (Finset.card_pos.mpr ⟨X, hX⟩) (by omega)
  | succ k => rw [Function.iterate_succ_apply']; exact overlapStep_subset _ _

lemma mem_reachComponent_self {N : ℕ} {S : Polymer N} {X : Finset (Fin N)}
    (hX : X ∈ S) (hXne : X.Nonempty) : X ∈ reachComponent S X := by
  unfold reachComponent
  suffices ∀ k : ℕ, X ∈ (overlapStep S)^[k] {X} from this S.card
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine Finset.mem_filter.mpr ⟨hX, X, ih, ?_⟩
    intro hd; rcases hXne with ⟨x, hx⟩; exact Finset.disjoint_left.mp hd hx hx

lemma reachComponent_fixpoint {N : ℕ} {S : Polymer N} {X : Finset (Fin N)}
    (hX : X ∈ S) (hne : ∀ Y ∈ S, Y.Nonempty) :
    overlapStep S (reachComponent S X) = reachComponent S X := by
  have hmono : ∀ k : ℕ, (overlapStep S)^[k] {X} ⊆ (overlapStep S)^[k + 1] {X} := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Function.iterate_one]
      exact subset_overlapStep (Finset.singleton_subset_iff.mpr hX)
        (fun Y hY ↦ by rw [Finset.mem_singleton.mp hY]; exact hne X hX)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact overlapStep_mono S ih
  have hsubS : ∀ k : ℕ, (overlapStep S)^[k] {X} ⊆ S := by
    intro k; cases k with
    | zero => exact Finset.singleton_subset_iff.mpr hX
    | succ k => rw [Function.iterate_succ_apply']; exact overlapStep_subset _ _
  have hex : ∃ k ≤ S.card, (overlapStep S)^[k + 1] {X} = (overlapStep S)^[k] {X} := by
    by_contra hall
    push Not at hall
    have hstrict : ∀ k ≤ S.card, k + 1 ≤ ((overlapStep S)^[k] {X}).card := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hlt : ((overlapStep S)^[k] {X}).card < ((overlapStep S)^[k + 1] {X}).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hmono k, Ne.symm (hall k (by omega))⟩)
        have := ih (by omega)
        omega
    have hbig := hstrict S.card le_rfl
    have hle := Finset.card_le_card (hsubS S.card)
    omega
  rcases hex with ⟨k, hk, heq⟩
  have hconst : ∀ m ≥ k, (overlapStep S)^[m] {X} = (overlapStep S)^[k] {X} := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega),
        ← Function.iterate_succ_apply' (overlapStep S), heq]
  unfold reachComponent
  rw [← Function.iterate_succ_apply' (overlapStep S), hconst (S.card + 1) (by omega), hconst S.card hk]

lemma reachComponent_disjoint_compl {N : ℕ} {S : Polymer N} {X : Finset (Fin N)}
    (hX : X ∈ S) (hne : ∀ Y ∈ S, Y.Nonempty) :
    Disjoint (polySupp (reachComponent S X)) (polySupp (S \ reachComponent S X)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_biUnion.mp hx1 with ⟨Z, hZ, hxZ⟩
  rcases Finset.mem_biUnion.mp hx2 with ⟨Y, hY, hxY⟩
  rcases Finset.mem_sdiff.mp hY with ⟨hYS, hYnot⟩
  have hYstep : Y ∈ overlapStep S (reachComponent S X) := by
    refine Finset.mem_filter.mpr ⟨hYS, Z, hZ, ?_⟩
    intro hd; exact Finset.disjoint_left.mp hd hxY hxZ
  rw [reachComponent_fixpoint hX hne] at hYstep
  exact hYnot hYstep

lemma reachComponent_connected {N : ℕ} {S : Polymer N} {X : Finset (Fin N)}
    (hX : X ∈ S) (hne : ∀ Y ∈ S, Y.Nonempty) :
    isConnectedPolymer (reachComponent S X) := by
  refine ⟨⟨X, mem_reachComponent_self hX (hne X hX)⟩, ?_⟩
  intro γ₁ γ₂ hne1 hne2 hunion hdisj hsupp_disj
  have hXmem : X ∈ γ₁ ∪ γ₂ := hunion.symm ▸ mem_reachComponent_self hX (hne X hX)
  suffices hstep : ∀ A B : Polymer N, X ∈ A → A ∪ B = reachComponent S X →
      Disjoint (polySupp A) (polySupp B) → ¬ B.Nonempty by
    rcases Finset.mem_union.mp hXmem with hX1 | hX2
    · exact hstep γ₁ γ₂ hX1 hunion hsupp_disj hne2
    · exact hstep γ₂ γ₁ hX2 (Finset.union_comm γ₂ γ₁ ▸ hunion) hsupp_disj.symm hne1
  intro A B hXA hAB hdAB hBne
  have hreach_in_A : ∀ k : ℕ, (overlapStep S)^[k] {X} ⊆ A := by
    intro k
    induction k with
    | zero => exact Finset.singleton_subset_iff.mpr hXA
    | succ k ih =>
      intro Y hY
      have hY_in_reach : Y ∈ reachComponent S X := by
        have hstep_sub : ∀ m : ℕ, (overlapStep S)^[m] {X} ⊆ reachComponent S X := by
          intro m
          induction m with
          | zero => exact Finset.singleton_subset_iff.mpr (mem_reachComponent_self hX (hne X hX))
          | succ m ihm =>
            rw [Function.iterate_succ_apply', ← reachComponent_fixpoint hX hne]
            exact overlapStep_mono S ihm
        exact hstep_sub (k + 1) hY
      rw [← hAB] at hY_in_reach
      rcases Finset.mem_union.mp hY_in_reach with hYA | hYB
      · exact hYA
      · exfalso
        rw [Function.iterate_succ_apply'] at hY
        rcases Finset.mem_filter.mp hY with ⟨_, Z, hZ, hnd⟩
        have hZA : Z ∈ A := ih hZ
        apply hnd
        rw [Finset.disjoint_left]
        intro x hxY hxZ
        exact Finset.disjoint_left.mp hdAB
          (Finset.mem_biUnion.mpr ⟨Z, hZA, hxZ⟩)
          (Finset.mem_biUnion.mpr ⟨Y, hYB, hxY⟩)
  have hsubA : reachComponent S X ⊆ A := hreach_in_A S.card
  rcases hBne with ⟨Y, hYB⟩
  have hYreach : Y ∈ reachComponent S X := hAB ▸ Finset.mem_union_right A hYB
  have hYA : Y ∈ A := hsubA hYreach
  rcases hne Y (reachComponent_subset hX hYreach) with ⟨x, hxY⟩
  exact Finset.disjoint_left.mp hdAB
    (Finset.mem_biUnion.mpr ⟨Y, hYA, hxY⟩)
    (Finset.mem_biUnion.mpr ⟨Y, hYB, hxY⟩)

/-- **Unique Connected-Component Decomposition**:
For any `E` whose hyperedges are nonempty, the map `I ↦ I.biUnion id` is a bijection from
compatible subsets of `connectedPolymers E` onto `E.powerset`. -/
lemma compatible_connectedPolymers_bijection {N : ℕ} (E : Finset (Finset (Fin N)))
    (hne : ∀ X ∈ E, X.Nonempty) :
    (∀ I₁ ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
      ∀ I₂ ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
      I₁.biUnion id = I₂.biUnion id → I₁ = I₂) ∧
    (∀ S ∈ E.powerset, ∃ I ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
      I.biUnion id = S) := by
  constructor
  · intro I₁ hI₁ I₂ hI₂ heq
    have hsub : ∀ J₁ J₂ : Finset (Polymer N),
        J₁ ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I) →
        J₂ ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I) →
        J₁.biUnion id = J₂.biUnion id → J₁ ⊆ J₂ := by
      intro J₁ J₂ hJ₁ hJ₂ hU γ hγ
      rcases Finset.mem_filter.mp hJ₁ with ⟨hJ₁sub, hJ₁comp⟩
      rcases Finset.mem_filter.mp hJ₂ with ⟨hJ₂sub, hJ₂comp⟩
      have hγconn : isConnectedPolymer γ :=
        (mem_connectedPolymers.mp (Finset.mem_powerset.mp hJ₁sub hγ)).2
      rcases hγconn.1 with ⟨X₀, hX₀γ⟩
      have hX₀U : X₀ ∈ J₂.biUnion id := hU ▸ Finset.mem_biUnion.mpr ⟨γ, hγ, hX₀γ⟩
      rcases Finset.mem_biUnion.mp hX₀U with ⟨δ, hδJ₂, hX₀δ⟩
      have hγ_sub_δ : γ ⊆ δ := by
        by_contra hnot
        have h1ne : (γ ∩ δ).Nonempty := ⟨X₀, Finset.mem_inter.mpr ⟨hX₀γ, hX₀δ⟩⟩
        have h2ne : (γ \ δ).Nonempty := Finset.sdiff_nonempty.mpr hnot
        have hunion : (γ ∩ δ) ∪ (γ \ δ) = γ := by ext Z; by_cases hZ : Z ∈ δ <;> simp [hZ]
        have hdisj : Disjoint (γ ∩ δ) (γ \ δ) := Finset.disjoint_left.mpr fun Z h1 h2 ↦ (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
        have hsupp_disj : Disjoint (polySupp (γ ∩ δ)) (polySupp (γ \ δ)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_biUnion.mp hx1 with ⟨Y, hY, hxY⟩
          rcases Finset.mem_biUnion.mp hx2 with ⟨Z, hZ, hxZ⟩
          have hYδ : Y ∈ δ := (Finset.mem_inter.mp hY).2
          have hZγ : Z ∈ γ := (Finset.mem_sdiff.mp hZ).1
          have hZnotδ : Z ∉ δ := (Finset.mem_sdiff.mp hZ).2
          have hZU : Z ∈ J₂.biUnion id := hU ▸ Finset.mem_biUnion.mpr ⟨γ, hγ, hZγ⟩
          rcases Finset.mem_biUnion.mp hZU with ⟨δ', hδ'J₂, hZδ'⟩
          have hne_δ : δ ≠ δ' := fun h ↦ hZnotδ (h ▸ hZδ')
          have hcomp := hJ₂comp δ hδJ₂ δ' hδ'J₂ hne_δ
          unfold polyIncompat at hcomp; push Not at hcomp
          exact Finset.disjoint_left.mp hcomp
            (Finset.mem_biUnion.mpr ⟨Y, hYδ, hxY⟩)
            (Finset.mem_biUnion.mpr ⟨Z, hZδ', hxZ⟩)
        exact hγconn.2 (γ ∩ δ) (γ \ δ) h1ne h2ne hunion hdisj hsupp_disj
      have hδ_sub_γ : δ ⊆ γ := by
        have hδconn : isConnectedPolymer δ :=
          (mem_connectedPolymers.mp (Finset.mem_powerset.mp hJ₂sub hδJ₂)).2
        by_contra hnot
        have h1ne : (δ ∩ γ).Nonempty := ⟨X₀, Finset.mem_inter.mpr ⟨hX₀δ, hX₀γ⟩⟩
        have h2ne : (δ \ γ).Nonempty := Finset.sdiff_nonempty.mpr hnot
        have hunion : (δ ∩ γ) ∪ (δ \ γ) = δ := by ext Z; by_cases hZ : Z ∈ γ <;> simp [hZ]
        have hdisj : Disjoint (δ ∩ γ) (δ \ γ) := Finset.disjoint_left.mpr fun Z h1 h2 ↦ (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
        have hsupp_disj : Disjoint (polySupp (δ ∩ γ)) (polySupp (δ \ γ)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_biUnion.mp hx1 with ⟨Y, hY, hxY⟩
          rcases Finset.mem_biUnion.mp hx2 with ⟨Z, hZ, hxZ⟩
          have hYγ : Y ∈ γ := (Finset.mem_inter.mp hY).2
          have hZδ : Z ∈ δ := (Finset.mem_sdiff.mp hZ).1
          have hZnotγ : Z ∉ γ := (Finset.mem_sdiff.mp hZ).2
          have hZU : Z ∈ J₁.biUnion id := hU.symm ▸ Finset.mem_biUnion.mpr ⟨δ, hδJ₂, hZδ⟩
          rcases Finset.mem_biUnion.mp hZU with ⟨γ', hγ'J₁, hZγ'⟩
          have hne_γ : γ ≠ γ' := fun h ↦ hZnotγ (h ▸ hZγ')
          have hcomp := hJ₁comp γ hγ γ' hγ'J₁ hne_γ
          unfold polyIncompat at hcomp; push Not at hcomp
          exact Finset.disjoint_left.mp hcomp
            (Finset.mem_biUnion.mpr ⟨Y, hYγ, hxY⟩)
            (Finset.mem_biUnion.mpr ⟨Z, hZγ', hxZ⟩)
        exact hδconn.2 (δ ∩ γ) (δ \ γ) h1ne h2ne hunion hdisj hsupp_disj
      have hγeq : γ = δ := Finset.Subset.antisymm hγ_sub_δ hδ_sub_γ
      exact hγeq ▸ hδJ₂
    exact Finset.Subset.antisymm (hsub I₁ I₂ hI₁ hI₂ heq) (hsub I₂ I₁ hI₂ hI₁ heq.symm)
  · intro S hS
    have hSE : S ⊆ E := Finset.mem_powerset.mp hS
    induction hn : S.card using Nat.strong_induction_on generalizing S with
    | h n ih =>
      rcases S.eq_empty_or_nonempty with rfl | ⟨X, hXS⟩
      · refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩, ?_⟩
        · intro γ hγ; simp at hγ
        · simp
      · let C := reachComponent S X
        have hCS : C ⊆ S := reachComponent_subset hXS
        have hXne : X.Nonempty := hne X (hSE hXS)
        have hXC : X ∈ C := mem_reachComponent_self hXS hXne
        have hCne : C.Nonempty := ⟨X, hXC⟩
        have hS'lt : (S \ C).card < n := by
          rw [← hn]
          exact Finset.card_lt_card (Finset.sdiff_ssubset hCS hCne)
        have hS'E : S \ C ⊆ E := Finset.Subset.trans Finset.sdiff_subset hSE
        rcases ih (S \ C).card hS'lt (S \ C) (Finset.mem_powerset.mpr hS'E) hS'E rfl with
          ⟨I', hI'mem, hI'U⟩
        rcases Finset.mem_filter.mp hI'mem with ⟨hI'sub, hI'comp⟩
        have hCmem : C ∈ connectedPolymers E :=
          mem_connectedPolymers.mpr ⟨Finset.Subset.trans hCS hSE,
            reachComponent_connected hXS (fun Y hY ↦ hne Y (hSE hY))⟩
        have hdisj_C : Disjoint (polySupp C) (polySupp (S \ C)) :=
          reachComponent_disjoint_compl hXS (fun Y hY ↦ hne Y (hSE hY))
        refine ⟨insert C I', Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hCmem, Finset.mem_powerset.mp hI'sub⟩
        · intro γ₁ hγ₁ γ₂ hγ₂ hne12
          rcases Finset.mem_insert.mp hγ₁ with rfl | hγ₁' <;>
          rcases Finset.mem_insert.mp hγ₂ with rfl | hγ₂'
          · exact absurd rfl hne12
          · unfold polyIncompat; push Not
            refine Finset.disjoint_of_subset_right ?_ hdisj_C
            intro x hx
            rcases Finset.mem_biUnion.mp hx with ⟨Y, hY, hxY⟩
            have hY' : Y ∈ S \ C := hI'U ▸ Finset.mem_biUnion.mpr ⟨γ₂, hγ₂', hY⟩
            exact Finset.mem_biUnion.mpr ⟨Y, hY', hxY⟩
          · unfold polyIncompat; push Not
            refine Finset.disjoint_of_subset_left ?_ hdisj_C.symm
            intro x hx
            rcases Finset.mem_biUnion.mp hx with ⟨Y, hY, hxY⟩
            have hY' : Y ∈ S \ C := hI'U ▸ Finset.mem_biUnion.mpr ⟨γ₁, hγ₁', hY⟩
            exact Finset.mem_biUnion.mpr ⟨Y, hY', hxY⟩
          · exact hI'comp γ₁ hγ₁' γ₂ hγ₂' hne12
        · rw [Finset.biUnion_insert, id_eq, hI'U, Finset.union_sdiff_of_subset hCS]

/-- Order-`m` surjective word sum on a polymer `γ`:
`∑_{f : Fin m → γ, im f = γ} ∏_j h(f j)`. -/
noncomputable def polyTermSum {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (γ : Polymer N) (m : ℕ) : QubitOp N :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin m ↦ γ).filter (fun f ↦ Finset.univ.image f = γ),
    (List.ofFn (fun j : Fin m ↦ h (f j))).prod

/-- Concrete non-commutative polymer operator `Q_γ(β') := ∑' m, ((-β')^m / m!) • polyTermSum h γ m`. -/
noncomputable def polyOp {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (β' : ℝ) (γ : Polymer N) : QubitOp N :=
  ∑' m : ℕ, ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m

/-- Concrete depolarized polymer weight `w_s(γ; β') := depolDualWeight s (polyOp h β' γ)`. -/
noncomputable def polyWeight {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (s : Fin N → Fin 6) (β' : ℝ) (γ : Polymer N) : ℂ :=
  depolDualWeight s (polyOp h β' γ)

lemma polyTermSum_mem_supportedOn {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (γ : Polymer N) (m : ℕ) :
    polyTermSum h γ m ∈ supportedOn (polySupp γ) := by
  unfold polyTermSum
  apply Submodule.sum_mem
  intro f hf
  apply supportedOn_list_prod_mem
  intro M hM
  rw [List.mem_ofFn] at hM
  rcases hM with ⟨j, rfl⟩
  have hfj : f j ∈ γ := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) j
  exact supportedOn_mono (Finset.subset_biUnion_of_mem id hfj) (hsupp (f j))

/-- Scalar surjective-word sum `∑_{f : Fin m → γ, im f = γ} ∏_j a(f j)`. -/
noncomputable def scalarWordSum {α : Type*} [DecidableEq α]
    (a : α → ℝ) (γ : Finset α) (m : ℕ) : ℝ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin m ↦ γ).filter (fun f ↦ Finset.univ.image f = γ),
    ∏ j : Fin m, a (f j)

lemma scalarWordSum_nonneg {α : Type*} [DecidableEq α]
    (a : α → ℝ) (ha : ∀ X, 0 ≤ a X) (γ : Finset α) (m : ℕ) :
    0 ≤ scalarWordSum a γ m :=
  Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun j _ ↦ ha _

lemma sum_scalarWordSum_powerset {α : Type*} [DecidableEq α]
    (a : α → ℝ) (γ : Finset α) (m : ℕ) :
    ∑ S ∈ γ.powerset, scalarWordSum a S m = (∑ X ∈ γ, a X) ^ m := by
  have hpi : (∑ X ∈ γ, a X) ^ m = ∑ f ∈ Fintype.piFinset (fun _ : Fin m ↦ γ), ∏ j : Fin m, a (f j) := by
    induction m with
    | zero =>
      have hsing : Fintype.piFinset (fun _ : Fin 0 ↦ γ) = {Fin.elim0} := by
        ext f; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
        constructor
        · intro _; funext j; exact Fin.elim0 j
        · rintro rfl j; exact Fin.elim0 j
      rw [hsing, Finset.sum_singleton]; simp
    | succ m ih =>
      rw [pow_succ', ih, Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_bij (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
      · intro p hp; rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
        rw [Fintype.mem_piFinset]; intro j
        exact Fin.cases h1 (fun k ↦ Fintype.mem_piFinset.mp h2 k) j
      · intro p₁ _ p₂ _ heq
        apply Prod.ext
        · have := congrFun heq 0; simpa using this
        · funext k; have := congrFun heq k.succ; simpa using this
      · intro f hf
        refine ⟨(f 0, Fin.tail f), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hf 0,
          Fintype.mem_piFinset.mpr fun k ↦ Fintype.mem_piFinset.mp hf k.succ⟩, ?_⟩
        funext j; exact Fin.cases rfl (fun _ ↦ rfl) j
      · intro p _; rw [Fin.prod_univ_succ]; rfl
  rw [hpi]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin m → α ↦ Finset.univ.image f)
    (t := γ.powerset)]
  · apply Finset.sum_congr rfl; intro S hS
    unfold scalarWordSum
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, him⟩
      refine ⟨fun j ↦ him ▸ Finset.mem_image_of_mem f (Finset.mem_univ j), him⟩
    · rintro ⟨hfS, him⟩
      exact ⟨fun j ↦ (Finset.mem_powerset.mp hS) (hfS j), him⟩
  · intro f hf
    rw [Finset.mem_powerset]
    intro X hX
    rcases Finset.mem_image.mp hX with ⟨j, _, rfl⟩
    exact Fintype.mem_piFinset.mp hf j

lemma scalarWordSum_le_pow {α : Type*} [DecidableEq α]
    (a : α → ℝ) (ha : ∀ X, 0 ≤ a X) (γ : Finset α) (m : ℕ) :
    scalarWordSum a γ m ≤ (∑ X ∈ γ, a X) ^ m := by
  rw [← sum_scalarWordSum_powerset a γ m]
  exact Finset.single_le_sum (fun S _ ↦ scalarWordSum_nonneg a ha S m)
    (Finset.mem_powerset.mpr Finset.Subset.rfl)

lemma hasSum_scalarWordSum_exp {α : Type*} [DecidableEq α]
    (a : α → ℝ) (ha : ∀ X, 0 ≤ a X) (γ : Finset α) :
    HasSum (fun m : ℕ ↦ scalarWordSum a γ m / (m.factorial : ℝ))
      (∏ X ∈ γ, (Real.exp (a X) - 1)) := by
  have hsumm : ∀ S : Finset α, Summable (fun m : ℕ ↦ scalarWordSum a S m / (m.factorial : ℝ)) := by
    intro S
    refine Summable.of_nonneg_of_le
      (fun m ↦ div_nonneg (scalarWordSum_nonneg a ha S m) (Nat.cast_nonneg _))
      (fun m ↦ div_le_div_of_nonneg_right (scalarWordSum_le_pow a ha S m) (Nat.cast_nonneg _)) ?_
    simpa [div_eq_mul_inv] using (Real.summable_pow_div_factorial (∑ X ∈ S, a X))
  have hpow : ∀ S : Finset α,
      ∑ T ∈ S.powerset, (∑' m : ℕ, scalarWordSum a T m / (m.factorial : ℝ)) =
        Real.exp (∑ X ∈ S, a X) := by
    intro S
    rw [← Summable.tsum_finsetSum (fun T _ ↦ hsumm T)]
    have hterm : ∀ m : ℕ, (∑ T ∈ S.powerset, scalarWordSum a T m / (m.factorial : ℝ)) =
        (∑ X ∈ S, a X) ^ m / (m.factorial : ℝ) := by
      intro m; rw [← Finset.sum_div, sum_scalarWordSum_powerset]
    simp_rw [hterm]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have heq : ∑' m : ℕ, scalarWordSum a γ m / (m.factorial : ℝ) =
      ∏ X ∈ γ, (Real.exp (a X) - 1) := by
    induction γ using Finset.strongInduction with
    | H S ih =>
      have hprod : ∏ X ∈ S, Real.exp (a X) =
          ∑ T ∈ S.powerset, ∏ X ∈ T, (Real.exp (a X) - 1) := by
        have h1 : ∀ X ∈ S, Real.exp (a X) = 1 + (Real.exp (a X) - 1) := fun X _ ↦ by ring
        rw [Finset.prod_congr rfl h1, Finset.prod_one_add]
      have h1 : ∑ T ∈ S.powerset, (∑' m : ℕ, scalarWordSum a T m / (m.factorial : ℝ)) =
          ∑ T ∈ S.powerset, ∏ X ∈ T, (Real.exp (a X) - 1) := by
        rw [hpow S, Real.exp_sum, hprod]
      have hsplit : ∀ f : Finset α → ℝ,
          ∑ T ∈ S.powerset, f T = f S + ∑ T ∈ S.powerset.erase S, f T := fun f ↦
        (Finset.add_sum_erase _ f (Finset.mem_powerset_self S)).symm
      rw [hsplit, hsplit] at h1
      have hrest : ∑ T ∈ S.powerset.erase S, (∑' m : ℕ, scalarWordSum a T m / (m.factorial : ℝ)) =
          ∑ T ∈ S.powerset.erase S, ∏ X ∈ T, (Real.exp (a X) - 1) := by
        apply Finset.sum_congr rfl; intro T hT
        rcases Finset.mem_erase.mp hT with ⟨hne, hTsub⟩
        exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hTsub, hne⟩)
      linarith
  rw [← heq]
  exact (hsumm γ).hasSum

lemma opNorm_polyTermSum_le {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (γ : Polymer N) (m : ℕ) :
    opNorm (polyTermSum h γ m) ≤ scalarWordSum (fun X ↦ opNorm (h X)) γ m := by
  unfold polyTermSum scalarWordSum
  refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun f _ ↦ ?_)
  refine le_trans (opNorm_list_prod_le _) ?_
  rw [List.map_ofFn, List.prod_ofFn]; exact le_refl _

lemma opNorm_polyTermSum_scaled_le {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (β' : ℝ) (γ : Polymer N) (m : ℕ) :
    opNorm (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m) ≤
      scalarWordSum (fun X ↦ |β'| * opNorm (h X)) γ m / (m.factorial : ℝ) := by
  rw [opNorm_smul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast]
  have hmul : |β'| ^ m * scalarWordSum (fun X ↦ opNorm (h X)) γ m =
      scalarWordSum (fun X ↦ |β'| * opNorm (h X)) γ m := by
    unfold scalarWordSum
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro f _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc |β'| ^ m / (m.factorial : ℝ) * opNorm (polyTermSum h γ m)
      ≤ |β'| ^ m / (m.factorial : ℝ) * scalarWordSum (fun X ↦ opNorm (h X)) γ m :=
        mul_le_mul_of_nonneg_left (opNorm_polyTermSum_le h γ m)
          (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))
    _ = scalarWordSum (fun X ↦ |β'| * opNorm (h X)) γ m / (m.factorial : ℝ) := by
        rw [← hmul]; ring

lemma hasSum_polyOp {N : ℕ} (h : Finset (Fin N) → QubitOp N) (β' : ℝ) (γ : Polymer N) :
    HasSum (fun m : ℕ ↦ ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m)
      (polyOp h β' γ) := by
  unfold polyOp
  apply Summable.hasSum
  have hsumm_real : Summable (fun m : ℕ ↦
      scalarWordSum (fun X ↦ |β'| * opNorm (h X)) γ m / (m.factorial : ℝ)) :=
    (hasSum_scalarWordSum_exp (fun X ↦ |β'| * opNorm (h X))
      (fun X ↦ mul_nonneg (abs_nonneg _) (opNorm_nonneg _)) γ).summable
  exact Pi.summable.mpr fun i ↦ Pi.summable.mpr fun j ↦
    Summable.of_norm_bounded hsumm_real fun m ↦
      le_trans (norm_entry_le_opNorm _ i j) (opNorm_polyTermSum_scaled_le h β' γ m)

/-- **Concrete Polymer Operator-Norm Bound**:
`opNorm (polyOp h β' γ) ≤ ∏ X ∈ γ, (Real.exp (|β'| * opNorm (h X)) - 1)`. -/
theorem opNorm_polyOp_le {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (β' : ℝ) (γ : Polymer N) :
    opNorm (polyOp h β' γ) ≤ ∏ X ∈ γ, (Real.exp (|β'| * opNorm (h X)) - 1) := by
  let a : Finset (Fin N) → ℝ := fun X ↦ |β'| * opNorm (h X)
  have ha : ∀ X, 0 ≤ a X := fun X ↦ mul_nonneg (abs_nonneg _) (opNorm_nonneg _)
  have hhas_op := hasSum_polyOp h β' γ
  have hhas_real := hasSum_scalarWordSum_exp a ha γ
  have hhas_clm : HasSum (fun m : ℕ ↦ opToCLM (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m))
      (opToCLM (polyOp h β' γ)) := by
    let L : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
      LinearMap.toContinuousLinearMap
        { toFun := opToCLM, map_add' := opToCLM_add, map_smul' := fun c A ↦ by simp [opToCLM_smul] }
    exact hhas_op.map L L.continuous
  have hle_partial : ∀ F : Finset ℕ,
      ‖∑ m ∈ F, opToCLM (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m)‖ ≤
        ∏ X ∈ γ, (Real.exp (a X) - 1) := by
    intro F
    calc ‖∑ m ∈ F, opToCLM (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m)‖
        ≤ ∑ m ∈ F, ‖opToCLM (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ m ∈ F, scalarWordSum a γ m / (m.factorial : ℝ) :=
          Finset.sum_le_sum fun m _ ↦ opNorm_polyTermSum_scaled_le h β' γ m
      _ ≤ ∑' m : ℕ, scalarWordSum a γ m / (m.factorial : ℝ) :=
          hhas_real.summable.sum_le_tsum F fun m _ ↦
            div_nonneg (scalarWordSum_nonneg a ha γ m) (Nat.cast_nonneg _)
      _ = ∏ X ∈ γ, (Real.exp (a X) - 1) := hhas_real.tsum_eq
  exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hhas_clm)
    (Filter.Eventually.of_forall hle_partial)

lemma polyOp_mem_supportedOn {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (β' : ℝ) (γ : Polymer N) :
    polyOp h β' γ ∈ supportedOn (polySupp γ) := by
  have hclosed : IsClosed (supportedOn (polySupp γ) : Set (QubitOp N)) :=
    Submodule.closed_of_finiteDimensional _
  refine hclosed.mem_of_tendsto (hasSum_polyOp h β' γ) (Filter.Eventually.of_forall fun F ↦ ?_)
  exact Submodule.sum_mem _ fun m _ ↦ Submodule.smul_mem _ _ (polyTermSum_mem_supportedOn h hsupp γ m)

/-- **Concrete Depolarized Polymer Weight Bound**:
`‖polyWeight h s β' γ‖ ≤ ∏ X ∈ γ, 6 ^ X.card * (Real.exp (|β'| * opNorm (h X)) - 1)`. -/
theorem norm_polyWeight_le {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (s : Fin N → Fin 6) (β' : ℝ) (γ : Polymer N) :
    ‖polyWeight h s β' γ‖ ≤
      ∏ X ∈ γ, (6 : ℝ) ^ X.card * (Real.exp (|β'| * opNorm (h X)) - 1) := by
  unfold polyWeight
  have h1 := norm_depolDualWeight_le s (polyOp_mem_supportedOn h hsupp β' γ)
  have h2 := opNorm_polyOp_le h β' γ
  have hcard : (polySupp γ).card ≤ ∑ X ∈ γ, X.card := Finset.card_biUnion_le
  have hpow : (6 : ℝ) ^ (polySupp γ).card ≤ (6 : ℝ) ^ (∑ X ∈ γ, X.card) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) hcard
  calc ‖depolDualWeight s (polyOp h β' γ)‖
      ≤ (6 : ℝ) ^ (polySupp γ).card * opNorm (polyOp h β' γ) := h1
    _ ≤ (6 : ℝ) ^ (∑ X ∈ γ, X.card) * ∏ X ∈ γ, (Real.exp (|β'| * opNorm (h X)) - 1) :=
        mul_le_mul hpow h2 (opNorm_nonneg _) (pow_nonneg (by norm_num) _)
    _ = (∏ X ∈ γ, (6 : ℝ) ^ X.card) * ∏ X ∈ γ, (Real.exp (|β'| * opNorm (h X)) - 1) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ X ∈ γ, (6 : ℝ) ^ X.card * (Real.exp (|β'| * opNorm (h X)) - 1) := by
        rw [Finset.prod_mul_distrib]

/-- **Hermitian Matrix Exponential Power Series**:
`hermFunc hH (fun e ↦ Complex.exp (c * e)) = ∑' m, (c^m / m!) • H^m`. -/
lemma hasSum_hermFunc_exp {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (c : ℂ) :
    HasSum (fun m : ℕ ↦ (c ^ m / (m.factorial : ℂ)) • H ^ m)
      (hermFunc hH (fun e ↦ Complex.exp (c * (e : ℂ)))) := by
  have hpow : ∀ m : ℕ, H ^ m = hermFunc hH (fun e ↦ (e : ℂ) ^ m) := by
    intro m
    induction m with
    | zero => simpa [pow_zero] using (hermFunc_one hH).symm
    | succ m ih =>
      rw [pow_succ, ih]
      conv_lhs => arg 2; rw [← hermFunc_id hH]
      rw [hermFunc_mul]
      exact congrArg (hermFunc hH) (funext fun e ↦ (pow_succ (e : ℂ) m).symm)
  simp_rw [hpow]
  change HasSum (fun m : ℕ ↦ fun (i j : QubitIdx N) ↦
      ((c ^ m / (m.factorial : ℂ)) • hermFunc hH (fun e ↦ (e : ℂ) ^ m)) i j)
    (fun (i j : QubitIdx N) ↦ hermFunc hH (fun e ↦ Complex.exp (c * (e : ℂ))) i j)
  rw [Pi.hasSum]
  intro i
  rw [Pi.hasSum]
  intro j
  let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hentry : ∀ f : ℝ → ℂ, (hermFunc hH f) i j =
      ∑ k : QubitIdx N, U i k * f (hH.eigenvalues k) * Uᴴ k j := by
    intro f
    unfold hermFunc
    simp only [U, Matrix.mul_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx; simp [hyx]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [hentry]
  have hterm : ∀ m : ℕ, ((c ^ m / (m.factorial : ℂ)) • hermFunc hH (fun e ↦ (e : ℂ) ^ m)) i j =
      ∑ k : QubitIdx N, U i k * ((c * (hH.eigenvalues k : ℂ)) ^ m / (m.factorial : ℂ)) * Uᴴ k j := by
    intro m
    rw [Matrix.smul_apply, smul_eq_mul, hentry, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [mul_pow]; ring
  simp_rw [hterm]
  apply hasSum_sum
  intro k _
  have hexp : HasSum (fun m : ℕ ↦ (c * (hH.eigenvalues k : ℂ)) ^ m / (m.factorial : ℂ))
      (Complex.exp (c * (hH.eigenvalues k : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (c * (hH.eigenvalues k : ℂ))
  exact (hexp.mul_left (U i k)).mul_right (Uᴴ k j)

/-- Key algebraic identity: if `γ₁, γ₂` have disjoint supports and `h X ∈ supportedOn X`,
then `polyOp h β' (γ₁ ∪ γ₂) = polyOp h β' γ₁ * polyOp h β' γ₂`. -/
lemma real_prod_le_prod {α : Type*} (s : Finset α) (f g : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a t)
    have hft : 0 ≤ ∏ i ∈ t, f i :=
      Finset.prod_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hga : 0 ≤ g a := le_trans hfa (hfg a (Finset.mem_insert_self a t))
    exact mul_le_mul (hfg a (Finset.mem_insert_self a t))
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))) hft hga

lemma real_sum_biUnion_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ b ∈ s.biUnion t, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hsub : t a ∪ u.biUnion t = t a ∪ (u.biUnion t \ t a) := by
      ext x; by_cases hx : x ∈ t a <;> simp [hx]
    have hdisj : Disjoint (t a) (u.biUnion t \ t a) := Finset.disjoint_sdiff
    rw [hsub, Finset.sum_union hdisj]
    have h1 : ∑ b ∈ u.biUnion t \ t a, f b ≤ ∑ b ∈ u.biUnion t, f b :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun b hb _ ↦
        hf b (Finset.mem_biUnion.mpr (by
          rcases Finset.mem_biUnion.mp hb with ⟨x, hxu, hbx⟩
          exact ⟨x, Finset.mem_insert_of_mem hxu, hbx⟩))
    have h2 := ih fun b hb ↦ hf b (by
      rcases Finset.mem_biUnion.mp hb with ⟨x, hxu, hbx⟩
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_insert_of_mem hxu, hbx⟩)
    linarith

private lemma hasSum_cauchy_product_complex {a b : ℕ → ℂ} {A B : ℂ}
    (ha : HasSum a A) (hb : HasSum b B)
    (hsa : Summable (fun k ↦ ‖a k‖)) (hsb : Summable (fun k ↦ ‖b k‖)) :
    HasSum (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) (A * B) := by
  have hanti_norm : Summable (fun m : ℕ ↦ ‖∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2‖) := by
    have h1 : Summable (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, ‖a p.1‖ * ‖b p.2‖) := by
      have hfib : ∀ n : ℕ, ∑ m ∈ Finset.range n, ∑ p ∈ Finset.antidiagonal m, ‖a p.1‖ * ‖b p.2‖ ≤
          (∑' i : ℕ, ‖a i‖) * (∑' j : ℕ, ‖b j‖) := by
        intro n
        have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
          intro i _ j _ hij
          change Disjoint (Finset.antidiagonal i) (Finset.antidiagonal j)
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          exact hij ((Finset.mem_antidiagonal.mp hp1).symm.trans (Finset.mem_antidiagonal.mp hp2))
        rw [← Finset.sum_biUnion hdisj]
        have hsub : (Finset.range n).biUnion Finset.antidiagonal ⊆ Finset.range n ×ˢ Finset.range n := by
          intro p hp
          rcases Finset.mem_biUnion.mp hp with ⟨m, hm, hpm⟩
          rw [Finset.mem_range] at hm
          rw [Finset.mem_antidiagonal] at hpm
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; omega
        calc ∑ p ∈ (Finset.range n).biUnion Finset.antidiagonal, ‖a p.1‖ * ‖b p.2‖
            ≤ ∑ p ∈ Finset.range n ×ˢ Finset.range n, ‖a p.1‖ * ‖b p.2‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
          _ = (∑ i ∈ Finset.range n, ‖a i‖) * (∑ j ∈ Finset.range n, ‖b j‖) := by
              rw [Finset.sum_product, Finset.sum_mul_sum]
          _ ≤ (∑' i : ℕ, ‖a i‖) * (∑' j : ℕ, ‖b j‖) :=
              mul_le_mul (hsa.sum_le_tsum _ fun _ _ ↦ norm_nonneg _)
                (hsb.sum_le_tsum _ fun _ _ ↦ norm_nonneg _)
                (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
                (tsum_nonneg fun _ ↦ norm_nonneg _)
      exact summable_of_sum_range_le (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfib
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) h1
    exact le_trans (norm_sum_le _ _) (by simp only [norm_mul]; exact le_refl _)
  have hanti_summ : Summable (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) :=
    hanti_norm.of_norm
  suffices hlim : Filter.Tendsto
      (fun n : ℕ ↦ ∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)
      Filter.atTop (nhds (A * B)) by
    have hsubseq : Filter.Tendsto
        (fun n : ℕ ↦ ∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)
        Filter.atTop (nhds (∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)) :=
      hanti_summ.hasSum.tendsto_sum_nat.comp
        (Filter.tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 2 * n)) Filter.tendsto_id)
    have heq := tendsto_nhds_unique hsubseq hlim
    rw [← heq]
    exact hanti_summ.hasSum
  have hsq_lim : Filter.Tendsto
      (fun n : ℕ ↦ (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j))
      Filter.atTop (nhds (A * B)) :=
    ha.tendsto_sum_nat.mul hb.tendsto_sum_nat
  have hdiff_zero : Filter.Tendsto
      (fun n : ℕ ↦ (∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) -
        (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j))
      Filter.atTop (nhds 0) := by
    have hrem_bound : ∀ n : ℕ,
        ‖(∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) -
          (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j)‖ ≤
        ((∑ i ∈ Finset.range (2 * n), ‖a i‖) - ∑ i ∈ Finset.range n, ‖a i‖) * (∑' j : ℕ, ‖b j‖) +
        (∑' i : ℕ, ‖a i‖) * ((∑ j ∈ Finset.range (2 * n), ‖b j‖) - ∑ j ∈ Finset.range n, ‖b j‖) := by
      intro n
      let T := (Finset.range (2 * n)).biUnion Finset.antidiagonal
      have hdisj : (Finset.range (2 * n) : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
        intro i _ j _ hij
        change Disjoint (Finset.antidiagonal i) (Finset.antidiagonal j)
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hij ((Finset.mem_antidiagonal.mp hp1).symm.trans (Finset.mem_antidiagonal.mp hp2))
      have hsq_sub : Finset.range n ×ˢ Finset.range n ⊆ T := by
        intro p hp
        rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
        rw [Finset.mem_range] at h1 h2
        exact Finset.mem_biUnion.mpr ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
          Finset.mem_antidiagonal.mpr rfl⟩
      have hdiff_eq : (∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) -
            (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j) =
          ∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), a p.1 * b p.2 := by
        rw [← Finset.sum_biUnion hdisj, Finset.sum_mul_sum, ← Finset.sum_product']
        rw [← Finset.sum_sdiff hsq_sub]; ring
      rw [hdiff_eq]
      have hsub_u : T \ (Finset.range n ×ˢ Finset.range n) ⊆
          (Finset.Ico n (2 * n) ×ˢ Finset.range (2 * n)) ∪
          (Finset.range (2 * n) ×ˢ Finset.Ico n (2 * n)) := by
        intro p hp
        rcases Finset.mem_sdiff.mp hp with ⟨hpT, hpnot⟩
        rcases Finset.mem_biUnion.mp hpT with ⟨m, hm, hpm⟩
        rw [Finset.mem_range] at hm; rw [Finset.mem_antidiagonal] at hpm
        rw [Finset.mem_union, Finset.mem_product, Finset.mem_product,
          Finset.mem_Ico, Finset.mem_Ico, Finset.mem_range, Finset.mem_range]
        by_cases h1 : p.1 < n
        · right
          have h2 : ¬ p.2 < n := fun h2 ↦ hpnot (Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩)
          omega
        · left; omega
      have hIco_a : ∑ i ∈ Finset.Ico n (2 * n), ‖a i‖ =
          (∑ i ∈ Finset.range (2 * n), ‖a i‖) - ∑ i ∈ Finset.range n, ‖a i‖ := by
        have h := Finset.sum_range_add_sum_Ico (fun i ↦ ‖a i‖) ((by omega : n ≤ 2 * n))
        linarith
      have hIco_b : ∑ j ∈ Finset.Ico n (2 * n), ‖b j‖ =
          (∑ j ∈ Finset.range (2 * n), ‖b j‖) - ∑ j ∈ Finset.range n, ‖b j‖ := by
        have h := Finset.sum_range_add_sum_Ico (fun j ↦ ‖b j‖) ((by omega : n ≤ 2 * n))
        linarith
      calc ‖∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), a p.1 * b p.2‖
          ≤ ∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), ‖a p.1‖ * ‖b p.2‖ :=
            le_trans (norm_sum_le _ _) (by simp only [norm_mul]; exact le_refl _)
        _ ≤ ∑ p ∈ (Finset.Ico n (2 * n) ×ˢ Finset.range (2 * n)) ∪
              (Finset.range (2 * n) ×ˢ Finset.Ico n (2 * n)), ‖a p.1‖ * ‖b p.2‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_u fun _ _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
        _ ≤ (∑ p ∈ Finset.Ico n (2 * n) ×ˢ Finset.range (2 * n), ‖a p.1‖ * ‖b p.2‖) +
            (∑ p ∈ Finset.range (2 * n) ×ˢ Finset.Ico n (2 * n), ‖a p.1‖ * ‖b p.2‖) := by
            rw [← Finset.sum_union_inter]
            linarith [Finset.sum_nonneg
              (s := (Finset.Ico n (2 * n) ×ˢ Finset.range (2 * n)) ∩
                    (Finset.range (2 * n) ×ˢ Finset.Ico n (2 * n)))
              (fun p _ ↦ mul_nonneg (norm_nonneg (a p.1)) (norm_nonneg (b p.2)))]
        _ = (∑ i ∈ Finset.Ico n (2 * n), ‖a i‖) * (∑ j ∈ Finset.range (2 * n), ‖b j‖) +
            (∑ i ∈ Finset.range (2 * n), ‖a i‖) * (∑ j ∈ Finset.Ico n (2 * n), ‖b j‖) := by
            rw [Finset.sum_product, Finset.sum_product, Finset.sum_mul_sum, Finset.sum_mul_sum]
        _ ≤ (∑ i ∈ Finset.Ico n (2 * n), ‖a i‖) * (∑' j : ℕ, ‖b j‖) +
            (∑' i : ℕ, ‖a i‖) * (∑ j ∈ Finset.Ico n (2 * n), ‖b j‖) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hsb.sum_le_tsum _ fun _ _ ↦ norm_nonneg _)
                (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            · exact mul_le_mul_of_nonneg_right (hsa.sum_le_tsum _ fun _ _ ↦ norm_nonneg _)
                (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        _ = _ := by rw [hIco_a, hIco_b]
    have hzero_rhs : Filter.Tendsto (fun n : ℕ ↦
        ((∑ i ∈ Finset.range (2 * n), ‖a i‖) - ∑ i ∈ Finset.range n, ‖a i‖) * (∑' j : ℕ, ‖b j‖) +
        (∑' i : ℕ, ‖a i‖) * ((∑ j ∈ Finset.range (2 * n), ‖b j‖) - ∑ j ∈ Finset.range n, ‖b j‖))
        Filter.atTop (nhds 0) := by
      have ha1 := hsa.hasSum.tendsto_sum_nat
      have ha2 := ha1.comp (Filter.tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 2 * n)) Filter.tendsto_id)
      have hb1 := hsb.hasSum.tendsto_sum_nat
      have hb2 := hb1.comp (Filter.tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 2 * n)) Filter.tendsto_id)
      have h := ((ha2.sub ha1).mul tendsto_const_nhds).add (tendsto_const_nhds.mul (hb2.sub hb1))
      simpa using h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hrem_bound hzero_rhs
  have hadd := hsq_lim.add hdiff_zero
  simp only [add_zero] at hadd
  exact hadd.congr fun n ↦ by ring

private lemma hasSum_entry {N : ℕ} {f : ℕ → QubitOp N} {S : QubitOp N}
    (hf : HasSum f S) (i j : QubitIdx N) : HasSum (fun k ↦ f k i j) (S i j) := by
  have h' : HasSum (fun k (p q : QubitIdx N) ↦ f k p q) (fun p q ↦ S p q) := hf
  exact (Pi.hasSum.mp ((Pi.hasSum.mp h') i)) j

lemma polyTermSum_union_of_disjoint {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X)
    {γ₁ γ₂ : Polymer N} (hdisj_supp : Disjoint (polySupp γ₁) (polySupp γ₂))
    (hdisj : Disjoint γ₁ γ₂) (m : ℕ) :
    polyTermSum h (γ₁ ∪ γ₂) m =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℂ) •
        (polyTermSum h γ₁ k * polyTermSum h γ₂ (m - k)) := by
  have hlist_split : ∀ (l : List (Finset (Fin N))),
      (∀ X ∈ l, X ∈ γ₁ ∪ γ₂) →
      (l.map h).prod = ((l.filter (· ∈ γ₁)).map h).prod * ((l.filter (· ∈ γ₂)).map h).prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons X tl ih =>
      intro hl
      have htl := ih fun Y hY ↦ hl Y (List.mem_cons_of_mem X hY)
      rcases Finset.mem_union.mp (hl X List.mem_cons_self) with hX1 | hX2
      · have hXnot2 : X ∉ γ₂ := Finset.disjoint_left.mp hdisj hX1
        simp only [List.map_cons, List.prod_cons, List.filter_cons, decide_eq_true_eq, hX1,
          ↓reduceIte, hXnot2, htl, Matrix.mul_assoc]
      · have hXnot1 : X ∉ γ₁ := Finset.disjoint_right.mp hdisj hX2
        simp only [List.map_cons, List.prod_cons, List.filter_cons, decide_eq_true_eq, hXnot1,
          ↓reduceIte, hX2, htl]
        have hcomm_list : h X * ((tl.filter (· ∈ γ₁)).map h).prod =
            ((tl.filter (· ∈ γ₁)).map h).prod * h X := by
          have hmem : ((tl.filter (· ∈ γ₁)).map h).prod ∈ supportedOn (polySupp γ₁) := by
            apply supportedOn_list_prod_mem
            intro M hM
            rcases List.mem_map.mp hM with ⟨Y, hY, rfl⟩
            have hY1 : Y ∈ γ₁ := of_decide_eq_true (List.mem_filter.mp hY).2
            exact supportedOn_mono (Finset.subset_biUnion_of_mem id hY1) (hsupp Y)
          exact supportedOn_comm_of_disjoint
            (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem id hX2) hdisj_supp.symm)
            (hsupp X) hmem
        rw [← Matrix.mul_assoc, hcomm_list, Matrix.mul_assoc]
  have hconv :
      polyTermSum h (γ₁ ∪ γ₂) m =
        ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℂ) • (polyTermSum h γ₁ k * polyTermSum h γ₂ (m - k)) := by
    let S_all := (Fintype.piFinset fun _ : Fin m ↦ γ₁ ∪ γ₂).filter
      (fun f ↦ Finset.univ.image f = γ₁ ∪ γ₂)
    have hsplit_S : polyTermSum h (γ₁ ∪ γ₂) m =
        ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∑ f ∈ S_all.filter (fun f ↦ Finset.univ.filter (fun j ↦ f j ∈ γ₁) = T),
            (List.ofFn (fun j : Fin m ↦ h (f j))).prod := by
      unfold polyTermSum
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun f : Fin m → Finset (Fin N) ↦ Finset.univ.filter (fun j ↦ f j ∈ γ₁))
        (t := (Finset.univ : Finset (Fin m)).powerset)]
      · intro _ _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    rw [hsplit_S]
    have hT_eq : ∀ T : Finset (Fin m),
        ∑ f ∈ S_all.filter (fun f ↦ Finset.univ.filter (fun j ↦ f j ∈ γ₁) = T),
          (List.ofFn (fun j : Fin m ↦ h (f j))).prod =
        polyTermSum h γ₁ T.card * polyTermSum h γ₂ (m - T.card) := by
      intro T
      let e1 : Fin T.card ≃o {j : Fin m // j ∈ T} := T.orderIsoOfFin rfl
      let T2 : Finset (Fin m) := Finset.univ \ T
      have hT2card : T2.card = m - T.card := by
        simp [T2, Finset.card_sdiff, Finset.subset_univ]
      let e2 : Fin (m - T.card) ≃o {j : Fin m // j ∈ T2} := T2.orderIsoOfFin hT2card
      unfold polyTermSum
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_bij
        (fun f _ ↦
          (fun a : Fin T.card ↦ f (e1 a).1,
           fun b : Fin (m - T.card) ↦ f (e2 b).1)) ?_ ?_ ?_ ?_
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfS, hfT⟩
        rcases Finset.mem_filter.mp hfS with ⟨hfpi, hfim⟩
        rw [Finset.mem_product]
        have hf1 : ∀ a : Fin T.card, f (e1 a).1 ∈ γ₁ := fun a ↦ by
          have : (e1 a).1 ∈ Finset.univ.filter (fun j ↦ f j ∈ γ₁) := hfT.symm ▸ (e1 a).2
          exact (Finset.mem_filter.mp this).2
        have hf2 : ∀ b : Fin (m - T.card), f (e2 b).1 ∈ γ₂ := fun b ↦ by
          have hnotT : (e2 b).1 ∉ T := (Finset.mem_sdiff.mp (e2 b).2).2
          have hnot1 : f (e2 b).1 ∉ γ₁ := fun h1 ↦
            hnotT (hfT ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          exact (Finset.mem_union.mp (Fintype.mem_piFinset.mp hfpi (e2 b).1)).resolve_left hnot1
        constructor
        · refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hf1, ?_⟩
          apply Finset.Subset.antisymm
          · intro X hX; rcases Finset.mem_image.mp hX with ⟨a, _, rfl⟩; exact hf1 a
          · intro X hX
            have hXU : X ∈ Finset.univ.image f := hfim.symm ▸ Finset.mem_union_left γ₂ hX
            rcases Finset.mem_image.mp hXU with ⟨j, _, rfl⟩
            have hjT : j ∈ T := hfT ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
            refine Finset.mem_image.mpr ⟨e1.symm ⟨j, hjT⟩, Finset.mem_univ _, by simp⟩
        · refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hf2, ?_⟩
          apply Finset.Subset.antisymm
          · intro X hX; rcases Finset.mem_image.mp hX with ⟨b, _, rfl⟩; exact hf2 b
          · intro X hX
            have hXU : X ∈ Finset.univ.image f := hfim.symm ▸ Finset.mem_union_right γ₁ hX
            rcases Finset.mem_image.mp hXU with ⟨j, _, rfl⟩
            have hjnot1 : f j ∉ γ₁ := Finset.disjoint_right.mp hdisj hX
            have hjT2 : j ∈ T2 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hjT ↦
              hjnot1 (Finset.mem_filter.mp (show j ∈ Finset.univ.filter (fun j ↦ f j ∈ γ₁) from hfT.symm ▸ hjT)).2⟩
            refine Finset.mem_image.mpr ⟨e2.symm ⟨j, hjT2⟩, Finset.mem_univ _, by simp⟩
      · intro f₁ _ f₂ _ heq
        funext j
        by_cases hj : j ∈ T
        · have := congrFun (Prod.mk.inj heq).1 (e1.symm ⟨j, hj⟩); simpa using this
        · have hj2 : j ∈ T2 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
          have := congrFun (Prod.mk.inj heq).2 (e2.symm ⟨j, hj2⟩); simpa using this
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        rcases Finset.mem_filter.mp hp1 with ⟨hp1pi, hp1im⟩
        rcases Finset.mem_filter.mp hp2 with ⟨hp2pi, hp2im⟩
        let f : Fin m → Finset (Fin N) := fun j ↦
          if hj : j ∈ T then p.1 (e1.symm ⟨j, hj⟩)
          else p.2 (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩)
        refine ⟨f, ?_, ?_⟩
        · have hf1 : ∀ j, j ∈ T → f j ∈ γ₁ := fun j hj ↦ by
            simp only [f, hj, ↓reduceDIte]; exact Fintype.mem_piFinset.mp hp1pi _
          have hf2 : ∀ j, j ∉ T → f j ∈ γ₂ := fun j hj ↦ by
            simp only [f, hj, ↓reduceDIte]; exact Fintype.mem_piFinset.mp hp2pi _
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j ↦ ?_, ?_⟩, ?_⟩
          · by_cases hj : j ∈ T
            · exact Finset.mem_union_left _ (hf1 j hj)
            · exact Finset.mem_union_right _ (hf2 j hj)
          · apply Finset.Subset.antisymm
            · intro X hX; rcases Finset.mem_image.mp hX with ⟨j, _, rfl⟩
              by_cases hj : j ∈ T
              · exact Finset.mem_union_left _ (hf1 j hj)
              · exact Finset.mem_union_right _ (hf2 j hj)
            · intro X hX
              rcases Finset.mem_union.mp hX with hX1 | hX2
              · rcases Finset.mem_image.mp (hp1im.symm ▸ hX1) with ⟨a, _, rfl⟩
                exact Finset.mem_image.mpr ⟨(e1 a).1, Finset.mem_univ _, by simp [f, (e1 a).2]⟩
              · rcases Finset.mem_image.mp (hp2im.symm ▸ hX2) with ⟨b, _, rfl⟩
                have hnotT : (e2 b).1 ∉ T := (Finset.mem_sdiff.mp (e2 b).2).2
                exact Finset.mem_image.mpr ⟨(e2 b).1, Finset.mem_univ _, by simp [f, hnotT]⟩
          · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h1; by_contra hnotT
              exact Finset.disjoint_left.mp hdisj h1 (hf2 j hnotT)
            · exact hf1 j
        · ext a <;> simp [f, (e1 _).2, (Finset.mem_sdiff.mp (e2 _).2).2]
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfS, hfT⟩
        rcases Finset.mem_filter.mp hfS with ⟨hfpi, _⟩
        have hlist_eq : List.ofFn (fun j : Fin m ↦ h (f j)) = (List.ofFn f).map h := by
          rw [List.map_ofFn]; rfl
        rw [hlist_eq, hlist_split (List.ofFn f) (fun X hX ↦ by
          rcases List.mem_ofFn.mp hX with ⟨j, rfl⟩; exact Fintype.mem_piFinset.mp hfpi j)]
        have hfilt1 : (List.ofFn f).filter (· ∈ γ₁) = List.ofFn (fun a : Fin T.card ↦ f (e1 a).1) := by
          have hfin : (List.finRange m).filter (fun j ↦ f j ∈ γ₁) = List.ofFn (fun a : Fin T.card ↦ (e1 a).1) := by
            have hl1 : ((List.finRange m).filter (fun j ↦ f j ∈ γ₁)).Pairwise (· < ·) :=
              (List.pairwise_lt_finRange m).filter _
            have hl2 : (List.ofFn (fun a : Fin T.card ↦ (e1 a).1)).Pairwise (· < ·) :=
              List.pairwise_ofFn.mpr fun a b hab ↦ e1.strictMono hab
            have hperm : ((List.finRange m).filter (fun j ↦ f j ∈ γ₁)).Perm
                (List.ofFn (fun a : Fin T.card ↦ (e1 a).1)) := by
              rw [List.perm_ext_iff_of_nodup (hl1.imp ne_of_lt) (hl2.imp ne_of_lt)]
              intro j
              simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_ofFn]
              constructor
              · intro hj1
                have hjT : j ∈ T := by rw [← hfT]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj1⟩
                exact ⟨e1.symm ⟨j, hjT⟩, by simp⟩
              · rintro ⟨a, rfl⟩
                have haT : (e1 a).1 ∈ Finset.univ.filter (fun j : Fin m ↦ f j ∈ γ₁) := hfT.symm ▸ (e1 a).2
                exact (Finset.mem_filter.mp haT).2
            exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 ↦ le_antisymm h1 h2)
              (hl1.imp le_of_lt) (hl2.imp le_of_lt)
          have hmap : (List.ofFn f).filter (· ∈ γ₁) = ((List.finRange m).filter (fun j ↦ f j ∈ γ₁)).map f := by
            rw [List.ofFn_eq_map, List.filter_map]; rfl
          rw [hmap, hfin, List.map_ofFn]; rfl
        have hfilt2 : (List.ofFn f).filter (· ∈ γ₂) = List.ofFn (fun b : Fin (m - T.card) ↦ f (e2 b).1) := by
          have hfin : (List.finRange m).filter (fun j ↦ f j ∈ γ₂) = List.ofFn (fun b : Fin (m - T.card) ↦ (e2 b).1) := by
            have hl1 : ((List.finRange m).filter (fun j ↦ f j ∈ γ₂)).Pairwise (· < ·) :=
              (List.pairwise_lt_finRange m).filter _
            have hl2 : (List.ofFn (fun b : Fin (m - T.card) ↦ (e2 b).1)).Pairwise (· < ·) :=
              List.pairwise_ofFn.mpr fun a b hab ↦ e2.strictMono hab
            have hperm : ((List.finRange m).filter (fun j ↦ f j ∈ γ₂)).Perm
                (List.ofFn (fun b : Fin (m - T.card) ↦ (e2 b).1)) := by
              rw [List.perm_ext_iff_of_nodup (hl1.imp ne_of_lt) (hl2.imp ne_of_lt)]
              intro j
              simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_ofFn]
              constructor
              · intro hj2
                have hjnot1 : j ∉ T := by
                  rw [← hfT]; intro h1; exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp h1).2 hj2
                have hjT2 : j ∈ T2 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot1⟩
                exact ⟨e2.symm ⟨j, hjT2⟩, by simp⟩
              · rintro ⟨b, rfl⟩
                have hbT2 : (e2 b).1 ∈ T2 := (e2 b).2
                have hbnot1 : (e2 b).1 ∉ Finset.univ.filter (fun j : Fin m ↦ f j ∈ γ₁) :=
                  fun h1 ↦ (Finset.mem_sdiff.mp hbT2).2 (hfT ▸ h1)
                have hbnot : f (e2 b).1 ∉ γ₁ := fun h1 ↦ hbnot1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
                exact (Finset.mem_union.mp (Fintype.mem_piFinset.mp hfpi (e2 b).1)).resolve_left hbnot
            exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 ↦ le_antisymm h1 h2)
              (hl1.imp le_of_lt) (hl2.imp le_of_lt)
          have hmap : (List.ofFn f).filter (· ∈ γ₂) = ((List.finRange m).filter (fun j ↦ f j ∈ γ₂)).map f := by
            rw [List.ofFn_eq_map, List.filter_map]; rfl
          rw [hmap, hfin, List.map_ofFn]; rfl
        rw [hfilt1, hfilt2, List.map_ofFn, List.map_ofFn]; rfl
    simp_rw [hT_eq]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (m + 1))]
    · apply Finset.sum_congr rfl; intro k _
      have hcard_eq : ((Finset.univ : Finset (Fin m)).powerset.filter (fun T ↦ T.card = k)).card =
          Nat.choose m k := by
        rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      rw [Finset.sum_congr rfl (fun T hT ↦ by rw [(Finset.mem_filter.mp hT).2]),
        Finset.sum_const, hcard_eq, ← Nat.cast_smul_eq_nsmul ℂ]
    · intro T _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (by simpa using Finset.card_le_univ T)
  exact hconv

private lemma hasSum_matrix_cauchy_product {N : ℕ}
    {A B : ℕ → QubitOp N} {P1 P2 : QubitOp N} {r1 r2 : ℕ → ℝ}
    (hA : HasSum A P1) (hB : HasSum B P2)
    (hb1 : ∀ k, opNorm (A k) ≤ r1 k) (hs1 : Summable r1)
    (hb2 : ∀ k, opNorm (B k) ≤ r2 k) (hs2 : Summable r2)
    (i j : QubitIdx N) :
    HasSum (fun m : ℕ ↦ (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j) ((P1 * P2) i j) := by
  have hterm : ∀ m : ℕ, (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j =
      ∑ l : QubitIdx N, ∑ p ∈ Finset.antidiagonal m, A p.1 i l * B p.2 l j := by
    intro m; simp only [Matrix.sum_apply, Matrix.mul_apply]; rw [Finset.sum_comm]
  simp_rw [hterm]
  change HasSum (fun m : ℕ ↦ ∑ l : QubitIdx N, ∑ p ∈ Finset.antidiagonal m, A p.1 i l * B p.2 l j)
    (∑ l : QubitIdx N, P1 i l * P2 l j)
  apply hasSum_sum
  intro l _
  have h1l : HasSum (fun k ↦ A k i l) (P1 i l) := hasSum_entry hA i l
  have h2l : HasSum (fun k ↦ B k l j) (P2 l j) := hasSum_entry hB l j
  have hs1l : Summable (fun k ↦ ‖A k i l‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ le_trans (norm_entry_le_opNorm (A k) i l) (hb1 k)) hs1
  have hs2l : Summable (fun k ↦ ‖B k l j‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ le_trans (norm_entry_le_opNorm (B k) l j) (hb2 k)) hs2
  exact hasSum_cauchy_product_complex h1l h2l hs1l hs2l

lemma polyOp_union_of_disjoint {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (β' : ℝ)
    {γ₁ γ₂ : Polymer N} (hdisj_supp : Disjoint (polySupp γ₁) (polySupp γ₂))
    (hdisj : Disjoint γ₁ γ₂) :
    polyOp h β' (γ₁ ∪ γ₂) = polyOp h β' γ₁ * polyOp h β' γ₂ := by
  have hconv := fun m ↦ polyTermSum_union_of_disjoint h hsupp hdisj_supp hdisj m
  let A : ℕ → QubitOp N := fun k ↦ ((-(β' : ℂ)) ^ k / (k.factorial : ℂ)) • polyTermSum h γ₁ k
  let B : ℕ → QubitOp N := fun k ↦ ((-(β' : ℂ)) ^ k / (k.factorial : ℂ)) • polyTermSum h γ₂ k
  have hA_has : HasSum A (polyOp h β' γ₁) := hasSum_polyOp h β' γ₁
  have hB_has : HasSum B (polyOp h β' γ₂) := hasSum_polyOp h β' γ₂
  have hsr1 := (hasSum_scalarWordSum_exp (fun X ↦ |β'| * opNorm (h X))
    (fun X ↦ mul_nonneg (abs_nonneg _) (opNorm_nonneg _)) γ₁).summable
  have hsr2 := (hasSum_scalarWordSum_exp (fun X ↦ |β'| * opNorm (h X))
    (fun X ↦ mul_nonneg (abs_nonneg _) (opNorm_nonneg _)) γ₂).summable
  have hanti : ∀ m : ℕ,
      ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h (γ₁ ∪ γ₂) m =
        ∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2 := by
    intro m
    rw [hconv m, Finset.smul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦ A a * B b)]
    apply Finset.sum_congr rfl; intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [A, B]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    have hch : (Nat.choose m k : ℂ) * (k.factorial : ℂ) * ((m - k).factorial : ℂ) = (m.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
    have hm_ne : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hk_ne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hmk_ne : ((m - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - k))
    have hpow_eq : (-(β' : ℂ)) ^ m = (-(β' : ℂ)) ^ k * (-(β' : ℂ)) ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkm]
    rw [hpow_eq]
    field_simp [hm_ne, hk_ne, hmk_ne]
    linear_combination ((-(β' : ℂ)) ^ k * (-(β' : ℂ)) ^ (m - k)) * hch
  have hmul_has : ∀ (i j : QubitIdx N),
      HasSum (fun m : ℕ ↦ (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j)
        ((polyOp h β' γ₁ * polyOp h β' γ₂) i j) :=
    hasSum_matrix_cauchy_product hA_has hB_has
      (fun k ↦ opNorm_polyTermSum_scaled_le h β' γ₁ k) hsr1
      (fun k ↦ opNorm_polyTermSum_scaled_le h β' γ₂ k) hsr2
  ext i j
  have hhas_lhs : HasSum (fun m : ℕ ↦ (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j)
      (polyOp h β' (γ₁ ∪ γ₂) i j) :=
    (hasSum_entry (hasSum_polyOp h β' (γ₁ ∪ γ₂)) i j).congr_fun fun m ↦ by rw [hanti m]
  exact hhas_lhs.unique (hmul_has i j)

lemma depolDualWeight_polyOp_biUnion {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (s : Fin N → Fin 6) (β' : ℝ)
    (I : Finset (Polymer N)) (hcomp : isCompatPolymer polyIncompat I)
    (hne : ∀ γ ∈ I, ∀ X ∈ γ, X.Nonempty) :
    depolDualWeight s (polyOp h β' (I.biUnion id)) = ∏ γ ∈ I, polyWeight h s β' γ := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty]
    have hempty : polyOp h β' ∅ = 1 := by
      have h0 : polyTermSum h ∅ 0 = 1 := by
        unfold polyTermSum
        have hsing : (Fintype.piFinset fun _ : Fin 0 ↦ (∅ : Polymer N)).filter
            (fun f ↦ Finset.univ.image f = ∅) = {Fin.elim0} := by
          ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
          constructor
          · intro _; funext j; exact Fin.elim0 j
          · rintro rfl; refine ⟨fun j ↦ Fin.elim0 j, ?_⟩; simp
        rw [hsing, Finset.sum_singleton]; simp
      have hsucc : ∀ m : ℕ, polyTermSum h ∅ (m + 1) = 0 := by
        intro m; unfold polyTermSum
        apply Finset.sum_eq_zero; intro f hf
        exfalso
        have := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) (0 : Fin (m + 1))
        simp at this
      have hhas := hasSum_polyOp h β' ∅
      have hhas1 : HasSum (fun m : ℕ ↦ ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h ∅ m) 1 := by
        have hs0 : HasSum (fun m : ℕ ↦ ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h ∅ m)
            (((-(β' : ℂ)) ^ 0 / ((0 : ℕ).factorial : ℂ)) • polyTermSum h ∅ 0) :=
          hasSum_single 0 fun m hm ↦ by
            obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
            simp [hsucc k]
        simpa [h0] using hs0
      exact hhas.unique hhas1
    rw [hempty, depolDualWeight_one]
  | insert γ I' hγnot ih =>
    rw [Finset.biUnion_insert, id_eq, Finset.prod_insert hγnot]
    have hcomp' : isCompatPolymer polyIncompat I' := fun a ha b hb hab ↦
      hcomp a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdisj_supp : Disjoint (polySupp γ) (polySupp (I'.biUnion id)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_biUnion.mp hx2 with ⟨Y, hY, hxY⟩
      rcases Finset.mem_biUnion.mp hY with ⟨δ, hδI', hYδ⟩
      have hne_gd : γ ≠ δ := fun heq ↦ hγnot (heq ▸ hδI')
      have hc := hcomp γ (Finset.mem_insert_self _ _) δ (Finset.mem_insert_of_mem hδI') hne_gd
      unfold polyIncompat at hc; push Not at hc
      exact Finset.disjoint_left.mp hc hx1 (Finset.mem_biUnion.mpr ⟨Y, hYδ, hxY⟩)
    have hdisj_set : Disjoint γ (I'.biUnion id) := by
      rw [Finset.disjoint_left]
      intro X hXγ hXI'
      rcases hne γ (Finset.mem_insert_self _ _) X hXγ with ⟨x, hxX⟩
      exact Finset.disjoint_left.mp hdisj_supp
        (Finset.mem_biUnion.mpr ⟨X, hXγ, hxX⟩)
        (Finset.mem_biUnion.mpr ⟨X, hXI', hxX⟩)
    rw [polyOp_union_of_disjoint h hsupp β' hdisj_supp hdisj_set,
      depolDualWeight_mul_of_disjoint s hdisj_supp
        (polyOp_mem_supportedOn h hsupp β' γ) (polyOp_mem_supportedOn h hsupp β' (I'.biUnion id)),
      ih hcomp' (fun δ hδ ↦ hne δ (Finset.mem_insert_of_mem hδ))]
    rfl

/-- **Exact Non-Commutative Polymer Partition Function Identity**:
For `H = ∑ X ∈ E, h X` with `h X ∈ supportedOn X` and `∀ X ∈ E, X.Nonempty`,
`depolDualWeight s (exp(-β' H)) = polymerZ polyIncompat (polyWeight h s β') (connectedPolymers E)`. -/
theorem depolDualWeight_exp_eq_polymerZ {N : ℕ}
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian) (s : Fin N → Fin 6) (β' : ℝ) :
    depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β' : ℂ) * (e : ℂ)))) =
      polymerZ polyIncompat (polyWeight h s β') (connectedPolymers E) := by
  have hpow_expand : ∀ m : ℕ, (∑ X ∈ E, h X) ^ m = ∑ S ∈ E.powerset, polyTermSum h S m := by
    intro m
    have hpi : (∑ X ∈ E, h X) ^ m =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin m ↦ E), (List.ofFn (fun j : Fin m ↦ h (f j))).prod := by
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
      rw [Finset.mem_powerset]; intro X hX
      rcases Finset.mem_image.mp hX with ⟨j, _, rfl⟩
      exact Fintype.mem_piFinset.mp hf j
  have hhas_sum : HasSum (fun m : ℕ ↦ ((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • (∑ X ∈ E, h X) ^ m)
      (∑ S ∈ E.powerset, polyOp h β' S) := by
    have h1 := hasSum_sum fun S (_ : S ∈ E.powerset) ↦ hasSum_polyOp h β' S
    exact h1.congr_fun fun m ↦ by rw [hpow_expand m, Finset.smul_sum]
  have hexp_eq : hermFunc hH (fun e ↦ Complex.exp (-(β' : ℂ) * (e : ℂ))) =
      ∑ S ∈ E.powerset, polyOp h β' S :=
    (hasSum_hermFunc_exp hH (-(β' : ℂ))).unique hhas_sum
  rw [hexp_eq, depolDualWeight_sum]
  unfold polymerZ
  rcases compatible_connectedPolymers_bijection E hne with ⟨hinj, hsurj⟩
  have hfilt_eq : (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I) =
      (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I) := by
    ext I; simp only [Finset.mem_filter]
  symm
  refine Finset.sum_bij (fun I _ ↦ I.biUnion id) ?_ ?_ ?_ ?_
  · intro I hI
    have hI' : I ∈ (connectedPolymers E).powerset ∧ isCompatPolymer polyIncompat I := by
      simpa [Finset.mem_filter] using hI
    rw [Finset.mem_powerset]
    intro X hX
    rcases Finset.mem_biUnion.mp hX with ⟨γ, hγI, hXγ⟩
    exact (mem_connectedPolymers.mp (Finset.mem_powerset.mp hI'.1 hγI)).1 hXγ
  · intro I₁ hI₁ I₂ hI₂ heq
    exact hinj I₁ (by simpa [Finset.mem_filter] using hI₁)
      I₂ (by simpa [Finset.mem_filter] using hI₂) heq
  · intro S hS
    rcases hsurj S hS with ⟨I, hI, hIU⟩
    exact ⟨I, by simpa [Finset.mem_filter] using hI, hIU⟩
  · intro I hI
    have hI' : I ∈ (connectedPolymers E).powerset ∧ isCompatPolymer polyIncompat I := by
      simpa [Finset.mem_filter] using hI
    have hneI : ∀ γ ∈ I, ∀ X ∈ γ, X.Nonempty := fun γ hγ X hX ↦
      hne X ((mem_connectedPolymers.mp (Finset.mem_powerset.mp hI'.1 hγ)).1 hX)
    exact (depolDualWeight_polyOp_biUnion h hsupp s β' I hI'.2 hneI).symm

end PolymerExpansion

end KrylovChaos
