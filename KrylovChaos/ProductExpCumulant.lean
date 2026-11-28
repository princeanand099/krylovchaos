/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempPolymerZ
import KrylovChaos.HighTempCumulant
import Mathlib.Tactic

/-!
# Lemma 6.3 (Eq. 6.3): Product-Exponential Trace Cumulant Bound

Establishes the literal product-exponential form of Lemma 6.3 (Eq. 6.3) via the two-hypergraph
polymer expansion of `τ(e^{-β H} e^{ζ X})` on `E ∪ E_X`:
1. `prodPolyOp` and `prodPolyWeight`: two-hypergraph product-exponential polymer operator and
   normalized-trace weight `∑_{T₁ ∪ T₂ = S} polyOp A 1 T₁ * polyOp B 1 T₂`.
2. `norm_prodPolyWeight_le`: proves `‖prodPolyWeight A B γ‖ ≤ ∏ Z ∈ γ, (exp (‖A Z‖ + ‖B Z‖) - 1)`
   via the exact subset-cover identity `∑_{T₁ ∪ T₂ = γ} (∏_{T₁} u) (∏_{T₂} v) = ∏_{γ} (u + v + u v)`.
3. `normalizedTrace_exp_mul_exp_eq_polymerZ`: proves the exact identity
   `τ(e^{-β H} e^{ζ X}) = polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ)) (connectedPolymers (E ∪ E_X))`.
4. `lemma_6_3_product_exp_cumulant_bound`: proves the literal Eq. (6.3) product-exponential bound
   `Real.log ((gibbsRho hH β * hermFunc hXtilde (fun x ↦ Complex.exp ((lam : ℂ) * (x : ℂ)))).trace.re) ≤
     8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2` for all `|lam| ≤ Λ₀' / 2`.
-/

namespace KrylovChaos

open scoped BigOperators Matrix ComplexOrder
open Complex Matrix Filter Topology

noncomputable section ProductExpPolymer

/-- Two-hypergraph product-exponential polymer operator on `S ⊆ E ∪ E_X`:
`prodPolyOp A B S = ∑ T₁ ⊆ S, ∑ T₂ ⊆ S [T₁ ∪ T₂ = S], polyOp A 1 T₁ * polyOp B 1 T₂`. -/
def prodPolyOp {N : ℕ} (A B : Finset (Fin N) → QubitOp N)
    (S : Finset (Finset (Fin N))) : QubitOp N :=
  ∑ T₁ ∈ S.powerset, ∑ T₂ ∈ S.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = S),
    polyOp A 1 T₁ * polyOp B 1 T₂

/-- Normalized-trace polymer weight for the two-hypergraph product exponential. -/
def prodPolyWeight {N : ℕ} (A B : Finset (Fin N) → QubitOp N)
    (S : Finset (Finset (Fin N))) : ℂ :=
  normalizedTrace (prodPolyOp A B S)

/-- Subset-cover algebraic identity:
`∑ T₁ ⊆ S, ∑ T₂ ⊆ S [T₁ ∪ T₂ = S], (∏ Z ∈ T₁, u Z) * (∏ Z ∈ T₂, v Z) = ∏ Z ∈ S, (u Z + v Z + u Z * v Z)`. -/
private lemma sum_union_cover_prod {α : Type*} [DecidableEq α]
    (u v : α → ℝ) (S : Finset α) :
    ∑ T₁ ∈ S.powerset, ∑ T₂ ∈ S.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = S),
      (∏ Z ∈ T₁, u Z) * (∏ Z ∈ T₂, v Z) =
    ∏ Z ∈ S, (u Z + v Z + u Z * v Z) := by
  classical
  induction S using Finset.induction with
  | empty => simp [Finset.filter_eq']
  | @insert a S' ha ih =>
    rw [Finset.prod_insert ha]
    let P_full := ((insert a S').powerset ×ˢ (insert a S').powerset).filter
      (fun p ↦ p.1 ∪ p.2 = insert a S')
    let P_sub := (S'.powerset ×ˢ S'.powerset).filter (fun p ↦ p.1 ∪ p.2 = S')
    have hflat_full : ∑ T₁ ∈ (insert a S').powerset,
        ∑ T₂ ∈ (insert a S').powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = insert a S'),
          (∏ Z ∈ T₁, u Z) * (∏ Z ∈ T₂, v Z) =
        ∑ p ∈ P_full, (∏ Z ∈ p.1, u Z) * (∏ Z ∈ p.2, v Z) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl; intro T₁ _
      rw [Finset.sum_filter]
    have hflat_sub : ∑ T₁ ∈ S'.powerset,
        ∑ T₂ ∈ S'.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = S'),
          (∏ Z ∈ T₁, u Z) * (∏ Z ∈ T₂, v Z) =
        ∑ p ∈ P_sub, (∏ Z ∈ p.1, u Z) * (∏ Z ∈ p.2, v Z) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl; intro T₁ _
      rw [Finset.sum_filter]
    rw [hflat_full, ← ih, hflat_sub]
    let f1 : Finset α × Finset α → Finset α × Finset α := fun p ↦ (insert a p.1, p.2)
    let f2 : Finset α × Finset α → Finset α × Finset α := fun p ↦ (p.1, insert a p.2)
    let f3 : Finset α × Finset α → Finset α × Finset α := fun p ↦ (insert a p.1, insert a p.2)
    have hP_eq : P_full = (P_sub.image f1 ∪ P_sub.image f2) ∪ P_sub.image f3 := by
      ext ⟨T₁, T₂⟩
      simp only [P_full, P_sub, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_union, Finset.mem_image, f1, f2, f3, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, hun⟩
        have ha_mem : a ∈ T₁ ∪ T₂ := by rw [hun]; exact Finset.mem_insert_self a S'
        rcases Finset.mem_union.mp ha_mem with ha1 | ha2
        · by_cases ha2' : a ∈ T₂
          · right
            refine ⟨(T₁.erase a, T₂.erase a), ⟨⟨?_, ?_⟩, ?_⟩, Finset.insert_erase ha1, Finset.insert_erase ha2'⟩
            · intro x hx; have := h1 (Finset.mem_of_mem_erase hx)
              rcases Finset.mem_insert.mp this with rfl | h'
              · exact absurd hx (Finset.notMem_erase _ _)
              · exact h'
            · intro x hx; have := h2 (Finset.mem_of_mem_erase hx)
              rcases Finset.mem_insert.mp this with rfl | h'
              · exact absurd hx (Finset.notMem_erase _ _)
              · exact h'
            · ext x; simp only [Finset.mem_union, Finset.mem_erase]
              constructor
              · rintro (⟨hxa, hx1⟩ | ⟨hxa, hx2⟩)
                · have : x ∈ insert a S' := by rw [← hun]; exact Finset.mem_union_left _ hx1
                  exact (Finset.mem_insert.mp this).resolve_left hxa
                · have : x ∈ insert a S' := by rw [← hun]; exact Finset.mem_union_right _ hx2
                  exact (Finset.mem_insert.mp this).resolve_left hxa
              · intro hxS
                have hxa : x ≠ a := fun h ↦ ha (h ▸ hxS)
                have : x ∈ T₁ ∪ T₂ := by rw [hun]; exact Finset.mem_insert_of_mem hxS
                rcases Finset.mem_union.mp this with h' | h'
                · left; exact ⟨hxa, h'⟩
                · right; exact ⟨hxa, h'⟩
          · left; left
            refine ⟨(T₁.erase a, T₂), ⟨⟨?_, ?_⟩, ?_⟩, Finset.insert_erase ha1, rfl⟩
            · intro x hx; have := h1 (Finset.mem_of_mem_erase hx)
              rcases Finset.mem_insert.mp this with rfl | h'
              · exact absurd hx (Finset.notMem_erase _ _)
              · exact h'
            · intro x hx; exact (Finset.mem_insert.mp (h2 hx)).resolve_left (fun h ↦ ha2' (h ▸ hx))
            · ext x; simp only [Finset.mem_union, Finset.mem_erase]
              constructor
              · rintro (⟨hxa, hx1⟩ | hx2)
                · have : x ∈ insert a S' := by rw [← hun]; exact Finset.mem_union_left _ hx1
                  exact (Finset.mem_insert.mp this).resolve_left hxa
                · exact (Finset.mem_insert.mp (h2 hx2)).resolve_left (fun h ↦ ha2' (h ▸ hx2))
              · intro hxS
                have hxa : x ≠ a := fun h ↦ ha (h ▸ hxS)
                have : x ∈ T₁ ∪ T₂ := by rw [hun]; exact Finset.mem_insert_of_mem hxS
                rcases Finset.mem_union.mp this with h' | h'
                · left; exact ⟨hxa, h'⟩
                · right; exact h'
        · by_cases ha1' : a ∈ T₁
          · right
            refine ⟨(T₁.erase a, T₂.erase a), ⟨⟨?_, ?_⟩, ?_⟩, Finset.insert_erase ha1', Finset.insert_erase ha2⟩
            · intro x hx; exact (Finset.mem_insert.mp (h1 (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
            · intro x hx; exact (Finset.mem_insert.mp (h2 (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
            · ext x; simp only [Finset.mem_union, Finset.mem_erase]
              constructor
              · rintro (⟨hxa, hx1⟩ | ⟨hxa, hx2⟩)
                · exact (Finset.mem_insert.mp (h1 hx1)).resolve_left hxa
                · exact (Finset.mem_insert.mp (h2 hx2)).resolve_left hxa
              · intro hxS
                have hxa : x ≠ a := fun h ↦ ha (h ▸ hxS)
                have : x ∈ T₁ ∪ T₂ := by rw [hun]; exact Finset.mem_insert_of_mem hxS
                rcases Finset.mem_union.mp this with h' | h'
                · left; exact ⟨hxa, h'⟩
                · right; exact ⟨hxa, h'⟩
          · left; right
            refine ⟨(T₁, T₂.erase a), ⟨⟨?_, ?_⟩, ?_⟩, rfl, Finset.insert_erase ha2⟩
            · intro x hx; exact (Finset.mem_insert.mp (h1 hx)).resolve_left (fun h ↦ ha1' (h ▸ hx))
            · intro x hx; exact (Finset.mem_insert.mp (h2 (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
            · ext x; simp only [Finset.mem_union, Finset.mem_erase]
              constructor
              · rintro (hx1 | ⟨hxa, hx2⟩)
                · exact (Finset.mem_insert.mp (h1 hx1)).resolve_left (fun h ↦ ha1' (h ▸ hx1))
                · exact (Finset.mem_insert.mp (h2 hx2)).resolve_left hxa
              · intro hxS
                have hxa : x ≠ a := fun h ↦ ha (h ▸ hxS)
                have : x ∈ T₁ ∪ T₂ := by rw [hun]; exact Finset.mem_insert_of_mem hxS
                rcases Finset.mem_union.mp this with h' | h'
                · left; exact h'
                · right; exact ⟨hxa, h'⟩
      · rintro ((⟨⟨A, B⟩, ⟨⟨hA, hB⟩, hAB⟩, rfl, rfl⟩ | ⟨⟨A, B⟩, ⟨⟨hA, hB⟩, hAB⟩, rfl, rfl⟩) |
          ⟨⟨A, B⟩, ⟨⟨hA, hB⟩, hAB⟩, rfl, rfl⟩)
        · exact ⟨⟨Finset.insert_subset_insert a hA, Finset.Subset.trans hB (Finset.subset_insert a S')⟩,
            by rw [Finset.insert_union, hAB]⟩
        · exact ⟨⟨Finset.Subset.trans hA (Finset.subset_insert a S'), Finset.insert_subset_insert a hB⟩,
            by rw [Finset.union_insert, hAB]⟩
        · exact ⟨⟨Finset.insert_subset_insert a hA, Finset.insert_subset_insert a hB⟩,
            by rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hAB]⟩
    have hdisj12 : Disjoint (P_sub.image f1) (P_sub.image f2) := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨⟨A, B⟩, hAB, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨⟨C, D⟩, hCD, heq⟩
      have hB : B ⊆ S' := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hAB).1).2
      have hB_eq : insert a D = B := congrArg Prod.snd heq
      exact ha (hB (hB_eq ▸ Finset.mem_insert_self a D))
    have hdisj123 : Disjoint (P_sub.image f1 ∪ P_sub.image f2) (P_sub.image f3) := by
      rw [Finset.disjoint_left]; intro p hp12 hp3
      rcases Finset.mem_image.mp hp3 with ⟨⟨E, F⟩, _, rfl⟩
      rcases Finset.mem_union.mp hp12 with hp1 | hp2
      · rcases Finset.mem_image.mp hp1 with ⟨⟨A, B⟩, hAB, heq⟩
        have hB : B ⊆ S' := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hAB).1).2
        have hB_eq : B = insert a F := congrArg Prod.snd heq
        exact ha (hB (hB_eq ▸ Finset.mem_insert_self a F))
      · rcases Finset.mem_image.mp hp2 with ⟨⟨C, D⟩, hCD, heq⟩
        have hC : C ⊆ S' := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hCD).1).1
        have hC_eq : C = insert a E := congrArg Prod.fst heq
        exact ha (hC (hC_eq ▸ Finset.mem_insert_self a E))
    have hinj1 : Set.InjOn f1 (P_sub : Set _) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only [f1] at heq
      have ha1 : a ∉ p₁.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).1 h)
      have ha2 : a ∉ p₂.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).1 h)
      exact Prod.ext (by have := congrArg (fun s ↦ s.erase a) (congrArg Prod.fst heq); simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this)
        (congrArg Prod.snd heq)
    have hinj2 : Set.InjOn f2 (P_sub : Set _) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only [f2] at heq
      have ha1 : a ∉ p₁.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).2 h)
      have ha2 : a ∉ p₂.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).2 h)
      exact Prod.ext (congrArg Prod.fst heq)
        (by have := congrArg (fun s ↦ s.erase a) (congrArg Prod.snd heq); simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this)
    have hinj3 : Set.InjOn f3 (P_sub : Set _) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only [f3] at heq
      have ha1 : a ∉ p₁.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).1 h)
      have ha2 : a ∉ p₂.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).1 h)
      have hb1 : a ∉ p₁.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).2 h)
      have hb2 : a ∉ p₂.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).2 h)
      exact Prod.ext
        (by have := congrArg (fun s ↦ s.erase a) (congrArg Prod.fst heq); simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this)
        (by have := congrArg (fun s ↦ s.erase a) (congrArg Prod.snd heq); simpa [Finset.erase_insert hb1, Finset.erase_insert hb2] using this)
    rw [hP_eq, Finset.sum_union hdisj123, Finset.sum_union hdisj12,
      Finset.sum_image hinj1, Finset.sum_image hinj2, Finset.sum_image hinj3]
    have hsum1 : ∑ p ∈ P_sub, (∏ Z ∈ (f1 p).1, u Z) * (∏ Z ∈ (f1 p).2, v Z) =
        u a * ∑ p ∈ P_sub, (∏ Z ∈ p.1, u Z) * (∏ Z ∈ p.2, v Z) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp
      have ha1 : a ∉ p.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1 h)
      simp only [f1, Finset.prod_insert ha1]; ring
    have hsum2 : ∑ p ∈ P_sub, (∏ Z ∈ (f2 p).1, u Z) * (∏ Z ∈ (f2 p).2, v Z) =
        v a * ∑ p ∈ P_sub, (∏ Z ∈ p.1, u Z) * (∏ Z ∈ p.2, v Z) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp
      have ha2 : a ∉ p.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2 h)
      simp only [f2, Finset.prod_insert ha2]; ring
    have hsum3 : ∑ p ∈ P_sub, (∏ Z ∈ (f3 p).1, u Z) * (∏ Z ∈ (f3 p).2, v Z) =
        u a * v a * ∑ p ∈ P_sub, (∏ Z ∈ p.1, u Z) * (∏ Z ∈ p.2, v Z) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp
      have ha1 : a ∉ p.1 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1 h)
      have ha2 : a ∉ p.2 := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2 h)
      simp only [f3, Finset.prod_insert ha1, Finset.prod_insert ha2]; ring
    rw [hsum1, hsum2, hsum3]; ring

/-- Norm bound on the two-hypergraph product-exponential polymer weight:
`‖prodPolyWeight A B γ‖ ≤ ∏ Z ∈ γ, (Real.exp (opNorm (A Z) + opNorm (B Z)) - 1)`. -/
lemma norm_prodPolyWeight_le {N : ℕ} (A B : Finset (Fin N) → QubitOp N)
    (γ : Finset (Finset (Fin N))) :
    ‖prodPolyWeight A B γ‖ ≤ ∏ Z ∈ γ, (Real.exp (opNorm (A Z) + opNorm (B Z)) - 1) := by
  unfold prodPolyWeight prodPolyOp
  refine le_trans (norm_normalizedTrace_le _) ?_
  calc opNorm (∑ T₁ ∈ γ.powerset, ∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
          polyOp A 1 T₁ * polyOp B 1 T₂)
      ≤ ∑ T₁ ∈ γ.powerset, opNorm (∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
          polyOp A 1 T₁ * polyOp B 1 T₂) := opNorm_sum_le _ _
    _ ≤ ∑ T₁ ∈ γ.powerset, ∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
          opNorm (polyOp A 1 T₁ * polyOp B 1 T₂) :=
        Finset.sum_le_sum fun _ _ ↦ opNorm_sum_le _ _
    _ ≤ ∑ T₁ ∈ γ.powerset, ∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
          (∏ Z ∈ T₁, (Real.exp (opNorm (A Z)) - 1)) *
          (∏ Z ∈ T₂, (Real.exp (opNorm (B Z)) - 1)) := by
        apply Finset.sum_le_sum; intro T₁ _
        apply Finset.sum_le_sum; intro T₂ _
        refine le_trans (opNorm_mul_le _ _) ?_
        have h1 : opNorm (polyOp A 1 T₁) ≤ ∏ Z ∈ T₁, (Real.exp (opNorm (A Z)) - 1) := by
          simpa using opNorm_polyOp_le A 1 T₁
        have h2 : opNorm (polyOp B 1 T₂) ≤ ∏ Z ∈ T₂, (Real.exp (opNorm (B Z)) - 1) := by
          simpa using opNorm_polyOp_le B 1 T₂
        exact mul_le_mul h1 h2 (opNorm_nonneg _)
          (Finset.prod_nonneg fun Z _ ↦ by linarith [Real.one_le_exp (opNorm_nonneg (A Z))])
    _ = ∏ Z ∈ γ, ((Real.exp (opNorm (A Z)) - 1) + (Real.exp (opNorm (B Z)) - 1) +
          (Real.exp (opNorm (A Z)) - 1) * (Real.exp (opNorm (B Z)) - 1)) :=
        sum_union_cover_prod _ _ γ
    _ = ∏ Z ∈ γ, (Real.exp (opNorm (A Z) + opNorm (B Z)) - 1) := by
        apply Finset.prod_congr rfl; intro Z _
        rw [Real.exp_add]; ring

/-- Support containment of `prodPolyOp A B S`. -/
lemma prodPolyOp_mem_supportedOn {N : ℕ} (A B : Finset (Fin N) → QubitOp N)
    (hA : ∀ X, A X ∈ supportedOn X) (hB : ∀ X, B X ∈ supportedOn X)
    (S : Finset (Finset (Fin N))) :
    prodPolyOp A B S ∈ supportedOn (polySupp S) := by
  unfold prodPolyOp
  refine Submodule.sum_mem _ fun T₁ hT₁ ↦ Submodule.sum_mem _ fun T₂ hT₂ ↦ ?_
  have h1 : polySupp T₁ ⊆ polySupp S := Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.mem_powerset.mp hT₁)
  have h2 : polySupp T₂ ⊆ polySupp S :=
    Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.mem_powerset.mp (Finset.mem_filter.mp hT₂).1)
  exact supportedOn_mul_mem
    (supportedOn_mono h1 (polyOp_mem_supportedOn A hA 1 T₁))
    (supportedOn_mono h2 (polyOp_mem_supportedOn B hB 1 T₂))

/-- Disjoint-support multiplicative factorization of `prodPolyOp A B (S₁ ∪ S₂)`. -/
lemma prodPolyOp_union_of_disjoint {N : ℕ} (A B : Finset (Fin N) → QubitOp N)
    (hA : ∀ X, A X ∈ supportedOn X) (hB : ∀ X, B X ∈ supportedOn X)
    {S₁ S₂ : Finset (Finset (Fin N))}
    (hdisj_supp : Disjoint (polySupp S₁) (polySupp S₂))
    (hdisj : Disjoint S₁ S₂) :
    prodPolyOp A B (S₁ ∪ S₂) = prodPolyOp A B S₁ * prodPolyOp A B S₂ := by
  classical
  have hflat : ∀ S : Finset (Finset (Fin N)),
      prodPolyOp A B S =
      ∑ p ∈ (S.powerset ×ˢ S.powerset).filter (fun p ↦ p.1 ∪ p.2 = S),
        polyOp A 1 p.1 * polyOp B 1 p.2 := by
    intro S; unfold prodPolyOp
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro T₁ _
    rw [Finset.sum_filter]
  rw [hflat (S₁ ∪ S₂), hflat S₁, hflat S₂, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun q _ ↦ (q.1.1 ∪ q.2.1, q.1.2 ∪ q.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨⟨A₁, B₁⟩, ⟨A₂, B₂⟩⟩ hq
    rcases Finset.mem_product.mp hq with ⟨h1, h2⟩
    rcases Finset.mem_filter.mp h1 with ⟨h1p, h1u⟩
    rcases Finset.mem_filter.mp h2 with ⟨h2p, h2u⟩
    rcases Finset.mem_product.mp h1p with ⟨hA1, hB1⟩
    rcases Finset.mem_product.mp h2p with ⟨hA2, hB2⟩
    rw [Finset.mem_powerset] at hA1 hB1 hA2 hB2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset_union hA1 hA2),
      Finset.mem_powerset.mpr (Finset.union_subset_union hB1 hB2)⟩, ?_⟩
    rw [← h1u, ← h2u]
    ext X; simp only [Finset.mem_union]; tauto
  · rintro ⟨⟨A₁, B₁⟩, ⟨A₂, B₂⟩⟩ hq₁ ⟨⟨C₁, D₁⟩, ⟨C₂, D₂⟩⟩ hq₂ heq
    have hA1 : A₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₁).1).1).1
    have hB1 : B₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₁).1).1).2
    have hA2 : A₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₁).2).1).1
    have hB2 : B₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₁).2).1).2
    have hC1 : C₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₂).1).1).1
    have hD1 : D₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₂).1).1).2
    have hC2 : C₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₂).2).1).1
    have hD2 : D₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq₂).2).1).2
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have hinter : ∀ {U₁ U₂ V₁ V₂ : Finset (Finset (Fin N))}, U₁ ⊆ S₁ → U₂ ⊆ S₂ → V₁ ⊆ S₁ → V₂ ⊆ S₂ →
        U₁ ∪ U₂ = V₁ ∪ V₂ → U₁ = V₁ ∧ U₂ = V₂ := by
      intro U₁ U₂ V₁ V₂ hU1 hU2 hV1 hV2 hU
      constructor
      · ext X; have hX := Finset.ext_iff.mp hU X; simp only [Finset.mem_union] at hX
        constructor
        · intro hx; exact (hX.mp (Or.inl hx)).resolve_right fun h ↦ Finset.disjoint_left.mp hdisj (hU1 hx) (hV2 h)
        · intro hx; exact (hX.mpr (Or.inl hx)).resolve_right fun h ↦ Finset.disjoint_left.mp hdisj (hV1 hx) (hU2 h)
      · ext X; have hX := Finset.ext_iff.mp hU X; simp only [Finset.mem_union] at hX
        constructor
        · intro hx; exact (hX.mp (Or.inr hx)).resolve_left fun h ↦ Finset.disjoint_left.mp hdisj (hV1 h) (hU2 hx)
        · intro hx; exact (hX.mpr (Or.inr hx)).resolve_left fun h ↦ Finset.disjoint_left.mp hdisj (hU1 h) (hV2 hx)
    rcases hinter hA1 hA2 hC1 hC2 h1 with ⟨rfl, rfl⟩
    rcases hinter hB1 hB2 hD1 hD2 h2 with ⟨rfl, rfl⟩
    rfl
  · rintro ⟨T₁, T₂⟩ hT
    rcases Finset.mem_filter.mp hT with ⟨hTp, hTu⟩
    rcases Finset.mem_product.mp hTp with ⟨hT1, hT2⟩
    rw [Finset.mem_powerset] at hT1 hT2
    refine ⟨((T₁ ∩ S₁, T₂ ∩ S₁), (T₁ ∩ S₂, T₂ ∩ S₂)), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩, ?_⟩
      rw [← Finset.union_inter_distrib_right, hTu, Finset.inter_eq_right.mpr Finset.subset_union_left]
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩, ?_⟩
      rw [← Finset.union_inter_distrib_right, hTu, Finset.inter_eq_right.mpr Finset.subset_union_right]
    · apply Prod.ext
      · dsimp only; rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hT1]
      · dsimp only; rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hT2]
  · rintro ⟨⟨A₁, B₁⟩, ⟨A₂, B₂⟩⟩ hq
    have hA1 : A₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).1).1
    have hB1 : B₁ ⊆ S₁ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).1).2
    have hA2 : A₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).1).1
    have hB2 : B₂ ⊆ S₂ := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).1).2
    have hdA_supp : Disjoint (polySupp A₁) (polySupp A₂) :=
      hdisj_supp.mono (Finset.biUnion_subset_biUnion_of_subset_left _ hA1)
        (Finset.biUnion_subset_biUnion_of_subset_left _ hA2)
    have hdB_supp : Disjoint (polySupp B₁) (polySupp B₂) :=
      hdisj_supp.mono (Finset.biUnion_subset_biUnion_of_subset_left _ hB1)
        (Finset.biUnion_subset_biUnion_of_subset_left _ hB2)
    have hdA2B1_supp : Disjoint (polySupp A₂) (polySupp B₁) :=
      (hdisj_supp.mono (Finset.biUnion_subset_biUnion_of_subset_left _ hB1)
        (Finset.biUnion_subset_biUnion_of_subset_left _ hA2)).symm
    have hdA : Disjoint A₁ A₂ := hdisj.mono hA1 hA2
    have hdB : Disjoint B₁ B₂ := hdisj.mono hB1 hB2
    rw [polyOp_union_of_disjoint A hA 1 hdA_supp hdA, polyOp_union_of_disjoint B hB 1 hdB_supp hdB]
    have hcomm := supportedOn_comm_of_disjoint hdA2B1_supp
      (polyOp_mem_supportedOn A hA 1 A₂) (polyOp_mem_supportedOn B hB 1 B₁)
    calc polyOp A 1 A₁ * polyOp B 1 B₁ * (polyOp A 1 A₂ * polyOp B 1 B₂)
        = polyOp A 1 A₁ * (polyOp B 1 B₁ * polyOp A 1 A₂) * polyOp B 1 B₂ := by simp only [Matrix.mul_assoc]
      _ = polyOp A 1 A₁ * (polyOp A 1 A₂ * polyOp B 1 B₁) * polyOp B 1 B₂ := by rw [← hcomm]
      _ = polyOp A 1 A₁ * polyOp A 1 A₂ * (polyOp B 1 B₁ * polyOp B 1 B₂) := by simp only [Matrix.mul_assoc]

/-- Disjoint-support multiplicative factorization of `normalizedTrace (prodPolyOp A B (I.biUnion id))`. -/
lemma normalizedTrace_prodPolyOp_biUnion {N : ℕ}
    (A B : Finset (Fin N) → QubitOp N)
    (hA : ∀ X, A X ∈ supportedOn X) (hB : ∀ X, B X ∈ supportedOn X)
    (I : Finset (Polymer N))
    (hcomp : ∀ γ₁ ∈ I, ∀ γ₂ ∈ I, γ₁ ≠ γ₂ → ¬polyIncompat γ₁ γ₂)
    (hne : ∀ γ ∈ I, ∀ X ∈ γ, X.Nonempty) :
    normalizedTrace (prodPolyOp A B (I.biUnion id)) = ∏ γ ∈ I, prodPolyWeight A B γ := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty]
    have h1 : prodPolyOp A B ∅ = 1 := by
      unfold prodPolyOp
      simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.empty_union,
        Finset.sum_filter, if_pos rfl]
      have hpoly0 : ∀ g : Finset (Fin N) → QubitOp N, polyOp g 1 ∅ = 1 := by
        intro g; unfold polyOp
        have hterm : ∀ n : ℕ, ((-(1 : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) • polyTermSum g ∅ n =
            if n = 0 then (1 : QubitOp N) else 0 := by
          intro n; cases n with
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
        simp_rw [hterm]; rw [tsum_ite_eq]
      rw [hpoly0 A, hpoly0 B, Matrix.mul_one]
    rw [h1, normalizedTrace_one]
  | @insert γ I' hγ ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hγ]
    have hcomp' : ∀ γ₁ ∈ I', ∀ γ₂ ∈ I', γ₁ ≠ γ₂ → ¬polyIncompat γ₁ γ₂ :=
      fun γ₁ h₁ γ₂ h₂ hne' ↦ hcomp γ₁ (Finset.mem_insert_of_mem h₁) γ₂ (Finset.mem_insert_of_mem h₂) hne'
    have hdisj_supp : Disjoint (polySupp γ) (polySupp (I'.biUnion id)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
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
        (Finset.mem_biUnion.mpr ⟨X, hXγ, hxX⟩) (Finset.mem_biUnion.mpr ⟨X, hXI', hxX⟩)
    dsimp only [id]
    rw [prodPolyOp_union_of_disjoint A B hA hB hdisj_supp hdisj_set,
      normalizedTrace_mul_of_disjoint hdisj_supp
        (prodPolyOp_mem_supportedOn A B hA hB γ) (prodPolyOp_mem_supportedOn A B hA hB (I'.biUnion id)),
      ih hcomp' (fun δ hδ ↦ hne δ (Finset.mem_insert_of_mem hδ))]
    rfl

/-- Exact operator-level polymer sum: `hermFunc hM (exp (c * ·)) = ∑ S ∈ E.powerset, polyOp ((-c) • m) 1 S`. -/
private lemma hermFunc_exp_eq_sum_polyOp {N : ℕ}
    (E : Finset (Finset (Fin N))) (m : Finset (Fin N) → QubitOp N)
    (hM : (∑ Z ∈ E, m Z).IsHermitian) (c : ℂ) :
    hermFunc hM (fun e ↦ Complex.exp (c * (e : ℂ))) =
      ∑ S ∈ E.powerset, polyOp (fun Z ↦ (-c) • m Z) 1 S := by
  classical
  let g : Finset (Fin N) → QubitOp N := fun Z ↦ (-c) • m Z
  have hsum_g : ∑ Z ∈ E, g Z = (-c) • ∑ Z ∈ E, m Z := by
    dsimp only [g]; rw [← Finset.smul_sum]
  have hpow_expand : ∀ k : ℕ, (∑ Z ∈ E, g Z) ^ k = ∑ S ∈ E.powerset, polyTermSum g S k := by
    intro k
    have hpi : (∑ Z ∈ E, g Z) ^ k =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin k ↦ E), (List.ofFn (fun j : Fin k ↦ g (f j))).prod := by
      induction k with
      | zero =>
        simp only [pow_zero]
        have hsing : Fintype.piFinset (fun _ : Fin 0 ↦ E) = {Fin.elim0} := by
          ext f; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
          constructor
          · intro _; funext j; exact Fin.elim0 j
          · rintro rfl; intro j; exact Fin.elim0 j
        rw [hsing, Finset.sum_singleton]; simp
      | succ k ih =>
        rw [pow_succ', ih, Finset.mul_sum]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_product']
        refine Finset.sum_bij (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
        · rintro ⟨Z, f⟩ hp
          rcases Finset.mem_product.mp hp with ⟨hZ, hf⟩
          rw [Fintype.mem_piFinset] at hf ⊢
          intro j; refine Fin.cases hZ (fun i ↦ hf i) j
        · rintro ⟨Z₁, f₁⟩ _ ⟨Z₂, f₂⟩ _ heq
          apply Prod.ext
          · simpa using congrFun heq 0
          · funext i; simpa using congrFun heq i.succ
        · intro f hf
          rw [Fintype.mem_piFinset] at hf
          refine ⟨(f 0, fun i ↦ f i.succ), Finset.mem_product.mpr ⟨hf 0, Fintype.mem_piFinset.mpr fun i ↦ hf i.succ⟩, ?_⟩
          funext j; refine Fin.cases rfl (fun _ ↦ rfl) j
        · rintro ⟨Z, f⟩ _; simp [List.ofFn_succ, List.prod_cons]
    rw [hpi]
    have hpart := Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset (fun _ : Fin k ↦ E))
      (t := E.powerset) (g := fun f ↦ Finset.univ.image f)
      (fun f hf ↦ Finset.mem_powerset.mpr fun Z hZ ↦ by
        rcases Finset.mem_image.mp hZ with ⟨j, _, rfl⟩
        exact Fintype.mem_piFinset.mp hf j)
      (fun f ↦ (List.ofFn (fun j : Fin k ↦ g (f j))).prod)
    rw [← hpart]
    apply Finset.sum_congr rfl; intro S hS
    unfold polyTermSum
    apply Finset.sum_congr _ fun _ _ ↦ rfl
    ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hf, him⟩
      refine ⟨fun j ↦ ?_, him⟩
      rw [← him]; exact Finset.mem_image_of_mem f (Finset.mem_univ j)
    · rintro ⟨hf, him⟩
      exact ⟨fun j ↦ Finset.mem_powerset.mp hS (hf j), him⟩
  have hhas1 : HasSum (fun k : ℕ ↦ (c ^ k / (k.factorial : ℂ)) • (∑ Z ∈ E, m Z) ^ k)
      (hermFunc hM (fun e ↦ Complex.exp (c * (e : ℂ)))) := hasSum_hermFunc_exp hM c
  have hhas2 : HasSum (fun k : ℕ ↦ ∑ S ∈ E.powerset,
        ((-(1 : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) • polyTermSum g S k)
      (∑ S ∈ E.powerset, polyOp g 1 S) :=
    hasSum_sum fun S _ ↦ hasSum_polyOp g 1 S
  have hterm_eq : (fun k : ℕ ↦ (c ^ k / (k.factorial : ℂ)) • (∑ Z ∈ E, m Z) ^ k) =
      fun k : ℕ ↦ ∑ S ∈ E.powerset, ((-(1 : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) • polyTermSum g S k := by
    funext k
    rw [← Finset.smul_sum, ← hpow_expand k, hsum_g, smul_pow, smul_smul]
    congr 1
    have : (-(1 : ℝ) : ℂ) ^ k / (k.factorial : ℂ) * (-c) ^ k = c ^ k / (k.factorial : ℂ) := by
      rw [div_mul_eq_mul_div, ← mul_pow]
      have : (-(1 : ℝ) : ℂ) * -c = c := by push_cast; ring
      rw [this]
    exact this.symm
  rw [hterm_eq] at hhas1
  exact hhas1.unique hhas2

/-- **Exact Two-Hypergraph Product-Exponential Polymer Partition Function Identity**:
`normalizedTrace (hermFunc hH (exp (-β * ·)) * hermFunc hX (exp (ζ * ·))) =
  polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ)) (connectedPolymers (E ∪ E_X))`. -/
theorem normalizedTrace_exp_mul_exp_eq_polymerZ {N : ℕ}
    (E E_X : Finset (Finset (Fin N)))
    (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hEX_ne : ∀ Z ∈ E_X, Z.Nonempty)
    (h xOp : Finset (Fin N) → QubitOp N)
    (hh_supp : ∀ Z, h Z ∈ supportedOn Z) (hx_supp : ∀ Z, xOp Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian) (hX : (∑ Z ∈ E_X, xOp Z).IsHermitian)
    (β : ℝ) (ζ : ℂ) :
    let E_tot := E ∪ E_X
    let A_op : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E then (β : ℂ) • h Z else 0
    let B_op : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E_X then (-ζ) • xOp Z else 0
    normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) *
      hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ)))) =
      polymerZ polyIncompat (prodPolyWeight A_op B_op) (connectedPolymers E_tot) := by
  classical
  intro E_tot A_op B_op
  have hEtot_ne : ∀ Z ∈ E_tot, Z.Nonempty := by
    intro Z hZ; rcases Finset.mem_union.mp hZ with h1 | h2
    · exact hE_ne Z h1
    · exact hEX_ne Z h2
  have hA_supp : ∀ Z, A_op Z ∈ supportedOn Z := by
    intro Z; dsimp only [A_op]; split_ifs
    · exact (supportedOn Z).smul_mem _ (hh_supp Z)
    · exact (supportedOn Z).zero_mem
  have hB_supp : ∀ Z, B_op Z ∈ supportedOn Z := by
    intro Z; dsimp only [B_op]; split_ifs
    · exact (supportedOn Z).smul_mem _ (hx_supp Z)
    · exact (supportedOn Z).zero_mem
  have hH_sum : ∑ Z ∈ E_tot, (if Z ∈ E then h Z else 0) = ∑ Z ∈ E, h Z := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr Finset.subset_union_left]
  have hX_sum : ∑ Z ∈ E_tot, (if Z ∈ E_X then xOp Z else 0) = ∑ Z ∈ E_X, xOp Z := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr Finset.subset_union_right]
  have hH_tot : (∑ Z ∈ E_tot, (if Z ∈ E then h Z else 0)).IsHermitian := by
    rwa [hH_sum]
  have hX_tot : (∑ Z ∈ E_tot, (if Z ∈ E_X then xOp Z else 0)).IsHermitian := by
    rwa [hX_sum]
  have hA_eq : (fun Z ↦ (-(-(β : ℂ))) • (if Z ∈ E then h Z else 0)) = A_op := by
    funext Z; dsimp only [A_op]; split_ifs <;> simp
  have hB_eq : (fun Z ↦ (-ζ) • (if Z ∈ E_X then xOp Z else 0)) = B_op := by
    funext Z; dsimp only [B_op]; split_ifs <;> simp
  have hexpH : hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) =
      ∑ T₁ ∈ E_tot.powerset, polyOp A_op 1 T₁ := by
    have h1 := hermFunc_exp_eq_sum_polyOp E_tot (fun Z ↦ if Z ∈ E then h Z else 0) hH_tot (-(β : ℂ))
    rw [hA_eq] at h1
    convert h1 using 1
    have hhas1 := hasSum_hermFunc_exp hH (-(β : ℂ))
    have hhas2 := hasSum_hermFunc_exp hH_tot (-(β : ℂ))
    have hfun : (fun m : ℕ ↦ ((-(β : ℂ)) ^ m / (m.factorial : ℂ)) • (∑ Z ∈ E_tot, if Z ∈ E then h Z else 0) ^ m) =
        fun m : ℕ ↦ ((-(β : ℂ)) ^ m / (m.factorial : ℂ)) • (∑ Z ∈ E, h Z) ^ m := by
      funext m; rw [hH_sum]
    rw [hfun] at hhas2
    exact hhas1.unique hhas2
  have hexpX : hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ))) =
      ∑ T₂ ∈ E_tot.powerset, polyOp B_op 1 T₂ := by
    have h1 := hermFunc_exp_eq_sum_polyOp E_tot (fun Z ↦ if Z ∈ E_X then xOp Z else 0) hX_tot ζ
    rw [hB_eq] at h1
    convert h1 using 1
    have hhas1 := hasSum_hermFunc_exp hX ζ
    have hhas2 := hasSum_hermFunc_exp hX_tot ζ
    have hfun : (fun m : ℕ ↦ (ζ ^ m / (m.factorial : ℂ)) • (∑ Z ∈ E_tot, if Z ∈ E_X then xOp Z else 0) ^ m) =
        fun m : ℕ ↦ (ζ ^ m / (m.factorial : ℂ)) • (∑ Z ∈ E_X, xOp Z) ^ m := by
      funext m; rw [hX_sum]
    rw [hfun] at hhas2
    exact hhas1.unique hhas2
  have hprod_eq : hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) *
      hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ))) =
      ∑ S ∈ E_tot.powerset, prodPolyOp A_op B_op S := by
    rw [hexpH, hexpX, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    have hfib := Finset.sum_fiberwise_of_maps_to (s := E_tot.powerset ×ˢ E_tot.powerset)
      (t := E_tot.powerset) (g := fun p : Finset (Finset (Fin N)) × Finset (Finset (Fin N)) ↦ p.1 ∪ p.2)
      (fun p hp ↦ Finset.mem_powerset.mpr (Finset.union_subset
        (Finset.mem_powerset.mp (Finset.mem_product.mp hp).1)
        (Finset.mem_powerset.mp (Finset.mem_product.mp hp).2)))
      (fun p ↦ polyOp A_op 1 p.1 * polyOp B_op 1 p.2)
    rw [← hfib]
    apply Finset.sum_congr rfl; intro S hS
    unfold prodPolyOp
    rw [Finset.sum_filter, Finset.sum_product]
    have hsubS : S ⊆ E_tot := Finset.mem_powerset.mp hS
    symm
    have hflat : ∑ T₁ ∈ S.powerset, ∑ T₂ ∈ S.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = S),
        polyOp A_op 1 T₁ * polyOp B_op 1 T₂ =
        ∑ p ∈ (E_tot.powerset ×ˢ E_tot.powerset).filter (fun p ↦ p.1 ∪ p.2 = S),
          polyOp A_op 1 p.1 * polyOp B_op 1 p.2 := by
      have h1 : ∑ T₁ ∈ S.powerset, ∑ T₂ ∈ S.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = S),
          polyOp A_op 1 T₁ * polyOp B_op 1 T₂ =
          ∑ p ∈ (S.powerset ×ˢ S.powerset).filter (fun p ↦ p.1 ∪ p.2 = S),
            polyOp A_op 1 p.1 * polyOp B_op 1 p.2 := by
        rw [Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl; intro T₁ _; rw [Finset.sum_filter]
      rw [h1]
      apply Finset.sum_congr _ fun _ _ ↦ rfl
      ext ⟨T₁, T₂⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨h1, h2⟩, hu⟩
        exact ⟨⟨Finset.Subset.trans h1 hsubS, Finset.Subset.trans h2 hsubS⟩, hu⟩
      · rintro ⟨_, hu⟩
        exact ⟨⟨hu ▸ Finset.subset_union_left, hu ▸ Finset.subset_union_right⟩, hu⟩
    rw [hflat, Finset.sum_filter, Finset.sum_product]
  rw [hprod_eq, normalizedTrace_sum]
  rcases compatible_connectedPolymers_bijection E_tot hEtot_ne with ⟨hinj, hsurj⟩
  unfold polymerZ
  symm
  have hmem_filt : ∀ {s : Finset (Finset (Polymer N))} {p : Finset (Polymer N) → Prop}
      {inst : DecidablePred p} {a : Finset (Polymer N)},
      a ∈ @Finset.filter (Finset (Polymer N)) p inst s ↔ a ∈ s ∧ p a :=
    fun {_ _ _ _} ↦ Finset.mem_filter
  refine Finset.sum_bij (fun I _ ↦ I.biUnion id) ?_ ?_ ?_ ?_
  · intro I hI
    have hI' := hmem_filt.mp hI
    rw [Finset.mem_powerset]
    intro X hX
    rcases Finset.mem_biUnion.mp hX with ⟨γ, hγI, hXγ⟩
    exact (mem_connectedPolymers.mp (Finset.mem_powerset.mp hI'.1 hγI)).1 hXγ
  · intro I₁ hI₁ I₂ hI₂ heq
    have h1 := hmem_filt.mp hI₁
    have h2 := hmem_filt.mp hI₂
    exact hinj I₁ I₂ (Finset.mem_powerset.mp h1.1) h1.2 (Finset.mem_powerset.mp h2.1) h2.2 heq
  · intro S hS
    rcases hsurj S (Finset.mem_powerset.mp hS) with ⟨I, hIsub, hIcomp, hIeq⟩
    exact ⟨I, hmem_filt.mpr ⟨Finset.mem_powerset.mpr hIsub, hIcomp⟩, hIeq⟩
  · intro I hI
    have hI' := hmem_filt.mp hI
    exact (normalizedTrace_prodPolyOp_biUnion A_op B_op hA_supp hB_supp I hI'.2
      (fun γ hγ X hXγ ↦ hEtot_ne X ((mem_connectedPolymers.mp (Finset.mem_powerset.mp hI'.1 hγ)).1 hXγ))).symm

/-- Holomorphy of `ζ ↦ prodPolyWeight A (fun Z ↦ (-ζ) • B Z) γ`. -/
lemma differentiable_prodPolyWeight {N : ℕ}
    (A B : Finset (Fin N) → QubitOp N) (γ : Polymer N) :
    Differentiable ℂ (fun ζ : ℂ ↦ prodPolyWeight A (fun Z ↦ (-ζ) • B Z) γ) := by
  unfold prodPolyWeight prodPolyOp
  have hrew : (fun ζ : ℂ ↦ normalizedTrace (∑ T₁ ∈ γ.powerset,
      ∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
        polyOp A 1 T₁ * polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂)) =
      fun ζ : ℂ ↦ ∑ T₁ ∈ γ.powerset, ∑ T₂ ∈ γ.powerset.filter (fun T₂ ↦ T₁ ∪ T₂ = γ),
        normalizedTrace (polyOp A 1 T₁ * polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂) := by
    funext ζ; rw [normalizedTrace_sum]
    apply Finset.sum_congr rfl; intro T₁ _; rw [normalizedTrace_sum]
  rw [hrew]
  refine Differentiable.fun_sum fun T₁ _ ↦ Differentiable.fun_sum fun T₂ _ ↦ ?_
  intro ζ₀
  set M : QubitOp N := polyOp A 1 T₁
  set R : ℝ := ‖ζ₀‖ + 1
  have hR : 0 < R := by positivity
  let f : ℕ → ℂ → ℂ := fun m ζ ↦
    ((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) *
      normalizedTrace (M * polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m)
  have hf_diff : ∀ m : ℕ, Differentiable ℂ (f m) := by
    intro m
    dsimp only [f]
    refine Differentiable.const_mul ?_ _
    unfold normalizedTrace
    refine Differentiable.const_mul ?_ _
    unfold Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, polyTermSum, Matrix.sum_apply]
    refine Differentiable.fun_sum fun i _ ↦ Differentiable.fun_sum fun j _ ↦
      (differentiable_const (M i j)).mul (Differentiable.fun_sum fun w _ ↦ ?_)
    have hprod_diff : ∀ (k : ℕ) (P : Fin k → ℂ → QubitOp N),
        (∀ idx a b, Differentiable ℂ (fun ζ ↦ P idx ζ a b)) →
        ∀ a b, Differentiable ℂ (fun ζ ↦ (List.ofFn (fun idx : Fin k ↦ P idx ζ)).prod a b) := by
      intro k
      induction k with
      | zero => intro P _ a b; simp only [List.ofFn_zero, List.prod_nil]; exact differentiable_const _
      | succ k ih =>
        intro P hP a b
        simp only [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
        refine Differentiable.fun_sum fun c _ ↦
          (hP 0 a c).mul (ih (fun idx ↦ P idx.succ) (fun idx ↦ hP idx.succ) c b)
    refine hprod_diff m (fun idx ζ ↦ (-ζ) • B (w idx)) (fun idx a b ↦ ?_) j i
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (differentiable_id.neg).mul (differentiable_const _)
  set C : ℝ := ∑ Z ∈ T₂, R * opNorm (B Z)
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun Z _ ↦ by have := opNorm_nonneg (B Z); positivity
  have hf_bound : ∀ m : ℕ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ‖f m ζ‖ ≤ opNorm M * (C ^ m / (m.factorial : ℝ)) := by
    intro m ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    dsimp only [f]
    rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_one,
      one_pow, Complex.norm_natCast]
    have htr := le_trans (norm_normalizedTrace_le (M * polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m))
      (opNorm_mul_le M (polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m))
    have hpt := opNorm_polyTermSum_le (fun Z ↦ (-ζ) • B Z) T₂ m
    have hsum_le : ∑ Z ∈ T₂, opNorm ((-ζ) • B Z) ≤ C := by
      apply Finset.sum_le_sum; intro Z _
      rw [opNorm_smul, norm_neg]
      exact mul_le_mul_of_nonneg_right hζ (opNorm_nonneg (B Z))
    have hpow_le : (∑ Z ∈ T₂, opNorm ((-ζ) • B Z)) ^ m ≤ C ^ m :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun Z _ ↦ opNorm_nonneg _) hsum_le m
    have hinner : ‖normalizedTrace (M * polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m)‖ ≤ opNorm M * C ^ m :=
      le_trans htr (mul_le_mul_of_nonneg_left
        (le_trans hpt (le_trans (scalarWordSum_le_pow (fun Z ↦ opNorm ((-ζ) • B Z))
          (fun _ ↦ opNorm_nonneg _) T₂ m) hpow_le)) (opNorm_nonneg M))
    calc 1 / (m.factorial : ℝ) * ‖normalizedTrace (M * polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m)‖
        ≤ 1 / (m.factorial : ℝ) * (opNorm M * C ^ m) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = opNorm M * (C ^ m / (m.factorial : ℝ)) := by ring
  have hsumm_u : Summable (fun m : ℕ ↦ opNorm M * (C ^ m / (m.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial C).mul_left (opNorm M)
  have htend : TendstoUniformlyOn (fun K : ℕ ↦ fun ζ : ℂ ↦ ∑ m ∈ Finset.range K, f m ζ)
      (fun ζ : ℂ ↦ normalizedTrace (M * polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂)) atTop
      (Metric.closedBall 0 R) := by
    have hweier := tendstoUniformlyOn_tsum_nat hsumm_u (fun m ζ hζ ↦ hf_bound m ζ hζ)
    refine hweier.congr_right fun ζ _ ↦ ?_
    let Φ : QubitOp N →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun P ↦ normalizedTrace (M * P)
          map_add' := fun P₁ P₂ ↦ by rw [Matrix.mul_add, normalizedTrace_add]
          map_smul' := fun α P ↦ by simp [Matrix.mul_smul, normalizedTrace_smul] }
    have hs := (hasSum_polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂).map Φ Φ.continuous
    have hs' : HasSum (fun m : ℕ ↦ f m ζ) (Φ (polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂)) := by
      refine hs.congr_fun fun m ↦ ?_
      change Φ (((-(1 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • polyTermSum (fun Z ↦ (-ζ) • B Z) T₂ m) = f m ζ
      dsimp only [Φ, f]; simp [Matrix.mul_smul, normalizedTrace_smul]
    exact hs'.tsum_eq
  have hloc := (htend.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff_ball : DifferentiableOn ℂ
      (fun ζ : ℂ ↦ normalizedTrace (M * polyOp (fun Z ↦ (-ζ) • B Z) 1 T₂)) (Metric.ball 0 R) :=
    hloc.differentiableOn (Eventually.of_forall fun K ↦
      (Differentiable.fun_sum fun m _ ↦ hf_diff m).differentiableOn) Metric.isOpen_ball
  exact (hdiff_ball ζ₀ (by rw [Metric.mem_ball, dist_zero_right]; linarith)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; linarith))

/-- Derivative at `ζ = 0` of `ζ ↦ normalizedTrace (M * hermFunc hX (fun e ↦ cexp (ζ * e)))`. -/
private lemma hasDerivAt_normalizedTrace_mul_hermFunc_exp {N : ℕ}
    (M : QubitOp N) {X : QubitOp N} (hX : X.IsHermitian) :
    HasDerivAt
      (fun ζ : ℂ ↦ normalizedTrace (M * hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ)))))
      (normalizedTrace (M * X)) 0 := by
  let U : QubitOp N := (hX.eigenvectorUnitary : QubitOp N)
  have hrew : (fun ζ : ℂ ↦ normalizedTrace (M * hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ))))) =
      fun ζ : ℂ ↦ ((2 : ℝ) ^ N : ℂ)⁻¹ *
        ∑ i : QubitIdx N, (Uᴴ * M * U) i i * Complex.exp (ζ * (hX.eigenvalues i : ℂ)) := by
    funext ζ
    unfold normalizedTrace hermFunc
    dsimp only
    congr 1
    calc (M * (U * Matrix.diagonal (fun i ↦ Complex.exp (ζ * (hX.eigenvalues i : ℂ))) * Uᴴ)).trace
        = (Uᴴ * (M * (U * Matrix.diagonal (fun i ↦ Complex.exp (ζ * (hX.eigenvalues i : ℂ)))))).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = ((Uᴴ * M * U) * Matrix.diagonal (fun i ↦ Complex.exp (ζ * (hX.eigenvalues i : ℂ)))).trace := by
          simp only [Matrix.mul_assoc]
      _ = ∑ i : QubitIdx N, (Uᴴ * M * U) i i * Complex.exp (ζ * (hX.eigenvalues i : ℂ)) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
            mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hval : normalizedTrace (M * X) =
      ((2 : ℝ) ^ N : ℂ)⁻¹ * ∑ i : QubitIdx N, (Uᴴ * M * U) i i * (hX.eigenvalues i : ℂ) := by
    conv_lhs => rw [← hermFunc_id hX]
    unfold normalizedTrace hermFunc
    dsimp only
    congr 1
    calc (M * (U * Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ)) * Uᴴ)).trace
        = (Uᴴ * (M * (U * Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ))))).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = ((Uᴴ * M * U) * Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ))).trace := by
          simp only [Matrix.mul_assoc]
      _ = ∑ i : QubitIdx N, (Uᴴ * M * U) i i * (hX.eigenvalues i : ℂ) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
            mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hrew, hval]
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ ↦ ?_)
  have hlin : HasDerivAt (fun ζ : ℂ ↦ ζ * (hX.eigenvalues i : ℂ)) (hX.eigenvalues i : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (hX.eigenvalues i : ℂ)
  have hd := hlin.cexp
  simpa [zero_mul, Complex.exp_zero, one_mul] using hd.const_mul ((Uᴴ * M * U) i i)

/-- Shift identity for centered Hermitian exponentials:
`hermFunc hXt (exp (lam * ·)) = cexp (-lam * μ) • hermFunc hX (exp (lam * ·))`. -/
private lemma hermFunc_sub_scalar_exp {N : ℕ} {X : QubitOp N} (hX : X.IsHermitian)
    (μ lam : ℝ)
    (hXt : (X - (μ : ℂ) • (1 : QubitOp N)).IsHermitian) :
    hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ))) =
      Complex.exp (-(lam : ℂ) * (μ : ℂ)) • hermFunc hX (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ))) := by
  let U : QubitOp N := (hX.eigenvectorUnitary : QubitOp N)
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.prop
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.prop
  have hXt_diag : X - (μ : ℂ) • (1 : QubitOp N) =
      U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ)) * Uᴴ := by
    have hX_id := (hermFunc_id hX).symm
    unfold hermFunc at hX_id
    conv_lhs => rw [hX_id]
    calc U * Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ)) * Uᴴ - (μ : ℂ) • (1 : QubitOp N)
        = U * Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ)) * Uᴴ -
          U * Matrix.diagonal (fun _ ↦ (μ : ℂ)) * Uᴴ := by
          congr 1
          rw [← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1]
      _ = U * (Matrix.diagonal (fun i ↦ (hX.eigenvalues i : ℂ)) - Matrix.diagonal (fun _ ↦ (μ : ℂ))) * Uᴴ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ)) * Uᴴ := by
          congr 2; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  have hXt_pow : ∀ k : ℕ, (X - (μ : ℂ) • (1 : QubitOp N)) ^ k =
      U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ) ^ k) * Uᴴ := by
    intro k
    induction k with
    | zero => simp [Matrix.diagonal_one, hU1]
    | succ k ih =>
      rw [pow_succ, ih, hXt_diag]
      calc U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ) ^ k) * Uᴴ *
            (U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ)) * Uᴴ)
          = U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ) ^ k) * (Uᴴ * U) *
            Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ)) * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ) ^ k) *
            Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ))) * Uᴴ := by
            rw [hU2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i ↦ ((hX.eigenvalues i - μ : ℝ) : ℂ) ^ (k + 1)) * Uᴴ := by
            rw [Matrix.diagonal_mul_diagonal]; congr 2; funext i; rw [pow_succ]
  have hhas1 := hasSum_hermFunc_exp hXt (lam : ℂ)
  have hhas2 : HasSum (fun k : ℕ ↦ ((lam : ℂ) ^ k / (k.factorial : ℂ)) • (X - (μ : ℂ) • (1 : QubitOp N)) ^ k)
      (U * Matrix.diagonal (fun i ↦ Complex.exp ((lam : ℂ) * ((hX.eigenvalues i - μ : ℝ) : ℂ))) * Uᴴ) := by
    let Ψ : (QubitIdx N → ℂ) →L[ℂ] QubitOp N :=
      LinearMap.toContinuousLinearMap
        { toFun := fun v ↦ U * Matrix.diagonal v * Uᴴ
          map_add' := fun v w ↦ by rw [Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun c v ↦ by simp [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul] }
    have hvec : HasSum (fun k : ℕ ↦ fun i : QubitIdx N ↦
        ((lam : ℂ) * ((hX.eigenvalues i - μ : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
        (fun i : QubitIdx N ↦ Complex.exp ((lam : ℂ) * ((hX.eigenvalues i - μ : ℝ) : ℂ))) := by
      rw [hasSum_pi_iff]
      intro i
      simpa [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div] using
        (NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * ((hX.eigenvalues i - μ : ℝ) : ℂ)))
    have hmapped := hvec.map Ψ Ψ.continuous
    refine hmapped.congr_fun fun k ↦ ?_
    change U * Matrix.diagonal (fun i ↦ ((lam : ℂ) * ((hX.eigenvalues i - μ : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) * Uᴴ = _
    rw [hXt_pow k, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    congr 2; funext i; simp only [Pi.smul_apply, smul_eq_mul, mul_pow]; ring
  rw [hhas1.unique hhas2]
  unfold hermFunc
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 2; funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Reality and non-negativity of `Tr(gibbsRho hH β * hermFunc hXt (exp (lam * ·)))`. -/
private lemma trace_gibbsRho_mul_hermFunc_exp_real_nonneg {N : ℕ}
    {H Xt : QubitOp N} (hH : H.IsHermitian) (hXt : Xt.IsHermitian) (β lam : ℝ) :
    (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.im = 0 ∧
    0 ≤ (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.re := by
  let B : QubitOp N := ((Real.sqrt (gibbsPartitionFn hH β)⁻¹ : ℝ) : ℂ) •
    hermFunc hH (fun e ↦ ((Real.exp (-(β * e / 2)) : ℝ) : ℂ))
  let D : QubitOp N := hermFunc hXt (fun e ↦ ((Real.exp (lam * e / 2) : ℝ) : ℂ))
  have hB_herm : Bᴴ = B := by
    dsimp only [B]; rw [Matrix.conjTranspose_smul, hermFunc_conjTranspose]
    congr 1; · simp [Complex.star_def, Complex.conj_ofReal]
    · congr 1; funext e; simp [Complex.star_def, Complex.conj_ofReal]
  have hD_herm : Dᴴ = D := by
    dsimp only [D]; rw [hermFunc_conjTranspose]
    congr 1; funext e; simp [Complex.star_def, Complex.conj_ofReal]
  have hBB : B * B = gibbsRho hH β := by
    dsimp only [B]; unfold gibbsRho
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hermFunc_mul]
    congr 1
    · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.mpr (gibbsPartitionFn_pos hH β).le),
        Complex.ofReal_inv]
    · congr 1; funext e
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have hDD : D * D = hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ))) := by
    dsimp only [D]; rw [hermFunc_mul]
    congr 1; funext e
    rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
    congr 1; push_cast; ring
  have htr_eq : (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace =
      ((B * D)ᴴ * (B * D)).trace := by
    rw [← hBB, ← hDD, Matrix.conjTranspose_mul, hB_herm, hD_herm]
    calc (B * B * (D * D)).trace = (B * (B * D * D)).trace := by simp only [Matrix.mul_assoc]
      _ = (B * D * D * B).trace := Matrix.trace_mul_comm B (B * D * D)
      _ = (D * B * (B * D)).trace := by
          rw [Matrix.trace_mul_comm (B * D) (D * B)]; simp only [Matrix.mul_assoc]
  rw [htr_eq]
  have hsum : ((B * D)ᴴ * (B * D)).trace =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N, (((‖(B * D) j i‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  rw [hsum]
  constructor
  · simp [Complex.im_sum]
  · simp only [Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

set_option maxHeartbeats 1200000 in
/-- **Lemma 6.3 (Literal Product-Exponential Trace Cumulant Bound, Eq. 6.3)**:
Under the exact high-temperature hypotheses of Lemma 6.3 (`r ≥ 2`, `k_X ≥ 1`, `β ∈ [0, (8 e² r Jsite)⁻¹]`,
`k_r = max r k_X`, `Λ₀' = (16 k_r exp(1 + k_r / r) gX)⁻¹`, `|lam| ≤ Λ₀' / 2`):
`Real.log ((gibbsRho hH β * hermFunc hXtilde (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.re) ≤
  8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2`,
where `Xtilde = X - ((gibbsRho hH β * X).trace.re : ℂ) • 1`. -/
theorem lemma_6_3_product_exp_cumulant_bound {N r k_X : ℕ}
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
    let X := ∑ Z ∈ E_X, xOp Z
    let μ := (gibbsRho hH β * X).trace.re
    let Xtilde : QubitOp N := X - (μ : ℂ) • 1
    have hXt : Xtilde.IsHermitian := by
      simp only [Xtilde, X, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hX.eq]
    let kr := max r k_X
    let Λ₀' := 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * gX)
    Real.log ((gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.re) ≤
      8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := by
  classical
  intro X μ Xtilde hXt kr Λ₀'
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hkr_ge_r : r ≤ kr := le_max_left r k_X
  have hkr_ge_kX : k_X ≤ kr := le_max_right r k_X
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by exact_mod_cast (by omega : 0 < kr)
  have hΛ_pos : 0 < Λ₀' := by dsimp only [Λ₀']; positivity
  let E_tot : Finset (Finset (Fin N)) := E ∪ E_X
  have hEtot_ne : ∀ Z ∈ E_tot, Z.Nonempty := by
    intro Z hZ; rcases Finset.mem_union.mp hZ with h1 | h2
    · exact hE_ne Z h1
    · exact hEX_ne Z h2
  let A_op : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E then (β : ℂ) • h Z else 0
  let B₀ : Finset (Fin N) → QubitOp N := fun Z ↦ if Z ∈ E_X then xOp Z else 0
  let B_op : ℂ → Finset (Fin N) → QubitOp N := fun ζ Z ↦ (-ζ) • B₀ Z
  have hB_op_eq : ∀ ζ Z, B_op ζ Z = if Z ∈ E_X then (-ζ) • xOp Z else 0 := by
    intro ζ Z; dsimp only [B_op, B₀]; split_ifs <;> simp
  let c : ℝ := 1 / (2 * (r : ℝ))
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  have hc_le : c ≤ 1 / 4 := by
    dsimp only [c]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  let a : Polymer N → ℝ := fun γ ↦ c * (polySupp γ).card
  have ha_nn : ∀ γ, 0 ≤ a γ := fun γ ↦ by dsimp only [a]; positivity
  let Γ : Finset (Polymer N) := connectedPolymers E_tot
  have hsite_pin : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ x : Fin N,
      ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ),
        ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ) ≤ c / 2 := by
    intro ζ hζ x
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    let η : Finset (Fin N) → ℝ := fun Z ↦
      (Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1) * Real.exp (c * (Z.card : ℝ))
    have hη_nn : ∀ Z ∈ E_tot, 0 ≤ η Z := fun Z _ ↦ by
      dsimp only [η]
      exact mul_nonneg (by linarith [Real.one_le_exp (add_nonneg (opNorm_nonneg (A_op Z)) (opNorm_nonneg (B_op ζ Z)))])
        (Real.exp_pos _).le
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
        have hop_le : opNorm (A_op Z) + opNorm (B_op ζ Z) ≤ u1 + u2 := by
          dsimp only [A_op, u1, u2]
          rw [hB_op_eq]
          refine add_le_add ?_ ?_
          · split_ifs
            · rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
            · simp [opNorm, opToCLM]
          · split_ifs
            · rw [opNorm_smul, norm_neg]
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
        have hexp_sub : Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1 ≤ (u1 + u2) * Real.exp 1 := by
          have h1 : Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1 ≤ Real.exp (u1 + u2) - 1 := by
            linarith [Real.exp_le_exp.mpr hop_le]
          have h2 : Real.exp (u1 + u2) - 1 ≤ (u1 + u2) * Real.exp (u1 + u2) := by
            have := Real.add_one_le_exp (-(u1 + u2))
            have hpos := Real.exp_pos (u1 + u2)
            have hmul := mul_le_mul_of_nonneg_right this hpos.le
            rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
            linarith
          exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_u_lt1) (by linarith)))
        have hprod_eq : η Z * Real.exp (c * (Z.card : ℝ)) =
            (Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1) * Real.exp (2 * c * (Z.card : ℝ)) := by
          dsimp only [η]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        rw [hprod_eq]
        have h1 : (Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1) * Real.exp (2 * c * (Z.card : ℝ)) ≤
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
            exact mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hβ0 (opNorm_nonneg _))
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
            exact mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hΛ_pos.le (opNorm_nonneg _))
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
    have hpoly_le : ∀ γ ∈ Γ, ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ) ≤ ∏ Z ∈ γ, η Z := by
      intro γ _
      have hcard_bi : (polySupp γ).card ≤ ∑ Z ∈ γ, Z.card := Finset.card_biUnion_le
      have hexp_le : Real.exp (a γ) ≤ ∏ Z ∈ γ, Real.exp (c * (Z.card : ℝ)) := by
        rw [← Real.exp_sum]
        apply Real.exp_le_exp.mpr
        have hcast : ((polySupp γ).card : ℝ) ≤ ∑ Z ∈ γ, (Z.card : ℝ) := by exact_mod_cast hcard_bi
        calc c * ((polySupp γ).card : ℝ) ≤ c * ∑ Z ∈ γ, (Z.card : ℝ) :=
              mul_le_mul_of_nonneg_left hcast hc_pos.le
          _ = ∑ Z ∈ γ, c * (Z.card : ℝ) := Finset.mul_sum _ _ _
      calc ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ)
          ≤ (∏ Z ∈ γ, (Real.exp (opNorm (A_op Z) + opNorm (B_op ζ Z)) - 1)) *
              (∏ Z ∈ γ, Real.exp (c * (Z.card : ℝ))) :=
            mul_le_mul (norm_prodPolyWeight_le A_op (B_op ζ) γ) hexp_le (Real.exp_pos _).le
              (Finset.prod_nonneg fun Z _ ↦ by
                linarith [Real.one_le_exp (add_nonneg (opNorm_nonneg (A_op Z)) (opNorm_nonneg (B_op ζ Z)))])
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
    calc ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ)
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
  have hkp_disk : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀',
      (∀ γ ∈ Γ, ∑ δ ∈ Γ.filter (fun δ ↦ polyIncompat γ δ),
          ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ) ≤ a γ / 2) ∧
      (∀ δ ∈ Γ, ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ) ≤ 1 / 2) := by
    intro ζ hζ
    constructor
    · intro γ _
      have hbi : Γ.filter (fun δ ↦ polyIncompat γ δ) ⊆
          (polySupp γ).biUnion (fun x ↦ Γ.filter (fun δ ↦ x ∈ polySupp δ)) := by
        intro δ hδ; rcases Finset.mem_filter.mp hδ with ⟨hδΓ, hinc⟩
        rcases Finset.not_disjoint_iff.mp hinc with ⟨x, hx1, hx2⟩
        exact Finset.mem_biUnion.mpr ⟨x, hx1, Finset.mem_filter.mpr ⟨hδΓ, hx2⟩⟩
      calc ∑ δ ∈ Γ.filter (fun δ ↦ polyIncompat γ δ), ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ)
          ≤ ∑ δ ∈ (polySupp γ).biUnion (fun x ↦ Γ.filter (fun δ ↦ x ∈ polySupp δ)),
              ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hbi fun _ _ _ ↦ by positivity
        _ ≤ ∑ x ∈ polySupp γ, ∑ δ ∈ Γ.filter (fun δ ↦ x ∈ polySupp δ),
              ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ) :=
            real_sum_biUnion_le _ _ _ fun _ _ ↦ by positivity
        _ ≤ ∑ _x ∈ polySupp γ, (c / 2) := Finset.sum_le_sum fun x _ ↦ hsite_pin ζ hζ x
        _ = a γ / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp only [a]; ring
    · intro δ hδ
      rcases (mem_connectedPolymers.mp hδ).2.1 with ⟨Z, hZδ⟩
      rcases hEtot_ne Z ((mem_connectedPolymers.mp hδ).1 hZδ) with ⟨x, hxZ⟩
      have hxδ : x ∈ polySupp δ := Finset.mem_biUnion.mpr ⟨Z, hZδ, hxZ⟩
      have h1 : ‖prodPolyWeight A_op (B_op ζ) δ‖ * Real.exp (a δ) ≤
          ∑ γ ∈ Γ.filter (fun γ ↦ x ∈ polySupp γ), ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ) :=
        Finset.single_le_sum (f := fun γ ↦ ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ))
          (fun _ _ ↦ by positivity) (Finset.mem_filter.mpr ⟨hδ, hxδ⟩)
      linarith [hsite_pin ζ hζ x, hc_le]
  let Zslice : ℕ → ℂ → ℂ := fun k ζ ↦ polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ)) (siteSlice Γ k)
  let siteRatio : ℕ → ℂ → ℂ := fun k ζ ↦ Zslice (k + 1) ζ / Zslice k ζ
  let L : ℂ → ℂ := fun ζ ↦ ∑ k ∈ Finset.range N, Complex.log (siteRatio k ζ)
  have hZslice_ne : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ k : ℕ, Zslice k ζ ≠ 0 := by
    intro ζ hζ k
    rcases hkp_disk ζ hζ with ⟨hkp_h, hsm⟩
    exact (polymerZ_nonvanishing_and_ratio polyIncompat polyIncompat_symm
      (prodPolyWeight A_op (B_op ζ)) a ha_nn Γ hkp_h hsm (siteSlice Γ k).card
      (siteSlice Γ k) le_rfl (Finset.filter_subset _ _)).1
  have hratio_close : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', ∀ k ∈ Finset.range N,
      ‖siteRatio k ζ - 1‖ ≤ 1 / 4 := by
    intro ζ hζ k hk
    have hkN : k < N := Finset.mem_range.mp hk
    rcases hkp_disk ζ hζ with ⟨hkp_h, hsm⟩
    have hZne := hZslice_ne ζ hζ k
    have hstep := polymerZ_siteSlice_step (prodPolyWeight A_op (B_op ζ)) Γ hkN
    have hsub_eq : siteRatio k ζ - 1 =
        ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
          prodPolyWeight A_op (B_op ζ) γ *
            (polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ))
              ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ) := by
      dsimp only [siteRatio, Zslice]
      rw [hstep, add_div, div_self hZne, add_sub_cancel_left, Finset.sum_div]
      apply Finset.sum_congr rfl; intro γ _; rw [mul_div_assoc]
    rw [hsub_eq]
    have hkp_rat := (polymerZ_nonvanishing_and_ratio polyIncompat polyIncompat_symm
      (prodPolyWeight A_op (B_op ζ)) a ha_nn Γ hkp_h hsm (siteSlice Γ k).card
      (siteSlice Γ k) le_rfl (Finset.filter_subset _ _)).2
    have hsub_pin : siteSlice Γ (k + 1) \ siteSlice Γ k ⊆ Γ.filter (fun γ ↦ (⟨k, hkN⟩ : Fin N) ∈ polySupp γ) := by
      intro γ hγ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hγ).1).1,
        mem_siteSlice_sdiff_mem_polySupp Γ hkN hγ⟩
    calc ‖∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            prodPolyWeight A_op (B_op ζ) γ *
              (polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ))
                ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ)‖
        ≤ ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            ‖prodPolyWeight A_op (B_op ζ) γ‖ *
              ‖polymerZ polyIncompat (prodPolyWeight A_op (B_op ζ))
                ((siteSlice Γ k).filter (fun δ ↦ ¬polyIncompat γ δ)) / Zslice k ζ‖ := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun γ _ ↦ ?_); rw [norm_mul]
      _ ≤ ∑ γ ∈ siteSlice Γ (k + 1) \ siteSlice Γ k,
            ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ) :=
          Finset.sum_le_sum fun γ hγ ↦ mul_le_mul_of_nonneg_left
            (hkp_rat γ (Finset.mem_filter.mp (Finset.mem_sdiff.mp hγ).1).1) (norm_nonneg _)
      _ ≤ ∑ γ ∈ Γ.filter (fun γ ↦ (⟨k, hkN⟩ : Fin N) ∈ polySupp γ),
            ‖prodPolyWeight A_op (B_op ζ) γ‖ * Real.exp (a γ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_pin fun _ _ _ ↦ by positivity
      _ ≤ c / 2 := hsite_pin ζ hζ ⟨k, hkN⟩
      _ ≤ 1 / 4 := by linarith [hc_le]
  let Zfn : ℂ → ℂ := fun ζ ↦
    normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) *
      hermFunc hX (fun e ↦ Complex.exp (ζ * (e : ℂ))))
  have hZfn_eq : ∀ ζ : ℂ, Zfn ζ = Zslice N ζ := by
    intro ζ
    have hpoly := normalizedTrace_exp_mul_exp_eq_polymerZ E E_X hE_ne hEX_ne h xOp hh_supp hx_supp hH hX β ζ
    dsimp only [Zslice, Zfn]
    rw [siteSlice_full]
    have hB_fun : (fun Z ↦ if Z ∈ E_X then (-ζ) • xOp Z else 0) = B_op ζ := funext (fun Z ↦ (hB_op_eq ζ Z).symm)
    simpa [hB_fun, E_tot, A_op, Γ] using hpoly
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
  have hZslice_diff : ∀ k : ℕ, Differentiable ℂ (Zslice k) := by
    intro k
    dsimp only [Zslice]
    unfold polymerZ
    refine Differentiable.fun_sum fun I _ ↦ Differentiable.fun_finset_prod fun γ _ ↦ ?_
    exact differentiable_prodPolyWeight A_op B₀ γ
  have hL_diffAt : ∀ ζ ∈ Metric.closedBall (0 : ℂ) Λ₀', DifferentiableAt ℂ L ζ := by
    intro ζ hζ
    dsimp only [L]
    refine DifferentiableAt.fun_sum fun k hk ↦ ?_
    have hrat_d : DifferentiableAt ℂ (siteRatio k) ζ :=
      (hZslice_diff (k + 1) ζ).div (hZslice_diff k ζ) (hZslice_ne ζ hζ k)
    exact hrat_d.clog (complex_log_bound_of_norm_sub_one_le (hratio_close ζ hζ k hk)).1
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
  have hZ0_re : Zfn 0 = (((2 : ℝ) ^ N : ℂ)⁻¹) * (gibbsPartitionFn hH β : ℂ) := by
    have hX0 : hermFunc hX (fun e ↦ Complex.exp ((0 : ℂ) * (e : ℂ))) = 1 := by
      unfold hermFunc
      simp only [zero_mul, Complex.exp_zero]
      have hU : (hX.eigenvectorUnitary : QubitOp N) * (hX.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.prop
      rw [Matrix.diagonal_one, Matrix.mul_one, hU]
    dsimp only [Zfn]
    rw [hX0, Matrix.mul_one]
    unfold normalizedTrace gibbsPartitionFn hermFunc
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
  have hZ'0 : HasDerivAt Zfn (normalizedTrace (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) * X)) 0 :=
    hasDerivAt_normalizedTrace_mul_hermFunc_exp (hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ)))) hX
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
  have hschwarz := cauchy_order2_schwarz_bound hΛ_pos (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
    g hg_cont hg_diff hg0 hg'0 hg_bdd (lam : ℂ)
    (by rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hlam)
  have hXt_exp := hermFunc_sub_scalar_exp hX μ lam hXt
  have hlam_cl : (lam : ℂ) ∈ Metric.closedBall (0 : ℂ) Λ₀' := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hexp_g : Complex.exp (g (lam : ℂ)) =
      (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace := by
    dsimp only [g]
    rw [Complex.exp_sub, Complex.exp_sub, hexp_L (lam : ℂ) hlam_cl,
      hexp_L 0 (Metric.mem_closedBall_self hΛ_pos.le), hZ0_re, hXt_exp,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hgibbs : gibbsRho hH β = ((gibbsPartitionFn hH β : ℂ)⁻¹) •
        hermFunc hH (fun e ↦ Complex.exp (-(β : ℂ) * (e : ℂ))) := by
      unfold gibbsRho; congr 1; congr 1; funext e; rw [Complex.ofReal_exp]; push_cast; rfl
    rw [hgibbs, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    dsimp only [Zfn]; unfold normalizedTrace
    have h2ne : ((2 : ℝ) ^ N : ℂ) ≠ 0 := by positivity
    have hZne : (gibbsPartitionFn hH β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gibbsPartitionFn_pos hH β).ne'
    have hexp_neg : (Complex.exp ((μ : ℂ) * (lam : ℂ)))⁻¹ = Complex.exp (-(lam : ℂ) * (μ : ℂ)) := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [div_eq_mul_inv, hexp_neg]
    field_simp [h2ne, hZne]
  have htr_real_nn := trace_gibbsRho_mul_hermFunc_exp_real_nonneg hH hXt β lam
  have htr_re_eq : (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.re =
      Real.exp (g (lam : ℂ)).re := by
    have hnorm := congrArg norm hexp_g
    rw [Complex.norm_exp] at hnorm
    have htr_c : (gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace =
        ((gibbsRho hH β * hermFunc hXt (fun e ↦ Complex.exp ((lam : ℂ) * (e : ℂ)))).trace.re : ℂ) :=
      Complex.ext rfl (by simp [htr_real_nn.1])
    rw [htr_c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htr_real_nn.2] at hnorm
    exact hnorm.symm
  rw [htr_re_eq, Real.log_exp]
  calc (g (lam : ℂ)).re ≤ |(g (lam : ℂ)).re| := le_abs_self _
    _ ≤ ‖g (lam : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ 4 * (2 * (N : ℝ)) * ‖(lam : ℂ)‖ ^ 2 / Λ₀' ^ 2 := hschwarz
    _ = 8 * (N : ℝ) * lam ^ 2 / Λ₀' ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring

end ProductExpPolymer

end KrylovChaos
