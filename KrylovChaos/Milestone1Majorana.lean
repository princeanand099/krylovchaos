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
import KrylovChaos.CausalNormBounds
import KrylovChaos.EndToEndTheorems
import KrylovChaos.Filtration
import KrylovChaos.WightmanProjectors
import KrylovChaos.ConcreteEndToEndWiring
import KrylovChaos.Theorem11bConcrete
import Mathlib.Tactic

/-!
# Milestone 1 Majorana Formalization: Lemma 2.1, Prop. 4.1, Lemma 4.2 & Thm. 1.1(b) (Items #1, #9)

Strictly Mathlib-only, complete proofs, zero custom axioms, zero hypothesis laundering:
1. **Majorana String Multiplication & Commutation Algebra**:
   - `majoranaString_mul_exists`: `∃ c : ℂ, majoranaString n P * majoranaString n Q = c • majoranaString n (symmDiff P Q)`.
   - `majoranaString_disjoint_comm`: for disjoint `P, Q`,
     `majoranaString n P * majoranaString n Q = ((-1 : ℂ) ^ (P.card * Q.card)) • (majoranaString n Q * majoranaString n P)`.
   - `majoranaString_even_disjoint_comm`: even-parity disjoint Majorana strings commute (`matComm = 0`).
2. **Item #1 (Majorana `LocalInteractionDecomp` & Lemma 2.1(1)–(3))**:
   - `majoranaSupportedSubmodule n U` and `majoranaEvenSupportedSubmodule n U`.
   - `majoranaLocalInteractionDecomp`: instantiates `LocalInteractionDecomp (QubitOpCLM n) (2 * n) r`
     for even-parity `r`-local Majorana Hamiltonians, yielding Lemma 2.1(1)–(3) via
     `CausalNormBounds.lemma_2_1_single_site_exp_bound` and `lemma_2_1_r_local_exp_bound`.
3. **Item #9 (Majorana Filtration, Prop. 4.1(1)–(2), Lemma 4.2 & Theorem 1.1(b))**:
   - `majorana_comm_mem_filtration`: for even-parity `H ∈ majoranaFiltrationSubmodule n r` (`1 ≤ r`)
     and `A ∈ majoranaFiltrationSubmodule n s`, `matComm H A ∈ majoranaFiltrationSubmodule n (s + r - 1)`.
   - `majoranaWightmanProj`, `majoranaWightmanQ`, `majoranaLambdaMSS`.
   - `prop_4_1_part2_majorana`: `Re (O(t) | 𝒬^{(β),Maj} O(t))_β^W ≤ (r - 1) * K_β^W(t) + s₀`.
   - `lemma_4_2_majorana_concrete`: Eq. (4.3) on `majoranaThermalSize` & `majoranaLambdaMSS`.
   - `theorem_1_1b_majorana_concrete` & `theorem_1_1b_family_majorana`: concrete fixed-`n` and
     family-level Theorem 1.1(b) (`λ_L ≤ 2 α`) for Majorana systems.
-/

namespace KrylovChaos

open Matrix

section MajoranaStringAlgebra

private def foldMajorana (n : ℕ) (l : List (Fin (2 * n))) : QubitOp n :=
  l.foldr (fun j acc ↦ majoranaProbe n j * acc) 1

private lemma foldMajorana_eq_of_sorted (n : ℕ) (Q : Finset (Fin (2 * n))) :
    majoranaString n Q = foldMajorana n (Q.sort (· ≤ ·)) := rfl

private lemma foldMajorana_sort_unique (n : ℕ) (l : List (Fin (2 * n)))
    (hsort : l.Pairwise (· < ·)) :
    foldMajorana n l = majoranaString n l.toFinset := by
  unfold majoranaString foldMajorana
  congr 1
  have hnd : l.Nodup := hsort.imp (fun h ↦ ne_of_lt h)
  have hle : l.Pairwise (· ≤ ·) := hsort.imp (fun h ↦ le_of_lt h)
  have hsort_eq : l.toFinset.sort (· ≤ ·) = l := by
    have hperm : (l.toFinset.sort (· ≤ ·)).Perm l :=
      (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnd).mpr
        (fun x ↦ by simp [Finset.mem_sort, List.mem_toFinset])
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 ↦ le_antisymm h1 h2) (Finset.pairwise_sort _ _) hle
  rw [hsort_eq]

private lemma majoranaProbe_mul_foldMajorana_sorted (n : ℕ) (j : Fin (2 * n)) :
    ∀ l : List (Fin (2 * n)), l.Pairwise (· < ·) →
      ∃ c : ℂ, majoranaProbe n j * foldMajorana n l =
        c • majoranaString n (symmDiff {j} l.toFinset) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨1, ?_⟩
    have hsym : symmDiff ({j} : Finset (Fin (2 * n))) ([] : List (Fin (2 * n))).toFinset = {j} := by
      ext x; simp [Finset.mem_symmDiff]
    rw [hsym]
    simp [foldMajorana, majoranaString, Finset.sort_singleton]
  | cons a t ih =>
    intro hsort
    rw [List.pairwise_cons] at hsort
    rcases hsort with ⟨ha_lt, ht_sort⟩
    by_cases hja : j < a
    · refine ⟨1, ?_⟩
      have hcons_sort : (j :: a :: t).Pairwise (· < ·) := by
        rw [List.pairwise_cons]
        refine ⟨fun x hx ↦ ?_, List.pairwise_cons.mpr ⟨ha_lt, ht_sort⟩⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact hja
        · exact lt_trans hja (ha_lt x hxt)
      have hnotmem : j ∉ (a :: t).toFinset := by
        intro hm
        rw [List.mem_toFinset] at hm
        rcases List.mem_cons.mp hm with rfl | hxt
        · exact lt_irrefl _ hja
        · exact lt_asymm hja (ha_lt j hxt)
      have hsym : symmDiff ({j} : Finset (Fin (2 * n))) (a :: t).toFinset = (j :: a :: t).toFinset := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons, Finset.mem_insert]
        constructor
        · rintro (⟨rfl, _⟩ | ⟨hx, hxj⟩)
          · left; rfl
          · right; exact hx
        · rintro (rfl | hx)
          · left; exact ⟨rfl, by simpa [List.toFinset_cons] using hnotmem⟩
          · right; refine ⟨hx, ?_⟩
            rintro rfl
            exact hnotmem (by simpa [List.toFinset_cons] using hx)
      rw [hsym, ← foldMajorana_sort_unique n (j :: a :: t) hcons_sort, one_smul]
      rfl
    · by_cases heq : j = a
      · subst heq
        refine ⟨1, ?_⟩
        have hnotmem : j ∉ t.toFinset := by
          intro hm
          exact lt_irrefl j (ha_lt j (List.mem_toFinset.mp hm))
        have hsym : symmDiff ({j} : Finset (Fin (2 * n))) (j :: t).toFinset = t.toFinset := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons, Finset.mem_insert]
          constructor
          · rintro (⟨rfl, h⟩ | ⟨rfl | hxt, hxj⟩)
            · exact (h (Or.inl rfl)).elim
            · exact (hxj rfl).elim
            · exact hxt
          · intro hxt
            right
            refine ⟨Or.inr hxt, ?_⟩
            rintro rfl; exact hnotmem hxt
        rw [hsym, ← foldMajorana_sort_unique n t ht_sort, one_smul]
        simp only [foldMajorana, List.foldr_cons]
        rw [← Matrix.mul_assoc, majoranaProbe_sq, Matrix.one_mul]
      · have haj : a < j := lt_of_le_of_ne (le_of_not_gt hja) (Ne.symm heq)
        rcases ih ht_sort with ⟨c, hc⟩
        refine ⟨-c, ?_⟩
        have ha_notmem : a ∉ symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset := by
          intro hm
          rw [Finset.mem_symmDiff] at hm
          rcases hm with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact (ne_of_lt haj) (Finset.mem_singleton.mp h1)
          · exact lt_irrefl a (ha_lt a (List.mem_toFinset.mp h2))
        have hsym : symmDiff ({j} : Finset (Fin (2 * n))) (a :: t).toFinset =
            insert a (symmDiff {j} t.toFinset) := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons, Finset.mem_insert]
          constructor
          · rintro (⟨rfl, h⟩ | ⟨rfl | hxt, hxj⟩)
            · right; left; exact ⟨rfl, fun hm ↦ h (Or.inr hm)⟩
            · left; rfl
            · right; right; exact ⟨hxt, hxj⟩
          · rintro (rfl | ⟨rfl, h⟩ | ⟨hxt, hxj⟩)
            · right; exact ⟨Or.inl rfl, ne_of_lt haj⟩
            · left; refine ⟨rfl, ?_⟩; rintro (hje | hjt)
              · exact heq hje
              · exact h hjt
            · right; exact ⟨Or.inr hxt, hxj⟩
        have hlt_all : ∀ x ∈ (symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset).sort (· ≤ ·), a < x := by
          intro x hx
          rw [Finset.mem_sort, Finset.mem_symmDiff] at hx
          rcases hx with ⟨h1, _⟩ | ⟨h2, _⟩
          · rw [Finset.mem_singleton.mp h1]; exact haj
          · exact ha_lt x (List.mem_toFinset.mp h2)
        have hsort_tail : ((symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset).sort (· ≤ ·)).Pairwise (· < ·) := by
          have hp := Finset.pairwise_sort (symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset) (· ≤ ·)
          have hnd := Finset.sort_nodup (symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset) (· ≤ ·)
          exact List.pairwise_iff_getElem.mpr fun i k hi hk hik ↦
            lt_of_le_of_ne (List.pairwise_iff_getElem.mp hp i k hi hk hik)
              (fun heq_ik ↦ (Nat.ne_of_lt hik) (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨i, hi⟩) (a₂ := ⟨k, hk⟩) heq_ik)))
        have hcons_sort : (a :: (symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset).sort (· ≤ ·)).Pairwise (· < ·) :=
          List.pairwise_cons.mpr ⟨hlt_all, hsort_tail⟩
        have htofin : (a :: (symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset).sort (· ≤ ·)).toFinset =
            insert a (symmDiff {j} t.toFinset) := by
          ext x; simp [List.toFinset_cons, Finset.mem_sort]
        have hstr_eq : majoranaString n (insert a (symmDiff {j} t.toFinset)) =
            majoranaProbe n a * majoranaString n (symmDiff {j} t.toFinset) := by
          rw [← htofin, ← foldMajorana_sort_unique n _ hcons_sort]
          rfl
        rw [hsym, hstr_eq]
        calc majoranaProbe n j * foldMajorana n (a :: t)
            = (majoranaProbe n j * majoranaProbe n a) * foldMajorana n t := by
                simp only [foldMajorana, List.foldr_cons, Matrix.mul_assoc]
          _ = -(majoranaProbe n a * majoranaProbe n j) * foldMajorana n t := by
                rw [majoranaProbe_anticomm (Ne.symm heq)]
          _ = -(majoranaProbe n a * (majoranaProbe n j * foldMajorana n t)) := by
                simp only [Matrix.neg_mul, Matrix.mul_assoc]
          _ = -(majoranaProbe n a * (c • majoranaString n (symmDiff {j} t.toFinset))) := by
                rw [hc]
          _ = (-c) • (majoranaProbe n a * majoranaString n (symmDiff {j} t.toFinset)) := by
                rw [Matrix.mul_smul, neg_smul]

/-- **Product of Any Two Majorana Strings**:
`majoranaString n P * majoranaString n Q = c • majoranaString n (symmDiff P Q)` for some `c : ℂ`. -/
theorem majoranaString_mul_exists (n : ℕ) (P Q : Finset (Fin (2 * n))) :
    ∃ c : ℂ, majoranaString n P * majoranaString n Q =
      c • majoranaString n (symmDiff P Q) := by
  have hlist : ∀ l : List (Fin (2 * n)), l.Nodup →
      ∀ Q : Finset (Fin (2 * n)),
        ∃ c : ℂ, foldMajorana n l * majoranaString n Q =
          c • majoranaString n (symmDiff l.toFinset Q) := by
    intro l
    induction l with
    | nil =>
      intro _ Q
      refine ⟨1, ?_⟩
      have hsym : symmDiff ([] : List (Fin (2 * n))).toFinset Q = Q := by ext x; simp [Finset.mem_symmDiff]
      rw [hsym]; simp [foldMajorana]
    | cons j t ih =>
      intro hnd Q
      rw [List.nodup_cons] at hnd
      rcases ih hnd.2 Q with ⟨c₁, hc₁⟩
      have hQsort : ((symmDiff t.toFinset Q).sort (· ≤ ·)).Pairwise (· < ·) := by
        have hp := Finset.pairwise_sort (symmDiff t.toFinset Q) (· ≤ ·)
        have hndQ := Finset.sort_nodup (symmDiff t.toFinset Q) (· ≤ ·)
        exact List.pairwise_iff_getElem.mpr fun i k hi hk hik ↦
          lt_of_le_of_ne (List.pairwise_iff_getElem.mp hp i k hi hk hik)
            (fun heq_ik ↦ (Nat.ne_of_lt hik) (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hndQ) (a₁ := ⟨i, hi⟩) (a₂ := ⟨k, hk⟩) heq_ik)))
      rcases majoranaProbe_mul_foldMajorana_sorted n j _ hQsort with ⟨c₂, hc₂⟩
      have htofin : ((symmDiff t.toFinset Q).sort (· ≤ ·)).toFinset = symmDiff t.toFinset Q := by
        ext x; simp [Finset.mem_sort]
      rw [htofin] at hc₂
      have hsym_assoc : symmDiff (j :: t).toFinset Q = symmDiff {j} (symmDiff t.toFinset Q) := by
        have hj_not : j ∉ t.toFinset := by simpa [List.mem_toFinset] using hnd.1
        have hdisj : symmDiff ({j} : Finset (Fin (2 * n))) t.toFinset = (j :: t).toFinset := by
          ext x; simp only [Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons, Finset.mem_insert]
          constructor
          · rintro (⟨rfl, _⟩ | ⟨hx, _⟩)
            · left; rfl
            · right; exact hx
          · rintro (rfl | hx)
            · left; exact ⟨rfl, hj_not⟩
            · right; refine ⟨hx, ?_⟩; rintro rfl; exact hj_not hx
        rw [← hdisj, symmDiff_assoc]
      refine ⟨c₁ * c₂, ?_⟩
      rw [hsym_assoc]
      calc foldMajorana n (j :: t) * majoranaString n Q
          = majoranaProbe n j * (foldMajorana n t * majoranaString n Q) := by
              simp only [foldMajorana, List.foldr_cons, Matrix.mul_assoc]
        _ = majoranaProbe n j * (c₁ • majoranaString n (symmDiff t.toFinset Q)) := by rw [hc₁]
        _ = c₁ • (majoranaProbe n j * foldMajorana n ((symmDiff t.toFinset Q).sort (· ≤ ·))) := by
              rw [Matrix.mul_smul]; rfl
        _ = c₁ • (c₂ • majoranaString n (symmDiff {j} (symmDiff t.toFinset Q))) := by rw [hc₂]
        _ = (c₁ * c₂) • majoranaString n (symmDiff {j} (symmDiff t.toFinset Q)) := by rw [smul_smul]
  have hP := hlist (P.sort (· ≤ ·)) (Finset.sort_nodup _ _) Q
  have hPto : (P.sort (· ≤ ·)).toFinset = P := by ext x; simp [Finset.mem_sort]
  rw [hPto] at hP
  exact hP

private lemma majoranaProbe_comm_fold_disjoint (n : ℕ) (j : Fin (2 * n))
    (l : List (Fin (2 * n))) (hj : j ∉ l) :
    majoranaProbe n j * foldMajorana n l =
      ((-1 : ℂ) ^ l.length) • (foldMajorana n l * majoranaProbe n j) := by
  induction l with
  | nil => simp [foldMajorana]
  | cons a t ih =>
    have hne : j ≠ a := fun h ↦ hj (h ▸ List.mem_cons_self)
    have hjt : j ∉ t := fun h ↦ hj (List.mem_cons_of_mem a h)
    calc majoranaProbe n j * foldMajorana n (a :: t)
        = (majoranaProbe n j * majoranaProbe n a) * foldMajorana n t := by
            simp only [foldMajorana, List.foldr_cons, Matrix.mul_assoc]
      _ = -(majoranaProbe n a * majoranaProbe n j) * foldMajorana n t := by
            rw [majoranaProbe_anticomm (Ne.symm hne)]
      _ = -(majoranaProbe n a * (majoranaProbe n j * foldMajorana n t)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(majoranaProbe n a * (((-1 : ℂ) ^ t.length) • (foldMajorana n t * majoranaProbe n j))) := by
            rw [ih hjt]
      _ = ((-1 : ℂ) ^ (a :: t).length) • (foldMajorana n (a :: t) * majoranaProbe n j) := by
            simp only [foldMajorana, List.foldr_cons, List.length_cons, pow_succ',
              Matrix.mul_smul, ← smul_smul, neg_one_smul, Matrix.mul_assoc]

/-- **Disjoint Majorana Strings Graded Commutation**:
If `Disjoint P Q`, then `M_P M_Q = (-1)^{|P| |Q|} M_Q M_P`. -/
theorem majoranaString_disjoint_comm (n : ℕ) {P Q : Finset (Fin (2 * n))} (hdisj : Disjoint P Q) :
    majoranaString n P * majoranaString n Q =
      ((-1 : ℂ) ^ (P.card * Q.card)) • (majoranaString n Q * majoranaString n P) := by
  have hlist : ∀ l : List (Fin (2 * n)), (∀ j ∈ l, j ∉ Q.sort (· ≤ ·)) →
      foldMajorana n l * majoranaString n Q =
        ((-1 : ℂ) ^ (l.length * Q.card)) • (majoranaString n Q * foldMajorana n l) := by
    intro l
    induction l with
    | nil => intro _; simp [foldMajorana]
    | cons a t ih =>
      intro hmem
      have ha : a ∉ Q.sort (· ≤ ·) := hmem a List.mem_cons_self
      have ht : ∀ j ∈ t, j ∉ Q.sort (· ≤ ·) := fun j hj ↦ hmem j (List.mem_cons_of_mem a hj)
      have hlenQ : (Q.sort (· ≤ ·)).length = Q.card := Finset.length_sort _
      calc foldMajorana n (a :: t) * majoranaString n Q
          = majoranaProbe n a * (foldMajorana n t * majoranaString n Q) := by
              simp only [foldMajorana, List.foldr_cons, Matrix.mul_assoc]
        _ = majoranaProbe n a * (((-1 : ℂ) ^ (t.length * Q.card)) •
              (majoranaString n Q * foldMajorana n t)) := by rw [ih ht]
        _ = ((-1 : ℂ) ^ (t.length * Q.card)) •
              ((majoranaProbe n a * majoranaString n Q) * foldMajorana n t) := by
              rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = ((-1 : ℂ) ^ (t.length * Q.card)) •
              ((((-1 : ℂ) ^ (Q.sort (· ≤ ·)).length) • (majoranaString n Q * majoranaProbe n a)) *
                foldMajorana n t) := by
              rw [foldMajorana_eq_of_sorted, majoranaProbe_comm_fold_disjoint n a _ ha]
        _ = ((-1 : ℂ) ^ ((a :: t).length * Q.card)) •
              (majoranaString n Q * foldMajorana n (a :: t)) := by
              rw [hlenQ, Matrix.smul_mul, smul_smul, ← pow_add, Matrix.mul_assoc]
              simp only [foldMajorana, List.foldr_cons, List.length_cons]
              congr 2; ring
  have hmem : ∀ j ∈ P.sort (· ≤ ·), j ∉ Q.sort (· ≤ ·) := by
    intro j hjP hjQ
    rw [Finset.mem_sort] at hjP hjQ
    exact Finset.disjoint_left.mp hdisj hjP hjQ
  have hres := hlist (P.sort (· ≤ ·)) hmem
  rwa [Finset.length_sort] at hres

/-- Even-parity disjoint Majorana strings commute (`[M_P, M_Q] = 0`). -/
theorem majoranaString_even_disjoint_comm (n : ℕ) {P Q : Finset (Fin (2 * n))}
    (hPeven : Even P.card) (hdisj : Disjoint P Q) :
    matComm (majoranaString n P) (majoranaString n Q) = 0 := by
  unfold matComm
  rw [majoranaString_disjoint_comm n hdisj]
  rcases hPeven with ⟨k, hk⟩
  have hev : Even (P.card * Q.card) := ⟨k * Q.card, by rw [hk]; ring⟩
  rw [hev.neg_one_pow, one_smul, sub_self]

end MajoranaStringAlgebra

section Item1MajoranaLocalInteractionDecomp

/-- Majorana operators supported on a subset `U ⊆ {0, …, 2n-1}` of Majorana modes. -/
def majoranaSupportedSubmodule (n : ℕ) (U : Finset (Fin (2 * n))) : Submodule ℂ (QubitOp n) :=
  Submodule.span ℂ { M : QubitOp n | ∃ Q : Finset (Fin (2 * n)), Q ⊆ U ∧ M = majoranaString n Q }

/-- Even-parity Majorana operators supported on `U ⊆ {0, …, 2n-1}`. -/
def majoranaEvenSupportedSubmodule (n : ℕ) (U : Finset (Fin (2 * n))) : Submodule ℂ (QubitOp n) :=
  Submodule.span ℂ { M : QubitOp n | ∃ Q : Finset (Fin (2 * n)), Q ⊆ U ∧ Even Q.card ∧ M = majoranaString n Q }

lemma majoranaSupported_comm_zero {n : ℕ} {U V : Finset (Fin (2 * n))} (hdisj : Disjoint U V)
    {A B : QubitOp n} (hA : A ∈ majoranaEvenSupportedSubmodule n U)
    (hB : B ∈ majoranaSupportedSubmodule n V) :
    A * B - B * A = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨P, hPU, hPeven, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨Q, hQV, rfl⟩
      exact majoranaString_even_disjoint_comm n hPeven (Disjoint.mono hPU hQV hdisj)
    · simp
    · intro X Y _ _ hX hY
      calc majoranaString n P * (X + Y) - (X + Y) * majoranaString n P
          = (majoranaString n P * X - X * majoranaString n P) +
            (majoranaString n P * Y - Y * majoranaString n P) := by
              simp only [Matrix.mul_add, Matrix.add_mul]; abel
        _ = 0 := by rw [hX, hY, add_zero]
    · intro c X _ hX
      calc majoranaString n P * (c • X) - (c • X) * majoranaString n P
          = c • (majoranaString n P * X - X * majoranaString n P) := by
              simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        _ = 0 := by rw [hX, smul_zero]
  · simp
  · intro X Y _ _ hX hY
    calc (X + Y) * B - B * (X + Y)
        = (X * B - B * X) + (Y * B - B * Y) := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
      _ = 0 := by rw [hX, hY, add_zero]
  · intro c X _ hX
    calc (c • X) * B - B * (c • X)
        = c • (X * B - B * X) := by simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      _ = 0 := by rw [hX, smul_zero]

lemma majoranaSupported_comm_union {n : ℕ} {U V : Finset (Fin (2 * n))}
    {A B : QubitOp n} (hA : A ∈ majoranaEvenSupportedSubmodule n U)
    (hB : B ∈ majoranaSupportedSubmodule n V) :
    A * B - B * A ∈ majoranaSupportedSubmodule n (U ∪ V) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨P, hPU, _, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨Q, hQV, rfl⟩
      rcases majoranaString_mul_exists n P Q with ⟨c₁, h1⟩
      rcases majoranaString_mul_exists n Q P with ⟨c₂, h2⟩
      have hsub : symmDiff P Q ⊆ U ∪ V := by
        intro x hx
        rcases Finset.mem_symmDiff.mp hx with ⟨hP, _⟩ | ⟨hQ, _⟩
        · exact Finset.mem_union_left V (hPU hP)
        · exact Finset.mem_union_right U (hQV hQ)
      rw [h1, h2, symmDiff_comm Q P]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ c₁ (Submodule.subset_span ⟨symmDiff P Q, hsub, rfl⟩))
        (Submodule.smul_mem _ c₂ (Submodule.subset_span ⟨symmDiff P Q, hsub, rfl⟩))
    · simp [Submodule.zero_mem]
    · intro X Y _ _ hX hY
      have heq : majoranaString n P * (X + Y) - (X + Y) * majoranaString n P =
          (majoranaString n P * X - X * majoranaString n P) +
          (majoranaString n P * Y - Y * majoranaString n P) := by
        simp only [Matrix.mul_add, Matrix.add_mul]; abel
      rw [heq]; exact Submodule.add_mem _ hX hY
    · intro c X _ hX
      have heq : majoranaString n P * (c • X) - (c • X) * majoranaString n P =
          c • (majoranaString n P * X - X * majoranaString n P) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rw [heq]; exact Submodule.smul_mem _ c hX
  · simp [Submodule.zero_mem]
  · intro X Y _ _ hX hY
    have heq : (X + Y) * B - B * (X + Y) = (X * B - B * X) + (Y * B - B * Y) := by
      simp only [Matrix.add_mul, Matrix.mul_add]; abel
    rw [heq]; exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    have heq : (c • X) * B - B * (c • X) = c • (X * B - B * X) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [heq]; exact Submodule.smul_mem _ c hX

private lemma qubitOpToCLM_mul' {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A * B) = qubitOpToCLM A * qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  change ∑ x, (A * B) i x * v.ofLp x = ∑ x, A i x * ∑ y, B x y * v.ofLp y
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma qubitOpToCLM_sub' {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A - B) = qubitOpToCLM A - qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  change ∑ x, (A i x - B i x) * v.ofLp x = (∑ x, A i x * v.ofLp x) - ∑ x, B i x * v.ofLp x
  simp_rw [sub_mul, Finset.sum_sub_distrib]

private lemma qubitOpToCLM_zero' (N : ℕ) :
    qubitOpToCLM (0 : QubitOp N) = 0 := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM]

/-- **Item #1 (Concrete Even-Parity Majorana `LocalInteractionDecomp` on `2n` Modes)**:
Instantiates `LocalInteractionDecomp (QubitOpCLM n) (2 * n) r` for ANY finite family of
even-parity `r`-local Majorana interaction terms `term : ι → QubitOp n` supported on
`supp : ι → Finset (Fin (2 * n))` (`|supp i| ≤ r`), so `CausalNormBounds.lemma_2_1_single_site_exp_bound`
(Eq. 2.4) and `CausalNormBounds.lemma_2_1_r_local_exp_bound` (Eq. 2.5) apply directly to Majoranas! -/
noncomputable def majoranaLocalInteractionDecomp {n r : ℕ} {ι : Type*} [Fintype ι]
    (term : ι → QubitOp n) (supp : ι → Finset (Fin (2 * n)))
    (hcard : ∀ i, (supp i).card ≤ r)
    (hsupp : ∀ i, term i ∈ majoranaEvenSupportedSubmodule n (supp i)) :
    LocalInteractionDecomp (QubitOpCLM n) (2 * n) r where
  ι := ι
  term := fun i ↦ qubitOpToCLM (term i)
  supp := supp
  supp_card_le := hcard
  SupportedOn := fun U T ↦ ∃ A : QubitOp n, A ∈ majoranaSupportedSubmodule n U ∧ T = qubitOpToCLM A
  supportedOn_comm_zero := by
    rintro U i _ ⟨A, hA, rfl⟩ hdisj
    rw [← qubitOpToCLM_mul', ← qubitOpToCLM_mul', ← qubitOpToCLM_sub',
      majoranaSupported_comm_zero hdisj (hsupp i) hA, qubitOpToCLM_zero']
  supportedOn_comm_union := by
    rintro U i _ ⟨A, hA, rfl⟩
    refine ⟨term i * A - A * term i, by rw [Finset.union_comm]; exact majoranaSupported_comm_union (hsupp i) hA, ?_⟩
    rw [← qubitOpToCLM_mul', ← qubitOpToCLM_mul', ← qubitOpToCLM_sub']

end Item1MajoranaLocalInteractionDecomp

section Item9MajoranaFiltrationProp41Lemma42Thm11b

/-- Even-parity Majorana filtration subspace `𝒱_r^{Maj, even} = span { M_P | |P| ≤ r, Even |P| }`. -/
def majoranaEvenFiltrationSubmodule (n r : ℕ) : Submodule ℂ (QubitOp n) :=
  Submodule.span ℂ { M : QubitOp n | ∃ P : Finset (Fin (2 * n)),
    P.card ≤ r ∧ Even P.card ∧ M = majoranaString n P }

/-- **Item #9 (Majorana Locality Step `[H, A] ∈ 𝒱_{s + r - 1}^{Maj}`)**:
For ANY even-parity `r`-local Majorana Hamiltonian `H ∈ majoranaEvenFiltrationSubmodule n r` (`1 ≤ r`)
and ANY `A ∈ majoranaFiltrationSubmodule n s`:
`matComm H A ∈ majoranaFiltrationSubmodule n (s + r - 1)`. -/
theorem majorana_comm_mem_filtration {n r s : ℕ} (hr : 1 ≤ r)
    {H A : QubitOp n}
    (hH : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hA : A ∈ majoranaFiltrationSubmodule n s) :
    matComm H A ∈ majoranaFiltrationSubmodule n (s + r - 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hH
  · rintro _ ⟨P, hPcard, hPeven, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
    · rintro _ ⟨Q, hQcard, rfl⟩
      by_cases hdisj : Disjoint P Q
      · rw [majoranaString_even_disjoint_comm n hPeven hdisj]
        exact Submodule.zero_mem _
      · have hinter : 1 ≤ (P ∩ Q).card := by
          rw [Finset.not_disjoint_iff] at hdisj
          rcases hdisj with ⟨x, hxP, hxQ⟩
          exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxP, hxQ⟩⟩
        have hsym_card : (symmDiff P Q).card ≤ s + r - 1 := by
          have h1 : (symmDiff P Q).card + 2 * (P ∩ Q).card = P.card + Q.card := by
            have hsd : symmDiff P Q = (P \ Q) ∪ (Q \ P) := rfl
            have hd : Disjoint (P \ Q) (Q \ P) :=
              Finset.disjoint_left.mpr fun x h1 h2 ↦ (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
            rw [hsd, Finset.card_union_of_disjoint hd]
            have hP := Finset.card_sdiff_add_card_inter P Q
            have hQ := Finset.card_sdiff_add_card_inter Q P
            rw [Finset.inter_comm] at hQ
            omega
          omega
        rcases majoranaString_mul_exists n P Q with ⟨c₁, h1⟩
        rcases majoranaString_mul_exists n Q P with ⟨c₂, h2⟩
        unfold matComm
        rw [h1, h2, symmDiff_comm Q P]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ c₁ (Submodule.subset_span ⟨symmDiff P Q, hsym_card, rfl⟩))
          (Submodule.smul_mem _ c₂ (Submodule.subset_span ⟨symmDiff P Q, hsym_card, rfl⟩))
    · unfold matComm; simp [Submodule.zero_mem]
    · intro X Y _ _ hX hY
      have heq : matComm (majoranaString n P) (X + Y) =
          matComm (majoranaString n P) X + matComm (majoranaString n P) Y := by
        unfold matComm; simp only [Matrix.mul_add, Matrix.add_mul]; abel
      rw [heq]; exact Submodule.add_mem _ hX hY
    · intro c X _ hX
      have heq : matComm (majoranaString n P) (c • X) = c • matComm (majoranaString n P) X := by
        unfold matComm; simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rw [heq]; exact Submodule.smul_mem _ c hX
  · unfold matComm; simp [Submodule.zero_mem]
  · intro X Y _ _ hX hY
    have heq : matComm (X + Y) A = matComm X A + matComm Y A := by
      unfold matComm; simp only [Matrix.add_mul, Matrix.mul_add]; abel
    rw [heq]; exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    have heq : matComm (c • X) A = c • matComm X A := by
      unfold matComm; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [heq]; exact Submodule.smul_mem _ c hX

lemma majoranaFiltrationSubmodule_mono {n s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    majoranaFiltrationSubmodule n s₁ ≤ majoranaFiltrationSubmodule n s₂ :=
  Submodule.span_mono fun _ ⟨Q, hQ, hEq⟩ ↦ ⟨Q, le_trans hQ h, hEq⟩

/-- **Majorana Lanczos Filtration Containment (`O_k^{(β)} ∈ 𝒱_{s₀ + k(r-1)}^{Maj}`)**:
Every Wightman Lanczos basis operator `lanczosOp G H O k` lies in
`majoranaFiltrationSubmodule n (s₀ + k * (r - 1))`. -/
theorem majorana_lanczosOp_mem_filtration {n r s₀ : ℕ} (hr : 1 ≤ r)
    (G : GibbsData n) {H O : QubitOp n}
    (hH : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hO : O ∈ majoranaFiltrationSubmodule n s₀) :
    ∀ k : ℕ, lanczosOp G H O k ∈ majoranaFiltrationSubmodule n (s₀ + k * (r - 1)) ∧
      (lanczosState G H O k).2.1 ∈ majoranaFiltrationSubmodule n (s₀ + k * (r - 1)) := by
  intro k
  induction k with
  | zero =>
    simp only [zero_mul, add_zero, lanczosOp, lanczosState]
    constructor
    · split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ hO
    · exact Submodule.zero_mem _
  | succ k ih =>
    rcases ih with ⟨hOk, hOprev⟩
    have hcomm : matComm H (lanczosOp G H O k) ∈ majoranaFiltrationSubmodule n (s₀ + (k + 1) * (r - 1)) := by
      have h1 := majorana_comm_mem_filtration hr hH hOk
      have heq : s₀ + k * (r - 1) + r - 1 = s₀ + (k + 1) * (r - 1) := by
        have : (k + 1) * (r - 1) = k * (r - 1) + (r - 1) := by ring
        omega
      rwa [heq] at h1
    have hprev_mono : (lanczosState G H O k).2.1 ∈ majoranaFiltrationSubmodule n (s₀ + (k + 1) * (r - 1)) :=
      majoranaFiltrationSubmodule_mono (by nlinarith) hOprev
    have hOk_mono : lanczosOp G H O k ∈ majoranaFiltrationSubmodule n (s₀ + (k + 1) * (r - 1)) :=
      majoranaFiltrationSubmodule_mono (by nlinarith) hOk
    have hAnext : matComm H (lanczosOp G H O k) -
        ((lanczosCoeff G H O k : ℝ) : ℂ) • (lanczosState G H O k).2.1 ∈
        majoranaFiltrationSubmodule n (s₀ + (k + 1) * (r - 1)) :=
      Submodule.sub_mem _ hcomm (Submodule.smul_mem _ _ hprev_mono)
    constructor
    · unfold lanczosOp
      simp only [lanczosState]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ hAnext
    · exact hOk_mono

/-- Majorana Krylov truncation `lanczosTrunc hH β O M t` lies in `𝒱_{s₀ + (M - 1)(r - 1)}^{Maj}`. -/
theorem majorana_lanczosTrunc_mem_filtration {n r s₀ M : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp n} (hH : H.IsHermitian) (β : ℝ) (t : ℝ)
    (hHf : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : O ∈ majoranaFiltrationSubmodule n s₀) :
    lanczosTrunc hH β O M t ∈ majoranaFiltrationSubmodule n (s₀ + (M - 1) * (r - 1)) := by
  unfold lanczosTrunc
  refine Submodule.sum_mem _ fun k hk ↦ ?_
  have hk_le : k ≤ M - 1 := by have := Finset.mem_range.mp hk; omega
  have hmem := (majorana_lanczosOp_mem_filtration hr (concreteGibbsData hH β) hHf hOf k).1
  have hmono := majoranaFiltrationSubmodule_mono (s₁ := s₀ + k * (r - 1))
    (s₂ := s₀ + (M - 1) * (r - 1)) (by nlinarith) hmem
  exact Submodule.smul_mem _ _ hmono

/-- Majorana Wightman orthogonal projector `Π_s^{(β),Maj}` onto `majoranaFiltrationSubmodule n s`. -/
noncomputable def majoranaWightmanProj {n : ℕ} (G : GibbsData n) (s : ℕ) :
    QubitOp n →ₗ[ℂ] QubitOp n :=
  wightmanSubspaceProj G (majoranaFiltrationSubmodule n s)

/-- Majorana Wightman filtration superoperator `𝒬^{(β),Maj} = ∑_{s=0}^{2n-1} (1 - Π_s^{(β),Maj})`. -/
noncomputable def majoranaWightmanQ {n : ℕ} (G : GibbsData n) : QubitOp n →ₗ[ℂ] QubitOp n :=
  ∑ s ∈ Finset.range (2 * n), (LinearMap.id - majoranaWightmanProj G s)

/-- Majorana static thermal-size supremum `Λ_β^{MSS,Maj}(s)`. -/
noncomputable def majoranaLambdaMSS {n : ℕ} (G : GibbsData n) (s : ℕ) : ℝ :=
  sSup { x : ℝ | ∃ A : QubitOp n, A ∈ majoranaFiltrationSubmodule n s ∧
    gibbsWightmanNormSq G A = 1 ∧ x = majoranaThermalSize G A }

/-- **Item #9 — Concrete Majorana Proposition 4.1(1) (Static Filtration Bound)**:
For ANY `A ∈ majoranaFiltrationSubmodule n s`, `Re (A | 𝒬^{(β),Maj} A)_β^W ≤ s * ‖A‖_{β,W}²`. -/
theorem prop_4_1_part1_majorana {n s : ℕ} (G : GibbsData n) {A : QubitOp n}
    (hA : A ∈ majoranaFiltrationSubmodule n s) :
    (gibbsWightmanInner G A (majoranaWightmanQ G A)).re ≤
      (s : ℝ) * gibbsWightmanNormSq G A := by
  unfold majoranaWightmanQ
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G A (∑ k ∈ Finset.range (2 * n), (A - majoranaWightmanProj G k A)) =
      ∑ k ∈ Finset.range (2 * n), gibbsWightmanInner G A (A - majoranaWightmanProj G k A) := by
    unfold gibbsWightmanInner wightmanInner; rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  have hterm : ∀ k ∈ Finset.range (2 * n),
      (gibbsWightmanInner G A (A - majoranaWightmanProj G k A)).re ≤
        if k < s then gibbsWightmanNormSq G A else 0 := by
    intro k _
    have hdist : (gibbsWightmanInner G A (A - majoranaWightmanProj G k A)).re =
        wightmanDistSq G (majoranaFiltrationSubmodule n k) A :=
      wightmanSubspaceProj_eq_distSq G (majoranaFiltrationSubmodule n k) A
    rw [hdist]
    by_cases hks : k < s
    · simp only [hks, ↓reduceIte]
      exact wightmanDistSq_le_normSq G (majoranaFiltrationSubmodule n k) A
    · simp only [hks, ↓reduceIte]
      have hAk : A ∈ majoranaFiltrationSubmodule n k :=
        majoranaFiltrationSubmodule_mono (by omega) hA
      rw [wightmanDistSq_eq_zero_of_mem G (majoranaFiltrationSubmodule n k) hAk]
  calc ∑ k ∈ Finset.range (2 * n), (gibbsWightmanInner G A (A - majoranaWightmanProj G k A)).re
      ≤ ∑ k ∈ Finset.range (2 * n), (if k < s then gibbsWightmanNormSq G A else 0) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.range (2 * n)).filter (· < s)).card * gibbsWightmanNormSq G A := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s : ℝ) * gibbsWightmanNormSq G A := by
        apply mul_le_mul_of_nonneg_right _ (gibbsWightmanNormSq_nonneg G A)
        have hsub : (Finset.range (2 * n)).filter (· < s) ⊆ Finset.range s := fun k hk ↦
          Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
        have hle : ((Finset.range (2 * n)).filter (· < s)).card ≤ s := by
          simpa using Finset.card_le_card hsub
        exact_mod_cast hle

/-- **Item #9 — Concrete Majorana Lemma 4.2 (Eq. 4.3 on `majoranaThermalSize` & `majoranaLambdaMSS`)**:
For ANY Hermitian even-parity `H ∈ majoranaEvenFiltrationSubmodule n r` (`1 ≤ r`),
Hermitian `O ∈ majoranaFiltrationSubmodule n s₀` with `‖O‖_{β,W}² = 1`, `M ≥ 1`, and `t : ℝ`:
`majoranaThermalSize G (heisenbergEvol hH t O) ≤ majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) + 4 n ε_M(t) + 2 n ε_M(t)²`
(where `2 n` is the total number of Majorana modes, bounding `majoranaTotalSizeOp ≤ 2 n`). -/
theorem lemma_4_2_majorana_concrete {n r s₀ M : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp n} (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) (t : ℝ)
    (hHf : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : O ∈ majoranaFiltrationSubmodule n s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    let G := concreteGibbsData hH β
    let A_M := lanczosTrunc hH β O M t
    let ε_M := Real.sqrt (gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - A_M))
    majoranaThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
      majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) +
      2 * ((2 * n : ℕ) : ℝ) * ε_M + ((2 * n : ℕ) : ℝ) * ε_M ^ 2 := by
  intro G A_M ε_M
  set U := heisenbergEvol hH (t : ℂ) O
  set R_M := U - A_M
  have hAM_mem : A_M ∈ majoranaFiltrationSubmodule n (s₀ + (M - 1) * (r - 1)) :=
    majorana_lanczosTrunc_mem_filtration hr hM hH β t hHf hOf
  have h1_mem : (1 : QubitOp n) ∈ majoranaFiltrationSubmodule n (s₀ + (M - 1) * (r - 1)) := by
    have h1 : (1 : QubitOp n) = majoranaString n ∅ := by unfold majoranaString; simp
    rw [h1]
    exact Submodule.subset_span ⟨∅, by simp, rfl⟩
  have hPsq : fermionParityOp n * fermionParityOp n = 1 := fermionParityOp_sq n
  have hPherm : (fermionParityOp n)ᴴ = fermionParityOp n := fermionParityOp_herm n
  have heven_par : ∀ X : QubitOp n, isEvenParity (evenPart n X) := by
    intro X; unfold isEvenParity evenPart
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    have h1 : fermionParityOp n * (fermionParityOp n * (X * (fermionParityOp n * fermionParityOp n))) = X := by
      rw [hPsq, Matrix.mul_one, ← Matrix.mul_assoc, hPsq, Matrix.one_mul]
    rw [h1, add_comm]
  have hodd_par : ∀ X : QubitOp n, isOddParity (oddPart n X) := by
    intro X; unfold isOddParity oddPart
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    have h1 : fermionParityOp n * (fermionParityOp n * (X * (fermionParityOp n * fermionParityOp n))) = X := by
      rw [hPsq, Matrix.mul_one, ← Matrix.mul_assoc, hPsq, Matrix.one_mul]
    rw [h1, ← smul_neg, neg_sub]
  have hsplit : ∀ X : QubitOp n, X = evenPart n X + oddPart n X := by
    intro X; unfold evenPart oddPart
    rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ X, smul_smul]; norm_num
  have horth_eo : ∀ X Y : QubitOp n, isEvenParity X → isOddParity Y → hsInner X Y = 0 := by
    intro X Y hXe hYo
    unfold hsInner
    have htr : (Xᴴ * Y).trace = - (Xᴴ * Y).trace := by
      have hXh : fermionParityOp n * Xᴴ * fermionParityOp n = Xᴴ := by
        have := congrArg Matrix.conjTranspose hXe
        simpa [Matrix.conjTranspose_mul, hPherm, Matrix.mul_assoc] using this
      calc (Xᴴ * Y).trace
          = ((fermionParityOp n * Xᴴ * fermionParityOp n) * Y).trace := by rw [hXh]
        _ = (fermionParityOp n * (Xᴴ * (fermionParityOp n * Y))).trace := by simp only [Matrix.mul_assoc]
        _ = ((Xᴴ * (fermionParityOp n * Y)) * fermionParityOp n).trace := Matrix.trace_mul_comm _ _
        _ = (Xᴴ * (fermionParityOp n * Y * fermionParityOp n)).trace := by simp only [Matrix.mul_assoc]
        _ = (Xᴴ * (-Y)).trace := by rw [hYo]
        _ = -(Xᴴ * Y).trace := by rw [Matrix.mul_neg, Matrix.trace_neg]
    have h2 : (2 : ℂ) * (Xᴴ * Y).trace = 0 := by linear_combination htr
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have heven_add : ∀ X Y : QubitOp n, evenPart n (X + Y) = evenPart n X + evenPart n Y := by
    intro X Y; unfold evenPart; simp only [Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  have hodd_add : ∀ X Y : QubitOp n, oddPart n (X + Y) = oddPart n X + oddPart n Y := by
    intro X Y; unfold oddPart; simp only [Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub]; abel
  have htot_add : ∀ X Y : QubitOp n, majoranaTotalSizeOp n (X + Y) = majoranaTotalSizeOp n X + majoranaTotalSizeOp n Y := by
    intro X Y; unfold majoranaTotalSizeOp majoranaModeSizeOp
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub]; abel
  have hoddtot_add : ∀ X Y : QubitOp n, majoranaOddTotalSizeOp n (X + Y) = majoranaOddTotalSizeOp n X + majoranaOddTotalSizeOp n Y := by
    intro X Y; unfold majoranaOddTotalSizeOp majoranaOddModeSizeOp
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  have hpar_add : ∀ X Y : QubitOp n,
      majoranaParitySizeOp n (X + Y) = majoranaParitySizeOp n X + majoranaParitySizeOp n Y := by
    intro X Y; unfold majoranaParitySizeOp
    rw [heven_add, hodd_add, htot_add, hoddtot_add]; abel
  have heven_smul : ∀ (c : ℂ) (X : QubitOp n), evenPart n (c • X) = c • evenPart n X := by
    intro c X; unfold evenPart; simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_comm c]
  have hodd_smul : ∀ (c : ℂ) (X : QubitOp n), oddPart n (c • X) = c • oddPart n X := by
    intro c X; unfold oddPart; simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_comm c]
  have htot_smul : ∀ (c : ℂ) (X : QubitOp n), majoranaTotalSizeOp n (c • X) = c • majoranaTotalSizeOp n X := by
    intro c X; unfold majoranaTotalSizeOp majoranaModeSizeOp
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_comm c]
  have hoddtot_smul : ∀ (c : ℂ) (X : QubitOp n), majoranaOddTotalSizeOp n (c • X) = c • majoranaOddTotalSizeOp n X := by
    intro c X; unfold majoranaOddTotalSizeOp majoranaOddModeSizeOp
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_comm c]
  have hpar_smul : ∀ (c : ℂ) (X : QubitOp n),
      majoranaParitySizeOp n (c • X) = c • majoranaParitySizeOp n X := by
    intro c X; unfold majoranaParitySizeOp
    rw [heven_smul, hodd_smul, htot_smul, hoddtot_smul, smul_add]
  have hpar_even_pres : ∀ X : QubitOp n, isEvenParity (majoranaTotalSizeOp n (evenPart n X)) := by
    intro X
    unfold isEvenParity majoranaTotalSizeOp majoranaModeSizeOp
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    have hPjm : fermionParityOp n * majoranaProbe n j = -(majoranaProbe n j * fermionParityOp n) :=
      fermionParityOp_anticomm_probe n j
    have hPjr : majoranaProbe n j * fermionParityOp n = -(fermionParityOp n * majoranaProbe n j) := by
      rw [hPjm, neg_neg]
    set E := evenPart n X
    have hPe : fermionParityOp n * E * fermionParityOp n = E := heven_par X
    have h2 : fermionParityOp n * (majoranaProbe n j * E * majoranaProbe n j) * fermionParityOp n =
        majoranaProbe n j * E * majoranaProbe n j := by
      calc fermionParityOp n * (majoranaProbe n j * E * majoranaProbe n j) * fermionParityOp n
          = (fermionParityOp n * majoranaProbe n j) * E * (majoranaProbe n j * fermionParityOp n) := by
              simp only [Matrix.mul_assoc]
        _ = (-(majoranaProbe n j * fermionParityOp n)) * E * (majoranaProbe n j * fermionParityOp n) := by
              rw [hPjm]
        _ = (-(majoranaProbe n j * fermionParityOp n)) * E * (-(fermionParityOp n * majoranaProbe n j)) := by
              congr 1; exact hPjr
        _ = majoranaProbe n j * (fermionParityOp n * E * fermionParityOp n) * majoranaProbe n j := by
              simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
        _ = majoranaProbe n j * E * majoranaProbe n j := by rw [hPe]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hPe, h2]
  have hpar_odd_pres : ∀ X : QubitOp n, isOddParity (majoranaOddTotalSizeOp n (oddPart n X)) := by
    intro X
    unfold isOddParity majoranaOddTotalSizeOp majoranaOddModeSizeOp
    simp only [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _
    have hPjm : fermionParityOp n * majoranaProbe n j = -(majoranaProbe n j * fermionParityOp n) :=
      fermionParityOp_anticomm_probe n j
    have hPjr : majoranaProbe n j * fermionParityOp n = -(fermionParityOp n * majoranaProbe n j) := by
      rw [hPjm, neg_neg]
    have hPo := hodd_par X
    unfold isOddParity at hPo
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← smul_neg]
    congr 1
    rw [hPo]
    have h2 : fermionParityOp n * (majoranaProbe n j * oddPart n X * majoranaProbe n j) * fermionParityOp n =
        -(majoranaProbe n j * oddPart n X * majoranaProbe n j) := by
      calc fermionParityOp n * (majoranaProbe n j * oddPart n X * majoranaProbe n j) * fermionParityOp n
          = (fermionParityOp n * majoranaProbe n j) * oddPart n X * (majoranaProbe n j * fermionParityOp n) := by
              simp only [Matrix.mul_assoc]
        _ = (-(majoranaProbe n j * fermionParityOp n)) * oddPart n X * (majoranaProbe n j * fermionParityOp n) := by
              rw [hPjm]
        _ = (-(majoranaProbe n j * fermionParityOp n)) * oddPart n X * (-(fermionParityOp n * majoranaProbe n j)) := by
              congr 1; exact hPjr
        _ = majoranaProbe n j * (fermionParityOp n * oddPart n X * fermionParityOp n) * majoranaProbe n j := by
              simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
        _ = -(majoranaProbe n j * oddPart n X * majoranaProbe n j) := by
              rw [hPo, Matrix.mul_neg, Matrix.neg_mul]
    rw [h2]; abel
  have hmaj_bounds : ∀ X : QubitOp n,
      0 ≤ (hsInner X (majoranaParitySizeOp n X)).re ∧
      (hsInner X (majoranaParitySizeOp n X)).re ≤ ((2 * n : ℕ) : ℝ) * hsNormSq X := by
    intro X
    have hnorm_split : hsNormSq X = hsNormSq (evenPart n X) + hsNormSq (oddPart n X) := by
      conv_lhs => rw [hsplit X]
      unfold hsNormSq hsInner
      simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      have h1 : ((evenPart n X)ᴴ * oddPart n X).trace = 0 := horth_eo _ _ (heven_par X) (hodd_par X)
      have h2 : ((oddPart n X)ᴴ * evenPart n X).trace = 0 := by
        have hc : ((oddPart n X)ᴴ * evenPart n X).trace = starRingEnd ℂ (((evenPart n X)ᴴ * oddPart n X).trace) := by
          rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        rw [hc, h1, map_zero]
      rw [h1, h2]; simp
    have hinner_split : (hsInner X (majoranaParitySizeOp n X)).re =
        (hsInner (evenPart n X) (majoranaParitySizeOp n (evenPart n X))).re +
        (hsInner (oddPart n X) (majoranaParitySizeOp n (oddPart n X))).re := by
      have he_eq : majoranaParitySizeOp n (evenPart n X) = majoranaTotalSizeOp n (evenPart n X) := by
        unfold majoranaParitySizeOp
        have ⟨he, ho⟩ := evenPart_of_even (heven_par X)
        rw [he, ho]; unfold majoranaOddTotalSizeOp majoranaOddModeSizeOp; simp
      have ho_eq : majoranaParitySizeOp n (oddPart n X) = majoranaOddTotalSizeOp n (oddPart n X) := by
        unfold majoranaParitySizeOp
        have ⟨he, ho⟩ := oddPart_of_odd (hodd_par X)
        rw [he, ho]; unfold majoranaTotalSizeOp majoranaModeSizeOp; simp
      rw [he_eq, ho_eq]
      conv_lhs => arg 1; arg 1; rw [hsplit X]
      unfold majoranaParitySizeOp hsInner
      simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      have h1 : ((evenPart n X)ᴴ * majoranaOddTotalSizeOp n (oddPart n X)).trace = 0 :=
        horth_eo _ _ (heven_par X) (hpar_odd_pres X)
      have h2 : ((oddPart n X)ᴴ * majoranaTotalSizeOp n (evenPart n X)).trace = 0 := by
        have hc : ((oddPart n X)ᴴ * majoranaTotalSizeOp n (evenPart n X)).trace =
            starRingEnd ℂ (((majoranaTotalSizeOp n (evenPart n X))ᴴ * oddPart n X).trace) := by
          rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        rw [hc, horth_eo _ _ (hpar_even_pres X) (hodd_par X), map_zero]
      rw [h1, h2]; simp
    have hb_e := majoranaParitySizeOp_bounds_of_parity (evenPart n X) (Or.inl (heven_par X))
    have hb_o := majoranaParitySizeOp_bounds_of_parity (oddPart n X) (Or.inr (hodd_par X))
    rw [hinner_split, hnorm_split]
    exact ⟨by linarith, by nlinarith⟩
  have hS_sa : ∀ P Q : QubitOp n,
      (hsInner P (majoranaParitySizeOp n Q)).re = (hsInner Q (majoranaParitySizeOp n P)).re := by
    intro P Q
    have hmode_sa : ∀ (V X Y : QubitOp n), Vᴴ = V →
        (Xᴴ * (V * Y * V)).trace.re = (Yᴴ * (V * X * V)).trace.re := by
      intro V X Y hVh
      have hc3 : starRingEnd ℂ (Xᴴ * (V * Y * V)).trace = (Yᴴ * (V * X * V)).trace := by
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hVh]
        calc (V * (Yᴴ * V) * X).trace
            = (V * (Yᴴ * (V * X))).trace := by simp only [Matrix.mul_assoc]
          _ = ((Yᴴ * (V * X)) * V).trace := Matrix.trace_mul_comm _ _
          _ = (Yᴴ * (V * X * V)).trace := by simp only [Matrix.mul_assoc]
      rw [← hc3, Complex.conj_re]
    have htr_sa : ∀ (X Y : QubitOp n), (Xᴴ * Y).trace.re = (Yᴴ * X).trace.re := by
      intro X Y
      have hc : (Xᴴ * Y).trace = starRingEnd ℂ (Yᴴ * X).trace := by
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hc, Complex.conj_re]
    have hinner_split : ∀ X Y : QubitOp n,
        (hsInner X (majoranaParitySizeOp n Y)).re =
        (hsInner (evenPart n X) (majoranaTotalSizeOp n (evenPart n Y))).re +
        (hsInner (oddPart n X) (majoranaOddTotalSizeOp n (oddPart n Y))).re := by
      intro X Y
      conv_lhs => rw [hsplit X]
      unfold majoranaParitySizeOp hsInner
      simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      have h1 : ((evenPart n X)ᴴ * majoranaOddTotalSizeOp n (oddPart n Y)).trace = 0 :=
        horth_eo _ _ (heven_par X) (hpar_odd_pres Y)
      have h2 : ((oddPart n X)ᴴ * majoranaTotalSizeOp n (evenPart n Y)).trace = 0 := by
        have hc : ((oddPart n X)ᴴ * majoranaTotalSizeOp n (evenPart n Y)).trace =
            starRingEnd ℂ (((majoranaTotalSizeOp n (evenPart n Y))ᴴ * oddPart n X).trace) := by
          rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        rw [hc, horth_eo _ _ (hpar_even_pres Y) (hodd_par X), map_zero]
      rw [h1, h2]; simp
    rw [hinner_split P Q, hinner_split Q P]
    congr 1
    · unfold majoranaTotalSizeOp hsInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
          Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      unfold majoranaModeSizeOp
      have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
      simp only [h12, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
        smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
      rw [htr_sa (evenPart n P) (evenPart n Q), hmode_sa _ (evenPart n P) (evenPart n Q) (majoranaProbe_herm n j)]
    · unfold majoranaOddTotalSizeOp hsInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
          Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      unfold majoranaOddModeSizeOp
      have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
      simp only [h12, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
        smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
      rw [htr_sa (oddPart n P) (oddPart n Q), hmode_sa _ (oddPart n P) (oddPart n Q) (majoranaProbe_herm n j)]
  have hS_bdd : BddAbove { x : ℝ | ∃ A : QubitOp n,
      A ∈ majoranaFiltrationSubmodule n (s₀ + (M - 1) * (r - 1)) ∧
      gibbsWightmanNormSq G A = 1 ∧ x = majoranaThermalSize G A } := by
    refine ⟨((2 * n : ℕ) : ℝ), ?_⟩
    rintro x ⟨A, _, hAnorm, rfl⟩
    unfold majoranaThermalSize
    have hle := (hmaj_bounds (jBeta G.ρQuarter A)).2
    have hbg := (hmaj_bounds G.ρHalf).1
    have hhs : hsNormSq (jBeta G.ρQuarter A) = 1 := by
      unfold gibbsWightmanNormSq gibbsWightmanInner at hAnorm
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hAnorm
      exact hAnorm
    rw [hhs, mul_one] at hle; linarith
  have hlam_nn : 0 ≤ majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) := by
    have h1_size : majoranaThermalSize G (1 : QubitOp n) = 0 := by
      unfold majoranaThermalSize jBeta
      rw [Matrix.mul_one, G.sq_quarter, sub_self]
    have h1_norm : gibbsWightmanNormSq G (1 : QubitOp n) = 1 := by
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_one, G.sq_half, G.trace_one,
        Complex.one_re]
    exact le_csSup hS_bdd ⟨1, h1_mem, h1_norm, h1_size.symm⟩
  have hAM_norm_le : gibbsWightmanNormSq G A_M ≤ 1 :=
    lanczosTrunc_wightmanNormSq_le_one hH hO β t hOnorm M
  have hlead : majoranaThermalSize G A_M ≤ majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) := by
    by_cases h0 : gibbsWightmanNormSq G A_M = 0
    · have hA0 : jBeta G.ρQuarter A_M = 0 := by
        have hAM0 : A_M = 0 := eq_zero_of_gibbsWightmanNormSq_eq_zero G h0
        rw [hAM0]; unfold jBeta; simp
      unfold majoranaThermalSize
      rw [hA0]; simp only [hsInner, Matrix.conjTranspose_zero, Matrix.zero_mul,
        Matrix.trace_zero, Complex.zero_re]
      have hbg := (hmaj_bounds G.ρHalf).1; unfold hsInner at hbg; linarith
    · have hpos : 0 < gibbsWightmanNormSq G A_M :=
        lt_of_le_of_ne (gibbsWightmanNormSq_nonneg G A_M) (Ne.symm h0)
      set c : ℝ := (Real.sqrt (gibbsWightmanNormSq G A_M))⁻¹
      set B : QubitOp n := (c : ℂ) • A_M
      have hB_mem : B ∈ majoranaFiltrationSubmodule n (s₀ + (M - 1) * (r - 1)) :=
        Submodule.smul_mem _ _ hAM_mem
      have hB_norm : gibbsWightmanNormSq G B = 1 := by
        unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner B
        simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.trace_smul, smul_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
        change c * c * gibbsWightmanNormSq G A_M = 1
        dsimp only [c]
        rw [← inv_mul, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
      have hB_le : majoranaThermalSize G B ≤ majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) :=
        le_csSup hS_bdd ⟨B, hB_mem, hB_norm, rfl⟩
      have hAM_eq : (hsInner (jBeta G.ρQuarter A_M) (majoranaParitySizeOp n (jBeta G.ρQuarter A_M))).re =
          gibbsWightmanNormSq G A_M *
            (hsInner (jBeta G.ρQuarter B) (majoranaParitySizeOp n (jBeta G.ρQuarter B))).re := by
        have hjB : jBeta G.ρQuarter B = (c : ℂ) • jBeta G.ρQuarter A_M := by
          unfold jBeta B; simp [Matrix.mul_smul, Matrix.smul_mul]
        rw [hjB, hpar_smul]
        unfold hsInner
        simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.trace_smul, smul_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
        have hcc : gibbsWightmanNormSq G A_M * (c * c) = 1 := by
          dsimp only [c]; rw [← inv_mul, Real.mul_self_sqrt hpos.le, mul_inv_cancel₀ hpos.ne']
        nlinarith [hcc]
      unfold majoranaThermalSize at hB_le ⊢
      have hbg_nn := (hmaj_bounds G.ρHalf).1
      have hB_hs_nn := (hmaj_bounds (jBeta G.ρQuarter B)).1
      nlinarith
  have hU_eq : U = A_M + R_M := by dsimp only [R_M]; abel
  have hdiff : majoranaThermalSize G U - majoranaThermalSize G A_M ≤
      2 * ((2 * n : ℕ) : ℝ) * ε_M + ((2 * n : ℕ) : ℝ) * ε_M ^ 2 := by
    unfold majoranaThermalSize
    set X := jBeta G.ρQuarter A_M
    set Y := jBeta G.ρQuarter R_M
    have hXY : jBeta G.ρQuarter U = X + Y := by
      rw [hU_eq]; dsimp only [X, Y]; unfold jBeta; rw [Matrix.mul_add, Matrix.add_mul]
    have hexpand : (hsInner (X + Y) (majoranaParitySizeOp n (X + Y))).re -
        (hsInner X (majoranaParitySizeOp n X)).re =
        2 * (hsInner X (majoranaParitySizeOp n Y)).re +
        (hsInner Y (majoranaParitySizeOp n Y)).re := by
      rw [hpar_add]
      unfold hsInner
      simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.trace_add, Complex.add_re]
      have hsym := hS_sa X Y
      unfold hsInner at hsym
      linarith
    have hY_hs : hsNormSq Y = ε_M ^ 2 := by
      dsimp only [ε_M, Y, R_M]
      rw [Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)]
      exact congrArg Complex.re
        (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter)
    have hX_hs : hsNormSq X ≤ 1 := by
      have : hsNormSq X = gibbsWightmanNormSq G A_M :=
        congrArg Complex.re
          (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter)
      linarith
    have hYY : (hsInner Y (majoranaParitySizeOp n Y)).re ≤ ((2 * n : ℕ) : ℝ) * ε_M ^ 2 := by
      rw [← hY_hs]; exact (hmaj_bounds Y).2
    have hquad_exp : ∀ α : ℝ,
        0 ≤ (hsInner X (majoranaParitySizeOp n X)).re +
            2 * α * (hsInner X (majoranaParitySizeOp n Y)).re +
            α ^ 2 * (hsInner Y (majoranaParitySizeOp n Y)).re := by
      intro α
      have hq := (hmaj_bounds (X + (α : ℂ) • Y)).1
      rw [hpar_add, hpar_smul] at hq
      have heq : (hsInner (X + (α : ℂ) • Y) (majoranaParitySizeOp n X + (α : ℂ) • majoranaParitySizeOp n Y)).re =
          (hsInner X (majoranaParitySizeOp n X)).re + 2 * α * (hsInner X (majoranaParitySizeOp n Y)).re +
          α ^ 2 * (hsInner Y (majoranaParitySizeOp n Y)).re := by
        unfold hsInner
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
          Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
          Matrix.trace_smul, smul_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
          Complex.add_re, Complex.re_ofReal_mul]
        have hsym := hS_sa X Y
        unfold hsInner at hsym
        rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
        ring_nf; linarith
      linarith
    have hcs_sq : ((hsInner X (majoranaParitySizeOp n Y)).re) ^ 2 ≤
        (hsInner X (majoranaParitySizeOp n X)).re * (hsInner Y (majoranaParitySizeOp n Y)).re := by
      by_cases hY0 : (hsInner Y (majoranaParitySizeOp n Y)).re = 0
      · have h0 : (hsInner X (majoranaParitySizeOp n Y)).re = 0 := by
          by_contra hne
          set α : ℝ := -(hsInner X (majoranaParitySizeOp n X)).re / (2 * (hsInner X (majoranaParitySizeOp n Y)).re) - 1 / (hsInner X (majoranaParitySizeOp n Y)).re
          have hq := hquad_exp α
          rw [hY0, mul_zero, add_zero] at hq
          have : 2 * α * (hsInner X (majoranaParitySizeOp n Y)).re = -(hsInner X (majoranaParitySizeOp n X)).re - 2 := by
            dsimp only [α]; field_simp [hne]; ring
          linarith
        rw [h0, hY0]; norm_num
      · have hYpos : 0 < (hsInner Y (majoranaParitySizeOp n Y)).re :=
          lt_of_le_of_ne (hmaj_bounds Y).1 (Ne.symm hY0)
        set α : ℝ := -(hsInner X (majoranaParitySizeOp n Y)).re / (hsInner Y (majoranaParitySizeOp n Y)).re
        have hmul := mul_nonneg (hquad_exp α) hYpos.le
        have hident : ((hsInner X (majoranaParitySizeOp n X)).re +
            2 * α * (hsInner X (majoranaParitySizeOp n Y)).re +
            α ^ 2 * (hsInner Y (majoranaParitySizeOp n Y)).re) *
            (hsInner Y (majoranaParitySizeOp n Y)).re =
            (hsInner X (majoranaParitySizeOp n X)).re * (hsInner Y (majoranaParitySizeOp n Y)).re -
            ((hsInner X (majoranaParitySizeOp n Y)).re) ^ 2 := by
          dsimp only [α]; field_simp [hYpos.ne']; ring
        linarith
    have hXX : (hsInner X (majoranaParitySizeOp n X)).re ≤ ((2 * n : ℕ) : ℝ) := by
      have := (hmaj_bounds X).2; nlinarith [Nat.cast_nonneg (α := ℝ) (2 * n)]
    have hprod : (hsInner X (majoranaParitySizeOp n X)).re * (hsInner Y (majoranaParitySizeOp n Y)).re ≤
        (((2 * n : ℕ) : ℝ) * ε_M) ^ 2 := by
      have : (((2 * n : ℕ) : ℝ) * ε_M) ^ 2 = ((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) * ε_M ^ 2) := by ring
      rw [this]; exact mul_le_mul hXX hYY (hmaj_bounds Y).1 (Nat.cast_nonneg _)
    have hsq_le : ((hsInner X (majoranaParitySizeOp n Y)).re) ^ 2 ≤ (((2 * n : ℕ) : ℝ) * ε_M) ^ 2 :=
      le_trans hcs_sq hprod
    have hnn_rhs : 0 ≤ ((2 * n : ℕ) : ℝ) * ε_M :=
      mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have hXY_cs : (hsInner X (majoranaParitySizeOp n Y)).re ≤ ((2 * n : ℕ) : ℝ) * ε_M := by
      nlinarith [sq_abs (hsInner X (majoranaParitySizeOp n Y)).re, le_abs_self (hsInner X (majoranaParitySizeOp n Y)).re]
    rw [hXY]; linarith
  linarith

/-- **Item #9 — Concrete End-to-End Majorana Theorem 1.1(b) (Fixed `n`, Eq. 1.14)**:
Wires `lemma_4_2_majorana_concrete` with `theorem_1_1a_concrete_qubit_tail` directly for
even-parity Majorana Hamiltonians. -/
theorem theorem_1_1b_majorana_concrete {n r s₀ M : ℕ} {α γ θ₀ : ℝ}
    (hr : 1 ≤ r) (hM : 1 ≤ M)
    {H O : QubitOp n} (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ)
    (hHf : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : O ∈ majoranaFiltrationSubmodule n s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb_lin : ∀ k, 1 ≤ k → k ≤ 4 ^ n - 1 →
      lanczosCoeff (concreteGibbsData hH β) H O k ≤ α * (k : ℝ) + γ)
    (t : ℝ) (ht : 0 ≤ t) :
    let G := concreteGibbsData hH β
    let q_M : ℝ := Real.exp ((1 / 2 + γ / α) * θ₀) *
      Real.exp (-4 * Real.tanh (θ₀ / 4) * (M : ℝ) * Real.exp (-2 * α * t))
    majoranaThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
      majoranaLambdaMSS G (s₀ + (M - 1) * (r - 1)) +
      2 * ((2 * n : ℕ) : ℝ) * Real.sqrt q_M + ((2 * n : ℕ) : ℝ) * q_M := by
  intro G q_M
  have hlem := lemma_4_2_majorana_concrete hr hM hH hO β t hHf hOf hOnorm
  have htail := theorem_1_1a_concrete_qubit_tail hH hO β hOnorm hα hγ hθ₀ hb_lin M t ht
  set ε_M := Real.sqrt (gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t))
  have hε_le : ε_M ≤ Real.sqrt q_M := Real.sqrt_le_sqrt htail
  have hε_sq : ε_M ^ 2 = gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O M t) :=
    Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)
  have h2n_nn : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : 2 * ((2 * n : ℕ) : ℝ) * ε_M ≤ 2 * ((2 * n : ℕ) : ℝ) * Real.sqrt q_M := by nlinarith
  have h2 : ((2 * n : ℕ) : ℝ) * ε_M ^ 2 ≤ ((2 * n : ℕ) : ℝ) * q_M := by
    rw [hε_sq]; exact mul_le_mul_of_nonneg_left htail h2n_nn
  linarith

/-- **Item #9 — Concrete Majorana Proposition 4.1(2) (Eq. 4.2)**:
For ANY Hermitian even-parity `H ∈ majoranaEvenFiltrationSubmodule n r` (`1 ≤ r`),
Hermitian `O ∈ majoranaFiltrationSubmodule n s₀` with `‖O‖_{β,W}² = 1`, `β : ℝ`, and `t : ℝ`:
`Re (𝒪(t) | 𝒬^{(β),Maj} 𝒪(t))_β^W ≤ (r - 1) * K_β^W(t) + s₀`. -/
theorem prop_4_1_part2_majorana {n r s₀ : ℕ} (hr : 1 ≤ r)
    {H O : QubitOp n} (hH : H.IsHermitian) (hO : O.IsHermitian) (β t : ℝ)
    (hHf : H ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : O ∈ majoranaFiltrationSubmodule n s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
      (majoranaWightmanQ G (heisenbergEvol hH (t : ℂ) O))).re ≤
    ((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ) := by
  intro G
  have hQ_eq : (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
      (majoranaWightmanQ G (heisenbergEvol hH (t : ℂ) O))).re =
      ∑ k ∈ Finset.range (2 * n),
        wightmanDistSq G (majoranaFiltrationSubmodule n k) (heisenbergEvol hH (t : ℂ) O) := by
    unfold majoranaWightmanQ
    simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
    unfold gibbsWightmanInner wightmanInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro k _
    exact wightmanSubspaceProj_eq_distSq G (majoranaFiltrationSubmodule n k) _
  rw [hQ_eq]
  unfold concreteKrylovComplexity
  apply prop_4_1_q_complexity_bound hr
    (fun m ↦ ‖concreteKrylovWavefn hH β O m t‖ ^ 2)
    (fun s ↦ wightmanDistSq G (majoranaFiltrationSubmodule n s) (heisenbergEvol hH (t : ℂ) O))
  · intro m; exact sq_nonneg _
  · intro s
    calc wightmanDistSq G (majoranaFiltrationSubmodule n s) (heisenbergEvol hH (t : ℂ) O)
        ≤ gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O) := wightmanDistSq_le_normSq G _ _
      _ = 1 := by rw [heisenbergEvol_real_wightmanNormSq hH β t O, hOnorm]
  · intro k s hks
    have hAk_mem : lanczosTrunc hH β O (k + 1) t ∈ majoranaFiltrationSubmodule n s := by
      have h1 := majorana_lanczosTrunc_mem_filtration hr (by omega : 1 ≤ k + 1) hH β t hHf hOf
      simp only [Nat.add_sub_cancel] at h1
      have hle : s₀ + k * (r - 1) ≤ s := by rw [mul_comm]; exact hks
      exact majoranaFiltrationSubmodule_mono hle h1
    have hdist_le : wightmanDistSq G (majoranaFiltrationSubmodule n s) (heisenbergEvol hH (t : ℂ) O) ≤
        gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t) := by
      unfold wightmanDistSq
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨B, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _
      · exact ⟨lanczosTrunc hH β O (k + 1) t, hAk_mem, rfl⟩
    have htail_norm : gibbsWightmanNormSq G (heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t) =
        ∑ m ∈ (Finset.range (4 ^ n)).filter (fun m ↦ k < m), ‖concreteKrylovWavefn hH β O m t‖ ^ 2 := by
      have hzero_ge : ∀ m ≥ 4 ^ n, lanczosOp G H O m = 0 := by
        intro m hm
        rcases lanczos_terminates hH hO β with ⟨k₀, hk₀, hbk₀⟩
        have hOk1 : lanczosOp G H O (k₀ + 1) = 0 := lanczosOp_eq_zero_of_coeff_zero G H O hbk₀
        have h := (lanczos_stays_zero G H O (k₀ + 1) hOk1 hbk₀ (m - (k₀ + 1))).1
        rwa [show k₀ + 1 + (m - (k₀ + 1)) = m by omega] at h
      have hdiff_eq : heisenbergEvol hH (t : ℂ) O - lanczosTrunc hH β O (k + 1) t =
          ∑ m ∈ (Finset.range (4 ^ n)).filter (fun m ↦ k < m),
            (Complex.I ^ m * concreteKrylovWavefn hH β O m t) • lanczosOp G H O m := by
        rw [heisenbergEvol_eq_lanczosTrunc_full hH hO β t hOnorm]
        unfold lanczosTrunc
        have htrunc_cap : (∑ m ∈ Finset.range (k + 1),
            (Complex.I ^ m * concreteKrylovWavefn hH β O m t) • lanczosOp G H O m) =
            ∑ m ∈ (Finset.range (4 ^ n)).filter (fun m ↦ ¬ k < m),
              (Complex.I ^ m * concreteKrylovWavefn hH β O m t) • lanczosOp G H O m := by
          by_cases hk4 : k + 1 ≤ 4 ^ n
          · refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
            ext m; simp only [Finset.mem_range, Finset.mem_filter, not_lt]; omega
          · symm
            refine Finset.sum_subset (fun m hm ↦ ?_) (fun m hm hnot ↦ ?_)
            · simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hm ⊢; omega
            · simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hnot
              have hge : 4 ^ n ≤ m := by
                have := Finset.mem_range.mp hm; by_contra hlt; apply hnot; exact ⟨by omega, by omega⟩
              rw [hzero_ge m hge, smul_zero]
        rw [htrunc_cap]
        have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (4 ^ n)) (fun m ↦ k < m)
          (fun m ↦ (Complex.I ^ m * concreteKrylovWavefn hH β O m t) • lanczosOp G H O m)
        rw [← hpart, add_sub_cancel_right]
      rw [hdiff_eq]
      set S := (Finset.range (4 ^ n)).filter (fun m ↦ k < m)
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
        Finset.mul_sum, Complex.re_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro m hm
      have hre_pull : (∑ j ∈ S,
          ((Complex.I ^ j * concreteKrylovWavefn hH β O j t) *
            (star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
              (G.ρHalf * (lanczosOp G H O m)ᴴ * G.ρHalf * lanczosOp G H O j).trace)).re) =
          (∑ j ∈ S,
            star (Complex.I ^ m * concreteKrylovWavefn hH β O m t) *
            (Complex.I ^ j * concreteKrylovWavefn hH β O j t *
              gibbsWightmanInner G (lanczosOp G H O m) (lanczosOp G H O j))).re := by
        rw [← Complex.re_sum]; congr 1; apply Finset.sum_congr rfl; intro j _
        unfold gibbsWightmanInner wightmanInner; ring
      rw [hre_pull, Finset.sum_eq_single m]
      · rw [lanczosOp_orthonormal_all hH hO β m m]
        by_cases hOm : lanczosOp G H O m = 0
        · have hOm' : lanczosOp (concreteGibbsData hH β) H O m = 0 := hOm
          rw [if_neg (by simp [hOm']), mul_zero, mul_zero, Complex.zero_re]
          have hφ0 : concreteKrylovWavefn hH β O m t = 0 := by
            unfold concreteKrylovWavefn gibbsWightmanInner wightmanInner
            dsimp only; rw [hOm']; simp
          rw [hφ0, norm_zero, zero_pow (by norm_num)]
        · rw [if_pos ⟨rfl, hOm⟩, mul_one, Complex.star_def, Complex.conj_mul',
            ← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_I,
            one_pow, one_mul]
      · intro j _ hjm
        rw [lanczosOp_orthonormal_all hH hO β m j, if_neg (by intro h; exact hjm h.1.symm),
          mul_zero, mul_zero]
      · intro hm'; exact absurd hm hm'
    rw [← htail_norm]
    exact hdist_le

/-- **Item #9 — Concrete Family-Level Majorana Theorem 1.1(b) (`λ_L ≤ 2 α`)**:
For any sequence of `n`-qubit (`2 n`-Majorana-mode) even-parity `r`-local Hamiltonians `H_n`
and Hermitian initial operators `O_n ∈ majoranaFiltrationSubmodule n s₀`, if (H1) and (H2)
hold along the sequence and the Majorana thermal size grows as `c * n^{1 - ε}` at
`t_n = ((1 - ε) / lamL) log n`, then `lamL ≤ 2 α`. -/
theorem theorem_1_1b_family_majorana {r s₀ : ℕ} (hr : 1 ≤ r)
    {α γ C₁ C₂ δ lamL : ℝ} (β : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hlam : 0 < lamL)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (H_n O_n : (n : ℕ) → QubitOp n)
    (hH : ∀ n, (H_n n).IsHermitian) (hO : ∀ n, (O_n n).IsHermitian)
    (hHf : ∀ n, H_n n ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : ∀ n, O_n n ∈ majoranaFiltrationSubmodule n s₀)
    (hOnorm : ∀ n, gibbsWightmanNormSq (concreteGibbsData (hH n) β) (O_n n) = 1)
    (hb_lin : ∀ n k, 1 ≤ k → k ≤ 4 ^ n - 1 →
      lanczosCoeff (concreteGibbsData (hH n) β) (H_n n) (O_n n) k ≤ α * (k : ℝ) + γ)
    (hH2 : ∀ (n s : ℕ), 1 ≤ n →
      majoranaLambdaMSS (concreteGibbsData (hH n) β) s ≤
        C₁ * (s : ℝ) + C₂ * ((2 * n : ℕ) : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)))
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ n ≥ N₁,
        let tn := ((1 - ε) / lamL) * Real.log (n : ℝ)
        c * (n : ℝ) ^ (1 - ε) ≤
          majoranaThermalSize (concreteGibbsData (hH n) β)
            (heisenbergEvol (hH n) (tn : ℂ) (O_n n))) :
    lamL ≤ 2 * α := by
  set C₀ : ℝ := 2 * Real.sqrt (Real.exp ((1 / 2 + γ / α) * 4))
  set C₂' : ℝ := C₂ * (2 : ℝ) ^ δ
  have hC₀ : 0 ≤ C₀ := by positivity
  have hC₂' : 0 ≤ C₂' := by positivity
  refine theorem_1_1b_static_reduction (C₀ := C₀) (C₁ := C₁) (C₂ := C₂') (r := r) (s₀ := s₀)
    hr hα hlam hδ0 hδ1 hC₀ hC₁ hC₂' ?_
  intro ε₀ hε₀
  obtain ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩ := hH1 (min ε₀ (1 / 2)) (lt_min hε₀ (by norm_num))
  have hε_lt₀ : ε < ε₀ := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  refine ⟨ε, ⟨hε_pos, hε_lt₀⟩, c, hc_pos, max N₁ 2, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  set tn : ℝ := ((1 - ε) / lamL) * Real.log (n : ℝ)
  have htn_nn : 0 ≤ tn := by
    dsimp only [tn]; apply mul_nonneg (div_nonneg (by linarith) hlam.le) hlogn_pos.le
  have htanh1_pos : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
    apply div_pos _ (Real.cosh_pos 1)
    have : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith
  set xM : ℝ := (1 / Real.tanh 1) * Real.exp (2 * α * tn) * Real.log (n : ℝ)
  have hxM_pos : 0 < xM := by dsimp only [xM]; positivity
  set M : ℕ := Nat.ceil xM
  have hM_ge_xM : xM ≤ (M : ℝ) := Nat.le_ceil xM
  have hM_ge1 : 1 ≤ M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le hxM_pos hM_ge_xM
    exact_mod_cast (Nat.pos_of_ne_zero (by intro h; simp [h] at this))
  have hM_le : (M : ℝ) ≤ xM + 1 := (Nat.ceil_lt_add_one hxM_pos.le).le
  set MN : ℝ := xM + 1
  set sN : ℝ := (s₀ : ℝ) + ((r : ℝ) - 1) * MN
  have hstep := theorem_1_1b_majorana_concrete hr hM_ge1 (hH n) (hO n) β
    (hHf n) (hOf n) (hOnorm n) hα hγ (by norm_num : (0 : ℝ) < 4) (hb_lin n) tn htn_nn
  set q_M : ℝ := Real.exp ((1 / 2 + γ / α) * 4) *
    Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn))
  have h4div4 : (4 : ℝ) / 4 = 1 := by norm_num
  have hqM_le : q_M ≤ (Real.exp ((1 / 2 + γ / α) * 4)) * (n : ℝ) ^ (-4 : ℝ) := by
    dsimp only [q_M]
    rw [h4div4]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hexp_le : -4 * Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tn) ≤ -4 * Real.log (n : ℝ) := by
      have h1 : Real.log (n : ℝ) ≤ Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tn) := by
        have hmul : Real.tanh 1 * xM * Real.exp (-2 * α * tn) = Real.log (n : ℝ) := by
          dsimp only [xM]
          have he : Real.exp (2 * α * tn) * Real.exp (-2 * α * tn) = 1 := by
            rw [← Real.exp_add]; simp
          field_simp [htanh1_pos.ne']
          rw [show -(2 * α * tn) = -2 * α * tn by ring]
          exact he
        have hle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_ge_xM htanh1_pos.le)
          (Real.exp_pos (-2 * α * tn)).le
        linarith
      linarith
    calc Real.exp (-4 * Real.tanh 1 * (M : ℝ) * Real.exp (-2 * α * tn))
        ≤ Real.exp (-4 * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexp_le
      _ = Real.exp (Real.log (n : ℝ) * (-4 : ℝ)) := by ring_nf
      _ = (n : ℝ) ^ (-4 : ℝ) := (Real.rpow_def_of_pos hn_pos (-4 : ℝ)).symm
  have hsqrt_qM : Real.sqrt q_M ≤ (C₀ / 2) * (n : ℝ) ^ (-2 : ℝ) := by
    have hsq : Real.exp ((1 / 2 + γ / α) * 4) * (n : ℝ) ^ (-4 : ℝ) =
        ((C₀ / 2) * (n : ℝ) ^ (-2 : ℝ)) ^ 2 := by
      dsimp only [C₀]
      have hpow : ((n : ℝ) ^ (-2 : ℝ)) ^ 2 = (n : ℝ) ^ (-4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
      have hc : (2 * Real.sqrt (Real.exp ((1 / 2 + γ / α) * 4)) / 2) ^ 2 =
          Real.exp ((1 / 2 + γ / α) * 4) := by
        rw [mul_div_cancel_left₀ _ (by norm_num), Real.sq_sqrt (Real.exp_pos _).le]
      rw [mul_pow, hc, hpow]
    calc Real.sqrt q_M
        ≤ Real.sqrt (((C₀ / 2) * (n : ℝ) ^ (-2 : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt (hsq ▸ hqM_le)
      _ = (C₀ / 2) * (n : ℝ) ^ (-2 : ℝ) := Real.sqrt_sq (by positivity)
  have hterm1 : 2 * ((2 * n : ℕ) : ℝ) * Real.sqrt q_M ≤ 2 * C₀ * (n : ℝ)⁻¹ := by
    have h2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [h2n]
    have h1 := mul_le_mul_of_nonneg_left hsqrt_qM (by positivity : (0 : ℝ) ≤ 2 * (2 * (n : ℝ)))
    have hnpow : (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) = (n : ℝ)⁻¹ := by
      calc (n : ℝ) * (n : ℝ) ^ (-2 : ℝ)
          = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((1 : ℝ) + -2) := (Real.rpow_add hn_pos 1 (-2)).symm
        _ = (n : ℝ)⁻¹ := by norm_num; exact Real.rpow_neg_one _
    have h2 : 2 * (2 * (n : ℝ)) * ((C₀ / 2) * (n : ℝ) ^ (-2 : ℝ)) = 2 * C₀ * (n : ℝ)⁻¹ := by
      calc 2 * (2 * (n : ℝ)) * ((C₀ / 2) * (n : ℝ) ^ (-2 : ℝ))
          = 2 * C₀ * ((n : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by ring
        _ = 2 * C₀ * (n : ℝ)⁻¹ := by rw [hnpow]
    linarith
  have hterm2 : ((2 * n : ℕ) : ℝ) * q_M ≤ C₀ ^ 2 * (n : ℝ) ^ (-3 : ℝ) := by
    have h2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [h2n]
    have h1 := mul_le_mul_of_nonneg_left hqM_le (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have hnpow : (n : ℝ) * (n : ℝ) ^ (-4 : ℝ) = (n : ℝ) ^ (-3 : ℝ) := by
      calc (n : ℝ) * (n : ℝ) ^ (-4 : ℝ)
          = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((1 : ℝ) + -4) := (Real.rpow_add hn_pos 1 (-4)).symm
        _ = (n : ℝ) ^ (-3 : ℝ) := by norm_num
    have hC0sq : C₀ ^ 2 = 4 * Real.exp ((1 / 2 + γ / α) * 4) := by
      dsimp only [C₀]; rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]; norm_num
    have h2 : 2 * (n : ℝ) * (Real.exp ((1 / 2 + γ / α) * 4) * (n : ℝ) ^ (-4 : ℝ)) =
        (2 * Real.exp ((1 / 2 + γ / α) * 4)) * (n : ℝ) ^ (-3 : ℝ) := by
      calc 2 * (n : ℝ) * (Real.exp ((1 / 2 + γ / α) * 4) * (n : ℝ) ^ (-4 : ℝ))
          = (2 * Real.exp ((1 / 2 + γ / α) * 4)) * ((n : ℝ) * (n : ℝ) ^ (-4 : ℝ)) := by ring
        _ = (2 * Real.exp ((1 / 2 + γ / α) * 4)) * (n : ℝ) ^ (-3 : ℝ) := by rw [hnpow]
    have h3 : (2 * Real.exp ((1 / 2 + γ / α) * 4)) * (n : ℝ) ^ (-3 : ℝ) ≤
        C₀ ^ 2 * (n : ℝ) ^ (-3 : ℝ) := by
      rw [hC0sq]
      nlinarith [Real.exp_pos ((1 / 2 + γ / α) * 4), Real.rpow_pos_of_pos hn_pos (-3 : ℝ)]
    linarith
  have hs_le : ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ≤ sN := by
    dsimp only [sN, MN]
    have hM1 : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
    have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr, Nat.cast_one]
    push_cast
    rw [hr1]
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) - 1 := by rw [← hr1]; exact Nat.cast_nonneg _
    nlinarith
  have hlam_le : majoranaLambdaMSS (concreteGibbsData (hH n) β) (s₀ + (M - 1) * (r - 1)) ≤
      C₁ * sN + C₂' * (n : ℝ) ^ δ * sN ^ (1 - δ) := by
    have h2 := hH2 n (s₀ + (M - 1) * (r - 1)) (by omega)
    have h2n_rpow : ((2 * n : ℕ) : ℝ) ^ δ = (2 : ℝ) ^ δ * (n : ℝ) ^ δ := by
      have : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
      rw [this, Real.mul_rpow (by norm_num) hn_pos.le]
    rw [h2n_rpow] at h2
    have hC2eq : C₂ * (2 : ℝ) ^ δ = C₂' := rfl
    rw [← mul_assoc C₂ ((2 : ℝ) ^ δ) ((n : ℝ) ^ δ), hC2eq] at h2
    have hs1 : C₁ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ≤ C₁ * sN :=
      mul_le_mul_of_nonneg_left hs_le hC₁
    have hs2 : ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ) ≤ sN ^ (1 - δ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hs_le (by linarith)
    have hmul2 : C₂' * (n : ℝ) ^ δ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ) ≤
        C₂' * (n : ℝ) ^ δ * sN ^ (1 - δ) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    linarith
  have hgn := hN₁ n hn1
  dsimp only at hgn hstep
  linarith

end Item9MajoranaFiltrationProp41Lemma42Thm11b

end KrylovChaos
