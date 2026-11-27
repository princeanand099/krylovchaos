/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Concrete Hypergraph Polymer & Tree Combinatorics (Appendix A, Flaw #9)

Replaces the scalar-wrapper lemmas in `PolymerTrees.lean` with concrete combinatorial
constructions and proofs (zero `htree`, `hcayley`, or abstract `S` hypotheses):
1. **Lemma A.1 (`lemma_A_1_concrete_bin_tree_sum`, `lemma_A_1_concrete_forest_sum`)**: Concrete
   binary-encoded plane hypergraph tree and Knuth left-child/right-sibling forest weight sums
   `binTreeSum E η m x` and `forestSum E η m S`, proved by strong induction on `m` via the
   Catalan recurrence `C_m = ∑_{j=0}^{m-1} C_j C_{m-1-j}` with the sharp constant `C_m ≤ 4^{m-1}`
   (`m ≥ 1`): `binTreeSum E η m x ≤ 4^{m-1} * (r * η₀)^{m-1} * η₀`.
2. **Forward Causal Sequence Bound (`lemma_A_2_concrete_causal_seq_sum`)**: Concrete ordered
   forward causal hyperedge sequence weight sum `causalSeqSum E w k U` (used in Lemma 2.1),
   proved by induction on `k`:
   `causalSeqSum E w k U ≤ (∏ j ∈ Finset.range k, (|U| + j * (r - 1))) * Jsite ^ k`.
   (The root-reversal Lemma A.2 `(1/k!) revCausalSum ≤ (k+1)(r J)^k ≤ (e r J)^k` is proved in
   `CausalExpansion.lean` as `revCausalSum_le` and `lemma_A_2_root_reversal_exp_bound`.)
3. **Lemma A.3 (`lemma_A_3_concrete_unordered_tree_sum`)**: Concrete Galton–Watson / Kotecký–Preiss
   unordered rooted hypergraph tree sum `unorderedTreeSum E η h X`, proved by induction on depth
   `h`: if `η₀ * exp(c * r) ≤ c`, then `unorderedTreeSum E η h X ≤ η X * exp(c * |X|)`.
-/

namespace KrylovChaos

private lemma real_prod_le_prod_cc {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a t)
    have hft : 0 ≤ ∏ i ∈ t, f i := Finset.prod_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hga : 0 ≤ g a := le_trans hfa (hfg a (Finset.mem_insert_self a t))
    exact mul_le_mul (hfg a (Finset.mem_insert_self a t))
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi)))
      hft hga

section CatalanRecurrence

/-- Catalan numbers defined via the Segner recurrence `C_0 = 1`,
`C_{n+1} = ∑_{j=0}^n C_j * C_{n - j}`. -/
def catalanRec : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ (Finset.range (n + 1)).attach, catalanRec j.1 * catalanRec (n - j.1)
termination_by n => n
decreasing_by
  all_goals (have := Finset.mem_range.mp j.2; omega)

lemma catalanRec_succ (n : ℕ) :
    catalanRec (n + 1) = ∑ j ∈ Finset.range (n + 1), catalanRec j * catalanRec (n - j) := by
  rw [catalanRec]
  exact Finset.sum_attach (Finset.range (n + 1)) (fun j ↦ catalanRec j * catalanRec (n - j))

/-- Generating-function partial sum bound at `x = 1/4`:
`∑ k ∈ Finset.range (M + 1), (catalanRec k : ℝ) / 4 ^ k ≤ 2` for all `M : ℕ`. -/
lemma catalanRec_quarter_sum_le_two :
    ∀ M : ℕ, ∑ k ∈ Finset.range (M + 1), (catalanRec k : ℝ) / (4 : ℝ) ^ k ≤ 2 := by
  intro M
  induction M with
  | zero =>
    simp [catalanRec]
  | succ M ih =>
    rw [Finset.sum_range_succ']
    have hc0 : (catalanRec 0 : ℝ) / (4 : ℝ) ^ 0 = 1 := by simp [catalanRec]
    rw [hc0]
    have hquad : ∑ k ∈ Finset.range (M + 1), (catalanRec (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1) ≤
        (1 / 4 : ℝ) * (∑ j ∈ Finset.range (M + 1), (catalanRec j : ℝ) / (4 : ℝ) ^ j) ^ 2 := by
      have hterm : ∀ k ∈ Finset.range (M + 1),
          (catalanRec (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1) =
            (1 / 4 : ℝ) * ∑ j ∈ Finset.range (k + 1),
              ((catalanRec j : ℝ) / (4 : ℝ) ^ j) *
              ((catalanRec (k - j) : ℝ) / (4 : ℝ) ^ (k - j)) := by
        intro k _
        rw [catalanRec_succ, Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hpow : (4 : ℝ) ^ j * (4 : ℝ) ^ (k - j) = (4 : ℝ) ^ k := by
          rw [← pow_add, Nat.add_sub_cancel' hjk]
        rw [Nat.cast_mul, pow_succ]
        field_simp [hpow]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      let S := (Finset.range (M + 1)).sigma (fun k ↦ Finset.range (k + 1))
      let f : ℕ → ℝ := fun j ↦ (catalanRec j : ℝ) / (4 : ℝ) ^ j
      have hf_nn : ∀ j : ℕ, 0 ≤ f j := fun j ↦ by positivity
      have h1 : (∑ k ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (k + 1), f j * f (k - j)) =
          ∑ p ∈ S, f p.2 * f (p.1 - p.2) := by
        rw [Finset.sum_sigma]
      rw [h1]
      have hinj : Set.InjOn (fun p : Σ _k : ℕ, ℕ ↦ (p.2, p.1 - p.2)) (S : Set _) := by
        intro p₁ hp₁ p₂ hp₂ heq
        have h1' : p₁.2 ≤ p₁.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_sigma.mp hp₁).2)
        have h2' : p₂.2 ≤ p₂.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_sigma.mp hp₂).2)
        have heq1 : p₁.2 = p₂.2 := congrArg Prod.fst heq
        have heq2 : p₁.1 - p₁.2 = p₂.1 - p₂.2 := congrArg Prod.snd heq
        have hp1eq : p₁.1 = p₂.1 := by omega
        cases p₁; cases p₂; simp only at hp1eq heq1; subst hp1eq; subst heq1; rfl
      have hsub : S.image (fun p ↦ (p.2, p.1 - p.2)) ⊆
          (Finset.range (M + 1)).product (Finset.range (M + 1)) := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
        have h1' : p.1 < M + 1 := Finset.mem_range.mp hp1
        have h2' : p.2 < p.1 + 1 := Finset.mem_range.mp hp2
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
      calc ∑ p ∈ S, f p.2 * f (p.1 - p.2)
          = ∑ q ∈ S.image (fun p ↦ (p.2, p.1 - p.2)), f q.1 * f q.2 := by
            rw [Finset.sum_image hinj]
        _ ≤ ∑ q ∈ (Finset.range (M + 1)).product (Finset.range (M + 1)), f q.1 * f q.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ ↦ mul_nonneg (hf_nn _) (hf_nn _)
        _ = (∑ j ∈ Finset.range (M + 1), f j) ^ 2 := by
            rw [Finset.sum_product, sq, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
    have hnn : 0 ≤ ∑ j ∈ Finset.range (M + 1), (catalanRec j : ℝ) / (4 : ℝ) ^ j :=
      Finset.sum_nonneg fun j _ ↦ by positivity
    have hsq : (∑ j ∈ Finset.range (M + 1), (catalanRec j : ℝ) / (4 : ℝ) ^ j) ^ 2 ≤ 4 := by
      nlinarith
    linarith

lemma catalanRec_le_four_pow (n : ℕ) : (catalanRec n : ℝ) ≤ (4 : ℝ) ^ n := by
  have hsum := catalanRec_quarter_sum_le_two n
  have hle1 : (catalanRec n : ℝ) / (4 : ℝ) ^ n ≤ 1 := by
    cases n with
    | zero => simp [catalanRec]
    | succ n =>
      have hsplit : ∑ k ∈ Finset.range (n + 2), (catalanRec k : ℝ) / (4 : ℝ) ^ k =
          1 + ∑ k ∈ Finset.range (n + 1), (catalanRec (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1) := by
        rw [Finset.sum_range_succ']; simp [catalanRec]
      have hterm : (catalanRec (n + 1) : ℝ) / (4 : ℝ) ^ (n + 1) ≤
          ∑ k ∈ Finset.range (n + 1), (catalanRec (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1) :=
        Finset.single_le_sum (f := fun k ↦ (catalanRec (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1))
          (fun k _ ↦ by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n))
      linarith
  have hpos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  rwa [div_le_one hpos] at hle1

/-- Sharp exponential bound `catalanRec m ≤ 4^(m - 1)` for all `m ≥ 1`. -/
lemma catalanRec_le_four_pow_pred (m : ℕ) (hm : 1 ≤ m) :
    (catalanRec m : ℝ) ≤ (4 : ℝ) ^ (m - 1) := by
  have hdiv : ∀ k : ℕ, 1 ≤ k → (catalanRec k : ℝ) / (4 : ℝ) ^ k ≤ 1 / 4 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero =>
          rw [catalanRec_succ]
          simp [catalanRec]
        | succ n =>
          have hrew : (catalanRec (n + 2) : ℝ) / (4 : ℝ) ^ (n + 2) =
              (1 / 4 : ℝ) * ∑ j ∈ Finset.range (n + 2),
                ((catalanRec j : ℝ) / (4 : ℝ) ^ j) *
                ((catalanRec (n + 1 - j) : ℝ) / (4 : ℝ) ^ (n + 1 - j)) := by
            rw [catalanRec_succ, Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j hj
            have hjn : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hpow : (4 : ℝ) ^ j * (4 : ℝ) ^ (n + 1 - j) = (4 : ℝ) ^ (n + 1) := by
              rw [← pow_add, Nat.add_sub_cancel' hjn]
            rw [Nat.cast_mul, pow_succ]
            field_simp [hpow]
          rw [hrew, Finset.sum_range_succ']
          have h0 : ((catalanRec 0 : ℝ) / (4 : ℝ) ^ 0) *
              ((catalanRec (n + 1 - 0) : ℝ) / (4 : ℝ) ^ (n + 1 - 0)) ≤ 1 / 4 := by
            simp only [catalanRec, Nat.cast_one, pow_zero, div_one, one_mul, Nat.sub_zero]
            exact ih (n + 1) (by omega) (by omega)
          have hrest : ∑ j ∈ Finset.range (n + 1),
              ((catalanRec (j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)) *
              ((catalanRec (n + 1 - (j + 1)) : ℝ) / (4 : ℝ) ^ (n + 1 - (j + 1))) ≤
              (1 / 4 : ℝ) * ∑ j ∈ Finset.range (n + 1),
                (catalanRec (n - j) : ℝ) / (4 : ℝ) ^ (n - j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum; intro j hj
            have hjn : j < n + 1 := Finset.mem_range.mp hj
            have hsub : n + 1 - (j + 1) = n - j := by omega
            rw [hsub]
            exact mul_le_mul_of_nonneg_right (ih (j + 1) (by omega) (by omega)) (by positivity)
          have hsum_le : ∑ j ∈ Finset.range (n + 1),
              (catalanRec (n - j) : ℝ) / (4 : ℝ) ^ (n - j) ≤ 2 := by
            have hrev : ∑ j ∈ Finset.range (n + 1),
                (catalanRec (n - j) : ℝ) / (4 : ℝ) ^ (n - j) =
                ∑ k ∈ Finset.range (n + 1), (catalanRec k : ℝ) / (4 : ℝ) ^ k := by
              refine Finset.sum_bij (fun j _ ↦ n - j) ?_ ?_ ?_ ?_
              · intro j hj; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
              · intro j₁ hj₁ j₂ hj₂ heq
                have h1 := Finset.mem_range.mp hj₁
                have h2 := Finset.mem_range.mp hj₂
                omega
              · intro k hk
                have hkn := Finset.mem_range.mp hk
                exact ⟨n - k, Finset.mem_range.mpr (by omega), by omega⟩
              · intro _ _; rfl
            rw [hrev]
            exact catalanRec_quarter_sum_le_two n
          linarith
  have hm_le := hdiv m hm
  have hpow4 : (4 : ℝ) ^ m = 4 * (4 : ℝ) ^ (m - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (m - 1) := by positivity
  rw [hpow4, div_le_iff₀ (by positivity)] at hm_le
  linarith

end CatalanRecurrence

section LemmaA1Concrete

/-- Concrete binary-encoded plane hypergraph tree weight sum of size `m` anchored at site `x`:
- `m = 0`: empty tree, weight `1`.
- `m + 1`: choose root hyperedge `X ∈ E` containing `x` (weight `η X`), split the remaining `m`
  nodes into a left subtree of size `j` and a right subtree of size `m - j` (`0 ≤ j ≤ m`), each
  attached to a site of `X` (or `1` if size `0`). -/
noncomputable def binTreeSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) : ℕ → Fin N → ℝ
  | 0, _ => 1
  | m + 1, x =>
    ∑ X ∈ E.filter (fun X ↦ x ∈ X),
      η X * ∑ j ∈ (Finset.range (m + 1)).attach,
        (if j.1 = 0 then 1 else ∑ y ∈ X, binTreeSum E η j.1 y) *
        (if m - j.1 = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j.1) z)
termination_by m _ => m
decreasing_by
  all_goals (have := Finset.mem_range.mp j.2; omega)

lemma binTreeSum_succ {N : ℕ} (E : Finset (Finset (Fin N))) (η : Finset (Fin N) → ℝ)
    (m : ℕ) (x : Fin N) :
    binTreeSum E η (m + 1) x =
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        η X * ∑ j ∈ Finset.range (m + 1),
          (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
          (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z) := by
  rw [binTreeSum]
  apply Finset.sum_congr rfl; intro X _
  congr 1
  exact Finset.sum_attach (Finset.range (m + 1))
    (fun j ↦ (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
             (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z))

lemma binTreeSum_nonneg {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X) :
    ∀ m : ℕ, ∀ x : Fin N, 0 ≤ binTreeSum E η m x := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x
    cases m with
    | zero => simp [binTreeSum]
    | succ m =>
      rw [binTreeSum_succ]
      apply Finset.sum_nonneg; intro X hX
      apply mul_nonneg (hη_nn X (Finset.mem_filter.mp hX).1)
      apply Finset.sum_nonneg; intro j hj
      have hj' : j < m + 1 := Finset.mem_range.mp hj
      apply mul_nonneg
      · split_ifs
        · exact zero_le_one
        · exact Finset.sum_nonneg fun y _ ↦ ih j (by omega) y
      · split_ifs
        · exact zero_le_one
        · exact Finset.sum_nonneg fun z _ ↦ ih (m - j) (by omega) z

/-- **Lemma A.1 (Concrete Catalan Plane-Tree Bound, Zero `htree` Hypothesis)**:
For any finite hypergraph `E` with `∀ X ∈ E, X.card ≤ r`, nonnegative edge weights `η`, and
site bound `∀ x, ∑_{X ∈ E, x ∈ X} η X ≤ η₀`, the concrete size-`m` (`m ≥ 1`) plane-tree
weight sum satisfies:
`binTreeSum E η m x ≤ catalanRec m * (r * η₀)^(m - 1) * η₀ ≤ 4^(m - 1) * (r * η₀)^(m - 1) * η₀`. -/
theorem lemma_A_1_concrete_bin_tree_sum {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X ≤ η₀) :
    ∀ m : ℕ, 1 ≤ m → ∀ x : Fin N,
      binTreeSum E η m x ≤ (catalanRec m : ℝ) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm x
    cases m with
    | zero => omega
    | succ m =>
      rw [binTreeSum_succ]
      have hterm : ∀ X ∈ E.filter (fun X ↦ x ∈ X),
          η X * (∑ j ∈ Finset.range (m + 1),
            (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
            (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z)) ≤
          η X * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) := by
        intro X hX
        have hXE : X ∈ E := (Finset.mem_filter.mp hX).1
        have hcardX : (X.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hcard X hXE
        apply mul_le_mul_of_nonneg_left _ (hη_nn X hXE)
        have hbranch : ∀ k : ℕ, k ≤ m →
            (if k = 0 then 1 else ∑ y ∈ X, binTreeSum E η k y) ≤
              (catalanRec k : ℝ) * ((r : ℝ) * η₀) ^ k := by
          intro k hk
          by_cases hk0 : k = 0
          · subst hk0; simp [catalanRec]
          · rw [if_neg hk0]
            have hk1 : 1 ≤ k := by omega
            calc ∑ y ∈ X, binTreeSum E η k y
                ≤ ∑ _y ∈ X, ((catalanRec k : ℝ) * ((r : ℝ) * η₀) ^ (k - 1) * η₀) := by
                  apply Finset.sum_le_sum; intro y _
                  exact ih k (by omega) hk1 y
              _ = (X.card : ℝ) * ((catalanRec k : ℝ) * ((r : ℝ) * η₀) ^ (k - 1) * η₀) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (r : ℝ) * ((catalanRec k : ℝ) * ((r : ℝ) * η₀) ^ (k - 1) * η₀) := by
                  apply mul_le_mul_of_nonneg_right hcardX (by positivity)
              _ = (catalanRec k : ℝ) * (((r : ℝ) * η₀) ^ (k - 1) * ((r : ℝ) * η₀)) := by ring
              _ = (catalanRec k : ℝ) * ((r : ℝ) * η₀) ^ k := by
                  rw [← pow_succ, Nat.sub_add_cancel hk1]
        have hbranch_nn : ∀ k : ℕ, 0 ≤ (if k = 0 then 1 else ∑ y ∈ X, binTreeSum E η k y) := by
          intro k; split_ifs
          · exact zero_le_one
          · exact Finset.sum_nonneg fun y _ ↦ binTreeSum_nonneg E η hη_nn k y
        calc ∑ j ∈ Finset.range (m + 1),
              (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
              (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z)
            ≤ ∑ j ∈ Finset.range (m + 1),
              ((catalanRec j : ℝ) * ((r : ℝ) * η₀) ^ j) *
              ((catalanRec (m - j) : ℝ) * ((r : ℝ) * η₀) ^ (m - j)) := by
              apply Finset.sum_le_sum; intro j hj
              have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              exact mul_le_mul (hbranch j hj') (hbranch (m - j) (Nat.sub_le m j))
                (hbranch_nn (m - j)) (by positivity)
          _ = ∑ j ∈ Finset.range (m + 1),
              ((catalanRec j : ℝ) * (catalanRec (m - j) : ℝ)) * ((r : ℝ) * η₀) ^ m := by
              apply Finset.sum_congr rfl; intro j hj
              have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hexp : ((r : ℝ) * η₀) ^ j * ((r : ℝ) * η₀) ^ (m - j) = ((r : ℝ) * η₀) ^ m := by
                rw [← pow_add, Nat.add_sub_cancel' hj']
              linear_combination (catalanRec j : ℝ) * (catalanRec (m - j) : ℝ) * hexp
          _ = (∑ j ∈ Finset.range (m + 1), (catalanRec j : ℝ) * (catalanRec (m - j) : ℝ)) *
              ((r : ℝ) * η₀) ^ m := by
              rw [← Finset.sum_mul]
          _ = (catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m := by
              rw [catalanRec_succ]; simp only [Nat.cast_sum, Nat.cast_mul]
      calc ∑ X ∈ E.filter (fun X ↦ x ∈ X),
            η X * (∑ j ∈ Finset.range (m + 1),
              (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
              (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z))
          ≤ ∑ X ∈ E.filter (fun X ↦ x ∈ X),
            η X * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) :=
            Finset.sum_le_sum hterm
        _ = (∑ X ∈ E.filter (fun X ↦ x ∈ X), η X) *
            ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) := by
            rw [← Finset.sum_mul]
        _ ≤ η₀ * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) :=
            mul_le_mul_of_nonneg_right (hsite x) (by positivity)
        _ = (catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ ((m + 1) - 1) * η₀ := by
            simp only [Nat.add_sub_cancel]; ring

/-- Corollary of Lemma A.1: sharp exponential bound
`binTreeSum E η m x ≤ 4^(m - 1) * (r * η₀)^(m - 1) * η₀` for all `m ≥ 1`. -/
theorem lemma_A_1_concrete_exp_bound {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X ≤ η₀)
    {m : ℕ} (hm : 1 ≤ m) (x : Fin N) :
    binTreeSum E η m x ≤ (4 : ℝ) ^ (m - 1) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
  have h1 := lemma_A_1_concrete_bin_tree_sum E hcard η hη_nn hη₀ hsite m hm x
  have h2 := catalanRec_le_four_pow_pred m hm
  have h3 : (catalanRec m : ℝ) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ ≤
      (4 : ℝ) ^ (m - 1) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
    apply mul_le_mul_of_nonneg_right _ hη₀
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  exact le_trans h1 h3

/-- Concrete Knuth left-child/right-sibling binary-tree encoding of a hypergraph forest of size `m`
whose connected components all intersect site set `S`. -/
noncomputable def forestSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) : ℕ → Finset (Fin N) → ℝ
  | 0, _ => 1
  | m + 1, S =>
    ∑ y ∈ S, ∑ X ∈ E.filter (fun X ↦ y ∈ X),
      η X * ∑ j ∈ (Finset.range (m + 1)).attach,
        forestSum E η j.1 X * forestSum E η (m - j.1) S
termination_by m _ => m
decreasing_by
  all_goals (have := Finset.mem_range.mp j.2; omega)

lemma forestSum_succ {N : ℕ} (E : Finset (Finset (Fin N))) (η : Finset (Fin N) → ℝ)
    (m : ℕ) (S : Finset (Fin N)) :
    forestSum E η (m + 1) S =
      ∑ y ∈ S, ∑ X ∈ E.filter (fun X ↦ y ∈ X),
        η X * ∑ j ∈ Finset.range (m + 1), forestSum E η j X * forestSum E η (m - j) S := by
  rw [forestSum]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro X _
  congr 1
  exact Finset.sum_attach (Finset.range (m + 1)) (fun j ↦ forestSum E η j X * forestSum E η (m - j) S)

lemma forestSum_nonneg {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X) :
    ∀ m : ℕ, ∀ S : Finset (Fin N), 0 ≤ forestSum E η m S := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S
    cases m with
    | zero => simp [forestSum]
    | succ m =>
      rw [forestSum_succ]
      apply Finset.sum_nonneg; intro y _
      apply Finset.sum_nonneg; intro X hX
      apply mul_nonneg (hη_nn X (Finset.mem_filter.mp hX).1)
      apply Finset.sum_nonneg; intro j hj
      have hj' : j < m + 1 := Finset.mem_range.mp hj
      exact mul_nonneg (ih j (by omega) X) (ih (m - j) (by omega) S)

/-- **Lemma A.1 (Knuth Forest Catalan Bound)**:
For any finite hypergraph `E` with `∀ X ∈ E, X.card ≤ r`, nonnegative weights `η`, and site bound
`∀ x, ∑_{X ∋ x} η X ≤ η₀`, every site set `S` with `S.card ≤ r` satisfies
`forestSum E η m S ≤ catalanRec m * (r * η₀)^m`. -/
theorem lemma_A_1_concrete_forest_sum {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X ≤ η₀) :
    ∀ m : ℕ, ∀ S : Finset (Fin N), S.card ≤ r →
      forestSum E η m S ≤ (catalanRec m : ℝ) * ((r : ℝ) * η₀) ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hS
    cases m with
    | zero => simp [forestSum, catalanRec]
    | succ m =>
      rw [forestSum_succ]
      have hterm : ∀ y ∈ S, ∀ X ∈ E.filter (fun X ↦ y ∈ X),
          η X * (∑ j ∈ Finset.range (m + 1), forestSum E η j X * forestSum E η (m - j) S) ≤
          η X * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) := by
        intro y _ X hX
        have hXE : X ∈ E := (Finset.mem_filter.mp hX).1
        apply mul_le_mul_of_nonneg_left _ (hη_nn X hXE)
        calc ∑ j ∈ Finset.range (m + 1), forestSum E η j X * forestSum E η (m - j) S
            ≤ ∑ j ∈ Finset.range (m + 1),
              ((catalanRec j : ℝ) * ((r : ℝ) * η₀) ^ j) *
              ((catalanRec (m - j) : ℝ) * ((r : ℝ) * η₀) ^ (m - j)) := by
              apply Finset.sum_le_sum; intro j hj
              have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              exact mul_le_mul (ih j (by omega) X (hcard X hXE))
                (ih (m - j) (by omega) S hS)
                (forestSum_nonneg E η hη_nn (m - j) S) (by positivity)
          _ = ∑ j ∈ Finset.range (m + 1),
              ((catalanRec j : ℝ) * (catalanRec (m - j) : ℝ)) * ((r : ℝ) * η₀) ^ m := by
              apply Finset.sum_congr rfl; intro j hj
              have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hexp : ((r : ℝ) * η₀) ^ j * ((r : ℝ) * η₀) ^ (m - j) = ((r : ℝ) * η₀) ^ m := by
                rw [← pow_add, Nat.add_sub_cancel' hj']
              linear_combination (catalanRec j : ℝ) * (catalanRec (m - j) : ℝ) * hexp
          _ = (∑ j ∈ Finset.range (m + 1), (catalanRec j : ℝ) * (catalanRec (m - j) : ℝ)) *
              ((r : ℝ) * η₀) ^ m := by rw [← Finset.sum_mul]
          _ = (catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m := by
              rw [catalanRec_succ]; simp only [Nat.cast_sum, Nat.cast_mul]
      calc ∑ y ∈ S, ∑ X ∈ E.filter (fun X ↦ y ∈ X),
            η X * (∑ j ∈ Finset.range (m + 1), forestSum E η j X * forestSum E η (m - j) S)
          ≤ ∑ y ∈ S, ∑ X ∈ E.filter (fun X ↦ y ∈ X),
            η X * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) :=
            Finset.sum_le_sum fun y hy ↦ Finset.sum_le_sum fun X hX ↦ hterm y hy X hX
        _ = ∑ y ∈ S, (∑ X ∈ E.filter (fun X ↦ y ∈ X), η X) *
            ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) := by
            apply Finset.sum_congr rfl; intro y _; rw [← Finset.sum_mul]
        _ ≤ ∑ _y ∈ S, η₀ * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m) := by
            apply Finset.sum_le_sum; intro y _
            exact mul_le_mul_of_nonneg_right (hsite y) (by positivity)
        _ = (S.card : ℝ) * (η₀ * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (r : ℝ) * (η₀ * ((catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ m)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)
        _ = (catalanRec (m + 1) : ℝ) * ((r : ℝ) * η₀) ^ (m + 1) := by
            rw [pow_succ]; ring

/-- Rooted forest exponential bound with sharp constant `4^(m - 1)` for `m ≥ 1`. -/
theorem lemma_A_1_concrete_rooted_forest_exp_bound {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X ≤ η₀)
    {m : ℕ} (hm : 1 ≤ m) (x : Fin N) :
    ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X * forestSum E η (m - 1) X ≤
      (4 : ℝ) ^ (m - 1) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
  calc ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X * forestSum E η (m - 1) X
      ≤ ∑ X ∈ E.filter (fun X ↦ x ∈ X),
          η X * ((catalanRec (m - 1) : ℝ) * ((r : ℝ) * η₀) ^ (m - 1)) := by
        apply Finset.sum_le_sum; intro X hX
        exact mul_le_mul_of_nonneg_left
          (lemma_A_1_concrete_forest_sum E hcard η hη_nn hη₀ hsite (m - 1) X
            (hcard X (Finset.mem_filter.mp hX).1))
          (hη_nn X (Finset.mem_filter.mp hX).1)
    _ = (∑ X ∈ E.filter (fun X ↦ x ∈ X), η X) *
          ((catalanRec (m - 1) : ℝ) * ((r : ℝ) * η₀) ^ (m - 1)) := by rw [← Finset.sum_mul]
    _ ≤ η₀ * ((catalanRec (m - 1) : ℝ) * ((r : ℝ) * η₀) ^ (m - 1)) :=
        mul_le_mul_of_nonneg_right (hsite x) (by positivity)
    _ ≤ η₀ * ((4 : ℝ) ^ (m - 1) * ((r : ℝ) * η₀) ^ (m - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hη₀
        exact mul_le_mul_of_nonneg_right (catalanRec_le_four_pow (m - 1)) (by positivity)
    _ = (4 : ℝ) ^ (m - 1) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by ring

end LemmaA1Concrete

section LemmaA2Concrete

/-- Concrete ordered causal hyperedge sequence weight sum `causalSeqSum E w k U`:
sum of `∏_{j=1}^k w(X_j)` over all length-`k` causal sequences `[X_1, ..., X_k]` in `E`
starting from initial support `U` (where each `X_{j+1}` intersects `U ∪ X_1 ∪ ... ∪ X_j`). -/
noncomputable def causalSeqSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (w : Finset (Fin N) → ℝ) : ℕ → Finset (Fin N) → ℝ
  | 0, _ => 1
  | k + 1, U =>
    ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X * causalSeqSum E w k (U ∪ X)

lemma causalSeqSum_nonneg {N : ℕ} (E : Finset (Finset (Fin N)))
    (w : Finset (Fin N) → ℝ) (hw_nn : ∀ X ∈ E, 0 ≤ w X) :
    ∀ k : ℕ, ∀ U : Finset (Fin N), 0 ≤ causalSeqSum E w k U := by
  intro k
  induction k with
  | zero => intro _; simp [causalSeqSum]
  | succ k ih =>
    intro U
    rw [causalSeqSum]
    exact Finset.sum_nonneg fun X hX ↦
      mul_nonneg (hw_nn X (Finset.mem_filter.mp hX).1) (ih (U ∪ X))

/-- Union bound over overlapping hyperedges:
`∑_{X ∈ E, U ∩ X ≠ ∅} w X ≤ |U| * Jsite`. -/
lemma sum_overlapping_le {N : ℕ} (E : Finset (Finset (Fin N)))
    (w : Finset (Fin N) → ℝ) (hw_nn : ∀ X ∈ E, 0 ≤ w X)
    {Jsite : ℝ} (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X ≤ Jsite)
    (U : Finset (Fin N)) :
    ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X ≤ (U.card : ℝ) * Jsite := by
  have h1 : ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X ≤
      ∑ x ∈ U, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X := by
    have h2 : ∑ x ∈ U, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X =
        ∑ X ∈ E, ((U ∩ X).card : ℝ) * w X := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro X _
      have hset : U.filter (fun x ↦ x ∈ X) = U ∩ X := by ext x; simp [Finset.mem_inter]
      rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul]
    rw [h2, Finset.sum_filter]
    apply Finset.sum_le_sum; intro X hX
    by_cases hne : (U ∩ X).Nonempty
    · rw [if_pos hne]
      have hge1 : (1 : ℝ) ≤ ((U ∩ X).card : ℝ) := by
        exact_mod_cast Finset.Nonempty.card_pos hne
      nlinarith [hw_nn X hX]
    · rw [if_neg hne]
      exact mul_nonneg (Nat.cast_nonneg _) (hw_nn X hX)
  calc ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X
      ≤ ∑ x ∈ U, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X := h1
    _ ≤ ∑ _x ∈ U, Jsite := Finset.sum_le_sum fun x _ ↦ hsite x
    _ = (U.card : ℝ) * Jsite := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Concrete Forward Causal Sequence Bound (used in Lemma 2.1, Zero `hcayley` Hypothesis)**:
For any finite hypergraph `E` with `∀ X ∈ E, X.card ≤ r` and nonnegative weights `w` with
`∀ x, ∑_{X ∋ x} w X ≤ Jsite`, the concrete length-`k` causal sequence weight sum satisfies:
`causalSeqSum E w k U ≤ (∏ j ∈ Finset.range k, (|U| + j * (r - 1))) * Jsite ^ k`
(for `r ≥ 1`). -/
theorem lemma_A_2_concrete_causal_seq_sum {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (w : Finset (Fin N) → ℝ) (hw_nn : ∀ X ∈ E, 0 ≤ w X)
    {Jsite : ℝ} (hJ : 0 ≤ Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X ≤ Jsite) :
    ∀ k : ℕ, ∀ U : Finset (Fin N),
      causalSeqSum E w k U ≤
        (∏ j ∈ Finset.range k, ((U.card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ k := by
  intro k
  induction k with
  | zero => intro U; simp [causalSeqSum]
  | succ k ih =>
    intro U
    rw [causalSeqSum]
    have hstep : ∀ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty),
        w X * causalSeqSum E w k (U ∪ X) ≤
        w X * ((∏ j ∈ Finset.range k,
          (((U.card : ℝ) + ((r - 1 : ℕ) : ℝ)) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ k) := by
      intro X hX
      have hXE : X ∈ E := (Finset.mem_filter.mp hX).1
      have hne : (U ∩ X).Nonempty := (Finset.mem_filter.mp hX).2
      apply mul_le_mul_of_nonneg_left _ (hw_nn X hXE)
      have hU_card : ((U ∪ X).card : ℝ) ≤ (U.card : ℝ) + ((r - 1 : ℕ) : ℝ) := by
        have h1 : (U ∪ X).card + (U ∩ X).card = U.card + X.card := Finset.card_union_add_card_inter U X
        have h2 : 1 ≤ (U ∩ X).card := Finset.Nonempty.card_pos hne
        have h3 : X.card ≤ r := hcard X hXE
        have hnat : (U ∪ X).card ≤ U.card + (r - 1) := by omega
        exact_mod_cast hnat
      have hih := ih (U ∪ X)
      refine le_trans hih (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hJ k))
      apply real_prod_le_prod_cc
      · intro j _; positivity
      · intro j _; linarith
    calc ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X * causalSeqSum E w k (U ∪ X)
        ≤ ∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty),
          w X * ((∏ j ∈ Finset.range k,
            (((U.card : ℝ) + ((r - 1 : ℕ) : ℝ)) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ k) :=
          Finset.sum_le_sum hstep
      _ = (∑ X ∈ E.filter (fun X ↦ (U ∩ X).Nonempty), w X) *
          ((∏ j ∈ Finset.range k,
            (((U.card : ℝ) + ((r - 1 : ℕ) : ℝ)) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ k) := by
          rw [← Finset.sum_mul]
      _ ≤ ((U.card : ℝ) * Jsite) *
          ((∏ j ∈ Finset.range k,
            (((U.card : ℝ) + ((r - 1 : ℕ) : ℝ)) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ k) := by
          apply mul_le_mul_of_nonneg_right (sum_overlapping_le E w hw_nn hsite U)
          exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ by positivity) (pow_nonneg hJ k)
      _ = (∏ j ∈ Finset.range (k + 1), ((U.card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) *
          Jsite ^ (k + 1) := by
          rw [Finset.prod_range_succ', pow_succ]
          have hprod : (∏ j ∈ Finset.range k,
              ((U.card : ℝ) + ((j + 1 : ℕ) : ℝ) * ((r - 1 : ℕ) : ℝ))) =
              ∏ j ∈ Finset.range k,
                (((U.card : ℝ) + ((r - 1 : ℕ) : ℝ)) + (j : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
            apply Finset.prod_congr rfl; intro j _; push_cast; ring
          rw [hprod]
          simp only [Nat.cast_zero, zero_mul, add_zero]
          ring

end LemmaA2Concrete

section LemmaA3Concrete

/-- Concrete depth-`h` unordered rooted hypergraph tree sum `unorderedTreeSum E η h X`
(Galton–Watson / Kotecký–Preiss tree-graph upper bound on connected polymer weights). -/
noncomputable def unorderedTreeSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) : ℕ → Finset (Fin N) → ℝ
  | 0, X => η X
  | h + 1, X =>
    η X * ∏ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), (1 + unorderedTreeSum E η h Y)

lemma unorderedTreeSum_nonneg {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X) :
    ∀ h : ℕ, ∀ X ∈ E, 0 ≤ unorderedTreeSum E η h X := by
  intro h
  induction h with
  | zero => intro X hX; exact hη_nn X hX
  | succ h ih =>
    intro X hX
    rw [unorderedTreeSum]
    exact mul_nonneg (hη_nn X hX)
      (Finset.prod_nonneg fun Y hY ↦ by linarith [ih Y (Finset.mem_filter.mp hY).1])

/-- **Lemma A.3 (Concrete Unordered Rooted Tree Sum Bound, Zero Abstract `S` Hypothesis)**:
For any finite hypergraph `E` with `∀ X ∈ E, X.card ≤ r`, nonnegative edge weights `η` with
`∀ x, ∑_{Y ∈ E, x ∈ Y} η Y ≤ η₀`, and any `c ≥ 0` satisfying `η₀ * Real.exp (c * r) ≤ c`:
for every depth `h : ℕ` and every hyperedge `X ∈ E`,
`unorderedTreeSum E η h X ≤ η X * Real.exp (c * |X|)`. -/
theorem lemma_A_3_concrete_unordered_tree_sum {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ c : ℝ} (hc : 0 ≤ c)
    (hsite : ∀ x : Fin N, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y), η Y ≤ η₀)
    (hcond : η₀ * Real.exp (c * (r : ℝ)) ≤ c) :
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
      apply real_prod_le_prod_cc
      · intro Y hY; linarith [unorderedTreeSum_nonneg E η hη_nn h Y (Finset.mem_filter.mp hY).1]
      · intro Y _; linarith [Real.add_one_le_exp (unorderedTreeSum E η h Y)]
    rw [← Real.exp_sum] at hprod_exp
    refine le_trans hprod_exp (Real.exp_le_exp.mpr ?_)
    have hsum_le : ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), unorderedTreeSum E η h Y ≤
        ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), η Y * Real.exp (c * (r : ℝ)) := by
      apply Finset.sum_le_sum; intro Y hY
      have hYE : Y ∈ E := (Finset.mem_filter.mp hY).1
      have h1 := ih Y hYE
      have h2 : Real.exp (c * (Y.card : ℝ)) ≤ Real.exp (c * (r : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc
        exact_mod_cast hcard Y hYE
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (hη_nn Y hYE))
    calc ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), unorderedTreeSum E η h Y
        ≤ ∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), η Y * Real.exp (c * (r : ℝ)) := hsum_le
      _ = (∑ Y ∈ E.filter (fun Y ↦ (X ∩ Y).Nonempty), η Y) * Real.exp (c * (r : ℝ)) := by
          rw [← Finset.sum_mul]
      _ ≤ ((X.card : ℝ) * η₀) * Real.exp (c * (r : ℝ)) := by
          apply mul_le_mul_of_nonneg_right (sum_overlapping_le E η hη_nn hsite X)
            (Real.exp_pos _).le
      _ = (X.card : ℝ) * (η₀ * Real.exp (c * (r : ℝ))) := by ring
      _ ≤ (X.card : ℝ) * c := mul_le_mul_of_nonneg_left hcond (Nat.cast_nonneg _)
      _ = c * (X.card : ℝ) := by ring

end LemmaA3Concrete

end KrylovChaos
