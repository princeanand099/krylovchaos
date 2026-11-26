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
1. **Lemma A.1 (`lemma_A_1_concrete_bin_tree_sum`)**: Concrete binary-encoded plane hypergraph
   tree weight sum `binTreeSum E η m x` rooted at site `x`, proved by strong induction on `m`
   via the Catalan recurrence `C_m = ∑_{j=0}^{m-1} C_j C_{m-1-j}`:
   `binTreeSum E η m x ≤ catalanRec m * (r * η₀)^(m - 1) * η₀ ≤ 4^m * (r * η₀)^(m - 1) * η₀`.
2. **Lemma A.2 (`lemma_A_2_concrete_causal_seq_sum`)**: Concrete ordered causal hyperedge
   sequence weight sum `causalSeqSum E w k U`, proved by induction on `k`:
   `causalSeqSum E w k U ≤ (∏ j ∈ Finset.range k, (|U| + j * (r - 1))) * Jsite ^ k`.
3. **Lemma A.3 (`lemma_A_3_concrete_unordered_tree_sum`)**: Concrete Galton–Watson / Kotecký–Preiss
   unordered rooted hypergraph tree sum `unorderedTreeSum E η h X`, proved by induction on depth
   `h`: if `η₀ * exp(c * r) ≤ c`, then `unorderedTreeSum E η h X ≤ η X * exp(c * |X|)`.
-/

namespace KrylovChaos

section CatalanRecurrence

/-- Catalan numbers defined via the Segner recurrence `C_0 = 1`,
`C_{n+1} = ∑_{j=0}^n C_j * C_{n - j}`. -/
def catalanRec : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1), catalanRec j * catalanRec (n - j)

lemma catalanRec_eq_nat_catalan (n : ℕ) : catalanRec n = Nat.catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [catalanRec, Nat.catalan_succ]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ Nat.catalan i * Nat.catalan j)]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < n + 1 := Finset.mem_range.mp hj
      rw [ih j (by omega), ih (n - j) (by omega)]

lemma catalanRec_le_four_pow (n : ℕ) : (catalanRec n : ℝ) ≤ (4 : ℝ) ^ n := by
  rw [catalanRec_eq_nat_catalan]
  have h1 : Nat.catalan n = Nat.centralBinom n / (n + 1) := Nat.catalan_eq_centralBinom_div n
  have h2 : Nat.centralBinom n / (n + 1) ≤ Nat.centralBinom n := Nat.div_le_self _ _
  have h3 : Nat.centralBinom n ≤ 4 ^ n := by
    rw [Nat.centralBinom]
    have hsum := Nat.sum_range_choose (2 * n)
    have hmem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    have hle : Nat.choose (2 * n) n ≤ ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
    rw [hsum] at hle
    have hpow : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    omega
  exact_mod_cast (h1 ▸ le_trans h2 h3)

end CatalanRecurrence

section LemmaA1Concrete

/-- Concrete binary-encoded plane hypergraph tree weight sum of size `m` anchored at site `x`. -/
noncomputable def binTreeSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (η : Finset (Fin N) → ℝ) : ℕ → Fin N → ℝ
  | 0, _ => 1
  | m + 1, x =>
    ∑ X ∈ E.filter (fun X ↦ x ∈ X),
      η X * ∑ j ∈ Finset.range (m + 1),
        (if j = 0 then 1 else ∑ y ∈ X, binTreeSum E η j y) *
        (if m - j = 0 then 1 else ∑ z ∈ X, binTreeSum E η (m - j) z)
termination_by m _ => m

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
      rw [binTreeSum]
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
`binTreeSum E η m x ≤ catalanRec m * (r * η₀)^(m - 1) * η₀ ≤ 4^m * (r * η₀)^(m - 1) * η₀`. -/
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
      rw [binTreeSum]
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
              simp only [catalanRec, Nat.cast_sum, Nat.cast_mul]
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

/-- Corollary of Lemma A.1: exponential bound `binTreeSum E η m x ≤ 4^m * (r * η₀)^(m - 1) * η₀`. -/
theorem lemma_A_1_concrete_exp_bound {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (η : Finset (Fin N) → ℝ) (hη_nn : ∀ X ∈ E, 0 ≤ η X)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), η X ≤ η₀)
    {m : ℕ} (hm : 1 ≤ m) (x : Fin N) :
    binTreeSum E η m x ≤ (4 : ℝ) ^ m * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
  have h1 := lemma_A_1_concrete_bin_tree_sum E hcard η hη_nn hη₀ hsite m hm x
  have h2 := catalanRec_le_four_pow m
  have h3 : (catalanRec m : ℝ) * ((r : ℝ) * η₀) ^ (m - 1) * η₀ ≤
      (4 : ℝ) ^ m * ((r : ℝ) * η₀) ^ (m - 1) * η₀ := by
    apply mul_le_mul_of_nonneg_right _ hη₀
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  exact le_trans h1 h3

end LemmaA1Concrete

section LemmaA2Concrete

/-- Concrete ordered causal hyperedge sequence weight sum `causalSeqSum E w k U`. -/
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

/-- Union bound over overlapping hyperedges: `∑_{X ∈ E, U ∩ X ≠ ∅} w X ≤ |U| * Jsite`. -/
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
      have hcard : (∑ x ∈ U, if x ∈ X then w X else 0) = ((U ∩ X).card : ℝ) * w X := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 2
        ext x; simp [Finset.mem_inter]
      exact hcard
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

/-- **Lemma A.2 (Concrete Forward Causal Sequence Bound, Zero `hcayley` Hypothesis)**:
`causalSeqSum E w k U ≤ (∏ j ∈ Finset.range k, (|U| + j * (r - 1))) * Jsite ^ k`. -/
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
      apply Finset.prod_le_prod
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

/-- Concrete depth-`h` unordered rooted hypergraph tree sum `unorderedTreeSum E η h X`. -/
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
If `η₀ * Real.exp (c * r) ≤ c` (`c ≥ 0`), then for every depth `h` and hyperedge `X ∈ E`,
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
      apply Finset.prod_le_prod
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
