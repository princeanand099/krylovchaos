/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.SupportAndDualFrame
import KrylovChaos.CausalNormBounds
import KrylovChaos.Araki1DConcrete
import KrylovChaos.Milestone3Sections678
import Mathlib.Tactic

/-!
# All-Temperature One-Dimensional Araki Bound and Proposition 8.1 (Eq. 8.1)

Proves Araki's 1969 all-temperature complex-time norm bound for one-dimensional finite-range
quantum spin chains strictly on top of Mathlib `v4.35.0`, with zero custom axioms and zero
`sorry`s, and wires it directly into Proposition 8.1 (Eq. 8.1):
1. `oneDimBall` and `shellOp`: decomposes a 1D range-`r` Hamiltonian `H = ∑ X ∈ E, h X` into
   concentric range-`r` shells `W_0, W_1, …, W_N` around a base site `x : Fin N` with uniform
   shell norm `opNorm (W_k) ≤ 2 * r * J` and range-1 shell causality (`[W_j, B] = 0` whenever
   `B ∈ supportedOn (oneDimBall N r x s)` and `s + 1 < j`).
2. `card_valid1DWords_eq_le`: proves by induction on `m` using Pascal's identity that the number
   of causally valid shell words `w : Fin m → Fin (N + 1)` reaching maximum shell `k ≤ m` is
   at most `m.choose k * (k + 1) ^ (m - k)`.
3. `araki1D_series_summable_and_le`: sums the majorant series over all `m ≥ 0` to obtain
   `∑' m, (a^m / m!) * ∑_{k ≤ m} (m.choose k) * (k + 1)^(m - k) ≤ exp (a * (1 + exp a))`
   for EVERY `a ≥ 0` (entire in complex time `z ∈ ℂ`).
4. `heisenbergEvol_1d_all_temp_bound`: proves for ANY `z : ℂ`, ANY `β : ℝ`, ANY `N : ℕ`,
   `r ≥ 1`, and 1D range-`r` Hermitian Hamiltonian `H = ∑ X ∈ E, h X` (site strength `≤ J`),
   `opNorm (heisenbergEvol hH z O) ≤ opNorm O * exp (4 * r * J * ‖z‖ * (1 + exp (4 * r * J * ‖z‖)))`.
5. `prop_8_1_araki_1d_unconditional`: proves Proposition 8.1 (Eq. 8.1) at ALL temperatures
   `β : ℝ` with the explicit `N`-independent constant
   `araki1DM β r J = exp (r * J * |β| * (1 + exp (r * J * |β|)))`.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section OneDimShellDecomposition

/-- One-dimensional ball of radius `k * r` around site `x : Fin N`. -/
def oneDimBall (N r : ℕ) (x : Fin N) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun y : Fin N ↦ y.val ≤ x.val + k * r ∧ x.val ≤ y.val + k * r)

lemma oneDimBall_zero (N r : ℕ) (x : Fin N) :
    oneDimBall N r x 0 = {x} := by
  ext y
  simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and, zero_mul, add_zero,
    Finset.mem_singleton]
  constructor
  · intro ⟨h1, h2⟩; exact Fin.ext (by omega)
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩

lemma oneDimBall_mono (N r : ℕ) (x : Fin N) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    oneDimBall N r x k₁ ⊆ oneDimBall N r x k₂ := by
  intro y hy
  simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  have hmul : k₁ * r ≤ k₂ * r := Nat.mul_le_mul_right r hk
  exact ⟨by omega, by omega⟩

lemma oneDimBall_full (N r : ℕ) (hr : 1 ≤ r) (x : Fin N) :
    oneDimBall N r x N = Finset.univ := by
  ext y
  simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  have hNr : N ≤ N * r := Nat.le_mul_of_pos_right N (by omega)
  exact ⟨by omega, by omega⟩

/-- The `k`-th concentric 1D annulus `oneDimBall N r x (k + 1) \ oneDimBall N r x k` has
at most `2 * r` sites. -/
lemma card_oneDimAnnulus_le (N r : ℕ) (x : Fin N) (k : ℕ) :
    (oneDimBall N r x (k + 1) \ oneDimBall N r x k).card ≤ 2 * r := by
  let A := oneDimBall N r x (k + 1) \ oneDimBall N r x k
  let L := A.filter (fun y : Fin N ↦ y.val < x.val)
  let R := A.filter (fun y : Fin N ↦ x.val ≤ y.val)
  have hcard_split : A.card = L.card + R.card := by
    have hunion : L ∪ R = A := by
      ext y; simp only [L, R, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases lt_or_ge y.val x.val with hlt | hge
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, hge⟩
    have hdisj : Disjoint L R := by
      rw [Finset.disjoint_left]; intro y h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hL_le : L.card ≤ r := by
    have hinj : Set.InjOn (fun y : Fin N ↦ y.val + (k + 1) * r - x.val) (L : Set (Fin N)) := by
      intro a ha b hb heq
      have haA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
      have hbA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
      simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at haA hbA
      dsimp only at heq
      exact Fin.ext (by omega)
    have himg : L.image (fun y : Fin N ↦ y.val + (k + 1) * r - x.val) ⊆ Finset.range r := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨y, hy, rfl⟩
      rcases Finset.mem_filter.mp hy with ⟨hyA, hylt⟩
      rcases Finset.mem_sdiff.mp hyA with ⟨hy1, hy2⟩
      simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      have hmul : (k + 1) * r = k * r + r := by ring
      rw [Finset.mem_range]; omega
    calc L.card = (L.image (fun y : Fin N ↦ y.val + (k + 1) * r - x.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range r).card := Finset.card_le_card himg
      _ = r := Finset.card_range r
  have hR_le : R.card ≤ r := by
    have hinj : Set.InjOn (fun y : Fin N ↦ x.val + (k + 1) * r - y.val) (R : Set (Fin N)) := by
      intro a ha b hb heq
      have haA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
      have hbA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
      simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at haA hbA
      dsimp only at heq
      exact Fin.ext (by omega)
    have himg : R.image (fun y : Fin N ↦ x.val + (k + 1) * r - y.val) ⊆ Finset.range r := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨y, hy, rfl⟩
      rcases Finset.mem_filter.mp hy with ⟨hyA, hyge⟩
      rcases Finset.mem_sdiff.mp hyA with ⟨hy1, hy2⟩
      simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      have hmul : (k + 1) * r = k * r + r := by ring
      rw [Finset.mem_range]; omega
    calc R.card = (R.image (fun y : Fin N ↦ x.val + (k + 1) * r - y.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range r).card := Finset.card_le_card himg
      _ = r := Finset.card_range r
  change A.card ≤ 2 * r
  omega

/-- Interactions in `E` belonging to the `k`-th concentric 1D shell around `x`. -/
def shellEdges {N : ℕ} (E : Finset (Finset (Fin N))) (r : ℕ) (x : Fin N) :
    ℕ → Finset (Finset (Fin N))
  | 0 => E.filter (fun X ↦ X ⊆ oneDimBall N r x 0)
  | k + 1 => E.filter (fun X ↦ X ⊆ oneDimBall N r x (k + 1) ∧ ¬(X ⊆ oneDimBall N r x k))

/-- The `k`-th concentric 1D shell Hamiltonian operator `W_k` around `x`. -/
def shellOp {N : ℕ} (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N)
    (r : ℕ) (x : Fin N) (k : ℕ) : QubitOp N :=
  ∑ X ∈ shellEdges E r x k, h X

lemma shellEdges_pairwiseDisjoint {N : ℕ} (E : Finset (Finset (Fin N))) (r : ℕ) (x : Fin N) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (N + 1))))
      (fun k : Fin (N + 1) ↦ shellEdges E r x k.val) := by
  intro k₁ _ k₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro X hX₁ hX₂
  have hlt_or : k₁.val < k₂.val ∨ k₂.val < k₁.val :=
    lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h))
  rcases hlt_or with hlt | hlt
  · have hk₂ : ∃ j, k₂.val = j + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    rcases hk₂ with ⟨j, hj⟩
    rw [hj] at hX₂
    have hsub1 : X ⊆ oneDimBall N r x k₁.val := by
      cases hk1 : k₁.val with
      | zero => rw [hk1] at hX₁; exact (Finset.mem_filter.mp hX₁).2
      | succ m => rw [hk1] at hX₁; exact (Finset.mem_filter.mp hX₁).2.1
    have hnot : ¬(X ⊆ oneDimBall N r x j) := (Finset.mem_filter.mp hX₂).2.2
    exact hnot (Finset.Subset.trans hsub1 (oneDimBall_mono N r x (by omega)))
  · have hk₁ : ∃ j, k₁.val = j + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    rcases hk₁ with ⟨j, hj⟩
    rw [hj] at hX₁
    have hsub2 : X ⊆ oneDimBall N r x k₂.val := by
      cases hk2 : k₂.val with
      | zero => rw [hk2] at hX₂; exact (Finset.mem_filter.mp hX₂).2
      | succ m => rw [hk2] at hX₂; exact (Finset.mem_filter.mp hX₂).2.1
    have hnot : ¬(X ⊆ oneDimBall N r x j) := (Finset.mem_filter.mp hX₁).2.2
    exact hnot (Finset.Subset.trans hsub2 (oneDimBall_mono N r x (by omega)))

lemma biUnion_shellEdges_eq {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (x : Fin N) :
    (Finset.univ : Finset (Fin (N + 1))).biUnion (fun k ↦ shellEdges E r x k.val) = E := by
  classical
  ext X
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hXk⟩
    cases hk : k.val with
    | zero => rw [hk] at hXk; exact (Finset.mem_filter.mp hXk).1
    | succ m => rw [hk] at hXk; exact (Finset.mem_filter.mp hXk).1
  · intro hXE
    have hex : ∃ k : ℕ, X ⊆ oneDimBall N r x k :=
      ⟨N, by rw [oneDimBall_full N r hr x]; exact Finset.subset_univ X⟩
    let k₀ := Nat.find hex
    have hk₀_sub : X ⊆ oneDimBall N r x k₀ := Nat.find_spec hex
    have hk₀_le : k₀ ≤ N := Nat.find_min' hex (by rw [oneDimBall_full N r hr x]; exact Finset.subset_univ X)
    refine ⟨⟨k₀, Nat.lt_succ_of_le hk₀_le⟩, ?_⟩
    dsimp only
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · rw [h0]; exact Finset.mem_filter.mpr ⟨hXE, h0 ▸ hk₀_sub⟩
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      rw [hm]
      exact Finset.mem_filter.mpr ⟨hXE, hm ▸ hk₀_sub, Nat.find_min hex (by omega)⟩

/-- Exact shell partition of the Hamiltonian: `∑ X ∈ E, h X = ∑ k : Fin (N + 1), shellOp E h r x k.val`. -/
lemma sum_h_eq_sum_shellOp {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N) (x : Fin N) :
    ∑ X ∈ E, h X = ∑ k : Fin (N + 1), shellOp E h r x k.val := by
  conv_lhs => rw [← biUnion_shellEdges_eq hr E x]
  rw [Finset.sum_biUnion (shellEdges_pairwiseDisjoint E r x)]
  rfl

/-- Uniform-in-`k` and uniform-in-`N` operator-norm bound on every 1D shell:
`opNorm (shellOp E h r x k) ≤ 2 * r * J`. -/
lemma opNorm_shellOp_le {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (x : Fin N) (k : ℕ) :
    opNorm (shellOp E h r x k) ≤ 2 * (r : ℝ) * J := by
  cases k with
  | zero =>
    have hsub : shellEdges E r x 0 ⊆ E.filter (fun X ↦ x ∈ X) := by
      intro X hX
      rcases Finset.mem_filter.mp hX with ⟨hXE, hXsub⟩
      rw [oneDimBall_zero] at hXsub
      rcases (h1d X hXE).1 with ⟨y, hyX⟩
      have hyx : y = x := Finset.mem_singleton.mp (hXsub hyX)
      exact Finset.mem_filter.mpr ⟨hXE, hyx ▸ hyX⟩
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    calc opNorm (shellOp E h r x 0)
        ≤ ∑ X ∈ shellEdges E r x 0, opNorm (h X) := opNorm_sum_le _ _
      _ ≤ ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ opNorm_nonneg _
      _ ≤ J := hsite x
      _ ≤ 2 * (r : ℝ) * J := by nlinarith
  | succ k =>
    let ann := oneDimBall N r x (k + 1) \ oneDimBall N r x k
    have hsub : shellEdges E r x (k + 1) ⊆ ann.biUnion (fun y ↦ E.filter (fun X ↦ y ∈ X)) := by
      intro X hX
      rcases Finset.mem_filter.mp hX with ⟨hXE, hX1, hXnot⟩
      rw [Finset.not_subset] at hXnot
      rcases hXnot with ⟨y, hyX, hyNot⟩
      exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hX1 hyX, hyNot⟩,
        Finset.mem_filter.mpr ⟨hXE, hyX⟩⟩
    calc opNorm (shellOp E h r x (k + 1))
        ≤ ∑ X ∈ shellEdges E r x (k + 1), opNorm (h X) := opNorm_sum_le _ _
      _ ≤ ∑ X ∈ ann.biUnion (fun y ↦ E.filter (fun X ↦ y ∈ X)), opNorm (h X) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ opNorm_nonneg _
      _ ≤ ∑ y ∈ ann, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) :=
          real_sum_biUnion_le _ _ _ (fun _ _ ↦ opNorm_nonneg _)
      _ ≤ ∑ _y ∈ ann, J := Finset.sum_le_sum fun y _ ↦ hsite y
      _ = (ann.card : ℝ) * J := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * r : ℝ) * J := by
          apply mul_le_mul_of_nonneg_right _ hJ
          exact_mod_cast card_oneDimAnnulus_le N r x k
      _ = 2 * (r : ℝ) * J := by ring

/-- Support of `shellOp E h r x k` is contained in `oneDimBall N r x k`. -/
lemma shellOp_mem_supportedOn {N : ℕ}
    (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (r : ℕ) (x : Fin N) (k : ℕ) :
    shellOp E h r x k ∈ supportedOn (oneDimBall N r x k) := by
  unfold shellOp
  apply Submodule.sum_mem
  intro X hX
  have hXsub : X ⊆ oneDimBall N r x k := by
    cases k with
    | zero => exact (Finset.mem_filter.mp hX).2
    | succ m => exact (Finset.mem_filter.mp hX).2.1
  exact supportedOn_mono hXsub (hsupp X)

/-- **1D Shell Causality**: if `B ∈ supportedOn (oneDimBall N r x s)` and `s + 1 < j`, then
`matComm (shellOp E h r x j) B = 0`. -/
lemma matComm_shellOp_eq_zero_of_gt {N r : ℕ}
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (x : Fin N) {s j : ℕ} (hsj : s + 1 < j)
    {B : QubitOp N} (hB : B ∈ supportedOn (oneDimBall N r x s)) :
    matComm (shellOp E h r x j) B = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  unfold shellOp matComm
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro X hX
  rcases Finset.mem_filter.mp hX with ⟨hXE, _, hXnot⟩
  have hdisj : Disjoint X (oneDimBall N r x s) := by
    rw [Finset.disjoint_left]
    intro a haX haS
    apply hXnot
    intro b hbX
    have hab1 : b.val < a.val + r := (h1d X hXE).2 b hbX a haX
    have hab2 : a.val < b.val + r := (h1d X hXE).2 a haX b hbX
    simp only [oneDimBall, Finset.mem_filter, Finset.mem_univ, true_and] at haS ⊢
    have hsm : (s + 1) * r ≤ m * r := Nat.mul_le_mul_right r (by omega)
    have hsr : (s + 1) * r = s * r + r := by ring
    exact ⟨by omega, by omega⟩
  rw [supportedOn_comm_of_disjoint hdisj (hsupp X) hB, sub_self]

end OneDimShellDecomposition

section Valid1DWordCombinatorics

/-- Iterated commutator along a word `w : Fin m → Fin (N + 1)` of shell operators `W`. -/
def iterShellComm {N : ℕ} (W : Fin (N + 1) → QubitOp N) :
    ∀ {m : ℕ}, (Fin m → Fin (N + 1)) → QubitOp N → QubitOp N
  | 0, _, O => O
  | m + 1, w, O => matComm (W (w (Fin.last m))) (iterShellComm W (Fin.init w) O)

/-- Running maximum shell index along a word `w : Fin m → Fin (N + 1)`. -/
def wordRunMax {N : ℕ} : ∀ {m : ℕ}, (Fin m → Fin (N + 1)) → ℕ
  | 0, _ => 0
  | m + 1, w => max (wordRunMax (Fin.init w)) (w (Fin.last m)).val

/-- Causal validity of a 1D shell word: each step extends the frontier by at most `1`. -/
def isValid1DWord {N : ℕ} : ∀ {m : ℕ}, (Fin m → Fin (N + 1)) → Prop
  | 0, _ => True
  | m + 1, w => isValid1DWord (Fin.init w) ∧ (w (Fin.last m)).val ≤ wordRunMax (Fin.init w) + 1

instance instDecidableIsValid1DWord {N : ℕ} : ∀ {m : ℕ} (w : Fin m → Fin (N + 1)),
    Decidable (isValid1DWord w)
  | 0, _ => isTrue trivial
  | _ + 1, w => @instDecidableAnd _ _ (instDecidableIsValid1DWord (Fin.init w)) (Nat.decLe _ _)

lemma wordRunMax_le_len {N : ℕ} : ∀ {m : ℕ} (w : Fin m → Fin (N + 1)),
    isValid1DWord w → wordRunMax w ≤ m
  | 0, _, _ => le_rfl
  | m + 1, w, hw => by
    have ih := wordRunMax_le_len (Fin.init w) hw.1
    have hstep := hw.2
    simp only [wordRunMax, max_le_iff]
    omega

/-- Exact expansion of `adPowMat (∑ k, W k) m O` as a sum over shell words `w : Fin m → Fin (N + 1)`. -/
lemma adPowMat_sum_eq_sum_iterShellComm {N : ℕ} (W : Fin (N + 1) → QubitOp N) (O : QubitOp N) :
    ∀ m : ℕ, adPowMat (∑ k : Fin (N + 1), W k) m O =
      ∑ w : Fin m → Fin (N + 1), iterShellComm W w O
  | 0 => by
    simp only [adPowMat]
    have hsing : (Finset.univ : Finset (Fin 0 → Fin (N + 1))) = {Fin.elim0} := by
      ext w; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext j; exact Fin.elim0 j
    rw [hsing, Finset.sum_singleton]; rfl
  | m + 1 => by
    rw [adPowMat, adPowMat_sum_eq_sum_iterShellComm W O m]
    have hcomm_sum : matComm (∑ k : Fin (N + 1), W k) (∑ w : Fin m → Fin (N + 1), iterShellComm W w O) =
        ∑ p : (Fin m → Fin (N + 1)) × Fin (N + 1), matComm (W p.2) (iterShellComm W p.1 O) := by
      unfold matComm
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      trans ∑ k : Fin (N + 1), ∑ w : Fin m → Fin (N + 1),
          (W k * iterShellComm W w O - iterShellComm W w O * W k)
      · apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      · rw [Finset.sum_comm]
        exact (Fintype.sum_prod_type (fun p : (Fin m → Fin (N + 1)) × Fin (N + 1) ↦
          W p.2 * iterShellComm W p.1 O - iterShellComm W p.1 O * W p.2)).symm
    rw [hcomm_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective (fun p : (Fin m → Fin (N + 1)) × Fin (N + 1) ↦ Fin.snoc p.1 p.2)
      ⟨fun p₁ p₂ heq ↦ by
        apply Prod.ext
        · funext i
          have h := congrFun heq i.castSucc
          simpa [Fin.snoc_castSucc] using h
        · have h := congrFun heq (Fin.last m)
          simpa [Fin.snoc_last] using h,
      fun w ↦ ⟨(Fin.init w, w (Fin.last m)), by
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [Fin.snoc_last]
        · simp [Fin.snoc_castSucc, Fin.init]⟩⟩) _ _ fun p ↦ ?_
    change matComm (W p.2) (iterShellComm W p.1 O) =
      matComm (W (Fin.snoc p.1 p.2 (Fin.last m))) (iterShellComm W (Fin.init (Fin.snoc p.1 p.2)) O)
    rw [Fin.snoc_last, Fin.init_snoc]

/-- Support preservation and vanishing outside causally valid 1D words. -/
lemma iterShellComm_support_and_vanish {N r : ℕ}
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (x : Fin N) {O : QubitOp N} (hO : O ∈ supportedOn (oneDimBall N r x 0)) :
    ∀ {m : ℕ} (w : Fin m → Fin (N + 1)),
      (isValid1DWord w →
        iterShellComm (fun k : Fin (N + 1) ↦ shellOp E h r x k.val) w O ∈
          supportedOn (oneDimBall N r x (wordRunMax w))) ∧
      (¬isValid1DWord w →
        iterShellComm (fun k : Fin (N + 1) ↦ shellOp E h r x k.val) w O = 0)
  | 0, _ => ⟨fun _ ↦ hO, fun hnot ↦ absurd trivial hnot⟩
  | m + 1, w => by
    have ih := iterShellComm_support_and_vanish E h1d h hsupp x hO (Fin.init w)
    constructor
    · intro hw
      have h1 := ih.1 hw.1
      have hW : shellOp E h r x (w (Fin.last m)).val ∈
          supportedOn (oneDimBall N r x (wordRunMax w)) :=
        supportedOn_mono (oneDimBall_mono N r x (le_max_right _ _))
          (shellOp_mem_supportedOn E h hsupp r x (w (Fin.last m)).val)
      have hB : iterShellComm (fun k : Fin (N + 1) ↦ shellOp E h r x k.val) (Fin.init w) O ∈
          supportedOn (oneDimBall N r x (wordRunMax w)) :=
        supportedOn_mono (oneDimBall_mono N r x (le_max_left _ _)) h1
      simp only [iterShellComm, matComm]
      exact Submodule.sub_mem _ (supportedOn_mul_mem hW hB) (supportedOn_mul_mem hB hW)
    · intro hnot
      simp only [iterShellComm]
      by_cases hinit : isValid1DWord (Fin.init w)
      · have hgt : wordRunMax (Fin.init w) + 1 < (w (Fin.last m)).val := by
          have : ¬((w (Fin.last m)).val ≤ wordRunMax (Fin.init w) + 1) :=
            fun hle ↦ hnot ⟨hinit, hle⟩
          omega
        exact matComm_shellOp_eq_zero_of_gt E h1d h hsupp x hgt (ih.1 hinit)
      · rw [ih.2 hinit]
        simp [matComm]

/-- Operator-norm bound on each shell word `iterShellComm W w O`. -/
lemma opNorm_iterShellComm_le {N : ℕ} (W : Fin (N + 1) → QubitOp N)
    {M : ℝ} (hM : 0 ≤ M) (hW : ∀ k, opNorm (W k) ≤ M) (O : QubitOp N) :
    ∀ {m : ℕ} (w : Fin m → Fin (N + 1)),
      opNorm (iterShellComm W w O) ≤ (2 * M) ^ m * opNorm O
  | 0, _ => by simp [iterShellComm]
  | m + 1, w => by
    simp only [iterShellComm, matComm]
    have ih := opNorm_iterShellComm_le W hM hW O (Fin.init w)
    have hWk := hW (w (Fin.last m))
    calc opNorm (W (w (Fin.last m)) * iterShellComm W (Fin.init w) O -
            iterShellComm W (Fin.init w) O * W (w (Fin.last m)))
        ≤ opNorm (W (w (Fin.last m)) * iterShellComm W (Fin.init w) O) +
          opNorm (iterShellComm W (Fin.init w) O * W (w (Fin.last m))) := by
            have hsub : ∀ X Y : QubitOp N, opNorm (X - Y) ≤ opNorm X + opNorm Y := fun X Y ↦ by
              calc opNorm (X - Y) = opNorm (X + (-1 : ℂ) • Y) := by rw [neg_one_smul, sub_eq_add_neg]
                _ ≤ opNorm X + opNorm ((-1 : ℂ) • Y) := opNorm_add_le _ _
                _ = opNorm X + opNorm Y := by rw [opNorm_smul, norm_neg, norm_one, one_mul]
            exact hsub _ _
      _ ≤ opNorm (W (w (Fin.last m))) * opNorm (iterShellComm W (Fin.init w) O) +
          opNorm (iterShellComm W (Fin.init w) O) * opNorm (W (w (Fin.last m))) :=
          add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
      _ = 2 * opNorm (W (w (Fin.last m))) * opNorm (iterShellComm W (Fin.init w) O) := by ring
      _ ≤ 2 * M * ((2 * M) ^ m * opNorm O) :=
          mul_le_mul (by linarith) ih (opNorm_nonneg _) (by positivity)
      _ = (2 * M) ^ (m + 1) * opNorm O := by rw [pow_succ']; ring

/-- **Inductive Valid-Word Counting Bound**:
For every `m k : ℕ`, the number of causally valid 1D shell words `w : Fin m → Fin (N + 1)`
with `wordRunMax w = k` is at most `m.choose k * (k + 1) ^ (m - k)`. -/
lemma card_valid1DWords_eq_le (N : ℕ) :
    ∀ m k : ℕ,
      (Finset.univ.filter (fun w : Fin m → Fin (N + 1) ↦ isValid1DWord w ∧ wordRunMax w = k)).card ≤
        m.choose k * (k + 1) ^ (m - k) := by
  intro m
  induction m with
  | zero =>
    intro k
    cases k with
    | zero =>
      calc (Finset.univ.filter (fun w : Fin 0 → Fin (N + 1) ↦ isValid1DWord w ∧ wordRunMax w = 0)).card
          ≤ (Finset.univ : Finset (Fin 0 → Fin (N + 1))).card := Finset.card_filter_le _ _
        _ = 1 := by simp
        _ = Nat.choose 0 0 * (0 + 1) ^ (0 - 0) := by simp
    | succ k =>
      have hemp : Finset.univ.filter (fun w : Fin 0 → Fin (N + 1) ↦ isValid1DWord w ∧ wordRunMax w = k + 1) = ∅ := by
        ext w; simp [wordRunMax]
      rw [hemp, Finset.card_empty]; exact Nat.zero_le _
  | succ m ih =>
    intro k
    let S := Finset.univ.filter (fun w : Fin (m + 1) → Fin (N + 1) ↦ isValid1DWord w ∧ wordRunMax w = k)
    let S_stay := S.filter (fun w ↦ wordRunMax (Fin.init w) = k)
    let S_grow := S.filter (fun w ↦ wordRunMax (Fin.init w) ≠ k)
    have hsplit : S.card = S_stay.card + S_grow.card := by
      have hunion : S_stay ∪ S_grow = S := by
        ext w; simp only [S_stay, S_grow, Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint S_stay S_grow := by
        rw [Finset.disjoint_left]; intro w h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    -- Bound `S_stay.card ≤ (k + 1) * v(m, k)`.
    let Vmk := Finset.univ.filter (fun u : Fin m → Fin (N + 1) ↦ isValid1DWord u ∧ wordRunMax u = k)
    have hstay_le : S_stay.card ≤ Vmk.card * (k + 1) := by
      have hinj : Set.InjOn (fun w : Fin (m + 1) → Fin (N + 1) ↦ (Fin.init w, (w (Fin.last m)).val))
          (S_stay : Set (Fin (m + 1) → Fin (N + 1))) := by
        intro w₁ _ w₂ _ heq
        have h1 : Fin.init w₁ = Fin.init w₂ := congrArg Prod.fst heq
        have h2 : w₁ (Fin.last m) = w₂ (Fin.last m) := Fin.ext (congrArg Prod.snd heq)
        funext i
        refine Fin.lastCases h2 (fun j ↦ ?_) i
        exact congrFun h1 j
      have himg : S_stay.image (fun w ↦ (Fin.init w, (w (Fin.last m)).val)) ⊆
          Vmk ×ˢ Finset.range (k + 1) := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨w, hw, rfl⟩
        rcases Finset.mem_filter.mp hw with ⟨hwS, hinit_eq⟩
        rcases Finset.mem_filter.mp hwS with ⟨_, hwv, hwmax⟩
        rw [Finset.mem_product, Finset.mem_range]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv.1, hinit_eq⟩, ?_⟩
        simp only [wordRunMax] at hwmax
        omega
      calc S_stay.card
          = (S_stay.image (fun w ↦ (Fin.init w, (w (Fin.last m)).val))).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Vmk ×ˢ Finset.range (k + 1)).card := Finset.card_le_card himg
        _ = Vmk.card * (k + 1) := by rw [Finset.card_product, Finset.card_range]
    cases k with
    | zero =>
      have hgrow_empty : S_grow = ∅ := by
        ext w
        simp only [S_grow, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro ⟨_, hwmax⟩ hne
        simp only [wordRunMax] at hwmax
        omega
      rw [hsplit, hgrow_empty, Finset.card_empty, add_zero]
      have hih0 := ih 0
      calc S_stay.card ≤ Vmk.card * 1 := hstay_le
        _ = Vmk.card := mul_one _
        _ ≤ m.choose 0 * (0 + 1) ^ (m - 0) := hih0
        _ = (m + 1).choose 0 * (0 + 1) ^ (m + 1 - 0) := by simp
    | succ k =>
      -- Bound `S_grow.card ≤ v(m, k)`.
      let Vmk' := Finset.univ.filter (fun u : Fin m → Fin (N + 1) ↦ isValid1DWord u ∧ wordRunMax u = k)
      have hgrow_le : S_grow.card ≤ Vmk'.card := by
        have hinj : Set.InjOn (fun w : Fin (m + 1) → Fin (N + 1) ↦ Fin.init w)
            (S_grow : Set (Fin (m + 1) → Fin (N + 1))) := by
          intro w₁ hw₁ w₂ hw₂ heq
          rcases Finset.mem_filter.mp hw₁ with ⟨hw₁S, hne₁⟩
          rcases Finset.mem_filter.mp hw₂ with ⟨hw₂S, hne₂⟩
          rcases Finset.mem_filter.mp hw₁S with ⟨_, _, hmax₁⟩
          rcases Finset.mem_filter.mp hw₂S with ⟨_, _, hmax₂⟩
          simp only [wordRunMax] at hmax₁ hmax₂
          have hlast₁ : (w₁ (Fin.last m)).val = k + 1 := by omega
          have hlast₂ : (w₂ (Fin.last m)).val = k + 1 := by omega
          funext i
          refine Fin.lastCases (Fin.ext (by omega)) (fun j ↦ congrFun heq j) i
        have himg : S_grow.image (fun w ↦ Fin.init w) ⊆ Vmk' := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
          rcases Finset.mem_filter.mp hw with ⟨hwS, hne⟩
          rcases Finset.mem_filter.mp hwS with ⟨_, hwv, hwmax⟩
          simp only [wordRunMax] at hwmax
          have hstep := hwv.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv.1, by omega⟩
        calc S_grow.card = (S_grow.image (fun w ↦ Fin.init w)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ Vmk'.card := Finset.card_le_card himg
      by_cases hkm : k + 1 ≤ m
      · have hih1 := ih (k + 1)
        have hih2 := ih k
        have hpow1 : (k + 1 + 1) ^ (m - (k + 1)) * (k + 1 + 1) = (k + 1 + 1) ^ (m + 1 - (k + 1)) := by
          rw [show m + 1 - (k + 1) = (m - (k + 1)) + 1 by omega, pow_succ]
        have hpow2 : (k + 1) ^ (m - k) ≤ (k + 1 + 1) ^ (m + 1 - (k + 1)) := by
          rw [show m + 1 - (k + 1) = m - k by omega]
          exact Nat.pow_le_pow_left (by omega) _
        calc S.card = S_stay.card + S_grow.card := hsplit
          _ ≤ Vmk.card * (k + 1 + 1) + Vmk'.card := Nat.add_le_add hstay_le hgrow_le
          _ ≤ (m.choose (k + 1) * (k + 1 + 1) ^ (m - (k + 1))) * (k + 1 + 1) +
              m.choose k * (k + 1) ^ (m - k) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hih1) hih2
          _ = m.choose (k + 1) * (k + 1 + 1) ^ (m + 1 - (k + 1)) +
              m.choose k * (k + 1) ^ (m - k) := by rw [mul_assoc, hpow1]
          _ ≤ m.choose (k + 1) * (k + 1 + 1) ^ (m + 1 - (k + 1)) +
              m.choose k * (k + 1 + 1) ^ (m + 1 - (k + 1)) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ hpow2) _
          _ = (m.choose k + m.choose (k + 1)) * (k + 1 + 1) ^ (m + 1 - (k + 1)) := by ring
          _ = (m + 1).choose (k + 1) * (k + 1 + 1) ^ (m + 1 - (k + 1)) := by
              rw [Nat.choose_succ_succ]
      · -- `m < k + 1`, so `Vmk = ∅` (since `wordRunMax u ≤ m` for valid `u : Fin m → _`).
        have hVmk_empty : Vmk = ∅ := by
          ext u; simp only [Vmk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro hu hmax; have := wordRunMax_le_len u hu; omega
        have hstay_zero : S_stay.card = 0 := by
          rw [hVmk_empty, Finset.card_empty, zero_mul] at hstay_le; omega
        rw [hsplit, hstay_zero, zero_add]
        by_cases hkeq : k = m
        · subst hkeq
          have hih2 := ih k
          calc S_grow.card ≤ Vmk'.card := hgrow_le
            _ ≤ k.choose k * (k + 1) ^ (k - k) := hih2
            _ = (k + 1).choose (k + 1) * (k + 1 + 1) ^ (k + 1 - (k + 1)) := by simp
        · have hVmk'_empty : Vmk' = ∅ := by
            ext u; simp only [Vmk', Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro hu hmax; have := wordRunMax_le_len u hu; omega
          rw [hVmk'_empty, Finset.card_empty] at hgrow_le
          omega

end Valid1DWordCombinatorics

section ArakiSeriesAndAllTempBound

/-- **Double-Exponential Majorant Series Bound**:
For EVERY `a ≥ 0`, the series
`∑' m, (a ^ m / m!) * ∑ k ∈ Finset.range (m + 1), (m.choose k) * (k + 1) ^ (m - k)`
converges and is bounded by `Real.exp (a * (1 + Real.exp a))`. -/
lemma araki1D_series_summable_and_le {a : ℝ} (ha : 0 ≤ a) :
    let f : ℕ → ℝ := fun m ↦
      (a ^ m / (m.factorial : ℝ)) *
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))
    Summable f ∧ ∑' m : ℕ, f m ≤ Real.exp (a * (1 + Real.exp a)) := by
  intro f
  have hf_nn : ∀ m : ℕ, 0 ≤ f m := fun m ↦ by
    dsimp only [f]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun k _ ↦ by positivity
  have hpart : ∀ M : ℕ, ∑ m ∈ Finset.range M, f m ≤ Real.exp (a * (1 + Real.exp a)) := by
    intro M
    have hterm_eq : ∀ m k : ℕ, k ≤ m →
        (a ^ m / (m.factorial : ℝ)) * ((m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))) =
          (a ^ k / (k.factorial : ℝ)) * ((a * (k + 1 : ℝ)) ^ (m - k) / ((m - k).factorial : ℝ)) := by
      intro m k hkm
      have hch : (m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) = (m.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
      have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
      have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      have hmkf : ((m - k).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (m - k)).ne'
      have hpow : a ^ m = a ^ k * a ^ (m - k) := by rw [← pow_add, Nat.add_sub_of_le hkm]
      rw [hpow, mul_pow]
      have hch_div : (m.choose k : ℝ) / (m.factorial : ℝ) =
          1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
        rw [div_eq_div_iff hmf (mul_ne_zero hkf hmkf)]
        linarith
      calc a ^ k * a ^ (m - k) / (m.factorial : ℝ) * ((m.choose k : ℝ) * (k + 1 : ℝ) ^ (m - k))
          = ((m.choose k : ℝ) / (m.factorial : ℝ)) *
              (a ^ k * (a ^ (m - k) * (k + 1 : ℝ) ^ (m - k))) := by ring
        _ = (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ))) *
              (a ^ k * (a ^ (m - k) * (k + 1 : ℝ) ^ (m - k))) := by rw [hch_div]
        _ = a ^ k / (k.factorial : ℝ) * (a ^ (m - k) * (k + 1 : ℝ) ^ (m - k) / ((m - k).factorial : ℝ)) := by ring
    let g : ℕ × ℕ → ℝ := fun p ↦
      (a ^ p.1 / (p.1.factorial : ℝ)) * ((a * (p.1 + 1 : ℝ)) ^ p.2 / (p.2.factorial : ℝ))
    let T : Finset (ℕ × ℕ) := (Finset.range M).sigma (fun m ↦ Finset.range (m + 1)) |>.image
      (fun p ↦ (p.2, p.1 - p.2))
    have hsum_eq_T : ∑ m ∈ Finset.range M, f m = ∑ p ∈ T, g p := by
      have h1 : ∑ m ∈ Finset.range M, f m =
          ∑ p ∈ (Finset.range M).sigma (fun m ↦ Finset.range (m + 1)), g (p.2, p.1 - p.2) := by
        rw [Finset.sum_sigma]
        apply Finset.sum_congr rfl; intro m _
        dsimp only [f]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k hk
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact hterm_eq m k hkm
      rw [h1]
      symm
      refine Finset.sum_image fun p₁ hp₁ p₂ hp₂ heq ↦ ?_
      rcases Finset.mem_sigma.mp hp₁ with ⟨_, hk₁⟩
      rcases Finset.mem_sigma.mp hp₂ with ⟨_, hk₂⟩
      have hle₁ : p₁.2 ≤ p₁.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₁)
      have hle₂ : p₂.2 ≤ p₂.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₂)
      have hfst : p₁.2 = p₂.2 := congrArg Prod.fst heq
      have hsnd : p₁.1 - p₁.2 = p₂.1 - p₂.2 := congrArg Prod.snd heq
      exact Sigma.ext (by omega) (heq_of_eq hfst)
    have hT_sub : T ⊆ Finset.range M ×ˢ Finset.range M := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      rcases Finset.mem_sigma.mp hp with ⟨hm, hk⟩
      rw [Finset.mem_range] at hm hk
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    calc ∑ m ∈ Finset.range M, f m
        = ∑ p ∈ T, g p := hsum_eq_T
      _ ≤ ∑ p ∈ Finset.range M ×ˢ Finset.range M, g p :=
          Finset.sum_le_sum_of_subset_of_nonneg hT_sub fun p _ _ ↦ by dsimp only [g]; positivity
      _ = ∑ k ∈ Finset.range M, (a ^ k / (k.factorial : ℝ)) *
            ∑ n ∈ Finset.range M, (a * (k + 1 : ℝ)) ^ n / (n.factorial : ℝ) := by
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range M, (a ^ k / (k.factorial : ℝ)) * Real.exp (a * (k + 1 : ℝ)) := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left
            (Real.sum_le_exp_of_nonneg (by positivity) M) (by positivity)
      _ = Real.exp a * ∑ k ∈ Finset.range M, (a * Real.exp a) ^ k / (k.factorial : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          rw [mul_pow, ← Real.exp_nat_mul]
          have hexp : Real.exp (a * (k + 1 : ℝ)) = Real.exp a * Real.exp ((k : ℝ) * a) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp]; ring
      _ ≤ Real.exp a * Real.exp (a * Real.exp a) :=
          mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) M) (Real.exp_pos _).le
      _ = Real.exp (a * (1 + Real.exp a)) := by
          rw [← Real.exp_add]; congr 1; ring
  have hsumm : Summable f := summable_of_sum_range_le hf_nn hpart
  exact ⟨hsumm, hsumm.tsum_le_of_sum_range_le hpart⟩

/-- **Araki's 1969 All-Temperature 1D Complex-Time Norm Bound**:
For ANY `N : ℕ`, ANY `r ≥ 1`, ANY 1D range-`r` Hermitian Hamiltonian `H = ∑ X ∈ E, h X`
with local site strength `≤ J`, ANY site `x : Fin N`, ANY single-site observable
`O ∈ supportedOn {x}`, and ANY complex time `z : ℂ`:
`opNorm (heisenbergEvol hH z O) ≤ opNorm O * Real.exp (4 * r * J * ‖z‖ * (1 + Real.exp (4 * r * J * ‖z‖)))`. -/
theorem heisenbergEvol_1d_all_temp_bound {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (x : Fin N) {O : QubitOp N} (hO : O ∈ supportedOn {x})
    (z : ℂ) :
    let a := 4 * (r : ℝ) * J * ‖z‖
    opNorm (heisenbergEvol hH z O) ≤ opNorm O * Real.exp (a * (1 + Real.exp a)) := by
  intro a
  have ha_nn : 0 ≤ a := by dsimp only [a]; positivity
  let W : Fin (N + 1) → QubitOp N := fun k ↦ shellOp E h r x k.val
  have hH_eq : ∑ X ∈ E, h X = ∑ k : Fin (N + 1), W k := sum_h_eq_sum_shellOp hr E h x
  have hW_norm : ∀ k : Fin (N + 1), opNorm (W k) ≤ 2 * (r : ℝ) * J :=
    fun k ↦ opNorm_shellOp_le hr E h1d h hJ hsite x k.val
  have hO0 : O ∈ supportedOn (oneDimBall N r x 0) := by
    rw [oneDimBall_zero]; exact hO
  have had_bound : ∀ m : ℕ,
      opNorm (adPowMat (∑ X ∈ E, h X) m O) ≤
        opNorm O * ((4 * (r : ℝ) * J) ^ m *
          ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))) := by
    intro m
    rw [hH_eq, adPowMat_sum_eq_sum_iterShellComm W O m]
    let validAll := Finset.univ.filter (fun w : Fin m → Fin (N + 1) ↦ isValid1DWord w)
    have hsum_valid : ∑ w : Fin m → Fin (N + 1), iterShellComm W w O =
        ∑ w ∈ validAll, iterShellComm W w O := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun w _ hw ↦ ?_
      have hnot : ¬isValid1DWord w := fun hv ↦ hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hv⟩)
      exact (iterShellComm_support_and_vanish E h1d h hsupp x hO0 w).2 hnot
    rw [hsum_valid]
    have hcard_valid : (validAll.card : ℝ) ≤
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k)) := by
      have hnat : validAll.card ≤
          ∑ k ∈ Finset.range (m + 1), m.choose k * (k + 1) ^ (m - k) := by
        have hfib : validAll.card = ∑ k ∈ Finset.range (m + 1), (validAll.filter (fun w ↦ wordRunMax w = k)).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
            (g := fun w : Fin m → Fin (N + 1) ↦ wordRunMax w) (t := Finset.range (m + 1))]
          · apply Finset.sum_congr rfl; intro k _; rw [Finset.card_eq_sum_ones]
          · intro w hw; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (wordRunMax_le_len w (Finset.mem_filter.mp hw).2))
        rw [hfib]
        apply Finset.sum_le_sum; intro k _
        have hfilt_eq : validAll.filter (fun w ↦ wordRunMax w = k) =
            Finset.univ.filter (fun w : Fin m → Fin (N + 1) ↦ isValid1DWord w ∧ wordRunMax w = k) := by
          ext w; simp only [validAll, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hfilt_eq]
        exact card_valid1DWords_eq_le N m k
      exact_mod_cast hnat
    have hM_nn : 0 ≤ 2 * (r : ℝ) * J := by positivity
    calc opNorm (∑ w ∈ validAll, iterShellComm W w O)
        ≤ ∑ w ∈ validAll, opNorm (iterShellComm W w O) := opNorm_sum_le _ _
      _ ≤ ∑ _w ∈ validAll, (2 * (2 * (r : ℝ) * J)) ^ m * opNorm O :=
          Finset.sum_le_sum fun w _ ↦ opNorm_iterShellComm_le W hM_nn hW_norm O w
      _ = (validAll.card : ℝ) * ((4 * (r : ℝ) * J) ^ m * opNorm O) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))) *
            ((4 * (r : ℝ) * J) ^ m * opNorm O) :=
          mul_le_mul_of_nonneg_right hcard_valid (mul_nonneg (by positivity) (opNorm_nonneg O))
      _ = opNorm O * ((4 * (r : ℝ) * J) ^ m *
            ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))) := by ring
  let f : ℕ → ℝ := fun m ↦
    (a ^ m / (m.factorial : ℝ)) *
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k))
  have hterm : ∀ m : ℕ,
      opNorm (((Complex.I * z) ^ m / (m.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) m O) ≤
        opNorm O * f m := by
    intro m
    rw [opNorm_smul]
    have hcoeff : ‖(Complex.I * z) ^ m / (m.factorial : ℂ)‖ = ‖z‖ ^ m / (m.factorial : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
    rw [hcoeff]
    calc ‖z‖ ^ m / (m.factorial : ℝ) * opNorm (adPowMat (∑ X ∈ E, h X) m O)
        ≤ ‖z‖ ^ m / (m.factorial : ℝ) *
            (opNorm O * ((4 * (r : ℝ) * J) ^ m *
              ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k + 1 : ℝ) ^ (m - k)))) :=
          mul_le_mul_of_nonneg_left (had_bound m) (by positivity)
      _ = opNorm O * f m := by
          dsimp only [f, a]; rw [mul_pow]; ring
  rcases araki1D_series_summable_and_le ha_nn with ⟨hsumm_f, htsum_f⟩
  have hsumm_norm : Summable (fun m : ℕ ↦
      opNorm (((Complex.I * z) ^ m / (m.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) m O)) :=
    Summable.of_nonneg_of_le (fun _ ↦ opNorm_nonneg _) hterm (hsumm_f.mul_left _)
  have hhas := hasSum_heisenbergEvol_adPow hH z O
  let φ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
    LinearMap.toContinuousLinearMap
      { toFun := opToCLM
        map_add' := opToCLM_add
        map_smul' := fun c A ↦ by simp [opToCLM_smul] }
  have hhas_clm := hhas.map φ φ.continuous
  calc opNorm (heisenbergEvol hH z O)
      = ‖∑' m : ℕ, opToCLM (((Complex.I * z) ^ m / (m.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) m O)‖ := by
        unfold opNorm
        change ‖φ (heisenbergEvol hH z O)‖ = _
        rw [← hhas_clm.tsum_eq]
        rfl
    _ ≤ ∑' m : ℕ, opNorm (((Complex.I * z) ^ m / (m.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) m O) :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' m : ℕ, opNorm O * f m :=
        hsumm_norm.tsum_le_tsum hterm (hsumm_f.mul_left _)
    _ = opNorm O * ∑' m : ℕ, f m := tsum_mul_left
    _ ≤ opNorm O * Real.exp (a * (1 + Real.exp a)) :=
        mul_le_mul_of_nonneg_left htsum_f (opNorm_nonneg O)

/-- Explicit `N`-independent all-temperature 1D Araki constant
`M_1D(β, r, J) = exp (r * J * |β| * (1 + exp (r * J * |β|)))`. -/
noncomputable def araki1DM (β : ℝ) (r : ℕ) (J : ℝ) : ℝ :=
  Real.exp ((r : ℝ) * J * |β| * (1 + Real.exp ((r : ℝ) * J * |β|)))

lemma araki1DM_nonneg (β : ℝ) (r : ℕ) (J : ℝ) : 0 ≤ araki1DM β r J :=
  (Real.exp_pos _).le

/-- Single-site Pauli imaginary-time evolution bound at ALL temperatures `β : ℝ`, uniform in `N`. -/
theorem opNorm_heisenbergEvol_pauliSite_1d_all_temp {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (β : ℝ) (x : Fin N) (α : Fin 3) :
    opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤
      araki1DM β r J ∧
    opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤
      araki1DM β r J := by
  have hpauli_supp : pauliSite x α.succ ∈ supportedOn {x} := pauliSite_mem_supportedOn x α
  have hpauli_norm : opNorm (pauliSite x α.succ) ≤ 1 := opNorm_pauliSite_le x α
  have hnorm_pos : ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ = |β| / 4 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div]
    norm_num
  have hnorm_neg : ‖-(Complex.I * ((β / 4 : ℝ) : ℂ))‖ = |β| / 4 := by
    rw [norm_neg, hnorm_pos]
  have ha_eq : 4 * (r : ℝ) * J * (|β| / 4) = (r : ℝ) * J * |β| := by ring
  constructor
  · have h1 := heisenbergEvol_1d_all_temp_bound hr E h1d h hsupp hH hJ hsite x hpauli_supp
      (Complex.I * ((β / 4 : ℝ) : ℂ))
    rw [hnorm_pos, ha_eq] at h1
    exact le_trans h1 (by
      dsimp only [araki1DM]
      simpa using mul_le_mul_of_nonneg_right hpauli_norm
        (Real.exp_pos ((r : ℝ) * J * |β| * (1 + Real.exp ((r : ℝ) * J * |β|)))).le)
  · have h2 := heisenbergEvol_1d_all_temp_bound hr E h1d h hsupp hH hJ hsite x hpauli_supp
      (-(Complex.I * ((β / 4 : ℝ) : ℂ)))
    rw [hnorm_neg, ha_eq] at h2
    exact le_trans h2 (by
      dsimp only [araki1DM]
      simpa using mul_le_mul_of_nonneg_right hpauli_norm
        (Real.exp_pos ((r : ℝ) * J * |β| * (1 + Real.exp ((r : ℝ) * J * |β|)))).le)

/-- **Proposition 8.1 (All-Temperature 1D Finite-Range Bounds, Eq. 8.1)**:
For ANY `N : ℕ`, ANY `r ≥ 1`, ANY 1D finite-range Hermitian Hamiltonian `H = ∑ X ∈ E, h X`
with local site strength `≤ J`, ANY inverse temperature `β : ℝ`, and EVERY observable `A : QubitOp N`:
1. `otocCW G A ≤ (3 / 2) * (araki1DM β r J) ^ 2 * Re (A | 𝒬̃^{(β)} A)_β^W`,
2. Under the 1D reverse-Poincaré bound `Re (A | 𝒬̃^{(β)} A)_β^W ≤ C_RP * Re (A | 𝒬^{(β)} A)_β^W`:
   `otocCW G A ≤ (3 / 2) * (araki1DM β r J) ^ 2 * C_RP * Re (A | 𝒬^{(β)} A)_β^W`,
where `araki1DM β r J = exp (r * J * |β| * (1 + exp (r * J * |β|)))` is strictly independent of `N`. -/
theorem prop_8_1_araki_1d_unconditional {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (β : ℝ) (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β r J) ^ 2 *
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ∧
    (∀ C_RP : ℝ,
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
        C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re →
      otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β r J) ^ 2 * C_RP *
        (gibbsWightmanInner G A (wightmanQ G A)).re) :=
  prop_8_1_araki_1d_exact_eq_8_1 hH β (araki1DM_nonneg β r J)
    (opNorm_heisenbergEvol_pauliSite_1d_all_temp hr E h1d h hsupp hH hJ hsite β) A

end ArakiSeriesAndAllTempBound

end KrylovChaos
