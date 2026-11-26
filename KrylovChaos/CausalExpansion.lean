/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.MultiSiteCommutator

/-!
# Concrete Imaginary-Time Causal Expansion & Reverse-Causal Sum Bound

Proves the eigenbasis expansion `hasSum_heisenbergEvol_adPow` of `heisenbergEvol hH z B`
into iterated commutators `adPowMat H k B`, causal-sequence support/norm bounds,
`fwdCausalSum_le`, and the inductive Cayley root-reversal bound `revCausalSum_le`.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section CausalExpansionAndThm13bOtocI

/-- Iterated matrix commutator `adPowMat H k B = [H, [H, ..., [H, B]...]]`. -/
def adPowMat {N : ℕ} (H : QubitOp N) : ℕ → QubitOp N → QubitOp N
  | 0, B => B
  | k + 1, B => matComm H (adPowMat H k B)

lemma adPowMat_eigen_entry {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (B : QubitOp N) :
    ∀ (k : ℕ) (a b : QubitIdx N),
      ((hH.eigenvectorUnitary : QubitOp N)ᴴ * adPowMat H k B *
        (hH.eigenvectorUnitary : QubitOp N)) a b =
        ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ) ^ k *
          ((hH.eigenvectorUnitary : QubitOp N)ᴴ * B * (hH.eigenvectorUnitary : QubitOp N)) a b := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hUHU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hH_diag : Uᴴ * H * U = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
    have hs : H = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := (hermFunc_id hH).symm
    conv_lhs => rw [hs]
    calc Uᴴ * (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by rw [hUHU, Matrix.one_mul, Matrix.mul_one]
  intro k
  induction k with
  | zero => intro a b; simp [adPowMat]
  | succ k ih =>
    intro a b
    rw [adPowMat, matComm]
    have h1 : Uᴴ * (H * adPowMat H k B) * U = (Uᴴ * H * U) * (Uᴴ * adPowMat H k B * U) := by
      calc Uᴴ * (H * adPowMat H k B) * U
          = Uᴴ * H * (1 * adPowMat H k B) * U := by noncomm_ring
        _ = Uᴴ * H * ((U * Uᴴ) * adPowMat H k B) * U := by rw [hUU]
        _ = (Uᴴ * H * U) * (Uᴴ * adPowMat H k B * U) := by noncomm_ring
    have h2 : Uᴴ * (adPowMat H k B * H) * U = (Uᴴ * adPowMat H k B * U) * (Uᴴ * H * U) := by
      calc Uᴴ * (adPowMat H k B * H) * U
          = Uᴴ * adPowMat H k B * (1 * H) * U := by noncomm_ring
        _ = Uᴴ * adPowMat H k B * ((U * Uᴴ) * H) * U := by rw [hUU]
        _ = (Uᴴ * adPowMat H k B * U) * (Uᴴ * H * U) := by noncomm_ring
    have hsplit : Uᴴ * (H * adPowMat H k B - adPowMat H k B * H) * U =
        (Uᴴ * H * U) * (Uᴴ * adPowMat H k B * U) - (Uᴴ * adPowMat H k B * U) * (Uᴴ * H * U) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    rw [hsplit, hH_diag, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, ih a b]
    push_cast; ring

private lemma conj_hermFunc_mul_hermFunc {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (f g : ℝ → ℂ) (B : QubitOp N) (a b : QubitIdx N) :
    ((hH.eigenvectorUnitary : QubitOp N)ᴴ * (hermFunc hH f * B * hermFunc hH g) *
      (hH.eigenvectorUnitary : QubitOp N)) a b =
      f (hH.eigenvalues a) * g (hH.eigenvalues b) *
        ((hH.eigenvectorUnitary : QubitOp N)ᴴ * B * (hH.eigenvectorUnitary : QubitOp N)) a b := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hUHU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hmat : Uᴴ * (hermFunc hH f * B * hermFunc hH g) * U =
      Matrix.diagonal (fun k ↦ f (hH.eigenvalues k)) * (Uᴴ * B * U) *
        Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) := by
    unfold hermFunc
    calc Uᴴ * (U * Matrix.diagonal (fun k ↦ f (hH.eigenvalues k)) * Uᴴ * B *
          (U * Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) * Uᴴ)) * U
        = (Uᴴ * U) * Matrix.diagonal (fun k ↦ f (hH.eigenvalues k)) * (Uᴴ * B * U) *
            Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun k ↦ f (hH.eigenvalues k)) * (Uᴴ * B * U) *
            Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) := by
          rw [hUHU, Matrix.one_mul, Matrix.mul_one]
  rw [hmat, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring

/-- **Concrete Eigenbasis Power-Series Expansion of `heisenbergEvol hH z B`**:
`heisenbergEvol hH z B = ∑' k, ((i z)^k / k!) • adPowMat H k B`. -/
lemma hasSum_heisenbergEvol_adPow {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (B : QubitOp N) :
    HasSum (fun k : ℕ ↦ ((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat H k B)
      (heisenbergEvol hH z B) := by
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hconj : ∀ X : QubitOp N, X = U * (Uᴴ * X * U) * Uᴴ := fun X ↦ by
    calc X = 1 * X * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (U * Uᴴ) * X * (U * Uᴴ) := by rw [hUU]
      _ = U * (Uᴴ * X * U) * Uᴴ := by simp only [Matrix.mul_assoc]
  have hmul3 : ∀ (A M C : QubitOp N) (i j : QubitIdx N),
      (A * M * C) i j = ∑ a : QubitIdx N, ∑ b : QubitIdx N, A i a * M a b * C b j := by
    intro A M C i j
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat_entry : ∀ (X : QubitOp N) (i j : QubitIdx N),
      X i j = ∑ a : QubitIdx N, ∑ b : QubitIdx N, U i a * (Uᴴ * X * U) a b * Uᴴ b j := by
    intro X i j
    conv_lhs => rw [hconj X]
    exact hmul3 U (Uᴴ * X * U) Uᴴ i j
  change HasSum (fun k (i j : QubitIdx N) ↦ (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat H k B) i j) (fun i j ↦ heisenbergEvol hH z B i j)
  rw [Pi.hasSum]; intro i; rw [Pi.hasSum]; intro j
  have hlhs_entry : ∀ k : ℕ,
      (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat H k B) i j =
        ∑ a : QubitIdx N, ∑ b : QubitIdx N,
          U i a * (Uᴴ * B * U) a b * Uᴴ b j *
            ((Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) := by
    intro k
    rw [Matrix.smul_apply, smul_eq_mul, hmat_entry (adPowMat H k B) i j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    rw [adPowMat_eigen_entry hH B k a b, mul_pow]; ring
  have hrhs_entry : heisenbergEvol hH z B i j =
      ∑ a : QubitIdx N, ∑ b : QubitIdx N,
        U i a * (Uᴴ * B * U) a b * Uᴴ b j *
          Complex.exp (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)) := by
    rw [hmat_entry (heisenbergEvol hH z B) i j]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have hev : (Uᴴ * heisenbergEvol hH z B * U) a b =
        Complex.exp (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)) *
          (Uᴴ * B * U) a b := by
      simp only [heisenbergEvol, complexPropagator]
      have hcf := conj_hermFunc_mul_hermFunc hH
        (fun lam ↦ Complex.exp (Complex.I * z * (lam : ℂ)))
        (fun lam ↦ Complex.exp (Complex.I * (-z) * (lam : ℂ))) B a b
      change ((hH.eigenvectorUnitary : QubitOp N)ᴴ *
        (hermFunc hH (fun lam ↦ Complex.exp (Complex.I * z * (lam : ℂ))) * B *
          hermFunc hH (fun lam ↦ Complex.exp (Complex.I * (-z) * (lam : ℂ)))) *
        (hH.eigenvectorUnitary : QubitOp N)) a b = _
      rw [hcf, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hev]; ring
  simp_rw [hlhs_entry]
  rw [hrhs_entry]
  apply hasSum_sum; intro a _
  apply hasSum_sum; intro b _
  have hexp : HasSum (fun k : ℕ ↦
      (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
      (Complex.exp (Complex.I * z * ((hH.eigenvalues a - hH.eigenvalues b : ℝ) : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  exact hexp.mul_left _

/-- Iterated commutator along a sequence `f : Fin k → Finset (Fin N)`. -/
def iterComm {N : ℕ} (h : Finset (Fin N) → QubitOp N) :
    ∀ {k : ℕ}, (Fin k → Finset (Fin N)) → QubitOp N → QubitOp N
  | 0, _, B => B
  | _ + 1, f, B => matComm (h (f 0)) (iterComm h (Fin.tail f) B)

/-- Union of `U₀` with all hyperedges in `f : Fin k → Finset (Fin N)`. -/
def causalUnion {N : ℕ} (U₀ : Finset (Fin N)) :
    ∀ {k : ℕ}, (Fin k → Finset (Fin N)) → Finset (Fin N)
  | 0, _ => U₀
  | _ + 1, f => f 0 ∪ causalUnion U₀ (Fin.tail f)

/-- Causality predicate: at each step (from inner to outer), the new hyperedge intersects
the accumulated support. -/
def isCausalSeq {N : ℕ} (U₀ : Finset (Fin N)) :
    ∀ {k : ℕ}, (Fin k → Finset (Fin N)) → Prop
  | 0, _ => True
  | _ + 1, f => (f 0 ∩ causalUnion U₀ (Fin.tail f)).Nonempty ∧ isCausalSeq U₀ (Fin.tail f)

instance instDecidablePredIsCausalSeq {N : ℕ} (U₀ : Finset (Fin N)) :
    ∀ {k : ℕ}, DecidablePred (isCausalSeq U₀ (k := k))
  | 0 => fun _ ↦ isTrue trivial
  | _ + 1 => fun f ↦ @instDecidableAnd _ _ inferInstance
      (instDecidablePredIsCausalSeq U₀ (Fin.tail f))

lemma iterComm_mem_supportedOn {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) {U₀ : Finset (Fin N)} {B : QubitOp N}
    (hB : B ∈ supportedOn U₀) :
    ∀ {k : ℕ} (f : Fin k → Finset (Fin N)),
      iterComm h f B ∈ supportedOn (causalUnion U₀ f)
  | 0, _ => hB
  | _ + 1, f => by
    rw [iterComm, causalUnion]
    have h1 : h (f 0) ∈ supportedOn (f 0 ∪ causalUnion U₀ (Fin.tail f)) :=
      supportedOn_mono Finset.subset_union_left (hsupp (f 0))
    have h2 : iterComm h (Fin.tail f) B ∈ supportedOn (f 0 ∪ causalUnion U₀ (Fin.tail f)) :=
      supportedOn_mono Finset.subset_union_right (iterComm_mem_supportedOn h hsupp hB (Fin.tail f))
    unfold matComm
    exact Submodule.sub_mem _ (supportedOn_mul_mem h1 h2) (supportedOn_mul_mem h2 h1)

lemma iterComm_eq_zero_of_not_causal {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) {U₀ : Finset (Fin N)} {B : QubitOp N}
    (hB : B ∈ supportedOn U₀) :
    ∀ {k : ℕ} (f : Fin k → Finset (Fin N)),
      ¬ isCausalSeq U₀ f → iterComm h f B = 0
  | 0, _, hnc => absurd trivial hnc
  | _ + 1, f, hnc => by
    rw [iterComm]
    rw [isCausalSeq, not_and_or] at hnc
    rcases hnc with hdisj | htail
    · rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hdisj
      unfold matComm
      rw [supportedOn_comm_of_disjoint hdisj (hsupp (f 0))
        (iterComm_mem_supportedOn h hsupp hB (Fin.tail f)), sub_self]
    · rw [iterComm_eq_zero_of_not_causal h hsupp hB (Fin.tail f) htail]
      unfold matComm; simp

lemma opNorm_iterComm_le {N : ℕ} (h : Finset (Fin N) → QubitOp N) (B : QubitOp N) :
    ∀ {k : ℕ} (f : Fin k → Finset (Fin N)),
      opNorm (iterComm h f B) ≤ (2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (f j))) * opNorm B
  | 0, _ => by simp [iterComm]
  | k + 1, f => by
    rw [iterComm, matComm, Fin.prod_univ_succ, pow_succ']
    have hih := opNorm_iterComm_le h B (Fin.tail f)
    have hcomm : opNorm (h (f 0) * iterComm h (Fin.tail f) B - iterComm h (Fin.tail f) B * h (f 0)) ≤
        2 * opNorm (h (f 0)) * opNorm (iterComm h (Fin.tail f) B) := by
      have hsub : h (f 0) * iterComm h (Fin.tail f) B - iterComm h (Fin.tail f) B * h (f 0) =
          h (f 0) * iterComm h (Fin.tail f) B + (-1 : ℂ) • (iterComm h (Fin.tail f) B * h (f 0)) := by
        simp [sub_eq_add_neg]
      rw [hsub]
      have h1 := opNorm_add_le (h (f 0) * iterComm h (Fin.tail f) B)
        ((-1 : ℂ) • (iterComm h (Fin.tail f) B * h (f 0)))
      rw [opNorm_smul, norm_neg, norm_one, one_mul] at h1
      have h2 := opNorm_mul_le (h (f 0)) (iterComm h (Fin.tail f) B)
      have h3 := opNorm_mul_le (iterComm h (Fin.tail f) B) (h (f 0))
      linarith
    have hnn : 0 ≤ 2 * opNorm (h (f 0)) := mul_nonneg (by norm_num) (opNorm_nonneg _)
    calc opNorm (h (f 0) * iterComm h (Fin.tail f) B - iterComm h (Fin.tail f) B * h (f 0))
        ≤ 2 * opNorm (h (f 0)) * opNorm (iterComm h (Fin.tail f) B) := hcomm
      _ ≤ 2 * opNorm (h (f 0)) * ((2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (Fin.tail f j))) * opNorm B) :=
          mul_le_mul_of_nonneg_left hih hnn
      _ = 2 * (2 : ℝ) ^ k * (opNorm (h (f 0)) * ∏ j : Fin k, opNorm (h (Fin.tail f j))) * opNorm B := by ring

lemma card_causalUnion_le {N r : ℕ} (hr : 1 ≤ r) (E : Finset (Finset (Fin N)))
    (hcard : ∀ X ∈ E, X.card ≤ r) (U₀ : Finset (Fin N)) :
    ∀ {k : ℕ} (f : Fin k → Finset (Fin N)),
      (∀ j, f j ∈ E) → isCausalSeq U₀ f →
      (causalUnion U₀ f).card ≤ U₀.card + k * (r - 1)
  | 0, _, _, _ => by simp [causalUnion]
  | k + 1, f, hfE, hcs => by
    rw [causalUnion]
    have hih := card_causalUnion_le hr E hcard U₀ (Fin.tail f) (fun j ↦ hfE j.succ) hcs.2
    have hinter : 1 ≤ (f 0 ∩ causalUnion U₀ (Fin.tail f)).card := Finset.card_pos.mpr hcs.1
    have hu := Finset.card_union_add_card_inter (f 0) (causalUnion U₀ (Fin.tail f))
    have hf0 : (f 0).card ≤ r := hcard (f 0) (hfE 0)
    have : (f 0 ∪ causalUnion U₀ (Fin.tail f)).card ≤ (f 0).card + (causalUnion U₀ (Fin.tail f)).card - 1 := by
      omega
    have hmul : (k + 1) * (r - 1) = k * (r - 1) + (r - 1) := by ring
    omega

lemma adPowMat_eq_sum_causal {N : ℕ} (E : Finset (Finset (Fin N)))
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    {U₀ : Finset (Fin N)} {B : QubitOp N} (hB : B ∈ supportedOn U₀) :
    ∀ k : ℕ, adPowMat (∑ X ∈ E, h X) k B =
      ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀), iterComm h f B := by
  intro k
  have hall : adPowMat (∑ X ∈ E, h X) k B =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k ↦ E), iterComm h f B := by
    induction k with
    | zero =>
      simp only [adPowMat]
      have hsing : Fintype.piFinset (fun _ : Fin 0 ↦ E) = {Fin.elim0} := by
        ext f; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
        constructor
        · intro _; funext j; exact Fin.elim0 j
        · rintro rfl j; exact Fin.elim0 j
      rw [hsing, Finset.sum_singleton]; rfl
    | succ k ih =>
      rw [adPowMat, ih]
      have hcomm_sum : matComm (∑ X ∈ E, h X)
          (∑ f ∈ Fintype.piFinset (fun _ : Fin k ↦ E), iterComm h f B) =
          ∑ X ∈ E, ∑ f ∈ Fintype.piFinset (fun _ : Fin k ↦ E), matComm (h X) (iterComm h f B) := by
        unfold matComm
        simp only [Matrix.sum_mul, Matrix.mul_sum, Finset.sum_sub_distrib]
        rw [Finset.sum_comm (s := Fintype.piFinset _)]
      rw [hcomm_sum, ← Finset.sum_product']
      refine Finset.sum_bij (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
      · intro p hp; rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        rw [Fintype.mem_piFinset]; intro j
        exact Fin.cases hp1 (fun l ↦ Fintype.mem_piFinset.mp hp2 l) j
      · intro p₁ _ p₂ _ heq; apply Prod.ext
        · have := congrFun heq 0; simpa using this
        · funext l; have := congrFun heq l.succ; simpa using this
      · intro f hf
        refine ⟨(f 0, Fin.tail f), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hf 0,
          Fintype.mem_piFinset.mpr fun l ↦ Fintype.mem_piFinset.mp hf l.succ⟩, ?_⟩
        funext j; exact Fin.cases rfl (fun _ ↦ rfl) j
      · intro p _; rfl
  rw [hall]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro f _
  by_cases hcs : isCausalSeq U₀ f
  · simp [hcs]
  · simp [hcs, iterComm_eq_zero_of_not_causal h hsupp hB f hcs]

/-- Forward causal sequence weight sum starting from `U₀`. -/
noncomputable def fwdCausalSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (w : Finset (Fin N) → ℝ) (k : ℕ) (U₀ : Finset (Fin N)) : ℝ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀), ∏ j : Fin k, w (f j)

lemma fwdCausalSum_le {N r : ℕ} (hr : 1 ≤ r) (E : Finset (Finset (Fin N)))
    (hcard : ∀ X ∈ E, X.card ≤ r) (w : Finset (Fin N) → ℝ)
    (hw_nn : ∀ X ∈ E, 0 ≤ w X) {J : ℝ} (hJ_nn : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X ≤ J) (x₀ : Fin N) :
    ∀ k : ℕ, fwdCausalSum E w k {x₀} ≤ (k.factorial : ℝ) * ((r : ℝ) * J) ^ k := by
  intro k
  induction k with
  | zero =>
    unfold fwdCausalSum
    have hsing : (Fintype.piFinset fun _ : Fin 0 ↦ E).filter (isCausalSeq {x₀}) = {Fin.elim0} := by
      ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _; funext j; exact Fin.elim0 j
      · rintro rfl; exact ⟨fun j ↦ Fin.elim0 j, trivial⟩
    rw [hsing, Finset.sum_singleton]; simp
  | succ k ih =>
    unfold fwdCausalSum
    have hsplit : ∑ f ∈ (Fintype.piFinset fun _ : Fin (k + 1) ↦ E).filter (isCausalSeq {x₀}),
          ∏ j : Fin (k + 1), w (f j) =
        ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x₀}),
          (∏ j : Fin k, w (g j)) *
            ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x₀} g).Nonempty), w X := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_sigma (f := fun p : (Σ _ : Fin k → Finset (Fin N), Finset (Fin N)) ↦ (∏ j : Fin k, w (p.1 j)) * w p.2)]
      refine Finset.sum_bij (fun f _ ↦ ⟨Fin.tail f, f 0⟩) ?_ ?_ ?_ ?_
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfpi, hf0, hft⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
          ⟨Fintype.mem_piFinset.mpr fun j ↦ Fintype.mem_piFinset.mp hfpi j.succ, hft⟩,
          Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfpi 0, hf0⟩⟩
      · intro f₁ _ f₂ _ heq
        have h1 : Fin.tail f₁ = Fin.tail f₂ := congrArg Sigma.fst heq
        have h0 : f₁ 0 = f₂ 0 := by
          have := (Sigma.mk.inj_iff.mp heq).2; simpa using this
        funext j; exact Fin.cases h0 (fun l ↦ congrFun h1 l) j
      · intro p hp
        rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
        rcases Finset.mem_filter.mp hp1 with ⟨hpi1, hcs1⟩
        rcases Finset.mem_filter.mp hp2 with ⟨hX2, hinter2⟩
        refine ⟨Fin.cons p.2 p.1, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j ↦
          Fin.cases hX2 (fun l ↦ Fintype.mem_piFinset.mp hpi1 l) j, hinter2, hcs1⟩, ?_⟩
        rfl
      · intro f _; rw [Fin.prod_univ_succ, mul_comm]; rfl
    rw [hsplit]
    have hstep : ∀ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x₀}),
        ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x₀} g).Nonempty), w X ≤
          ((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J) := by
      intro g hg
      rcases Finset.mem_filter.mp hg with ⟨hgpi, hgcs⟩
      have h1 := sum_overlapping_le E w hw_nn hsite (causalUnion {x₀} g)
      have h1' : ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x₀} g).Nonempty), w X =
          ∑ X ∈ E.filter (fun X ↦ (causalUnion {x₀} g ∩ X).Nonempty), w X := by
        apply Finset.sum_congr _ (fun _ _ ↦ rfl)
        ext X; simp only [Finset.mem_filter, Finset.inter_comm]
      rw [h1']
      have hcard_u := card_causalUnion_le hr E hcard {x₀} g (Fintype.mem_piFinset.mp hgpi) hgcs
      have hcard_le : ((causalUnion {x₀} g).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (r : ℝ) := by
        have hnat : (causalUnion {x₀} g).card ≤ (k + 1) * r := by
          have : 1 + k * (r - 1) ≤ (k + 1) * r := by
            have : k * (r - 1) ≤ k * r := Nat.mul_le_mul_left k (Nat.sub_le r 1)
            nlinarith
          simp only [Finset.card_singleton] at hcard_u
          omega
        exact_mod_cast hnat
      calc ∑ X ∈ E.filter (fun X ↦ (causalUnion {x₀} g ∩ X).Nonempty), w X
          ≤ ((causalUnion {x₀} g).card : ℝ) * J := h1
        _ ≤ (((k + 1 : ℕ) : ℝ) * (r : ℝ)) * J := mul_le_mul_of_nonneg_right hcard_le hJ_nn
        _ = ((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J) := by ring
    calc ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x₀}),
            (∏ j : Fin k, w (g j)) * ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x₀} g).Nonempty), w X
        ≤ ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x₀}),
            (∏ j : Fin k, w (g j)) * (((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J)) := by
          apply Finset.sum_le_sum; intro g hg
          exact mul_le_mul_of_nonneg_left (hstep g hg)
            (Finset.prod_nonneg fun j _ ↦ hw_nn _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 j))
      _ = fwdCausalSum E w k {x₀} * (((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J)) := by rw [← Finset.sum_mul]; rfl
      _ ≤ ((k.factorial : ℝ) * ((r : ℝ) * J) ^ k) * (((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ = ((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ (k + 1) := by
          rw [Nat.factorial_succ, pow_succ]; push_cast; ring

/-- Reverse causal sum: sum over all starting sites `x : Fin N` and all causal sequences `f`
of length `k` starting from `{x}` whose support union contains `y`. -/
noncomputable def revCausalSum {N : ℕ} (E : Finset (Finset (Fin N)))
    (w : Finset (Fin N) → ℝ) (k : ℕ) (y : Fin N) : ℝ :=
  ∑ x : Fin N, ∑ f ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
    (fun f ↦ y ∈ causalUnion {x} f), ∏ j : Fin k, w (f j)

/-- **Inductive Reverse-Causal Sum Bound (Cayley Root Reversal)**:
`revCausalSum E w k y ≤ (k + 1)! * (r * J) ^ k` for all `k : ℕ` and `y : Fin N`. -/
lemma revCausalSum_le {N r : ℕ} (hr : 1 ≤ r) (E : Finset (Finset (Fin N)))
    (hcard : ∀ X ∈ E, X.card ≤ r) (w : Finset (Fin N) → ℝ)
    (hw_nn : ∀ X ∈ E, 0 ≤ w X) {J : ℝ} (hJ_nn : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X ≤ J) :
    ∀ k : ℕ, ∀ y : Fin N, revCausalSum E w k y ≤ ((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k := by
  intro k
  induction k with
  | zero =>
    intro y
    unfold revCausalSum
    rw [Finset.sum_eq_single y]
    · have hsing : ((Fintype.piFinset fun _ : Fin 0 ↦ E).filter (isCausalSeq {y})).filter
          (fun f ↦ y ∈ causalUnion {y} f) = {Fin.elim0} := by
        ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
        constructor
        · intro _; funext j; exact Fin.elim0 j
        · rintro rfl; exact ⟨⟨fun j ↦ Fin.elim0 j, trivial⟩, by simp [causalUnion]⟩
      rw [hsing, Finset.sum_singleton]; simp
    · intro x _ hxy
      apply Finset.sum_eq_zero; intro f hf
      have hy := (Finset.mem_filter.mp hf).2
      simp [causalUnion, Ne.symm hxy] at hy
    · intro hy; exact absurd (Finset.mem_univ y) hy
  | succ k ih =>
    intro y
    unfold revCausalSum
    -- For each `x` and `f : Fin (k+1) → E` with `y ∈ f 0 ∪ causalUnion {x} (Fin.tail f)`,
    -- split into `y ∈ causalUnion {x} (Fin.tail f)` (Case 1) or `y ∈ f 0` (Case 2).
    have hsplit_x : ∀ x : Fin N,
        ∑ f ∈ ((Fintype.piFinset fun _ : Fin (k + 1) ↦ E).filter (isCausalSeq {x})).filter
            (fun f ↦ y ∈ causalUnion {x} f), ∏ j : Fin (k + 1), w (f j) ≤
        (∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
            (fun g ↦ y ∈ causalUnion {x} g),
            (∏ j : Fin k, w (g j)) *
              ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x} g).Nonempty), w X) +
        (∑ X ∈ E.filter (fun X ↦ y ∈ X), w X *
          ∑ z ∈ X, ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
            (fun g ↦ z ∈ causalUnion {x} g), ∏ j : Fin k, w (g j)) := by
      intro x
      let S := ((Fintype.piFinset fun _ : Fin (k + 1) ↦ E).filter (isCausalSeq {x})).filter
        (fun f ↦ y ∈ causalUnion {x} f)
      let S1 := S.filter (fun f ↦ y ∈ causalUnion {x} (Fin.tail f))
      let S2 := S.filter (fun f ↦ y ∉ causalUnion {x} (Fin.tail f))
      have hS_split : ∑ f ∈ S, ∏ j : Fin (k + 1), w (f j) =
          (∑ f ∈ S1, ∏ j : Fin (k + 1), w (f j)) + ∑ f ∈ S2, ∏ j : Fin (k + 1), w (f j) := by
        rw [← Finset.sum_filter_add_sum_filter_not S (fun f ↦ y ∈ causalUnion {x} (Fin.tail f))]
      rw [hS_split]
      apply add_le_add
      · -- Case 1: `y ∈ causalUnion {x} (Fin.tail f)`
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_sigma (f := fun p : (Σ _ : Fin k → Finset (Fin N), Finset (Fin N)) ↦ (∏ j : Fin k, w (p.1 j)) * w p.2)]
        have heq1 : ∑ f ∈ S1, ∏ j : Fin (k + 1), w (f j) =
            ∑ p ∈ (((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
              (fun g ↦ y ∈ causalUnion {x} g)).sigma
              (fun g ↦ E.filter (fun X ↦ (X ∩ causalUnion {x} g).Nonempty)),
              (∏ j : Fin k, w (p.1 j)) * w p.2 := by
          refine Finset.sum_bij (fun f _ ↦ ⟨Fin.tail f, f 0⟩) ?_ ?_ ?_ ?_
          · intro f hf
            rcases Finset.mem_filter.mp hf with ⟨hfS, hy_tail⟩
            rcases Finset.mem_filter.mp hfS with ⟨hfcs, _⟩
            rcases Finset.mem_filter.mp hfcs with ⟨hfpi, hf0, hft⟩
            exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨Fintype.mem_piFinset.mpr fun j ↦ Fintype.mem_piFinset.mp hfpi j.succ, hft⟩, hy_tail⟩,
              Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfpi 0, hf0⟩⟩
          · intro f₁ _ f₂ _ heq
            have h1 : Fin.tail f₁ = Fin.tail f₂ := congrArg Sigma.fst heq
            have h0 : f₁ 0 = f₂ 0 := by have := (Sigma.mk.inj_iff.mp heq).2; simpa using this
            funext j; exact Fin.cases h0 (fun l ↦ congrFun h1 l) j
          · intro p hp
            rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
            rcases Finset.mem_filter.mp hp1 with ⟨hcs1, hy1⟩
            rcases Finset.mem_filter.mp hcs1 with ⟨hpi1, hcs1'⟩
            rcases Finset.mem_filter.mp hp2 with ⟨hX2, hinter2⟩
            refine ⟨Fin.cons p.2 p.1, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j ↦
                Fin.cases hX2 (fun l ↦ Fintype.mem_piFinset.mp hpi1 l) j, hinter2, hcs1'⟩,
                Finset.mem_union_right _ hy1⟩, hy1⟩, rfl⟩
          · intro f _; rw [Fin.prod_univ_succ, mul_comm]; rfl
        exact heq1.le
      · -- Case 2: `y ∉ causalUnion {x} (Fin.tail f)`, so `y ∈ f 0`, and `∃ z ∈ f 0 ∩ causalUnion {x} (Fin.tail f)`
        have hS2_eq : ∑ f ∈ S2, ∏ j : Fin (k + 1), w (f j) ≤
            ∑ X ∈ E.filter (fun X ↦ y ∈ X), w X *
              ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
                (fun g ↦ (X ∩ causalUnion {x} g).Nonempty), ∏ j : Fin k, w (g j) := by
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_sigma (f := fun p : (Σ _ : Finset (Fin N), Fin k → Finset (Fin N)) ↦ w p.1 * ∏ j : Fin k, w (p.2 j))]
          have hmap : ∀ f ∈ S2, (⟨f 0, Fin.tail f⟩ : Σ _X : Finset (Fin N), Fin k → Finset (Fin N)) ∈
              (E.filter (fun X ↦ y ∈ X)).sigma (fun X ↦
                ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
                  (fun g ↦ (X ∩ causalUnion {x} g).Nonempty)) := by
            intro f hf
            rcases Finset.mem_filter.mp hf with ⟨hfS, hynot⟩
            rcases Finset.mem_filter.mp hfS with ⟨hfcs, hyu⟩
            rcases Finset.mem_filter.mp hfcs with ⟨hfpi, hf0, hft⟩
            have hyf0 : y ∈ f 0 := (Finset.mem_union.mp hyu).resolve_right hynot
            exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfpi 0, hyf0⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Fintype.mem_piFinset.mpr fun j ↦ Fintype.mem_piFinset.mp hfpi j.succ, hft⟩, hf0⟩⟩
          have hinj : Set.InjOn (fun f : Fin (k + 1) → Finset (Fin N) ↦
              (⟨f 0, Fin.tail f⟩ : Σ _X : Finset (Fin N), Fin k → Finset (Fin N))) (S2 : Set _) := by
            intro f₁ _ f₂ _ heq
            have h0 : f₁ 0 = f₂ 0 := congrArg Sigma.fst heq
            have h1 : Fin.tail f₁ = Fin.tail f₂ := by
              have := (Sigma.mk.inj_iff.mp heq).2; simpa using this
            funext j; exact Fin.cases h0 (fun l ↦ congrFun h1 l) j
          calc ∑ f ∈ S2, ∏ j : Fin (k + 1), w (f j)
              = ∑ f ∈ S2, w (f 0) * ∏ j : Fin k, w (Fin.tail f j) :=
                Finset.sum_congr rfl fun f _ ↦ Fin.prod_univ_succ _
            _ = ∑ p ∈ S2.image (fun f ↦ (⟨f 0, Fin.tail f⟩ : Σ _X : Finset (Fin N), Fin k → Finset (Fin N))),
                  w p.1 * ∏ j : Fin k, w (p.2 j) := by
                rw [Finset.sum_image hinj]
            _ ≤ ∑ p ∈ (E.filter (fun X ↦ y ∈ X)).sigma (fun X ↦
                  ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
                    (fun g ↦ (X ∩ causalUnion {x} g).Nonempty)),
                  w p.1 * ∏ j : Fin k, w (p.2 j) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmap) ?_
                intro p hp _
                rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
                exact mul_nonneg (hw_nn _ (Finset.mem_filter.mp hp1).1)
                  (Finset.prod_nonneg fun j _ ↦
                    hw_nn _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1 j))
        refine le_trans hS2_eq (Finset.sum_le_sum fun X hX ↦ ?_)
        apply mul_le_mul_of_nonneg_left _ (hw_nn X (Finset.mem_filter.mp hX).1)
        have hsub : ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
            (fun g ↦ (X ∩ causalUnion {x} g).Nonempty) ⊆
            X.biUnion (fun z ↦ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
              (fun g ↦ z ∈ causalUnion {x} g)) := by
          intro g hg
          rcases Finset.mem_filter.mp hg with ⟨hg1, z, hz⟩
          rcases Finset.mem_inter.mp hz with ⟨hzX, hzg⟩
          exact Finset.mem_biUnion.mpr ⟨z, hzX, Finset.mem_filter.mpr ⟨hg1, hzg⟩⟩
        calc ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
              (fun g ↦ (X ∩ causalUnion {x} g).Nonempty), ∏ j : Fin k, w (g j)
            ≤ ∑ g ∈ X.biUnion (fun z ↦ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
                (fun g ↦ z ∈ causalUnion {x} g)), ∏ j : Fin k, w (g j) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun g hg _ ↦ by
                rcases Finset.mem_biUnion.mp hg with ⟨_, _, hg'⟩
                exact Finset.prod_nonneg fun j _ ↦
                  hw_nn _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg').1).1 j)
          _ ≤ ∑ z ∈ X, ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
                (fun g ↦ z ∈ causalUnion {x} g), ∏ j : Fin k, w (g j) :=
              real_sum_biUnion_le _ _ _ fun g hg ↦ by
                rcases Finset.mem_biUnion.mp hg with ⟨_, _, hg'⟩
                exact Finset.prod_nonneg fun j _ ↦
                  hw_nn _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg').1).1 j)
    -- Bound the Case 1 factor `∑_{X hits causalUnion} w X ≤ (k + 1) * r * J`
    have hcase1_le : ∑ x : Fin N, ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
          (fun g ↦ y ∈ causalUnion {x} g),
          (∏ j : Fin k, w (g j)) * ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x} g).Nonempty), w X ≤
        (((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J)) * revCausalSum E w k y := by
      unfold revCausalSum
      rw [mul_comm, Finset.sum_mul]
      apply Finset.sum_le_sum; intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro g hg
      have hg1 := (Finset.mem_filter.mp hg).1
      rcases Finset.mem_filter.mp hg1 with ⟨hgpi, hgcs⟩
      have h1 := sum_overlapping_le E w hw_nn hsite (causalUnion {x} g)
      have h1' : ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion {x} g).Nonempty), w X =
          ∑ X ∈ E.filter (fun X ↦ (causalUnion {x} g ∩ X).Nonempty), w X := by
        apply Finset.sum_congr _ (fun _ _ ↦ rfl); ext X; simp [Finset.inter_comm]
      rw [h1']
      have hcard_u := card_causalUnion_le hr E hcard {x} g (Fintype.mem_piFinset.mp hgpi) hgcs
      have hcard_le : ((causalUnion {x} g).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (r : ℝ) := by
        have hnat : (causalUnion {x} g).card ≤ (k + 1) * r := by
          calc (causalUnion {x} g).card
              ≤ 1 + k * (r - 1) := by simpa using hcard_u
            _ ≤ r + k * r := Nat.add_le_add hr (Nat.mul_le_mul_left k (Nat.sub_le r 1))
            _ = (k + 1) * r := by ring
        exact_mod_cast hnat
      have hbound : ∑ X ∈ E.filter (fun X ↦ (causalUnion {x} g ∩ X).Nonempty), w X ≤
          ((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J) := by
        calc ∑ X ∈ E.filter (fun X ↦ (causalUnion {x} g ∩ X).Nonempty), w X
            ≤ ((causalUnion {x} g).card : ℝ) * J := h1
          _ ≤ (((k + 1 : ℕ) : ℝ) * (r : ℝ)) * J := mul_le_mul_of_nonneg_right hcard_le hJ_nn
          _ = ((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J) := by ring
      exact mul_le_mul_of_nonneg_left hbound
        (Finset.prod_nonneg fun j _ ↦ hw_nn _ (Fintype.mem_piFinset.mp hgpi j))
    -- Bound the Case 2 sum: swap `∑ x` inside `∑ X, ∑ z`
    have hcase2_le : ∑ x : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), w X *
          ∑ z ∈ X, ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
            (fun g ↦ z ∈ causalUnion {x} g), ∏ j : Fin k, w (g j) ≤
        ((r : ℝ) * J) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) := by
      rw [Finset.sum_comm]
      have hinner : ∀ X ∈ E.filter (fun X ↦ y ∈ X),
          ∑ x : Fin N, w X * ∑ z ∈ X,
            ∑ g ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {x})).filter
              (fun g ↦ z ∈ causalUnion {x} g), ∏ j : Fin k, w (g j) =
          w X * ∑ z ∈ X, revCausalSum E w k z := by
        intro X _
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl
      rw [Finset.sum_congr rfl hinner]
      calc ∑ X ∈ E.filter (fun X ↦ y ∈ X), w X * ∑ z ∈ X, revCausalSum E w k z
          ≤ ∑ X ∈ E.filter (fun X ↦ y ∈ X), w X * ((r : ℝ) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k)) := by
            apply Finset.sum_le_sum; intro X hX
            apply mul_le_mul_of_nonneg_left _ (hw_nn X (Finset.mem_filter.mp hX).1)
            calc ∑ z ∈ X, revCausalSum E w k z
                ≤ ∑ _z ∈ X, (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) :=
                  Finset.sum_le_sum fun z _ ↦ ih z
              _ = (X.card : ℝ) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) := by simp
              _ ≤ (r : ℝ) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hcard X (Finset.mem_filter.mp hX).1)
                    (by positivity)
        _ = (∑ X ∈ E.filter (fun X ↦ y ∈ X), w X) *
              ((r : ℝ) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k)) := by rw [← Finset.sum_mul]
        _ ≤ J * ((r : ℝ) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k)) :=
            mul_le_mul_of_nonneg_right (hsite y) (by positivity)
        _ = ((r : ℝ) * J) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) := by ring
    have htot := Finset.sum_le_sum fun x _ ↦ hsplit_x x
    rw [Finset.sum_add_distrib] at htot
    have h1 := le_trans hcase1_le (mul_le_mul_of_nonneg_left (ih y) (by positivity))
    calc ∑ x : Fin N, ∑ f ∈ ((Fintype.piFinset fun _ : Fin (k + 1) ↦ E).filter (isCausalSeq {x})).filter
            (fun f ↦ y ∈ causalUnion {x} f), ∏ j : Fin (k + 1), w (f j)
        ≤ (((k + 1 : ℕ) : ℝ) * ((r : ℝ) * J)) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) +
          ((r : ℝ) * J) * (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) := by linarith
      _ = ((k + 2).factorial : ℝ) * ((r : ℝ) * J) ^ (k + 1) := by
          rw [Nat.factorial_succ, pow_succ]; push_cast; ring

lemma sqrt_prodDepolNormSq_add_le {N : ℕ} (s s' : Fin N → Fin 6) (X Y : QubitOp N) :
    Real.sqrt (prodDepolNormSq s s' (X + Y)) ≤
      Real.sqrt (prodDepolNormSq s s' X) + Real.sqrt (prodDepolNormSq s s' Y) := by
  have hnorm_eq : ∀ Z : QubitOp N,
      Real.sqrt (prodDepolNormSq s s' Z) =
        ‖qubitOpToHS N (globalDepolPHalf N s' * Z * globalDepolPHalf N s)‖ := by
    intro Z
    unfold prodDepolNormSq
    rw [prodDepolInner_eq_hsInner]
    have h1 : (hsInner (globalDepolPHalf N s' * Z * globalDepolPHalf N s)
        (globalDepolPHalf N s' * Z * globalDepolPHalf N s)).re =
        ‖qubitOpToHS N (globalDepolPHalf N s' * Z * globalDepolPHalf N s)‖ ^ 2 := by
      rw [← qubitOpToHS_inner, inner_self_eq_norm_sq_to_K]
      change ((‖qubitOpToHS N (globalDepolPHalf N s' * Z * globalDepolPHalf N s)‖ : ℂ) ^ 2).re = _
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h1, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm_eq, hnorm_eq, hnorm_eq]
  have hadd : globalDepolPHalf N s' * (X + Y) * globalDepolPHalf N s =
      globalDepolPHalf N s' * X * globalDepolPHalf N s +
      globalDepolPHalf N s' * Y * globalDepolPHalf N s := by
    simp [Matrix.mul_add, Matrix.add_mul]
  rw [hadd, map_add]
  exact norm_add_le _ _

lemma sqrt_prodDepolNormSq_sum_le {N : ℕ} {ι : Type*} (s s' : Fin N → Fin 6)
    (t : Finset ι) (f : ι → QubitOp N) :
    Real.sqrt (prodDepolNormSq s s' (∑ i ∈ t, f i)) ≤
      ∑ i ∈ t, Real.sqrt (prodDepolNormSq s s' (f i)) := by
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : prodDepolNormSq s s' (0 : QubitOp N) = 0 := by unfold prodDepolNormSq prodDepolInner; simp
    rw [h0, Real.sqrt_zero]
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    linarith [sqrt_prodDepolNormSq_add_le s s' (f a) (∑ i ∈ u, f i), ih]

lemma sqrt_prodDepolNormSq_smul {N : ℕ} (s s' : Fin N → Fin 6) (c : ℂ) (X : QubitOp N) :
    Real.sqrt (prodDepolNormSq s s' (c • X)) = ‖c‖ * Real.sqrt (prodDepolNormSq s s' X) := by
  have hsq : prodDepolNormSq s s' (c • X) = ‖c‖ ^ 2 * prodDepolNormSq s s' X := by
    unfold prodDepolNormSq prodDepolInner
    rw [Matrix.conjTranspose_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul,
      Complex.normSq_eq_norm_sq]
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma pauliSite_mem_supportedOn {N : ℕ} (x : Fin N) (α : Fin 3) :
    pauliSite x α.succ ∈ supportedOn {x} := by
  unfold pauliSite
  exact pauliString_mem_supportedOn _ fun y hy ↦ by
    have hne : y ≠ x := by simpa using hy
    simp [hne]

lemma opNorm_pauliSite_le {N : ℕ} (x : Fin N) (α : Fin 3) :
    opNorm (pauliSite x α.succ) ≤ 1 := by
  apply opNorm_unitary_le
  unfold pauliSite pauliString
  rw [kronOp_conjTranspose, kronOp_mul]
  have h1 : (fun y : Fin N ↦ (pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y))ᴴ *
      pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ y)) = fun _ ↦ 1 := by
    funext y
    by_cases hy : y = x
    · simp only [hy, Function.update_self]
      fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, Complex.star_def]
    · simp only [Function.update_of_ne hy]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pauliMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  rw [h1]
  ext i j; simp only [kronOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, ↓reduceIte]
    have hne : ∃ y : Fin N, i y ≠ j y := by
      by_contra hall; push Not at hall; exact hij (funext hall)
    rcases hne with ⟨y, hy⟩
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [Matrix.one_apply, hy])



lemma fwdCausalSum_general_le {N r : ℕ} (hr : 1 ≤ r) (E : Finset (Finset (Fin N)))
    (hcard : ∀ X ∈ E, X.card ≤ r) (w : Finset (Fin N) → ℝ)
    (hw_nn : ∀ X ∈ E, 0 ≤ w X) {J : ℝ} (hJ_nn : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), w X ≤ J) :
    ∀ (k : ℕ) (U₀ : Finset (Fin N)),
      fwdCausalSum E w k U₀ ≤
        (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) * J ^ k := by
  intro k U₀
  induction k with
  | zero =>
    unfold fwdCausalSum
    have hsing : (Fintype.piFinset fun _ : Fin 0 ↦ E).filter (isCausalSeq U₀) = {Fin.elim0} := by
      ext f; simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _; funext j; exact Fin.elim0 j
      · rintro rfl; exact ⟨fun j ↦ Fin.elim0 j, trivial⟩
    rw [hsing, Finset.sum_singleton]; simp
  | succ k ih =>
    unfold fwdCausalSum
    have hsplit : ∑ f ∈ (Fintype.piFinset fun _ : Fin (k + 1) ↦ E).filter (isCausalSeq U₀),
          ∏ j : Fin (k + 1), w (f j) =
        ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀),
          (∏ j : Fin k, w (g j)) *
            ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion U₀ g).Nonempty), w X := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_sigma (f := fun p : (Σ _ : Fin k → Finset (Fin N), Finset (Fin N)) ↦ (∏ j : Fin k, w (p.1 j)) * w p.2)]
      refine Finset.sum_bij (fun f _ ↦ ⟨Fin.tail f, f 0⟩) ?_ ?_ ?_ ?_
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfpi, hf0, hft⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
          ⟨Fintype.mem_piFinset.mpr fun j ↦ Fintype.mem_piFinset.mp hfpi j.succ, hft⟩,
          Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfpi 0, hf0⟩⟩
      · intro f₁ _ f₂ _ heq
        have h1 : Fin.tail f₁ = Fin.tail f₂ := congrArg Sigma.fst heq
        have h0 : f₁ 0 = f₂ 0 := by have := (Sigma.mk.inj_iff.mp heq).2; simpa using this
        funext j; exact Fin.cases h0 (fun l ↦ congrFun h1 l) j
      · intro p hp
        rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
        rcases Finset.mem_filter.mp hp1 with ⟨hpi1, hcs1⟩
        rcases Finset.mem_filter.mp hp2 with ⟨hX2, hinter2⟩
        refine ⟨Fin.cons p.2 p.1, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j ↦
          Fin.cases hX2 (fun l ↦ Fintype.mem_piFinset.mp hpi1 l) j, hinter2, hcs1⟩, rfl⟩
      · intro f _; rw [Fin.prod_univ_succ, mul_comm]; rfl
    rw [hsplit]
    have hstep : ∀ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀),
        ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion U₀ g).Nonempty), w X ≤
          ((U₀.card : ℝ) + (k : ℝ) * (r : ℝ)) * J := by
      intro g hg
      rcases Finset.mem_filter.mp hg with ⟨hgpi, hgcs⟩
      have h1 := sum_overlapping_le E w hw_nn hsite (causalUnion U₀ g)
      have h1' : ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion U₀ g).Nonempty), w X =
          ∑ X ∈ E.filter (fun X ↦ (causalUnion U₀ g ∩ X).Nonempty), w X := by
        apply Finset.sum_congr _ (fun _ _ ↦ rfl); ext X; simp [Finset.inter_comm]
      rw [h1']
      have hcard_u := card_causalUnion_le hr E hcard U₀ g (Fintype.mem_piFinset.mp hgpi) hgcs
      have hcard_le : ((causalUnion U₀ g).card : ℝ) ≤ (U₀.card : ℝ) + (k : ℝ) * (r : ℝ) := by
        have hnat : (causalUnion U₀ g).card ≤ U₀.card + k * r :=
          le_trans hcard_u (Nat.add_le_add_left (Nat.mul_le_mul_left k (Nat.sub_le r 1)) _)
        exact_mod_cast hnat
      exact le_trans h1 (mul_le_mul_of_nonneg_right hcard_le hJ_nn)
    calc ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀),
            (∏ j : Fin k, w (g j)) * ∑ X ∈ E.filter (fun X ↦ (X ∩ causalUnion U₀ g).Nonempty), w X
        ≤ ∑ g ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq {U₀ := U₀} |>.filter _), 0 := by sorry
      _ = 0 := by sorry
