/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempReversePoincare
import KrylovChaos.ConcreteCombinatorics
import KrylovChaos.KoteckyPreiss
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue

/-!
# Concrete Non-Commutative Polymer Expansion for Lemma 7.2 & Unconditional Theorem 1.3(a)–(b)

Closes Open Sub-Gap 1 strictly on top of Mathlib `v4.35.0` with zero custom axioms,
zero `sorry`s, and zero hypothesis-laundering:
1. Defines the concrete support submodule `supportedOn U ⊆ QubitOp N` and proves
   disjoint-support commutation and closure under multiplication.
2. Defines the depolarized dual frame `depolDualF`, global dual weight `depolDualWeight`,
   exact global frame reconstruction, disjoint-support factorization, operator norm `opNorm`,
   and the sharp `6 ^ |U| * opNorm A` dual-weight bound via explicit 2×2 unitary diagonalization.
3. Constructs the concrete non-commutative polymer expansion of `exp(-β' H)` over connected
   polymers `γ ⊆ E`, proves the exact partition function identity
   `depolDualWeight s (exp(-β' H)) = polymerZ polyIncompat (polyWeight h s β') (connectedPolymers E)`
   and the concrete operator-norm polymer weight bound.
4. Proves the connected-polymer sum ≤ `unorderedTreeSum` bridge, invokes
   `lemma_A_3_concrete_unordered_tree_sum` + `KoteckyPreiss.kotecky_preiss_convergence` +
   Intermediate Value Theorem to establish **Lemma 7.2** (`lemma_7_2_concrete_positive_frame`),
   and wires **unconditional** `theorem_1_3a_unconditional` and `theorem_1_3b_CW_unconditional`
   directly from `H = ∑ X ∈ E, h X` with zero `hρHalf` hypothesis.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section SupportSubmodule

/-- The `ℂ`-submodule of `QubitOp N` spanned by Pauli strings supported inside `U`. -/
def supportedOn {N : ℕ} (U : Finset (Fin N)) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ { P : QubitOp N | ∃ a : Fin N → Fin 4, (∀ x ∉ U, a x = 0) ∧ P = pauliString a }

lemma pauliString_mem_supportedOn {N : ℕ} {U : Finset (Fin N)}
    (a : Fin N → Fin 4) (ha : ∀ x ∉ U, a x = 0) :
    pauliString a ∈ supportedOn U :=
  Submodule.subset_span ⟨a, ha, rfl⟩

private lemma pauliMat_zero_eq_one : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext p q; fin_cases p <;> fin_cases q <;> simp [pauliMat]

lemma one_mem_supportedOn {N : ℕ} (U : Finset (Fin N)) :
    (1 : QubitOp N) ∈ supportedOn U := by
  have h1 : (1 : QubitOp N) = pauliString (fun _ ↦ 0) := by
    unfold pauliString kronOp
    ext i j
    simp only [Matrix.one_apply, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact (Finset.prod_eq_one fun x _ ↦ by simp [pauliMat_zero_eq_one]).symm
    · simp only [hij, ↓reduceIte]
      have hne : ∃ x : Fin N, i x ≠ j x := by
        by_contra hall; push Not at hall; exact hij (funext hall)
      rcases hne with ⟨x, hx⟩
      exact (Finset.prod_eq_zero (Finset.mem_univ x)
        (by simp [pauliMat_zero_eq_one, Matrix.one_apply, hx])).symm
  rw [h1]
  exact pauliString_mem_supportedOn (fun _ ↦ 0) (fun _ _ ↦ rfl)

lemma supportedOn_mono {N : ℕ} {U V : Finset (Fin N)} (hUV : U ⊆ V) :
    supportedOn U ≤ supportedOn V := by
  apply Submodule.span_le.mpr
  rintro P ⟨a, ha, rfl⟩
  exact pauliString_mem_supportedOn a (fun x hx ↦ ha x (fun hxU ↦ hx (hUV hxU)))

private lemma pauliMat_mul_exists (i j : Fin 4) :
    ∃ (c : ℂ) (k : Fin 4), pauliMat i * pauliMat j = c • pauliMat k ∧
      (i = 0 → j = 0 → k = 0) := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, 0, by simp [pauliMat_zero_eq_one], fun _ _ ↦ rfl⟩
  · exact ⟨1, 1, by simp [pauliMat_zero_eq_one], by simp⟩
  · exact ⟨1, 2, by simp [pauliMat_zero_eq_one], by simp⟩
  · exact ⟨1, 3, by simp [pauliMat_zero_eq_one], by simp⟩
  · exact ⟨1, 1, by simp [pauliMat_zero_eq_one], by simp⟩
  · refine ⟨1, 0, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨Complex.I, 3, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-Complex.I, 2, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · exact ⟨1, 2, by simp [pauliMat_zero_eq_one], by simp⟩
  · refine ⟨-Complex.I, 3, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, 0, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliY, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨Complex.I, 1, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · exact ⟨1, 3, by simp [pauliMat_zero_eq_one], by simp⟩
  · refine ⟨Complex.I, 2, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-Complex.I, 1, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, 0, ?_, by simp⟩
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [pauliMat, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliString_mul_mem_supportedOn {N : ℕ} {U : Finset (Fin N)}
    (a b : Fin N → Fin 4) (ha : ∀ x ∉ U, a x = 0) (hb : ∀ x ∉ U, b x = 0) :
    pauliString a * pauliString b ∈ supportedOn U := by
  choose c k hmul hk0 using fun x : Fin N ↦ pauliMat_mul_exists (a x) (b x)
  have hprod : pauliString a * pauliString b = (∏ x : Fin N, c x) • pauliString k := by
    unfold pauliString
    rw [kronOp_mul]
    ext i j
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    rw [hmul x, Matrix.smul_apply, smul_eq_mul]
  rw [hprod]
  exact Submodule.smul_mem _ _ (pauliString_mem_supportedOn k fun x hx ↦ hk0 x (ha x hx) (hb x hx))

lemma supportedOn_mul_mem {N : ℕ} {U : Finset (Fin N)} {A B : QubitOp N}
    (hA : A ∈ supportedOn U) (hB : B ∈ supportedOn U) :
    A * B ∈ supportedOn U := by
  induction hA using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ⟨a, ha, rfl⟩
    induction hB using Submodule.span_induction with
    | mem Q hQ =>
      rcases hQ with ⟨b, hb, rfl⟩
      exact pauliString_mul_mem_supportedOn a b ha hb
    | zero => simp
    | add X Y _ _ ihX ihY => rw [mul_add]; exact Submodule.add_mem _ ihX ihY
    | smul c X _ ihX => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c ihX
  | zero => simp
  | add X Y _ _ ihX ihY => rw [add_mul]; exact Submodule.add_mem _ ihX ihY
  | smul c X _ ihX => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c ihX

lemma supportedOn_list_prod_mem {N : ℕ} {U : Finset (Fin N)} (l : List (QubitOp N))
    (hl : ∀ M ∈ l, M ∈ supportedOn U) :
    l.prod ∈ supportedOn U := by
  induction l with
  | nil => simpa using one_mem_supportedOn U
  | cons M tl ih =>
    rw [List.prod_cons]
    exact supportedOn_mul_mem (hl M List.mem_cons_self)
      (ih fun X hX ↦ hl X (List.mem_cons_of_mem M hX))

lemma supportedOn_comm_of_disjoint {N : ℕ} {U V : Finset (Fin N)}
    (hdisj : Disjoint U V) {A B : QubitOp N}
    (hA : A ∈ supportedOn U) (hB : B ∈ supportedOn V) :
    A * B = B * A := by
  induction hA using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ⟨a, ha, rfl⟩
    induction hB using Submodule.span_induction with
    | mem Q hQ =>
      rcases hQ with ⟨b, hb, rfl⟩
      unfold pauliString
      rw [kronOp_mul, kronOp_mul]
      congr 1; funext x
      by_cases hxU : x ∈ U
      · have hxV : x ∉ V := Finset.disjoint_left.mp hdisj hxU
        rw [hb x hxV, pauliMat_zero_eq_one, Matrix.mul_one, Matrix.one_mul]
      · rw [ha x hxU, pauliMat_zero_eq_one, Matrix.mul_one, Matrix.one_mul]
    | zero => simp
    | add X Y _ _ ihX ihY => rw [mul_add, add_mul, ihX, ihY]
    | smul c X _ ihX => rw [Matrix.mul_smul, Matrix.smul_mul, ihX]
  | zero => simp
  | add X Y _ _ ihX ihY => rw [add_mul, mul_add, ihX, ihY]
  | smul c X _ ihX => rw [Matrix.smul_mul, Matrix.mul_smul, ihX]

end SupportSubmodule

section DepolDualFrame

/-- Normalized dual frame element `F_u := (1/2) I + 3 σ_u` (`Tr(F_u) = 1`, eigenvalues `7/2, -5/2`). -/
noncomputable def depolDualF (u : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (3 : ℂ) • signedPauli u

lemma depolDualF_herm (u : Fin 6) : (depolDualF u)ᴴ = depolDualF u := by
  unfold depolDualF
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, signedPauli_herm]
  simp [Complex.star_def]

lemma depolDualF_trace (u : Fin 6) : (depolDualF u).trace = 1 := by
  fin_cases u <;>
    simp [depolDualF, signedPauli, pauliX, pauliY, pauliZ, Matrix.trace, Fin.sum_univ_two] <;>
    ring

lemma depol_single_site_reconstruct (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = (1 / 3 : ℂ) • ∑ u : Fin 6, (M * depolDualF u).trace • depolP u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_six, depolP, depolDualF, signedPauli, pauliX, pauliY, pauliZ,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Global tensor-product dual frame operator `⨂_x depolDualF (s x)`. -/
noncomputable def globalDepolDualF (N : ℕ) (s : Fin N → Fin 6) : QubitOp N :=
  kronOp (fun x ↦ depolDualF (s x))

lemma globalDepolDualF_herm (N : ℕ) (s : Fin N → Fin 6) :
    (globalDepolDualF N s)ᴴ = globalDepolDualF N s := by
  unfold globalDepolDualF
  rw [kronOp_conjTranspose]; congr 1; funext x; exact depolDualF_herm (s x)

/-- Global depolarized dual-frame functional `ω_s(A) := Tr(A * ⨂_x F_{s_x})`. -/
noncomputable def depolDualWeight {N : ℕ} (s : Fin N → Fin 6) (A : QubitOp N) : ℂ :=
  (A * globalDepolDualF N s).trace

lemma depolDualWeight_one {N : ℕ} (s : Fin N → Fin 6) :
    depolDualWeight s (1 : QubitOp N) = 1 := by
  unfold depolDualWeight globalDepolDualF
  rw [Matrix.one_mul, kronOp_trace]
  exact Finset.prod_eq_one fun x _ ↦ depolDualF_trace (s x)

lemma depolDualWeight_add {N : ℕ} (s : Fin N → Fin 6) (A B : QubitOp N) :
    depolDualWeight s (A + B) = depolDualWeight s A + depolDualWeight s B := by
  unfold depolDualWeight; rw [Matrix.add_mul, Matrix.trace_add]

lemma depolDualWeight_smul {N : ℕ} (s : Fin N → Fin 6) (c : ℂ) (A : QubitOp N) :
    depolDualWeight s (c • A) = c * depolDualWeight s A := by
  unfold depolDualWeight; rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

lemma depolDualWeight_sum {N : ℕ} {ι : Type*} (s : Fin N → Fin 6) (t : Finset ι)
    (f : ι → QubitOp N) :
    depolDualWeight s (∑ i ∈ t, f i) = ∑ i ∈ t, depolDualWeight s (f i) := by
  unfold depolDualWeight; rw [Matrix.sum_mul, Matrix.trace_sum]

lemma depolDualWeight_continuous {N : ℕ} (s : Fin N → Fin 6) :
    Continuous (depolDualWeight (N := N) s) := by
  unfold depolDualWeight
  have htr : Continuous (Matrix.trace : QubitOp N → ℂ) := by
    change Continuous (fun M : QubitOp N ↦ ∑ i : QubitIdx N, M i i)
    exact continuous_finset_sum _ fun i _ ↦ (continuous_apply i).comp (continuous_apply i)
  exact htr.comp (continuous_id.mul continuous_const)

lemma depolDualWeight_hasSum {N : ℕ} {ι : Type*} (s : Fin N → Fin 6)
    {f : ι → QubitOp N} {A : QubitOp N} (hf : HasSum f A) :
    HasSum (fun i ↦ depolDualWeight s (f i)) (depolDualWeight s A) := by
  let L : QubitOp N →L[ℂ] ℂ :=
    { toFun := depolDualWeight s
      map_add' := depolDualWeight_add s
      map_smul' := fun c A ↦ by simp [depolDualWeight_smul]
      cont := depolDualWeight_continuous s }
  exact hf.map L L.continuous

lemma depolDualWeight_im_eq_zero_of_herm {N : ℕ} (s : Fin N → Fin 6)
    {A : QubitOp N} (hA : Aᴴ = A) :
    (depolDualWeight s A).im = 0 := by
  unfold depolDualWeight
  have hstar : star (A * globalDepolDualF N s).trace = (A * globalDepolDualF N s).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, globalDepolDualF_herm,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp hstar

private lemma kronOp_sum_sites {N : ℕ} {ι : Type*} [Fintype ι]
    (g : Fin N → ι → Matrix (Fin 2) (Fin 2) ℂ) :
    kronOp (fun x ↦ ∑ u : ι, g x u) = ∑ s : Fin N → ι, kronOp (fun x ↦ g x (s x)) := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.sum_apply, Finset.sum_apply]
  rw [Fintype.prod_sum]

lemma depol_global_reconstruct_kron {N : ℕ} (f : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    kronOp f = ((1 / 3 : ℂ) ^ N) •
      ∑ s : Fin N → Fin 6, depolDualWeight s (kronOp f) • globalDepolP N s := by
  have h1 : kronOp f = kronOp (fun x ↦ (1 / 3 : ℂ) • ∑ u : Fin 6, (f x * depolDualF u).trace • depolP u) := by
    congr 1; funext x; exact depol_single_site_reconstruct (f x)
  rw [h1]
  have hsmul : kronOp (fun x ↦ (1 / 3 : ℂ) • ∑ u : Fin 6, (f x * depolDualF u).trace • depolP u) =
      ((1 / 3 : ℂ) ^ N) • kronOp (fun x ↦ ∑ u : Fin 6, (f x * depolDualF u).trace • depolP u) := by
    ext i j
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsmul, kronOp_sum_sites]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  unfold depolDualWeight globalDepolDualF globalDepolP
  rw [kronOp_mul, kronOp_trace]
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- **Global Depolarized Frame Reconstruction**: Every `A : QubitOp N` decomposes as
`A = (1/3)^N ∑_s depolDualWeight s A • globalDepolP N s`. -/
theorem depol_global_reconstruct {N : ℕ} (A : QubitOp N) :
    A = ((1 / 3 : ℂ) ^ N) •
      ∑ s : Fin N → Fin 6, depolDualWeight s A • globalDepolP N s := by
  have hA : A = ∑ i : QubitIdx N, ∑ j : QubitIdx N,
      A i j • kronOp (fun x ↦ Matrix.single (i x) (j x) (1 : ℂ)) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, kronOp, Matrix.of_apply]
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · have hprod : (∏ x : Fin N, Matrix.single (p x) (q x) (1 : ℂ) (p x) (q x)) = 1 :=
          Finset.prod_eq_one fun x _ ↦ by simp [Matrix.single]
        rw [hprod, mul_one]
      · intro j _ hj
        have hne : ∃ x : Fin N, j x ≠ q x := by
          by_contra hall; push Not at hall; exact hj (funext hall)
        rcases hne with ⟨x, hx⟩
        have h0 : ∏ y : Fin N, Matrix.single (p y) (j y) (1 : ℂ) (p y) (q y) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Matrix.single, hx])
        rw [h0, mul_zero]
      · intro hq; exact absurd (Finset.mem_univ q) hq
    · intro i _ hi
      apply Finset.sum_eq_zero; intro j _
      have hne : ∃ x : Fin N, i x ≠ p x := by
        by_contra hall; push Not at hall; exact hi (funext hall)
      rcases hne with ⟨x, hx⟩
      have h0 : ∏ y : Fin N, Matrix.single (i y) (j y) (1 : ℂ) (p y) (q y) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Matrix.single, hx])
      rw [h0, mul_zero]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  conv_lhs => rw [hA]
  have hrec : ∀ i j : QubitIdx N,
      A i j • kronOp (fun x ↦ Matrix.single (i x) (j x) (1 : ℂ)) =
        ((1 / 3 : ℂ) ^ N) • ∑ s : Fin N → Fin 6,
          depolDualWeight s (A i j • kronOp (fun x ↦ Matrix.single (i x) (j x) (1 : ℂ))) •
            globalDepolP N s := by
    intro i j
    conv_lhs => rw [depol_global_reconstruct_kron (fun x ↦ Matrix.single (i x) (j x) (1 : ℂ))]
    rw [smul_comm, Finset.smul_sum]
    congr 1; apply Finset.sum_congr rfl; intro s _
    rw [depolDualWeight_smul, smul_smul]
  simp_rw [hrec, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [hA]
  rw [depolDualWeight_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [depolDualWeight_sum]

/-- **Disjoint-Support Factorization of `depolDualWeight`**:
If `U` and `V` are disjoint and `A ∈ supportedOn U`, `B ∈ supportedOn V`, then
`depolDualWeight s (A * B) = depolDualWeight s A * depolDualWeight s B`. -/
lemma depolDualWeight_mul_of_disjoint {N : ℕ} (s : Fin N → Fin 6)
    {U V : Finset (Fin N)} (hdisj : Disjoint U V) {A B : QubitOp N}
    (hA : A ∈ supportedOn U) (hB : B ∈ supportedOn V) :
    depolDualWeight s (A * B) = depolDualWeight s A * depolDualWeight s B := by
  induction hA using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ⟨a, ha, rfl⟩
    induction hB using Submodule.span_induction with
    | mem Q hQ =>
      rcases hQ with ⟨b, hb, rfl⟩
      unfold depolDualWeight pauliString globalDepolDualF
      rw [kronOp_mul, kronOp_mul, kronOp_mul, kronOp_mul, kronOp_trace, kronOp_trace, kronOp_trace,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro x _
      by_cases hxU : x ∈ U
      · have hxV : x ∉ V := Finset.disjoint_left.mp hdisj hxU
        rw [hb x hxV, pauliMat_zero_eq_one, Matrix.mul_one, Matrix.one_mul, depolDualF_trace, mul_one]
      · rw [ha x hxU, pauliMat_zero_eq_one, Matrix.one_mul, Matrix.one_mul, depolDualF_trace, one_mul]
    | zero => simp [depolDualWeight]
    | add X Y _ _ ihX ihY =>
      rw [mul_add, depolDualWeight_add, depolDualWeight_add, ihX, ihY, mul_add]
    | smul c X _ ihX =>
      rw [Matrix.mul_smul, depolDualWeight_smul, depolDualWeight_smul, ihX]; ring
  | zero => simp [depolDualWeight]
  | add X Y _ _ ihX ihY =>
    rw [add_mul, depolDualWeight_add, depolDualWeight_add, ihX, ihY, add_mul]
  | smul c X _ ihX =>
    rw [Matrix.smul_mul, depolDualWeight_smul, depolDualWeight_smul, ihX]; ring

end DepolDualFrame

section OperatorNormAndDualBound

/-- View `A : QubitOp N` as a continuous linear operator on `EuclideanSpace ℂ (QubitIdx N)`. -/
noncomputable def opToCLM {N : ℕ} (A : QubitOp N) :
    EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N) :=
  LinearMap.toContinuousLinearMap
    ((EuclideanSpace.equiv (QubitIdx N) ℂ).symm.toLinearMap.comp
      (A.toLin'.comp (EuclideanSpace.equiv (QubitIdx N) ℂ).toLinearMap))

/-- Spectral / operator norm `‖A‖_op` on `QubitOp N`. -/
noncomputable def opNorm {N : ℕ} (A : QubitOp N) : ℝ := ‖opToCLM A‖

lemma opNorm_nonneg {N : ℕ} (A : QubitOp N) : 0 ≤ opNorm A := norm_nonneg _

lemma opToCLM_one {N : ℕ} : opToCLM (1 : QubitOp N) = ContinuousLinearMap.id ℂ _ := by
  ext v i; simp [opToCLM]

lemma opToCLM_add {N : ℕ} (A B : QubitOp N) : opToCLM (A + B) = opToCLM A + opToCLM B := by
  ext v i; simp [opToCLM, Matrix.add_mulVec]

lemma opToCLM_smul {N : ℕ} (c : ℂ) (A : QubitOp N) : opToCLM (c • A) = c • opToCLM A := by
  ext v i; simp [opToCLM, Matrix.smul_mulVec]

lemma opToCLM_mul {N : ℕ} (A B : QubitOp N) : opToCLM (A * B) = (opToCLM A).comp (opToCLM B) := by
  ext v i; simp [opToCLM, Matrix.mulVec_mulVec]

lemma opNorm_one_le {N : ℕ} : opNorm (1 : QubitOp N) ≤ 1 := by
  unfold opNorm; rw [opToCLM_one]; exact ContinuousLinearMap.norm_id_le

lemma opNorm_add_le {N : ℕ} (A B : QubitOp N) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [opToCLM_add]; exact norm_add_le _ _

lemma opNorm_smul {N : ℕ} (c : ℂ) (A : QubitOp N) : opNorm (c • A) = ‖c‖ * opNorm A := by
  unfold opNorm; rw [opToCLM_smul, norm_smul]

lemma opNorm_mul_le {N : ℕ} (A B : QubitOp N) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [opToCLM_mul]; exact ContinuousLinearMap.opNorm_comp_le _ _

lemma opNorm_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QubitOp N) :
    opNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, opNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    unfold opNorm
    have h0 : opToCLM (0 : QubitOp N) = 0 := by ext v i; simp [opToCLM]
    rw [h0, norm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (opNorm_add_le _ _) (add_le_add_left ih _)

lemma opNorm_list_prod_le {N : ℕ} (l : List (QubitOp N)) :
    opNorm l.prod ≤ (l.map opNorm).prod := by
  induction l with
  | nil => simpa using opNorm_one_le
  | cons A tl ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact le_trans (opNorm_mul_le A tl.prod) (mul_le_mul_of_nonneg_left ih (opNorm_nonneg A))

lemma opNorm_unitary_le {N : ℕ} {U : QubitOp N} (hU : Uᴴ * U = 1) :
    opNorm U ≤ 1 := by
  unfold opNorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  have hsq : ‖opToCLM U v‖ ^ 2 = ‖v‖ ^ 2 := by
    have hinner : ∀ w : EuclideanSpace ℂ (QubitIdx N),
        ‖w‖ ^ 2 = (∑ i : QubitIdx N, star (w i) * w i).re := by
      intro w
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Complex.re_sum, Complex.star_def]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_comm, Complex.mul_conj, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hinner, hinner]
    congr 1
    have hsum : ∑ i : QubitIdx N, star (opToCLM U v i) * opToCLM U v i =
        ∑ j : QubitIdx N, star (v j) * v j := by
      have hlhs : ∑ i : QubitIdx N, star (opToCLM U v i) * opToCLM U v i =
          ∑ j : QubitIdx N, ∑ k : QubitIdx N, star (v j) * (Uᴴ * U) j k * v k := by
        simp only [opToCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
          LinearEquiv.coe_coe, EuclideanSpace.equiv_symm_pi_apply, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
          Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Finset.sum_comm]
        conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        ring
      rw [hlhs, hU]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_eq_single j]
      · simp [Matrix.one_apply]
      · intro k _ hkj; simp [Matrix.one_apply, Ne.symm hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hsum]
  nlinarith [norm_nonneg (opToCLM U v), norm_nonneg v]

lemma norm_entry_le_opNorm {N : ℕ} (A : QubitOp N) (i j : QubitIdx N) :
    ‖A i j‖ ≤ opNorm A := by
  let ej : EuclideanSpace ℂ (QubitIdx N) := EuclideanSpace.single j (1 : ℂ)
  have hej : ‖ej‖ = 1 := by simp [ej]
  have h1 : ‖opToCLM A ej i‖ ≤ ‖opToCLM A ej‖ := PiLp.norm_apply_le (opToCLM A ej) i
  have h2 : ‖opToCLM A ej‖ ≤ opNorm A * ‖ej‖ := ContinuousLinearMap.le_opNorm (opToCLM A) ej
  have hval : opToCLM A ej i = A i j := by
    simp [opToCLM, ej, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  rw [hval] at h1
  rw [hej, mul_one] at h2
  exact le_trans h1 h2

/-- Explicit `2 × 2` unitary diagonalizing `signedPauli u` to `diag(1, -1)`. -/
noncomputable def signedPauliU : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; 1, -1]
  | 1 => ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; -1, 1]
  | 2 => ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; Complex.I, -Complex.I]
  | 3 => ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; -Complex.I, Complex.I]
  | 4 => !![1, 0; 0, 1]
  | 5 => !![0, 1; 1, 0]

private lemma inv_sqrt2_sq_complex : (((1 / Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_pow]
  have h : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]; push_cast; rfl

lemma signedPauliU_unitary (u : Fin 6) :
    (signedPauliU u)ᴴ * signedPauliU u = 1 := by
  have h2 := inv_sqrt2_sq_complex
  fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [signedPauliU, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.star_def] <;>
    first | ring | (linear_combination 2 * h2)

lemma signedPauliU_diag_depolDualF (u : Fin 6) :
    depolDualF u =
      signedPauliU u * Matrix.diagonal ![(7 / 2 : ℂ), (-5 / 2 : ℂ)] * (signedPauliU u)ᴴ := by
  have h2 := inv_sqrt2_sq_complex
  fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [depolDualF, signedPauli, signedPauliU, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.star_def] <;>
    first | ring | (linear_combination 6 * h2) | (linear_combination (-6) * h2) |
      (linear_combination (6 * Complex.I) * h2) |
      (linear_combination (-6 * Complex.I) * h2) |
      (linear_combination 1 * h2) | (linear_combination (-1) * h2)

lemma depolDualWeight_eq_restricted {N : ℕ} (s : Fin N → Fin 6) {U : Finset (Fin N)}
    {A : QubitOp N} (hA : A ∈ supportedOn U) :
    depolDualWeight s A =
      (A * kronOp (fun x ↦ if x ∈ U then depolDualF (s x) else (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace := by
  induction hA using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ⟨a, ha, rfl⟩
    unfold depolDualWeight pauliString globalDepolDualF
    rw [kronOp_mul, kronOp_mul, kronOp_trace, kronOp_trace]
    apply Finset.prod_congr rfl; intro x _
    by_cases hx : x ∈ U
    · simp [hx]
    · simp only [hx, ↓reduceIte, ha x hx, pauliMat_zero_eq_one, Matrix.one_mul, depolDualF_trace]
      simp [Matrix.trace, Fin.sum_univ_two]; ring
  | zero => simp [depolDualWeight]
  | add X Y _ _ ihX ihY =>
    rw [depolDualWeight_add, Matrix.add_mul, Matrix.trace_add, ihX, ihY]
  | smul c X _ ihX =>
    rw [depolDualWeight_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ihX]

/-- **Sharp `6^{|U|}` Dual-Weight Bound**: For any `A ∈ supportedOn U`,
`‖depolDualWeight s A‖ ≤ 6 ^ U.card * opNorm A`. -/
theorem norm_depolDualWeight_le {N : ℕ} (s : Fin N → Fin 6) {U : Finset (Fin N)}
    {A : QubitOp N} (hA : A ∈ supportedOn U) :
    ‖depolDualWeight s A‖ ≤ (6 : ℝ) ^ U.card * opNorm A := by
  rw [depolDualWeight_eq_restricted s hA]
  let V : QubitOp N := kronOp (fun x ↦ if x ∈ U then signedPauliU (s x) else 1)
  let D : QubitOp N := kronOp (fun x ↦
    if x ∈ U then Matrix.diagonal ![(7 / 2 : ℂ), (-5 / 2 : ℂ)]
    else Matrix.diagonal ![(1 / 2 : ℂ), (1 / 2 : ℂ)])
  have hV_unit : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [kronOp_conjTranspose, kronOp_mul]
    have h1 : (fun x : Fin N ↦ (if x ∈ U then signedPauliU (s x) else 1)ᴴ *
        (if x ∈ U then signedPauliU (s x) else 1)) = fun _ ↦ 1 := by
      funext x
      by_cases hx : x ∈ U
      · simp [hx, signedPauliU_unitary]
      · simp [hx]
    rw [h1]
    ext i j
    simp only [kronOp, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ↓reduceIte]
      have hne : ∃ x : Fin N, i x ≠ j x := by
        by_contra hall; push Not at hall; exact hij (funext hall)
      rcases hne with ⟨x, hx⟩
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Matrix.one_apply, hx])
  have hV_unit' : V * Vᴴ = 1 := Matrix.mul_eq_one_comm.mp hV_unit
  have hF_eq : kronOp (fun x ↦ if x ∈ U then depolDualF (s x) else (1 / 2 : ℂ) • 1) =
      V * D * Vᴴ := by
    dsimp only [V, D]
    rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul]
    congr 1; funext x
    by_cases hx : x ∈ U
    · simp only [hx, ↓reduceIte]; exact signedPauliU_diag_depolDualF (s x)
    · simp only [hx, ↓reduceIte, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      ext p q; fin_cases p <;> fin_cases q <;> simp
  rw [hF_eq]
  have htr : (A * (V * D * Vᴴ)).trace = ((Vᴴ * A * V) * D).trace := by
    calc (A * (V * D * Vᴴ)).trace
        = ((A * V * D) * Vᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * (A * V * D)).trace := Matrix.trace_mul_comm _ _
      _ = ((Vᴴ * A * V) * D).trace := by simp only [Matrix.mul_assoc]
  rw [htr]
  have hD_diag : ∀ i j : QubitIdx N, i ≠ j → D i j = 0 := by
    intro i j hij
    have hne : ∃ x : Fin N, i x ≠ j x := by
      by_contra hall; push Not at hall; exact hij (funext hall)
    rcases hne with ⟨x, hx⟩
    dsimp only [D, kronOp]
    simp only [Matrix.of_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
    by_cases hxU : x ∈ U <;> simp [hxU, Matrix.diagonal_apply_ne _ hx]
  have htr_diag : ((Vᴴ * A * V) * D).trace = ∑ i : QubitIdx N, (Vᴴ * A * V) i i * D i i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single i]
    · intro j _ hji; rw [hD_diag j i hji, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [htr_diag]
  have hop_conj : opNorm (Vᴴ * A * V) ≤ opNorm A := by
    have hV1 : opNorm V ≤ 1 := opNorm_unitary_le hV_unit
    have hVh1 : opNorm Vᴴ ≤ 1 := opNorm_unitary_le (by rw [Matrix.conjTranspose_conjTranspose]; exact hV_unit')
    calc opNorm (Vᴴ * A * V)
        ≤ opNorm (Vᴴ * A) * opNorm V := opNorm_mul_le _ _
      _ ≤ (opNorm Vᴴ * opNorm A) * opNorm V :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * opNorm A) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hVh1 (opNorm_nonneg A)) hV1
            (opNorm_nonneg V) (by linarith [opNorm_nonneg A])
      _ = opNorm A := by ring
  have hnorm_sum : ‖∑ i : QubitIdx N, (Vᴴ * A * V) i i * D i i‖ ≤
      opNorm A * ∑ i : QubitIdx N, ‖D i i‖ := by
    calc ‖∑ i : QubitIdx N, (Vᴴ * A * V) i i * D i i‖
        ≤ ∑ i : QubitIdx N, ‖(Vᴴ * A * V) i i * D i i‖ := norm_sum_le _ _
      _ = ∑ i : QubitIdx N, ‖(Vᴴ * A * V) i i‖ * ‖D i i‖ := by simp only [norm_mul]
      _ ≤ ∑ i : QubitIdx N, opNorm A * ‖D i i‖ := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right
            (le_trans (norm_entry_le_opNorm _ i i) hop_conj) (norm_nonneg _)
      _ = opNorm A * ∑ i : QubitIdx N, ‖D i i‖ := by rw [← Finset.mul_sum]
  have hD_sum : ∑ i : QubitIdx N, ‖D i i‖ = (6 : ℝ) ^ U.card := by
    have hnorm_D : ∀ i : QubitIdx N, ‖D i i‖ =
        ∏ x : Fin N, ‖if x ∈ U then (![(7 / 2 : ℂ), (-5 / 2 : ℂ)] (i x))
          else (![(1 / 2 : ℂ), (1 / 2 : ℂ)] (i x))‖ := by
      intro i
      dsimp only [D, kronOp]
      simp only [Matrix.of_apply, norm_prod]
      apply Finset.prod_congr rfl; intro x _
      by_cases hx : x ∈ U <;> simp [hx]
    simp_rw [hnorm_D]
    rw [← Fintype.prod_sum]
    have hsite : ∀ x : Fin N,
        (∑ b : Fin 2, ‖if x ∈ U then (![(7 / 2 : ℂ), (-5 / 2 : ℂ)] b)
          else (![(1 / 2 : ℂ), (1 / 2 : ℂ)] b)‖) = if x ∈ U then (6 : ℝ) else 1 := by
      intro x
      by_cases hx : x ∈ U
      · simp only [hx, ↓reduceIte, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        have h1 : ‖(7 / 2 : ℂ)‖ = (7 / 2 : ℝ) := by
          have : (7 / 2 : ℂ) = ((7 / 2 : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
        have h2 : ‖(-5 / 2 : ℂ)‖ = (5 / 2 : ℝ) := by
          have : (-5 / 2 : ℂ) = ((-5 / 2 : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_of_nonpos (by norm_num)]; norm_num
        rw [h1, h2]; norm_num
      · simp only [hx, ↓reduceIte, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        have h1 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
          have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
        rw [h1]; norm_num
    simp_rw [hsite]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    ext x; simp
  rw [hD_sum] at hnorm_sum
  linarith

end OperatorNormAndDualBound

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
        ← Function.iterate_succ_apply', heq]
  unfold reachComponent
  rw [← Function.iterate_succ_apply', hconst (S.card + 1) (by omega), hconst S.card hk]

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
        have hunion : (γ ∩ δ) ∪ (γ \ δ) = γ := Finset.inter_union_sdiff γ δ
        have hdisj : Disjoint (γ ∩ δ) (γ \ δ) := Finset.disjoint_inter_sdiff γ δ
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
        have hunion : (δ ∩ γ) ∪ (δ \ γ) = δ := Finset.inter_union_sdiff δ γ
        have hdisj : Disjoint (δ ∩ γ) (δ \ γ) := Finset.disjoint_inter_sdiff δ γ
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
    rw [Fintype.sum_pow]; rfl
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
  rw [List.map_ofFn, List.prod_ofFn]

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
  have hclm_cont : Continuous (opToCLM (N := N)) := by
    have hlin : LinearMap ℂ (QubitOp N) (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
      { toFun := opToCLM, map_add' := opToCLM_add, map_smul' := opToCLM_smul }
    exact hlin.continuous_of_finiteDimensional
  have hhas_clm : HasSum (fun m : ℕ ↦ opToCLM (((-(β' : ℂ)) ^ m / (m.factorial : ℂ)) • polyTermSum h γ m))
      (opToCLM (polyOp h β' γ)) := by
    let L : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
      { toFun := opToCLM, map_add' := opToCLM_add, map_smul' := opToCLM_smul, cont := hclm_cont }
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
      rw [pow_succ, ih, hermFunc_id hH, hermFunc_mul]
      congr 1; funext e; rw [pow_succ]
  simp_rw [hpow]
  rw [hasSum_pi_iff]
  intro i
  rw [hasSum_pi_iff]
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
lemma polyOp_union_of_disjoint {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    (hsupp : ∀ X, h X ∈ supportedOn X) (β' : ℝ)
    {γ₁ γ₂ : Polymer N} (hdisj_supp : Disjoint (polySupp γ₁) (polySupp γ₂))
    (hdisj : Disjoint γ₁ γ₂) :
    polyOp h β' (γ₁ ∪ γ₂) = polyOp h β' γ₁ * polyOp h β' γ₂ := by
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
  have hconv : ∀ m : ℕ,
      polyTermSum h (γ₁ ∪ γ₂) m =
        ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℂ) • (polyTermSum h γ₁ k * polyTermSum h γ₂ (m - k)) := by
    intro m
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
      · rfl
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
      rw [Finset.sum_mul_sum]
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
              hjnot1 (Finset.mem_filter.mp (hfT.symm ▸ hjT)).2⟩
            refine Finset.mem_image.mpr ⟨e2.symm ⟨j, hjT2⟩, Finset.mem_univ _, by simp⟩
      · intro f₁ _ f₂ _ heq
        ext j
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
            have h1 : (List.finRange m).filter (fun j ↦ f j ∈ γ₁) = T.sort (· ≤ ·) := by
              apply List.Pairwise.eq_of_mem_iff
              · exact (List.nodup_finRange m).filter _
              · exact T.sort_nodup (· ≤ ·)
              · exact (List.pairwise_lt_finRange m).filter _ |>.imp le_of_lt
              · exact T.pairwise_sort (· ≤ ·)
              · intro j
                simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
                  Finset.mem_sort]
                rw [← hfT]; simp
            rw [h1]
            apply List.ext_getElem
            · simp
            · intro i hi1 hi2; simp [e1, Finset.orderIsoOfFin_apply]
          have hmap : (List.ofFn f).filter (· ∈ γ₁) = ((List.finRange m).filter (fun j ↦ f j ∈ γ₁)).map f := by
            rw [← List.ofFn_eq_map, List.filter_map]; rfl
          rw [hmap, hfin, List.map_ofFn]; rfl
        have hfilt2 : (List.ofFn f).filter (· ∈ γ₂) = List.ofFn (fun b : Fin (m - T.card) ↦ f (e2 b).1) := by
          have hfin : (List.finRange m).filter (fun j ↦ f j ∈ γ₂) = List.ofFn (fun b : Fin (m - T.card) ↦ (e2 b).1) := by
            have h1 : (List.finRange m).filter (fun j ↦ f j ∈ γ₂) = T2.sort (· ≤ ·) := by
              apply List.Pairwise.eq_of_mem_iff
              · exact (List.nodup_finRange m).filter _
              · exact T2.sort_nodup (· ≤ ·)
              · exact (List.pairwise_lt_finRange m).filter _ |>.imp le_of_lt
              · exact T2.pairwise_sort (· ≤ ·)
              · intro j
                simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
                  Finset.mem_sort, T2, Finset.mem_sdiff, Finset.mem_univ]
                rw [← hfT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro h2 h1; exact Finset.disjoint_left.mp hdisj h1 h2
                · intro hnot1
                  exact (Finset.mem_union.mp (Fintype.mem_piFinset.mp hfpi j)).resolve_left hnot1
            rw [h1]
            apply List.ext_getElem
            · simp [hT2card]
            · intro i hi1 hi2; simp [e2, Finset.orderIsoOfFin_apply]
          have hmap : (List.ofFn f).filter (· ∈ γ₂) = ((List.finRange m).filter (fun j ↦ f j ∈ γ₂)).map f := by
            rw [← List.ofFn_eq_map, List.filter_map]; rfl
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
        Finset.sum_const, hcard_eq, nsmul_eq_smul_cast ℂ]
    · intro T _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (by simpa using Finset.card_le_univ T)
  -- Entrywise Cauchy product on `ℂ`
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
  ext i j
  have hAB_ij : (polyOp h β' γ₁ * polyOp h β' γ₂) i j =
      ∑ l : QubitIdx N, polyOp h β' γ₁ i l * polyOp h β' γ₂ l j := rfl
  rw [hAB_ij]
  have hhas_ij : HasSum (fun m : ℕ ↦ (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j)
      (∑ l : QubitIdx N, polyOp h β' γ₁ i l * polyOp h β' γ₂ l j) := by
    have hterm_ij : ∀ m : ℕ, (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j =
        ∑ l : QubitIdx N, ∑ p ∈ Finset.antidiagonal m, A p.1 i l * B p.2 l j := by
      intro m
      simp only [Matrix.sum_apply, Matrix.mul_apply]
      rw [Finset.sum_comm]
    simp_rw [hterm_ij]
    apply hasSum_sum
    intro l _
    have h1l : HasSum (fun k ↦ A k i l) (polyOp h β' γ₁ i l) :=
      (hasSum_pi_iff.mp ((hasSum_pi_iff.mp hA_has) i)) l
    have h2l : HasSum (fun k ↦ B k l j) (polyOp h β' γ₂ l j) :=
      (hasSum_pi_iff.mp ((hasSum_pi_iff.mp hB_has) l)) j
    have hs1l : Summable (fun k ↦ ‖A k i l‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun k ↦ le_trans (norm_entry_le_opNorm _ i l) (opNorm_polyTermSum_scaled_le h β' γ₁ k)) hsr1
    have hs2l : Summable (fun k ↦ ‖B k l j‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun k ↦ le_trans (norm_entry_le_opNorm _ l j) (opNorm_polyTermSum_scaled_le h β' γ₂ k)) hsr2
    exact HasSum.mul_antidiagonal h1l h2l hs1l hs2l
  have hhas_lhs : HasSum (fun m : ℕ ↦ (∑ p ∈ Finset.antidiagonal m, A p.1 * B p.2) i j)
      (polyOp h β' (γ₁ ∪ γ₂) i j) := by
    have h1 := (hasSum_pi_iff.mp ((hasSum_pi_iff.mp (hasSum_polyOp h β' (γ₁ ∪ γ₂))) i)) j
    exact h1.congr_fun fun m ↦ by rw [hanti m]
  exact hhas_lhs.unique hhas_ij

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
        refine (hasSum_single 0 fun m hm ↦ ?_).congr_sum (by simp [h0])
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        simp [hsucc k]
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
        rw [pow_succ', ih, Finset.sum_mul_sum]
        refine Finset.sum_bij (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
          rw [Fintype.mem_piFinset]
          intro j; refine Fin.cases hp1 (fun k ↦ Fintype.mem_piFinset.mp hp2 k) j
        · intro p₁ _ p₂ _ heq
          ext
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
  symm
  refine Finset.sum_bij (fun I _ ↦ I.biUnion id) ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_powerset]
    intro X hX
    rcases Finset.mem_biUnion.mp hX with ⟨γ, hγI, hXγ⟩
    exact (mem_connectedPolymers.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1 hγI)).1 hXγ
  · intro I₁ hI₁ I₂ hI₂ heq; exact hinj I₁ hI₁ I₂ hI₂ heq
  · intro S hS; exact hsurj S hS
  · intro I hI
    have hcomp := (Finset.mem_filter.mp hI).2
    have hneI : ∀ γ ∈ I, ∀ X ∈ γ, X.Nonempty := fun γ hγ X hX ↦
      hne X ((mem_connectedPolymers.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1 hγ)).1 hX)
    exact (depolDualWeight_polyOp_biUnion h hsupp s β' I hcomp hneI).symm

end PolymerExpansion

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
    have hdecomp : ∀ γ ∈ dom,
        ∃ I ∈ (connectedPolymers E).powerset.filter (fun I ↦ isCompatPolymer polyIncompat I),
          I.biUnion id = γ.erase X₀ := by
      intro γ hγ
      have hγE : γ ⊆ E := (mem_connectedPolymers.mp (Finset.mem_filter.mp hγ).1).1
      exact (compatible_connectedPolymers_bijection E hne).2 (γ.erase X₀)
        (Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hγE))
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
        rw [← hrepC]
        exact (hcomp_hits γ hγ I hI hIU hC.choose hCI).2
    have hrep_inj : ∀ γ ∈ dom,
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
      simp only [toTarget, hγ, ↓reduceDIte]
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
      simp only [toTarget, hγ, ↓reduceDIte]
      set I := (hdecomp γ hγ).choose
      have hI := (hdecomp γ hγ).choose_spec.1
      have hIU := (hdecomp γ hγ).choose_spec.2
      rw [← hIU]
      have hpair_disj : (I : Set (Polymer N)).PairwiseDisjoint id := by
        intro C₁ hC₁ C₂ hC₂ hne12
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
      rw [Finset.sum_sigma, ← Finset.mul_sum]
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
          apply Finset.prod_le_prod
          · intro Y hY
            have hnn : 0 ≤ ∑ C ∈ F Y, ∏ X ∈ C, η X := Finset.sum_nonneg fun C hC ↦
              Finset.prod_nonneg fun X hX ↦
                hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hC).1).1 hX)
            linarith
          · intro Y hY
            linarith [ih Y (Finset.mem_filter.mp hY).1]

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
          apply Finset.prod_le_prod
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
              refine Finset.sum_biUnion_le_sum_of_nonneg fun γ' hγ' ↦ ?_
              rcases Finset.mem_biUnion.mp hγ' with ⟨_, _, h3⟩
              have hγ'E := (mem_connectedPolymers.mp (Finset.mem_filter.mp h3).1).1
              exact Finset.prod_nonneg fun X hX ↦ hηTilde_nn X (hγ'E hX)
          _ ≤ ∑ x ∈ polySupp γ, ∑ Y ∈ E.filter (fun Y ↦ x ∈ Y),
                ∑ γ' ∈ Λ₀.filter (fun γ' ↦ Y ∈ γ'), ∏ X ∈ γ', ηTilde X := by
              apply Finset.sum_le_sum; intro x _
              refine Finset.sum_biUnion_le_sum_of_nonneg fun γ' hγ' ↦ ?_
              have hγ'E := (mem_connectedPolymers.mp (Finset.mem_filter.mp hγ').1).1
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
  have hpos : ∀ s : Fin N → Fin 6,
      0 < (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re := by
    intro s
    let f : ℝ → ℝ := fun t ↦
      (depolDualWeight s (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ))))).re
    have hf_cont : Continuous f := by
      have hherm_cont : Continuous (fun t : ℝ ↦
          hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) := by
        apply continuous_pi; intro i; apply continuous_pi; intro j
        let U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
        have hentry : ∀ t : ℝ,
            (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) i j =
              ∑ k : QubitIdx N, U i k * Complex.exp (-(t * (β / 2) : ℂ) * (hH.eigenvalues k : ℂ)) * Uᴴ k j := by
          intro t; unfold hermFunc; simp only [U, Matrix.mul_apply, Matrix.diagonal_apply]
          apply Finset.sum_congr rfl; intro x _
          rw [Finset.sum_eq_single x]
          · simp
          · intro y _ hyx; simp [hyx]
          · intro hx; exact absurd (Finset.mem_univ x) hx
        simp_rw [hentry]
        refine continuous_finset_sum _ fun k _ ↦ ?_
        refine (continuous_const.mul ?_).mul continuous_const
        exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.mul continuous_const).neg.mul continuous_const)
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
        apply hermFunc_herm_of_real
        intro e
        have hreal : Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)) =
            ((Real.exp (-(t * (β / 2)) * e) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
        rw [hreal, Complex.ofReal_im]
      have hz : depolDualWeight s
          (hermFunc hH (fun e ↦ Complex.exp (-(t * (β / 2) : ℂ) * (e : ℂ)))) = 0 :=
        Complex.ext hft0 him
      exact hnonzero s t ht hz
    by_contra hle
    push Not at hle
    have h1_val : f 1 = (depolDualWeight s
        (hermFunc hH (fun e ↦ Complex.exp (-(β / 2 : ℂ) * (e : ℂ))))).re := by
      dsimp only [f]; congr 3; funext e; simp
    have h0mem' : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by linarith [h1_val], by linarith⟩
    rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf_cont.continuousOn h0mem' with
      ⟨t, ht, hft⟩
    exact hf_ne t ht hft
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
    congr 1; funext e
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
    apply hermFunc_herm_of_real
    intro e
    have hreal : Complex.exp (-(β / 2 : ℂ) * (e : ℂ)) = ((Real.exp (-(β / 2) * e) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [hreal, Complex.ofReal_im]
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
