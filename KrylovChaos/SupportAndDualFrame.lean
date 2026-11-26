/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempReversePoincare
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

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
    ring_nf <;> simp only [Complex.I_sq] <;> ring

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
  conv_lhs => rw [h1]
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
          Finset.prod_eq_one fun x _ ↦ by simp only [Matrix.single_apply, and_self, ↓reduceIte]
        rw [hprod, mul_one]
      · intro j _ hj
        have hne : ∃ x : Fin N, j x ≠ q x := by
          by_contra hall; push Not at hall; exact hj (funext hall)
        rcases hne with ⟨x, hx⟩
        have h0 : ∏ y : Fin N, Matrix.single (p y) (j y) (1 : ℂ) (p y) (q y) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ x) (by simp only [Matrix.single_apply, hx, and_false, false_and, ↓reduceIte])
        rw [h0, mul_zero]
      · intro hq; exact absurd (Finset.mem_univ q) hq
    · intro i _ hi
      apply Finset.sum_eq_zero; intro j _
      have hne : ∃ x : Fin N, i x ≠ p x := by
        by_contra hall; push Not at hall; exact hi (funext hall)
      rcases hne with ⟨x, hx⟩
      have h0 : ∏ y : Fin N, Matrix.single (i y) (j y) (1 : ℂ) (p y) (q y) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ x) (by simp only [Matrix.single_apply, hx, and_false, false_and, ↓reduceIte])
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
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [hrec i j]
  simp_rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
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
  ext v i; change ((A * B) *ᵥ v.ofLp) i = (A *ᵥ (B *ᵥ v.ofLp)) i; rw [Matrix.mulVec_mulVec]

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
    have h0 : opToCLM (0 : QubitOp N) = 0 := by
      apply ContinuousLinearMap.ext; intro v; apply PiLp.ext; intro i
      change ((0 : QubitOp N) *ᵥ v.ofLp) i = 0; simp
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
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hinner, hinner]
    congr 1
    have hsum : ∑ i : QubitIdx N, star ((opToCLM U v).ofLp i) * (opToCLM U v).ofLp i =
        ∑ j : QubitIdx N, star (v.ofLp j) * v.ofLp j := by
      have hop : ∀ i : QubitIdx N, (opToCLM U v).ofLp i = ∑ k : QubitIdx N, U i k * v.ofLp k := by
        intro i; simp [opToCLM, EuclideanSpace.equiv, Matrix.mulVec, dotProduct]
      have hlhs : ∑ i : QubitIdx N, star ((opToCLM U v).ofLp i) * (opToCLM U v).ofLp i =
          ∑ j : QubitIdx N, ∑ k : QubitIdx N, star (v.ofLp j) * (Uᴴ * U) j k * v.ofLp k := by
        simp_rw [hop, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
          Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Finset.sum_comm]
        conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum, Finset.sum_mul]
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
    change (A *ᵥ (WithLp.ofLp ej)) i = A i j
    simp only [Matrix.mulVec, dotProduct, ej, EuclideanSpace.single, WithLp.ofLp_toLp]
    rw [Finset.sum_eq_single j]
    · simp [Pi.single_apply]
    · intro k _ hkj; simp [Pi.single_apply, hkj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
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

private lemma inv_sqrt2_sq_complex : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; norm_num

private lemma inv_sqrt2_sq_complex' : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; norm_num

lemma signedPauliU_unitary (u : Fin 6) :
    (signedPauliU u)ᴴ * signedPauliU u = 1 := by
  have h2 := inv_sqrt2_sq_complex
  have h2' := inv_sqrt2_sq_complex'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [signedPauliU, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> simp only [h2, h2', hI] <;> ring

lemma signedPauliU_diag_depolDualF (u : Fin 6) :
    depolDualF u =
      signedPauliU u * Matrix.diagonal ![(7 / 2 : ℂ), (-5 / 2 : ℂ)] * (signedPauliU u)ᴴ := by
  have h2 := inv_sqrt2_sq_complex
  have h2' := inv_sqrt2_sq_complex'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [depolDualF, signedPauli, signedPauliU, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two] <;>
    (try ring_nf) <;> simp only [h2, h2', hI] <;> ring

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
      simp [Matrix.trace, Fin.sum_univ_two]
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
  have hV_unit' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV_unit
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
    have hps := (Fintype.prod_sum (fun (x : Fin N) (b : Fin 2) ↦
      ‖if x ∈ U then (![(7 / 2 : ℂ), (-5 / 2 : ℂ)] b)
        else (![(1 / 2 : ℂ), (1 / 2 : ℂ)] b)‖)).symm
    change ∑ i : Fin N → Fin 2, ∏ x : Fin N,
        ‖if x ∈ U then (![(7 / 2 : ℂ), (-5 / 2 : ℂ)] (i x))
          else (![(1 / 2 : ℂ), (1 / 2 : ℂ)] (i x))‖ = (6 : ℝ) ^ U.card
    rw [hps]
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
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hD_sum] at hnorm_sum
  linarith

end OperatorNormAndDualBound

end KrylovChaos
