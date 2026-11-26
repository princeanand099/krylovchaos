/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.DepolarizedFrame
import KrylovChaos.OperatorBridges
import KrylovChaos.KoteckyPreiss
import KrylovChaos.ConcreteCombinatorics
import Mathlib.Tactic

/-!
# Operator-Level Lemma 7.2, Lemma 7.3, Theorem 1.3(a) & Theorem 1.3(b) (Flaws #2, #3, #13)

Replaces the scalar-wrapper proofs of Lemma 7.2, Lemma 7.3, and Theorem 1.3(a)–(b) with
genuine operator-level proofs directly on `QubitOp N`:
1. **Lemma 7.1/7.3 Single-Site & Multi-Site Conditioning on `QubitOp N`**:
   Constructs the explicit Hermitian square root `depolPHalf s` (`depolPHalf s * depolPHalf s = depolP s`)
   and proves `(1/16) ‖Y‖_HS² ≤ Re Tr(P̃_s Yᴴ P̃_{s'} Y) ≤ (9/16) ‖Y‖_HS²` directly on `Mat2`,
   then lifts to `prodDepolNormSq s s' (siteSizeOp x A) ≤ 9 * prodDepolNormSq s s' (A - B)`
   for all `A : QubitOp N` and `B ∈ singleSiteTrivialSubmodule N x`.
2. **Lemma 7.3(3) Concrete Product Filtration Identity**:
   Via the product orthonormal basis of `(QubitOp N, prodDepolInner s s')`, proves
   `∑ x, prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A = ∑ k < N, prodDepolDistSq s s' (filtrationSubmodule N k) A`.
3. **Theorem 1.3(a) (Operator-Level Reverse Poincaré on `QubitOp N`)**:
   For any `G : GibbsData N` with positive depolarized frame expansion `G.ρHalf = ∑ s, π(s) P̃_s`
   (`π s ≥ 0`) and EVERY `A : QubitOp N`:
   `Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`.
-/

namespace KrylovChaos

open Matrix

section DepolarizedConditioning

lemma hsNormSq_nonneg {N : ℕ} (A : QubitOp N) : 0 ≤ hsNormSq A := by
  unfold hsNormSq
  rw [← qubitOpToHS_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := qubitOpToHS N A)

/-- Explicit Hermitian square root of the single-site depolarized frame state
`P̃_s = (1/2) I + (1/4) σ_s` (eigenvalues `3/4` and `1/4`, so square-root eigenvalues are
`√3/2` and `1/2`). -/
noncomputable def depolPHalf (s : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.sqrt 3 + 1) / 4 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
  (((Real.sqrt 3 - 1) / 4 : ℝ) : ℂ) • signedPauli s

lemma signedPauli_herm (s : Fin 6) : (signedPauli s)ᴴ = signedPauli s := by
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [signedPauli, pauliX, pauliY, pauliZ, Complex.star_def]

lemma signedPauli_sq (s : Fin 6) : signedPauli s * signedPauli s = 1 := by
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [signedPauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma depolPHalf_herm (s : Fin 6) : (depolPHalf s)ᴴ = depolPHalf s := by
  unfold depolPHalf
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, signedPauli_herm]
  simp [Complex.star_def]

lemma depolPHalf_sq (s : Fin 6) : depolPHalf s * depolPHalf s = depolP s := by
  unfold depolPHalf depolP
  have hsq := signedPauli_sq s
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hmul : (((Real.sqrt 3 + 1) / 4 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      ((((Real.sqrt 3 + 1) / 4 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((((Real.sqrt 3 + 1) / 4 : ℝ) : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, sq]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  linear_combination ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j / 8 + signedPauli s i j / 8) * h3

/-- Explicit inverse `depolPHalfInv s` of `depolPHalf s` (eigenvalues `2/√3` and `2`). -/
noncomputable def depolPHalfInv (s : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((1 + 1 / Real.sqrt 3 : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
  (((1 / Real.sqrt 3 - 1 : ℝ)) : ℂ) • signedPauli s

lemma depolPHalfInv_mul (s : Fin 6) : depolPHalfInv s * depolPHalf s = 1 := by
  unfold depolPHalfInv depolPHalf
  have hsq := signedPauli_sq s
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp [hs3]
  ring

/-- Global product depolarized Wightman inner product `(A | B)_{s,s'} = Tr(P̃_s Aᴴ P̃_{s'} B)`. -/
lemma depolPHalf_mul_inv (s : Fin 6) : depolPHalf s * depolPHalfInv s = 1 := by
  have h1 := depolPHalfInv_mul s
  have hcomm : depolPHalf s * depolPHalfInv s = depolPHalfInv s * depolPHalf s := by
    unfold depolPHalf depolPHalfInv
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, signedPauli_sq]
    ext i j; simp; ring
  rw [hcomm, h1]

noncomputable def prodDepolInner {N : ℕ} (s s' : Fin N → Fin 6) (A B : QubitOp N) : ℂ :=
  Matrix.trace (globalDepolP N s * Aᴴ * globalDepolP N s' * B)

/-- Global product depolarized Wightman norm squared `‖A‖_{s,s'}² = Re Tr(P̃_s Aᴴ P̃_{s'} A)`. -/
noncomputable def prodDepolNormSq {N : ℕ} (s s' : Fin N → Fin 6) (A : QubitOp N) : ℝ :=
  (prodDepolInner s s' A A).re

/-- Global product depolarized square-root operator `P̃_s^{1/2} = ⨂_x depolPHalf (s x)`. -/
noncomputable def globalDepolPHalf (N : ℕ) (s : Fin N → Fin 6) : QubitOp N :=
  kronOp (fun x ↦ depolPHalf (s x))

lemma globalDepolPHalf_herm (N : ℕ) (s : Fin N → Fin 6) :
    (globalDepolPHalf N s)ᴴ = globalDepolPHalf N s := by
  unfold globalDepolPHalf
  rw [kronOp_conjTranspose]; congr 1; funext x; exact depolPHalf_herm (s x)

lemma globalDepolPHalf_sq (N : ℕ) (s : Fin N → Fin 6) :
    globalDepolPHalf N s * globalDepolPHalf N s = globalDepolP N s := by
  unfold globalDepolPHalf globalDepolP
  rw [kronOp_mul]; congr 1; funext x; exact depolPHalf_sq (s x)

/-- Exact Hilbert–Schmidt representation:
`prodDepolInner s s' A B = hsInner (P̃_{s'}^{1/2} A P̃_s^{1/2}) (P̃_{s'}^{1/2} B P̃_s^{1/2})`. -/
lemma prodDepolInner_eq_hsInner {N : ℕ} (s s' : Fin N → Fin 6) (A B : QubitOp N) :
    prodDepolInner s s' A B =
      hsInner (globalDepolPHalf N s' * A * globalDepolPHalf N s)
              (globalDepolPHalf N s' * B * globalDepolPHalf N s) := by
  unfold prodDepolInner hsInner
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    globalDepolPHalf_herm, globalDepolPHalf_herm]
  have h1 : (globalDepolPHalf N s * (Aᴴ * globalDepolPHalf N s') *
      (globalDepolPHalf N s' * B * globalDepolPHalf N s)).trace =
      (globalDepolPHalf N s * globalDepolPHalf N s * Aᴴ *
        (globalDepolPHalf N s' * globalDepolPHalf N s') * B).trace := by
    have hl : globalDepolPHalf N s * (Aᴴ * globalDepolPHalf N s') *
        (globalDepolPHalf N s' * B * globalDepolPHalf N s) =
        (globalDepolPHalf N s * Aᴴ * (globalDepolPHalf N s' * globalDepolPHalf N s') * B) *
          globalDepolPHalf N s := by simp only [Matrix.mul_assoc]
    have hr : globalDepolPHalf N s *
        (globalDepolPHalf N s * Aᴴ * (globalDepolPHalf N s' * globalDepolPHalf N s') * B) =
        globalDepolPHalf N s * globalDepolPHalf N s * Aᴴ *
          (globalDepolPHalf N s' * globalDepolPHalf N s') * B := by simp only [Matrix.mul_assoc]
    rw [hl, ← hr, Matrix.trace_mul_comm]
  rw [h1, globalDepolPHalf_sq, globalDepolPHalf_sq]

lemma prodDepolNormSq_nonneg {N : ℕ} (s s' : Fin N → Fin 6) (A : QubitOp N) :
    0 ≤ prodDepolNormSq s s' A := by
  unfold prodDepolNormSq
  rw [prodDepolInner_eq_hsInner]
  exact hsNormSq_nonneg _

/-- Exact `L²` distance squared from `A` to a subspace `S` in a Wightman inner product
defined by a positive Hermitian pair `(P, P')`. -/
noncomputable def wightmanDistSq {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) : ℝ :=
  sInf { r : ℝ | ∃ B ∈ S, r = gibbsWightmanNormSq G (A - B) }

/-- Concrete product-frame distance squared `inf_{B ∈ S} ‖A - B‖_{s,s'}²`. -/
noncomputable def prodDepolDistSq {N : ℕ} (s s' : Fin N → Fin 6)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) : ℝ :=
  sInf { r : ℝ | ∃ B ∈ S, r = prodDepolNormSq s s' (A - B) }

/-- **Exact Projection = Best Approximation Identity on `QubitOp N`**:
`Re (A | (1 - Π_S^{(β)}) A)_β^W = wightmanDistSq G S A`. -/
theorem wightmanSubspaceProj_eq_distSq {N : ℕ} (G : GibbsData N)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) :
    (gibbsWightmanInner G A (A - wightmanSubspaceProj G S A)).re =
      wightmanDistSq G S A := by
  have hj_inv : ∀ X : QubitOp N, jBeta G.ρQuarter (jBeta G.ρQuarterInv X) = X := by
    intro X; unfold jBeta
    calc G.ρQuarter * (G.ρQuarterInv * X * G.ρQuarterInv) * G.ρQuarter
        = (G.ρQuarter * G.ρQuarterInv) * X * (G.ρQuarterInv * G.ρQuarter) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [G.inv_right, G.inv_left, Matrix.one_mul, Matrix.mul_one]
  let jLin : QubitOp N →ₗ[ℂ] QubitOp N :=
    { toFun := fun X ↦ jBeta G.ρQuarter X
      map_add' := fun X Y ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let K : Submodule ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) :=
    S.map ((qubitOpToHS N).toLinearMap.comp jLin)
  letI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  set v : EuclideanSpace ℂ (QubitIdx N × QubitIdx N) := qubitOpToHS N (jBeta G.ρQuarter A)
  have hproj_mem : wightmanSubspaceProj G S A ∈ S := by
    have hKmem : K.starProjection v ∈ K := K.starProjection_apply_mem v
    rcases Submodule.mem_map.mp hKmem with ⟨B, hBS, hBeq⟩
    have hEq : wightmanSubspaceProj G S A = B := by
      unfold wightmanSubspaceProj
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.coe_mk,
        AddHom.coe_mk]
      change jBeta G.ρQuarterInv ((qubitOpToHS N).symm (K.starProjection v)) = B
      rw [← hBeq]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.coe_mk,
        AddHom.coe_mk, LinearEquiv.symm_apply_apply]
      unfold jBeta
      calc G.ρQuarterInv * (G.ρQuarter * B * G.ρQuarter) * G.ρQuarterInv
          = (G.ρQuarterInv * G.ρQuarter) * B * (G.ρQuarter * G.ρQuarterInv) := by
            simp only [Matrix.mul_assoc]
        _ = B := by rw [G.inv_left, G.inv_right, Matrix.one_mul, Matrix.mul_one]
    rw [hEq]; exact hBS
  have hv_proj : qubitOpToHS N (jBeta G.ρQuarter (wightmanSubspaceProj G S A)) =
      K.starProjection v := by
    unfold wightmanSubspaceProj
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [hj_inv, (qubitOpToHS N).apply_symm_apply]
    rfl
  have hJ_sub : ∀ X Y : QubitOp N,
      jBeta G.ρQuarter (X - Y) = jBeta G.ρQuarter X - jBeta G.ρQuarter Y := fun X Y ↦ by
    unfold jBeta; simp [Matrix.mul_sub, Matrix.sub_mul]
  have hinner_eq : ∀ X Y : QubitOp N,
      gibbsWightmanInner G X Y =
      @inner ℂ _ _ (qubitOpToHS N (jBeta G.ρQuarter X)) (qubitOpToHS N (jBeta G.ρQuarter Y)) := by
    intro X Y
    unfold gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf X Y G.ρQuarter_herm G.sq_quarter]
    exact (qubitOpToHS_inner _ _).symm
  have hself : (gibbsWightmanInner G A (A - wightmanSubspaceProj G S A)).re =
      gibbsWightmanNormSq G (A - wightmanSubspaceProj G S A) := by
    unfold gibbsWightmanNormSq
    rw [hinner_eq, hinner_eq, hJ_sub, map_sub, hv_proj]
    have horth : @inner ℂ _ _ (K.starProjection v) (v - K.starProjection v) = 0 :=
      (Submodule.mem_orthogonal K _).mp (Submodule.sub_starProjection_mem_orthogonal v) _
        (K.starProjection_apply_mem v)
    have hsplit : @inner ℂ _ _ v (v - K.starProjection v) =
        @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) := by
      calc @inner ℂ _ _ v (v - K.starProjection v)
          = @inner ℂ _ _ ((v - K.starProjection v) + K.starProjection v) (v - K.starProjection v) := by
            rw [sub_add_cancel]
        _ = @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) +
            @inner ℂ _ _ (K.starProjection v) (v - K.starProjection v) := inner_add_left _ _ _
        _ = @inner ℂ _ _ (v - K.starProjection v) (v - K.starProjection v) := by
            rw [horth, add_zero]
    rw [hsplit]
  rw [hself]
  apply le_antisymm
  · unfold wightmanDistSq
    apply le_csInf
    · exact ⟨_, wightmanSubspaceProj G S A, hproj_mem, rfl⟩
    · rintro r ⟨B, hBS, rfl⟩
      unfold gibbsWightmanNormSq
      rw [hinner_eq, hinner_eq, hJ_sub, hJ_sub, map_sub, map_sub, hv_proj]
      set w := qubitOpToHS N (jBeta G.ρQuarter B)
      have hwK : w ∈ K := Submodule.mem_map.mpr ⟨B, hBS, rfl⟩
      have hdiffK : K.starProjection v - w ∈ K := Submodule.sub_mem K (K.starProjection_apply_mem v) hwK
      have horth : @inner ℂ _ _ (v - K.starProjection v) (K.starProjection v - w) = 0 := by
        have h := (Submodule.mem_orthogonal K _).mp (Submodule.sub_starProjection_mem_orthogonal v) _ hdiffK
        rw [← inner_conj_symm] at h
        simpa using congrArg star h
      have hpyth : v - w = (v - K.starProjection v) + (K.starProjection v - w) := by abel
      rw [hpyth, inner_add_left, inner_add_right, inner_add_right, horth,
        show @inner ℂ _ _ (K.starProjection v - w) (v - K.starProjection v) = 0 from
          (Submodule.mem_orthogonal K _).mp (Submodule.sub_starProjection_mem_orthogonal v) _ hdiffK]
      simp only [add_zero, zero_add, Complex.add_re]
      have hnn : 0 ≤ (inner ℂ (K.starProjection v - w) (K.starProjection v - w)).re :=
        inner_self_nonneg (𝕜 := ℂ) (x := K.starProjection v - w)
      change (inner ℂ (v - K.starProjection v) (v - K.starProjection v)).re ≤ _
      linarith
  · unfold wightmanDistSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨B, _, rfl⟩
      unfold gibbsWightmanNormSq
      rw [hinner_eq]
      exact inner_self_nonneg (𝕜 := ℂ) (x := _)
    · exact ⟨wightmanSubspaceProj G S A, hproj_mem, rfl⟩

/-- **Exact Convex-Mixture Superadditivity of Wightman Distance**:
If `G.ρHalf = ∑ s, (π s : ℂ) • globalDepolP N s` with `π s ≥ 0`, then for ANY subspace
`S : Submodule ℂ (QubitOp N)` and ANY `A : QubitOp N`:
`∑ s, ∑ s', π s * π s' * prodDepolDistSq s s' S A ≤ (gibbsWightmanInner G A (A - wightmanSubspaceProj G S A)).re`. -/
theorem wightmanProj_convex_mixture_ge {N : ℕ} (G : GibbsData N)
    (π : (Fin N → Fin 6) → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hdecomp : G.ρHalf = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s)
    (S : Submodule ℂ (QubitOp N)) (A : QubitOp N) :
    ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
      π s * π s' * prodDepolDistSq s s' S A ≤
    (gibbsWightmanInner G A (A - wightmanSubspaceProj G S A)).re := by
  rw [wightmanSubspaceProj_eq_distSq]
  unfold wightmanDistSq
  apply le_csInf
  · exact ⟨_, 0, Submodule.zero_mem S, rfl⟩
  · rintro r ⟨B, hBS, rfl⟩
    have hexpand : gibbsWightmanNormSq G (A - B) =
        ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * prodDepolNormSq s s' (A - B) := by
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner prodDepolNormSq prodDepolInner
      rw [hdecomp]
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro s' _
      have hrew : (π s' : ℂ) * ((π s : ℂ) *
          (globalDepolP N s * (A - B)ᴴ * globalDepolP N s' * (A - B)).trace) =
          (((π s * π s' : ℝ) : ℂ)) *
            (globalDepolP N s * (A - B)ᴴ * globalDepolP N s' * (A - B)).trace := by
        push_cast; ring
      rw [hrew, Complex.re_ofReal_mul]
    rw [hexpand]
    apply Finset.sum_le_sum; intro s _
    apply Finset.sum_le_sum; intro s' _
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hπ s) (hπ s'))
    unfold prodDepolDistSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨B', _, rfl⟩
      exact prodDepolNormSq_nonneg s s' (A - B')
    · exact ⟨B, hBS, rfl⟩

/-- **First Inequality of Theorem 1.3(a) (Concrete Operator Form on `QubitOp N`)**:
For EVERY `G : GibbsData N` and EVERY `A : QubitOp N`,
`Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x : Fin N, ‖𝒮_x(A)‖_{β,W}²`.
Proved directly from best-approximation because `partialTraceSite x A ∈ singleSiteTrivialSubmodule N x`! -/
theorem theorem_1_3a_lower_concrete {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) := by
  unfold quantumGlauberGen
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G A (∑ x : Fin N, (A - singleSiteWightmanProj G x A)) =
      ∑ x : Fin N, gibbsWightmanInner G A (A - singleSiteWightmanProj G x A) := by
    unfold gibbsWightmanInner wightmanInner
    rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  apply Finset.sum_le_sum; intro x _
  rw [singleSiteWightmanProj, wightmanSubspaceProj_eq_distSq]
  unfold wightmanDistSq
  have hpt_mem : partialTraceSite x A ∈ singleSiteTrivialSubmodule N x := by
    have hexp : A = ∑ a : Fin N → Fin 4,
        (((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) • pauliString a) := by
      ext i j
      have hcomp : ∀ k l : QubitIdx N,
          ∑ a : Fin N → Fin 4, pauliString a k l * pauliString a i j =
            if k = j ∧ l = i then (2 : ℂ) ^ N else 0 := by
        intro k l
        unfold pauliString kronOp
        simp only [Matrix.of_apply]
        have hprod : (∑ a : Fin N → Fin 4,
            (∏ y : Fin N, pauliMat (a y) (k y) (l y)) *
            (∏ y : Fin N, pauliMat (a y) (i y) (j y))) =
            ∏ y : Fin N, ∑ c : Fin 4, pauliMat c (k y) (l y) * pauliMat c (i y) (j y) := by
          simp_rw [← Finset.prod_mul_distrib]
          exact (Fintype.prod_sum (fun (y : Fin N) (c : Fin 4) ↦
            pauliMat c (k y) (l y) * pauliMat c (i y) (j y))).symm
        rw [hprod]
        have hsingle : ∀ y : Fin N,
            (∑ c : Fin 4, pauliMat c (k y) (l y) * pauliMat c (i y) (j y)) =
            if k y = j y ∧ l y = i y then (2 : ℂ) else 0 := by
          intro y
          generalize k y = a1; generalize l y = a2; generalize i y = a3; generalize j y = a4
          fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;> fin_cases a4 <;>
            (simp [Fin.sum_univ_four, pauliMat]; try norm_num)
        simp_rw [hsingle]
        by_cases hkl : k = j ∧ l = i
        · rcases hkl with ⟨rfl, rfl⟩
          simp
        · rw [if_neg hkl]
          have hex : ∃ y : Fin N, ¬ (k y = j y ∧ l y = i y) := by
            by_contra hall; push Not at hall
            exact hkl ⟨funext fun y ↦ (hall y).1, funext fun y ↦ (hall y).2⟩
          rcases hex with ⟨y₀, hy₀⟩
          exact Finset.prod_eq_zero (Finset.mem_univ y₀) (if_neg hy₀)
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
        Matrix.mul_apply]
      have hrew : (∑ a : Fin N → Fin 4,
          1 / (2 : ℂ) ^ N * (∑ k : QubitIdx N, ∑ l : QubitIdx N, pauliString a k l * A l k) *
            pauliString a i j) =
          1 / (2 : ℂ) ^ N * ∑ k : QubitIdx N, ∑ l : QubitIdx N,
            A l k * (∑ a : Fin N → Fin 4, pauliString a k l * pauliString a i j) := by
        rw [Finset.mul_sum]
        have h1 : ∀ a : Fin N → Fin 4,
            1 / (2 : ℂ) ^ N * (∑ k : QubitIdx N, ∑ l : QubitIdx N, pauliString a k l * A l k) *
              pauliString a i j =
            ∑ k : QubitIdx N, ∑ l : QubitIdx N,
              1 / (2 : ℂ) ^ N * (A l k * (pauliString a k l * pauliString a i j)) := by
          intro a
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro l _; ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.mul_sum, Finset.mul_sum]
      rw [hrew]
      simp_rw [hcomp]
      have hsum_ij : (∑ k : QubitIdx N, ∑ l : QubitIdx N,
          A l k * if k = j ∧ l = i then (2 : ℂ) ^ N else 0) = A i j * (2 : ℂ) ^ N := by
        have hinner : ∀ k : QubitIdx N,
            (∑ l : QubitIdx N, A l k * if k = j ∧ l = i then (2 : ℂ) ^ N else 0) =
            if k = j then A i j * (2 : ℂ) ^ N else 0 := by
          intro k
          by_cases hkj : k = j
          · subst hkj; simp
          · simp [hkj]
        simp only [hinner, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [hsum_ij]
      have h2N : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
      field_simp [h2N]
    rw [hexp]
    have hpt_lin : partialTraceSite x (∑ a : Fin N → Fin 4,
        (((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) • pauliString a)) =
        ∑ a : Fin N → Fin 4,
          (((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) • partialTraceSite x (pauliString a)) := by
      unfold partialTraceSite
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro c _; rw [smul_comm]
    rw [hpt_lin]
    apply Submodule.sum_mem; intro a _
    apply Submodule.smul_mem
    have hpt_pauli : partialTraceSite x (pauliString a) =
        if a x = 0 then pauliString a else 0 := by
      unfold partialTraceSite pauliString
      have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
      have hconj : ∀ c : Fin 4,
          pauliSite x c * kronOp (fun y ↦ pauliMat (a y)) * pauliSite x c =
          kronOp (fun y ↦ if y = x then pauliMat c * pauliMat (a x) * pauliMat c else pauliMat (a y)) := by
        intro c; unfold pauliSite pauliString; rw [kronOp_mul, kronOp_mul]
        congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp
        · simp [hy, hp0]
      simp_rw [hconj]
      ext p q
      simp only [Matrix.smul_apply, Matrix.sum_apply, kronOp, Matrix.of_apply, smul_eq_mul]
      have hsplit : ∀ c : Fin 4,
          (∏ y : Fin N, (if y = x then pauliMat c * pauliMat (a x) * pauliMat c else pauliMat (a y)) (p y) (q y)) =
          (pauliMat c * pauliMat (a x) * pauliMat c) (p x) (q x) *
            ∏ y ∈ Finset.univ.erase x, pauliMat (a y) (p y) (q y) := by
        intro c
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
      simp_rw [hsplit, ← Finset.sum_mul, ← mul_assoc]
      have htw : (1 / 4 : ℂ) * (∑ c : Fin 4, (pauliMat c * pauliMat (a x) * pauliMat c) (p x) (q x)) =
          if a x = 0 then pauliMat 0 (p x) (q x) else 0 := by
        generalize a x = u; generalize p x = i1; generalize q x = j1
        fin_cases u <;> fin_cases i1 <;> fin_cases j1 <;>
          (simp [Fin.sum_univ_four, pauliMat, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
      rw [htw]
      by_cases hax : a x = 0
      · rw [if_pos hax, if_pos hax]
        simp only [kronOp, Matrix.of_apply]
        rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ pauliMat (a y) (p y) (q y)) (Finset.mem_univ x), hax]
      · rw [if_neg hax, if_neg hax, zero_mul, Matrix.zero_apply]
    rw [hpt_pauli]
    by_cases hax : a x = 0
    · rw [if_pos hax]
      exact Submodule.subset_span ⟨a, hax, rfl⟩
    · rw [if_neg hax]
      exact Submodule.zero_mem _
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨B, _, rfl⟩
    unfold gibbsWightmanNormSq gibbsWightmanInner
    rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
    exact hsNormSq_nonneg _
  · exact ⟨partialTraceSite x A, hpt_mem, rfl⟩

end DepolarizedConditioning


/-- Exact Pauli-string expansion of any `N`-qubit operator `A : QubitOp N`:
`A = ∑ a, ((1 / 2^N) * Tr(P_a * A)) • P_a`. -/
theorem pauli_expansion_concrete {N : ℕ} (A : QubitOp N) :
    A = ∑ a : Fin N → Fin 4,
      (((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) • pauliString a) := by
  ext i j
  have hcomp : ∀ k l : QubitIdx N,
      ∑ a : Fin N → Fin 4, pauliString a k l * pauliString a i j =
        if k = j ∧ l = i then (2 : ℂ) ^ N else 0 := by
    intro k l
    unfold pauliString kronOp
    simp only [Matrix.of_apply]
    have hprod : (∑ a : Fin N → Fin 4,
        (∏ y : Fin N, pauliMat (a y) (k y) (l y)) *
        (∏ y : Fin N, pauliMat (a y) (i y) (j y))) =
        ∏ y : Fin N, ∑ c : Fin 4, pauliMat c (k y) (l y) * pauliMat c (i y) (j y) := by
      simp_rw [← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun (y : Fin N) (c : Fin 4) ↦
        pauliMat c (k y) (l y) * pauliMat c (i y) (j y))).symm
    rw [hprod]
    have hsingle : ∀ y : Fin N,
        (∑ c : Fin 4, pauliMat c (k y) (l y) * pauliMat c (i y) (j y)) =
        if k y = j y ∧ l y = i y then (2 : ℂ) else 0 := by
      intro y
      generalize k y = a1; generalize l y = a2; generalize i y = a3; generalize j y = a4
      fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;> fin_cases a4 <;>
        (simp [Fin.sum_univ_four, pauliMat]; try norm_num)
    simp_rw [hsingle]
    by_cases hkl : k = j ∧ l = i
    · rcases hkl with ⟨rfl, rfl⟩; simp
    · rw [if_neg hkl]
      have hex : ∃ y : Fin N, ¬ (k y = j y ∧ l y = i y) := by
        by_contra hall; push Not at hall
        exact hkl ⟨funext fun y ↦ (hall y).1, funext fun y ↦ (hall y).2⟩
      rcases hex with ⟨y₀, hy₀⟩
      exact Finset.prod_eq_zero (Finset.mem_univ y₀) (if_neg hy₀)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]
  have hrew : (∑ a : Fin N → Fin 4,
      1 / (2 : ℂ) ^ N * (∑ k : QubitIdx N, ∑ l : QubitIdx N, pauliString a k l * A l k) *
        pauliString a i j) =
      1 / (2 : ℂ) ^ N * ∑ k : QubitIdx N, ∑ l : QubitIdx N,
        A l k * (∑ a : Fin N → Fin 4, pauliString a k l * pauliString a i j) := by
    rw [Finset.mul_sum]
    have h1 : ∀ a : Fin N → Fin 4,
        1 / (2 : ℂ) ^ N * (∑ k : QubitIdx N, ∑ l : QubitIdx N, pauliString a k l * A l k) *
          pauliString a i j =
        ∑ k : QubitIdx N, ∑ l : QubitIdx N,
          1 / (2 : ℂ) ^ N * (A l k * (pauliString a k l * pauliString a i j)) := by
      intro a
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro l _; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hrew]
  simp_rw [hcomp]
  have hsum_ij : (∑ k : QubitIdx N, ∑ l : QubitIdx N,
      A l k * if k = j ∧ l = i then (2 : ℂ) ^ N else 0) = A i j * (2 : ℂ) ^ N := by
    have hinner : ∀ k : QubitIdx N,
        (∑ l : QubitIdx N, A l k * if k = j ∧ l = i then (2 : ℂ) ^ N else 0) =
        if k = j then A i j * (2 : ℂ) ^ N else 0 := by
      intro k
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]
    simp only [hinner, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hsum_ij]
  have h2N : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
  field_simp [h2N]

section OperatorConditioningAndTheorem13

/-- Exact PSD decomposition `P̃_s = (1/4) I + (1/8) (I + σ_s)²`. -/
lemma depolP_sub_quarter (s : Fin 6) :
    depolP s = (1 / 4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 / 8 : ℂ) • ((1 + signedPauli s) * (1 + signedPauli s)) := by
  unfold depolP
  have hsq : (1 + signedPauli s) * (1 + signedPauli s) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 : ℂ) • signedPauli s := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      signedPauli_sq s]
    ext i j; simp; ring
  rw [hsq, smul_add, smul_smul, smul_smul]
  ext i j; simp; ring

/-- Exact PSD decomposition `(3/4) I - P̃_s = (1/8) (I - σ_s)²`. -/
lemma three_quarter_sub_depolP (s : Fin 6) :
    (3 / 4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      depolP s + (1 / 8 : ℂ) • ((1 - signedPauli s) * (1 - signedPauli s)) := by
  unfold depolP
  have hsq : (1 - signedPauli s) * (1 - signedPauli s) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (2 : ℂ) • signedPauli s := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      signedPauli_sq s]
    ext i j; simp; ring
  rw [hsq, smul_sub, smul_smul, smul_smul]
  ext i j; simp; ring

/-- General Hermitian product-trace nonnegativity:
for any `P = Lᴴ * L` and `Q = Rᴴ * R`, `0 ≤ Re Tr(P Aᴴ Q A)`. -/
lemma trace_quad_nonneg {N : ℕ} (L R A : QubitOp N) :
    0 ≤ (Matrix.trace ((Lᴴ * L) * Aᴴ * (Rᴴ * R) * A)).re := by
  have heq : Matrix.trace ((Lᴴ * L) * Aᴴ * (Rᴴ * R) * A) =
      hsInner (R * A * Lᴴ) (R * A * Lᴴ) := by
    unfold hsInner
    calc Matrix.trace ((Lᴴ * L) * Aᴴ * (Rᴴ * R) * A)
        = Matrix.trace (Lᴴ * (L * Aᴴ * (Rᴴ * R) * A)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((L * Aᴴ * (Rᴴ * R) * A) * Lᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((R * A * Lᴴ)ᴴ * (R * A * Lᴴ)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
  rw [heq]
  exact hsNormSq_nonneg _

/-- Operator `globalDepolP` with site `x` replaced by `M : Mat2`. -/
noncomputable def globalDepolPReplace {N : ℕ} (s : Fin N → Fin 6) (x : Fin N)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : QubitOp N :=
  kronOp (fun y ↦ if y = x then M else depolP (s y))

/-- **Lemma 7.3(1) (Concrete Operator-Level Single-Site Conditioning on `QubitOp N`)**:
For EVERY `s, s' : Fin N → Fin 6`, EVERY site `x : Fin N`, and EVERY `Y : QubitOp N`:
`(1/16) * Re Tr(P̃_{s, x→I} Yᴴ P̃_{s', x→I} Y) ≤ prodDepolNormSq s s' Y ≤ (9/16) * Re Tr(P̃_{s, x→I} Yᴴ P̃_{s', x→I} Y)`. -/
theorem lemma_7_3_operator_conditioning {N : ℕ} (s s' : Fin N → Fin 6) (x : Fin N)
    (Y : QubitOp N) :
    (1 / 16 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * globalDepolPReplace s' x 1 * Y)).re ≤
      prodDepolNormSq s s' Y ∧
    prodDepolNormSq s s' Y ≤
      (9 / 16 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * globalDepolPReplace s' x 1 * Y)).re := by
  have hrep_add : ∀ (t : Fin N → Fin 6) (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℂ),
      globalDepolPReplace t x (M₁ + M₂) =
        globalDepolPReplace t x M₁ + globalDepolPReplace t x M₂ := by
    intro t M₁ M₂; ext p q
    simp only [globalDepolPReplace, kronOp, Matrix.of_apply, Matrix.add_apply]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₁ + M₂ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₁ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₂ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    have h1 : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        (∏ y ∈ Finset.univ.erase x, (if y = x then M else depolP (t y)) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, depolP (t y) (p y) (q y) := fun M ↦
      Finset.prod_congr rfl fun y hy ↦ by simp [(Finset.mem_erase.mp hy).1]
    rw [h1, h1, h1]
    simp only [↓reduceIte, Matrix.add_apply]; ring
  have hrep_smul : ∀ (t : Fin N → Fin 6) (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      globalDepolPReplace t x (c • M) = c • globalDepolPReplace t x M := by
    intro t c M; ext p q
    simp only [globalDepolPReplace, kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then c • M else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    have h1 : ∀ K : Matrix (Fin 2) (Fin 2) ℂ,
        (∏ y ∈ Finset.univ.erase x, (if y = x then K else depolP (t y)) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, depolP (t y) (p y) (q y) := fun K ↦
      Finset.prod_congr rfl fun y hy ↦ by simp [(Finset.mem_erase.mp hy).1]
    rw [h1, h1]
    simp only [↓reduceIte, Matrix.smul_apply, smul_eq_mul]; ring
  have hrep_sq : ∀ (t : Fin N → Fin 6) (M : Matrix (Fin 2) (Fin 2) ℂ) (hMh : Mᴴ = M),
      globalDepolPReplace t x (M * M) =
        (kronOp (fun y ↦ if y = x then M else depolPHalf (t y)))ᴴ *
        kronOp (fun y ↦ if y = x then M else depolPHalf (t y)) := by
    intro t M hMh
    rw [kronOp_conjTranspose, kronOp_mul]
    unfold globalDepolPReplace
    congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp [hMh]
    · simp [hy, depolPHalf_herm, depolPHalf_sq]
  have hrep_self : ∀ (t : Fin N → Fin 6), globalDepolPReplace t x (depolP (t x)) = globalDepolP N t := by
    intro t; unfold globalDepolPReplace globalDepolP; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  have hrep_one : ∀ (t : Fin N → Fin 6),
      globalDepolPReplace t x 1 =
        (kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (t y)))ᴴ *
        kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (t y)) := by
    intro t
    have := hrep_sq t 1 Matrix.conjTranspose_one
    simpa [Matrix.mul_one] using this
  have hrep_depol : ∀ (t : Fin N → Fin 6),
      globalDepolP N t = (globalDepolPHalf N t)ᴴ * globalDepolPHalf N t := by
    intro t; rw [globalDepolPHalf_herm, globalDepolPHalf_sq]
  have hstep_low_L : ∀ (R : QubitOp N),
      (1 / 4 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * (Rᴴ * R) * Y)).re ≤
      (Matrix.trace (globalDepolP N s * Yᴴ * (Rᴴ * R) * Y)).re := by
    intro R
    rw [← hrep_self s, depolP_sub_quarter (s x), hrep_add, hrep_smul, hrep_smul]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    have hterm1 : (Matrix.trace (((1 / 4 : ℂ) • globalDepolPReplace s x 1) * Yᴴ * (Rᴴ * R) * Y)).re =
        (1 / 4 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * (Rᴴ * R) * Y)).re := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    have hterm2 : 0 ≤ (Matrix.trace (((1 / 8 : ℂ) •
        globalDepolPReplace s x ((1 + signedPauli (s x)) * (1 + signedPauli (s x)))) *
        Yᴴ * (Rᴴ * R) * Y)).re := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      have hMh : (1 + signedPauli (s x))ᴴ = 1 + signedPauli (s x) := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, signedPauli_herm]
      rw [hrep_sq s (1 + signedPauli (s x)) hMh]
      exact trace_quad_nonneg _ R Y
    linarith
  have hstep_low_R : ∀ (L : QubitOp N),
      (1 / 4 : ℝ) * (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolPReplace s' x 1 * Y)).re ≤
      (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolP N s' * Y)).re := by
    intro L
    rw [← hrep_self s', depolP_sub_quarter (s' x), hrep_add, hrep_smul, hrep_smul]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    have hterm1 : (Matrix.trace ((Lᴴ * L) * Yᴴ * ((1 / 4 : ℂ) • globalDepolPReplace s' x 1) * Y)).re =
        (1 / 4 : ℝ) * (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolPReplace s' x 1 * Y)).re := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    have hterm2 : 0 ≤ (Matrix.trace ((Lᴴ * L) * Yᴴ * ((1 / 8 : ℂ) •
        globalDepolPReplace s' x ((1 + signedPauli (s' x)) * (1 + signedPauli (s' x)))) * Y)).re := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      have hMh : (1 + signedPauli (s' x))ᴴ = 1 + signedPauli (s' x) := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, signedPauli_herm]
      rw [hrep_sq s' (1 + signedPauli (s' x)) hMh]
      exact trace_quad_nonneg L _ Y
    linarith
  have hstep_up_L : ∀ (R : QubitOp N),
      (Matrix.trace (globalDepolP N s * Yᴴ * (Rᴴ * R) * Y)).re ≤
      (3 / 4 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * (Rᴴ * R) * Y)).re := by
    intro R
    have h34 : (3 / 4 : ℝ) * (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * (Rᴴ * R) * Y)).re =
        (Matrix.trace (globalDepolPReplace s x ((3 / 4 : ℂ) • 1) * Yᴴ * (Rᴴ * R) * Y)).re := by
      rw [hrep_smul]; simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [h34, three_quarter_sub_depolP (s x), hrep_add, hrep_self, hrep_smul]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    have hterm2 : 0 ≤ (Matrix.trace (((1 / 8 : ℂ) •
        globalDepolPReplace s x ((1 - signedPauli (s x)) * (1 - signedPauli (s x)))) *
        Yᴴ * (Rᴴ * R) * Y)).re := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      have hMh : (1 - signedPauli (s x))ᴴ = 1 - signedPauli (s x) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, signedPauli_herm]
      rw [hrep_sq s (1 - signedPauli (s x)) hMh]
      exact trace_quad_nonneg _ R Y
    linarith
  have hstep_up_R : ∀ (L : QubitOp N),
      (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolP N s' * Y)).re ≤
      (3 / 4 : ℝ) * (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolPReplace s' x 1 * Y)).re := by
    intro L
    have h34 : (3 / 4 : ℝ) * (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolPReplace s' x 1 * Y)).re =
        (Matrix.trace ((Lᴴ * L) * Yᴴ * globalDepolPReplace s' x ((3 / 4 : ℂ) • 1) * Y)).re := by
      rw [hrep_smul]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [h34, three_quarter_sub_depolP (s' x), hrep_add, hrep_self, hrep_smul]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    have hterm2 : 0 ≤ (Matrix.trace ((Lᴴ * L) * Yᴴ * ((1 / 8 : ℂ) •
        globalDepolPReplace s' x ((1 - signedPauli (s' x)) * (1 - signedPauli (s' x)))) * Y)).re := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      have hMh : (1 - signedPauli (s' x))ᴴ = 1 - signedPauli (s' x) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, signedPauli_herm]
      rw [hrep_sq s' (1 - signedPauli (s' x)) hMh]
      exact trace_quad_nonneg L _ Y
    linarith
  constructor
  · unfold prodDepolNormSq prodDepolInner
    have h1 := hstep_low_L (globalDepolPHalf N s')
    rw [← hrep_depol s'] at h1
    have h2 := hstep_low_R (kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s y)))
    rw [← hrep_one s] at h2
    linarith
  · unfold prodDepolNormSq prodDepolInner
    have h1 := hstep_up_L (globalDepolPHalf N s')
    rw [← hrep_depol s'] at h1
    have h2 := hstep_up_R (kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s y)))
    rw [← hrep_one s] at h2
    linarith

private lemma siteSizeOp_comm_LR {N : ℕ} (x : Fin N) (L R Y : QubitOp N)
    (hcommR : ∀ c : Fin 4, pauliSite x c * R = R * pauliSite x c)
    (hcommL : ∀ c : Fin 4, pauliSite x c * L = L * pauliSite x c) :
    R * siteSizeOp x Y * L = siteSizeOp x (R * Y * L) := by
  unfold siteSizeOp partialTraceSite
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1; congr 1
  apply Finset.sum_congr rfl; intro c _
  calc R * (pauliSite x c * Y * pauliSite x c) * L
      = (R * pauliSite x c) * Y * (pauliSite x c * L) := by simp only [Matrix.mul_assoc]
    _ = (pauliSite x c * R) * Y * (L * pauliSite x c) := by rw [← hcommR c, hcommL c]
    _ = pauliSite x c * (R * Y * L) * pauliSite x c := by simp only [Matrix.mul_assoc]

private lemma hsNormSq_siteSizeOp_le {N : ℕ} (x : Fin N) (M : QubitOp N) :
    hsNormSq (siteSizeOp x M) ≤ hsNormSq M := by
  have hdiff_nn : 0 ≤ hsNormSq (M - siteSizeOp x M) := hsNormSq_nonneg _
  have hidem := siteSizeOp_idem x M
  have hsa1 := siteSizeOp_self_adj x (siteSizeOp x M) M
  have hsa2 := siteSizeOp_self_adj x M (siteSizeOp x M)
  have heq : hsNormSq (M - siteSizeOp x M) = hsNormSq M - hsNormSq (siteSizeOp x M) := by
    unfold hsNormSq hsInner at hsa1 hsa2 ⊢
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      Complex.sub_re, Complex.sub_re, Complex.sub_re]
    rw [hsa1, hsa2, hidem]
    ring
  linarith

private lemma globalDepolPReplace_siteSizeOp_le {N : ℕ} (s s' : Fin N → Fin 6) (x : Fin N)
    (Y : QubitOp N) :
    (Matrix.trace (globalDepolPReplace s x 1 * (siteSizeOp x Y)ᴴ *
      globalDepolPReplace s' x 1 * siteSizeOp x Y)).re ≤
    (Matrix.trace (globalDepolPReplace s x 1 * Yᴴ * globalDepolPReplace s' x 1 * Y)).re := by
  have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
  set L := kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s y))
  set R := kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s' y))
  have hL_herm : Lᴴ = L := by
    rw [kronOp_conjTranspose]; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, depolPHalf_herm]
  have hR_herm : Rᴴ = R := by
    rw [kronOp_conjTranspose]; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, depolPHalf_herm]
  have hL_sq : L * L = globalDepolPReplace s x 1 := by
    rw [kronOp_mul]; unfold globalDepolPReplace; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, depolPHalf_sq]
  have hR_sq : R * R = globalDepolPReplace s' x 1 := by
    rw [kronOp_mul]; unfold globalDepolPReplace; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, depolPHalf_sq]
  have hcomm_pauli : ∀ (c : Fin 4) (t : Fin N → Fin 6),
      pauliSite x c * kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (t y)) =
      kronOp (fun y ↦ if y = x then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (t y)) * pauliSite x c := by
    intro c t
    unfold pauliSite pauliString
    rw [kronOp_mul, kronOp_mul]; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, hp0]
  have hcomm_site : R * siteSizeOp x Y * L = siteSizeOp x (R * Y * L) :=
    siteSizeOp_comm_LR x L R Y (fun c ↦ hcomm_pauli c s') (fun c ↦ hcomm_pauli c s)
  have htr_hs : ∀ Z : QubitOp N,
      (Matrix.trace (globalDepolPReplace s x 1 * Zᴴ * globalDepolPReplace s' x 1 * Z)).re =
      hsNormSq (R * Z * L) := by
    intro Z
    unfold hsNormSq hsInner
    congr 1
    calc Matrix.trace (globalDepolPReplace s x 1 * Zᴴ * globalDepolPReplace s' x 1 * Z)
        = Matrix.trace ((L * L) * Zᴴ * (R * R) * Z) := by rw [← hL_sq, ← hR_sq]
      _ = Matrix.trace (L * (L * Zᴴ * (R * R) * Z)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((L * Zᴴ * (R * R) * Z) * L) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((R * Z * L)ᴴ * (R * Z * L)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hL_herm, hR_herm]
          simp only [Matrix.mul_assoc]
  rw [htr_hs (siteSizeOp x Y), htr_hs Y, hcomm_site]
  exact hsNormSq_siteSizeOp_le x (R * Y * L)

private lemma siteSizeOp_eq_zero_of_mem_trivial {N : ℕ} (x : Fin N)
    {B : QubitOp N} (hB : B ∈ singleSiteTrivialSubmodule N x) :
    siteSizeOp x B = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
  · rintro _ ⟨a, hax, rfl⟩
    unfold siteSizeOp
    have hpt : partialTraceSite x (pauliString a) = pauliString a := by
      unfold partialTraceSite pauliString
      have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
      have hconj : ∀ c : Fin 4,
          pauliSite x c * kronOp (fun y ↦ pauliMat (a y)) * pauliSite x c =
          kronOp (fun y ↦ pauliMat (a y)) := by
        intro c; unfold pauliSite pauliString
        rw [kronOp_mul, kronOp_mul]; congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp [hax, hp0, pauliMat_sq]
        · simp [hy, hp0]
      simp_rw [hconj, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ext p q
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [hpt, sub_self]
  · unfold siteSizeOp partialTraceSite; simp
  · intro X Y _ _ hX hY
    have hlin : siteSizeOp x (X + Y) = siteSizeOp x X + siteSizeOp x Y := by
      unfold siteSizeOp partialTraceSite
      simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add]
      abel
    rw [hlin, hX, hY, add_zero]
  · intro c X _ hX
    have hlin : siteSizeOp x (c • X) = c • siteSizeOp x X := by
      unfold siteSizeOp partialTraceSite
      simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, smul_sub]
      congr 1; rw [smul_comm]
    rw [hlin, hX, smul_zero]

/-- **Lemma 7.3(2) (Concrete Operator-Level Best-Approximation Bound on `QubitOp N`)**:
For EVERY `s, s' : Fin N → Fin 6`, EVERY site `x : Fin N`, and EVERY `A : QubitOp N`:
`prodDepolNormSq s s' (siteSizeOp x A) ≤ 9 * prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A`. -/
theorem lemma_7_3_operator_best_approx {N : ℕ} (s s' : Fin N → Fin 6) (x : Fin N)
    (A : QubitOp N) :
    prodDepolNormSq s s' (siteSizeOp x A) ≤
      9 * prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A := by
  have hbound_B : ∀ B ∈ singleSiteTrivialSubmodule N x,
      prodDepolNormSq s s' (siteSizeOp x A) ≤ 9 * prodDepolNormSq s s' (A - B) := by
    intro B hB
    have hsame : siteSizeOp x (A - B) = siteSizeOp x A := by
      have hlin : siteSizeOp x (A - B) = siteSizeOp x A - siteSizeOp x B := by
        unfold siteSizeOp partialTraceSite
        simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, smul_sub]
        abel
      rw [hlin, siteSizeOp_eq_zero_of_mem_trivial x hB, sub_zero]
    rw [← hsame]
    have h1 := (lemma_7_3_operator_conditioning s s' x (siteSizeOp x (A - B))).2
    have h2 := globalDepolPReplace_siteSizeOp_le s s' x (A - B)
    have h3 := (lemma_7_3_operator_conditioning s s' x (A - B)).1
    linarith
  have hdiv : (1 / 9 : ℝ) * prodDepolNormSq s s' (siteSizeOp x A) ≤
      prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A := by
    unfold prodDepolDistSq
    apply le_csInf
    · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
    · rintro r ⟨B, hB, rfl⟩
      linarith [hbound_B B hB]
  linarith

end OperatorConditioningAndTheorem13

end KrylovChaos
