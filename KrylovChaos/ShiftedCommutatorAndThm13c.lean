/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.CausalExpansion

/-!
# Unconditional Theorem 1.3(b) (`I(A) ≤ 216 Q(A)`) & End-to-End Theorem 1.3(c)

Combines `lemma_7_2_concrete_positive_frame`, `prodDepolNormSq_matComm_supportedOn_le`,
`hasSum_heisenbergEvol_adPow`, `revCausalSum_le`, and `theorem_1_1b_concrete_operator`
to prove `theorem_1_3b_otocI_unconditional` and `theorem_1_3c_concrete_end_to_end`
strictly on top of Mathlib `v4.35.0` with zero custom axioms and zero `sorry`s.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section CausalExpansionAndThm13bOtocI

/-- **Unconditional Theorem 1.3(b) Part 2 — Imaginary-Time Shifted Commutator Bound (Open Sub-Gap 2)**:
Directly from ANY `r`-local Hamiltonian `H = ∑ X ∈ E, h X` (`1 ≤ r`, `∀ X ∈ E, X.Nonempty ∧ X.card ≤ r`,
`∀ X, h X ∈ supportedOn X`) in the high-temperature regime:
- Kotecký–Preiss condition (`hsite_kp`, `hkp_param`) for `lemma_7_2_concrete_positive_frame`
- Causal-sum condition `∀ x, ∑_{X ∈ E, x ∈ X} opNorm (h X) ≤ J` with
  `q := (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * J ≤ 1 / 2`

for EVERY operator `A : QubitOp N`:
`otocI hH β A ≤ 216 * Re (A | 𝒬^{(β)} A)_β^W`.
**Zero `hρHalf` hypothesis and zero scalar-wrapper hypotheses!** -/
theorem theorem_1_3b_otocI_unconditional {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c J : ℝ} (hβ : 0 ≤ β) (hc : 0 < c) (hJ : 0 ≤ J)
    (hsite_kp : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c)
    (hsite_J : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    (hq : (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * J ≤ 1 / 2)
    (A : QubitOp N) :
    otocI hH β A ≤
      216 * (gibbsWightmanInner (concreteGibbsData hH β) A
        (wightmanQ (concreteGibbsData hH β) A)).re := by
  rcases lemma_7_2_concrete_positive_frame E hne hcard h hsupp hH hβ hc hsite_kp hkp_param with
    ⟨π, hπ_pos, hρHalf⟩
  let G := concreteGibbsData hH β
  let q : ℝ := (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * J
  have hq_nn : 0 ≤ q := by positivity
  have hq_lt1 : q < 1 := by dsimp only [q]; linarith
  -- Expand `gibbsWightmanNormSq G X` into `∑ s, ∑ s', π s * π s' * prodDepolNormSq s s' X`
  have hnorm_expand : ∀ X : QubitOp N,
      gibbsWightmanNormSq G X =
        ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6, π s * π s' * prodDepolNormSq s s' X := by
    intro X
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner prodDepolNormSq prodDepolInner
    change (gibbsRhoHalf hH β * Xᴴ * gibbsRhoHalf hH β * X).trace.re = _
    rw [hρHalf]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro s' _
    rw [← mul_assoc, mul_comm (π s' : ℂ) (π s : ℂ), ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  -- Core per-`(s, s')` bound:
  -- `(1/8) * ∑ x, ∑ α, prodDepolNormSq s s' (matComm A (σ_x^α(-iβ/4))) ≤ 216 * ∑ y, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A`
  have hper_ss : ∀ s s' : Fin N → Fin 6,
      (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
          prodDepolNormSq s s' (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
            (pauliSite x α.succ))) ≤
        216 * ∑ y : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
    intro s s'
    let D : Fin N → ℝ := fun y ↦ prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A
    have hD_nn : ∀ y : Fin N, 0 ≤ D y := fun y ↦ by
      dsimp only [D]; rw [prodDepolDistSq_singleSite_eq]
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    let W : ∀ (k : ℕ), (Fin k → Finset (Fin N)) → ℝ := fun k f ↦
      ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
        ∏ j : Fin k, opNorm (h (f j))
    have hW_nn : ∀ (k : ℕ) (f : Fin k → Finset (Fin N)), 0 ≤ W k f := fun k f ↦
      mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
        (pow_nonneg (Real.sqrt_nonneg _) _))
        (Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _)
    -- Bound for fixed `(x, α)`:
    have hxa : ∀ (x : Fin N) (α : Fin 3),
        prodDepolNormSq s s' (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
          (pauliSite x α.succ))) ≤
        24 * ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
          W k f * ∑ y ∈ causalUnionOp {x} f, D y := by
      intro x α
      let H := ∑ X ∈ E, h X
      let z : ℂ := -Complex.I * ((β / 4 : ℝ) : ℂ)
      have hiz : Complex.I * z = ((β / 4 : ℝ) : ℂ) := by
        dsimp only [z]; rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
      have hhas := hasSum_heisenbergEvol_adPow hH z (pauliSite x α.succ)
      -- Continuous linear map `X ↦ matComm A X`
      let commCLM : QubitOp N →L[ℂ] QubitOp N :=
        LinearMap.toContinuousLinearMap
          { toFun := fun X ↦ matComm A X
            map_add' := fun X Y ↦ by unfold matComm; simp [Matrix.mul_add, Matrix.add_mul]; abel
            map_smul' := fun c X ↦ by unfold matComm; simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub] }
      have hhas_comm : HasSum (fun k : ℕ ↦
          ((Complex.I * z) ^ k / (k.factorial : ℂ)) • matComm A (adPowMat H k (pauliSite x α.succ)))
          (matComm A (heisenbergEvol hH z (pauliSite x α.succ))) := by
        have h1 := hhas.map commCLM commCLM.continuous
        refine h1.congr_fun fun k ↦ ?_
        exact (commCLM.map_smul _ _).symm
      -- Continuity of `X ↦ Real.sqrt (prodDepolNormSq s s' X)`
      have hcont_norm : Continuous (fun X : QubitOp N ↦ Real.sqrt (prodDepolNormSq s s' X)) := by
        have htr : Continuous (Matrix.trace : QubitOp N → ℂ) := by
          change Continuous (fun M : QubitOp N ↦ ∑ i : QubitIdx N, M i i)
          exact continuous_finset_sum _ fun i _ ↦ (continuous_apply i).comp (continuous_apply i)
        have hct : Continuous (Matrix.conjTranspose : QubitOp N → QubitOp N) :=
          continuous_pi fun i ↦ continuous_pi fun j ↦
            Complex.continuous_conj.comp ((continuous_apply i).comp (continuous_apply j))
        have hsq_cont : Continuous (fun X : QubitOp N ↦ prodDepolNormSq s s' X) := by
          unfold prodDepolNormSq prodDepolInner
          exact Complex.continuous_re.comp (htr.comp (((continuous_const.mul hct).mul continuous_const).mul continuous_id))
        exact Real.continuous_sqrt.comp hsq_cont
      -- Termwise bound on `√(prodDepolNormSq s s' (term k))`
      have hterm_le : ∀ k : ℕ,
          Real.sqrt (prodDepolNormSq s s'
            (((Complex.I * z) ^ k / (k.factorial : ℂ)) • matComm A (adPowMat H k (pauliSite x α.succ)))) ≤
          2 * Real.sqrt 3 * ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) := by
        intro k
        rw [sqrt_prodDepolNormSq_smul, hiz, norm_div, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg (by linarith), Complex.norm_natCast]
        have hcomm_sum : matComm A (adPowMat H k (pauliSite x α.succ)) =
            ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              matComm A (iterComm h f (pauliSite x α.succ)) := by
          rw [adPowMat_eq_sum_causal E h hsupp (pauliSite_mem_supportedOn x α) k]
          unfold matComm; simp [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_sub_distrib]
        rw [hcomm_sum]
        have htri := sqrt_prodDepolNormSq_sum_le s s'
          ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}))
          (fun f ↦ matComm A (iterComm h f (pauliSite x α.succ)))
        calc (β / 4) ^ k / (k.factorial : ℝ) *
              Real.sqrt (prodDepolNormSq s s'
                (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                  matComm A (iterComm h f (pauliSite x α.succ))))
            ≤ (β / 4) ^ k / (k.factorial : ℝ) *
              ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                Real.sqrt (prodDepolNormSq s s' (matComm A (iterComm h f (pauliSite x α.succ)))) :=
              mul_le_mul_of_nonneg_left htri (div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
          _ = ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                ((β / 4) ^ k / (k.factorial : ℝ)) *
                  Real.sqrt (prodDepolNormSq s s' (matComm A (iterComm h f (pauliSite x α.succ)))) := by
              rw [Finset.mul_sum]
          _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                2 * Real.sqrt 3 * (W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) := by
              apply Finset.sum_le_sum; intro f hf
              rcases Finset.mem_filter.mp hf with ⟨hfpi, hfcs⟩
              have hmem := iterComm_mem_supportedOn h hsupp (pauliSite_mem_supportedOn x α) f
              have hcond := prodDepolNormSq_matComm_supportedOn_le s s' hmem A
              have hop := opNorm_iterComm_le h (pauliSite x α.succ) f
              have hop1 : opNorm (iterComm h f (pauliSite x α.succ)) ≤
                  (2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j)) := by
                have hprod_nn : (0 : ℝ) ≤ ∏ j : Fin k, opNorm (h (f j)) :=
                  Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _
                have := mul_le_mul_of_nonneg_left (opNorm_pauliSite_le x α)
                  (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k) hprod_nn)
                linarith
              have hcard_u := card_causalUnion_le hr E hcard {x} f (Fintype.mem_piFinset.mp hfpi) hfcs
              simp only [Finset.card_singleton] at hcard_u
              have h3pow : (3 : ℝ) ^ (causalUnionOp {x} f).card ≤ (3 : ℝ) ^ (1 + k * (r - 1)) :=
                pow_le_pow_right₀ (by norm_num) hcard_u
              have hsqrt_le : Real.sqrt (prodDepolNormSq s s' (matComm A (iterComm h f (pauliSite x α.succ)))) ≤
                  2 * Real.sqrt 3 * (Real.sqrt 3) ^ (k * (r - 1)) *
                    ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) *
                    Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) := by
                have hRHS_nn : 0 ≤ 2 * Real.sqrt 3 * (Real.sqrt 3) ^ (k * (r - 1)) *
                    ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) *
                    Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) := by
                  have hprod_nn : 0 ≤ ∏ j : Fin k, opNorm (h (f j)) :=
                    Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _
                  positivity
                rw [Real.sqrt_le_iff]
                refine ⟨hRHS_nn, ?_⟩
                have hsq3 : (Real.sqrt 3 ^ (k * (r - 1))) ^ 2 = (3 : ℝ) ^ (k * (r - 1)) := by
                  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
                have hsqD : (Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) ^ 2 = ∑ y ∈ causalUnionOp {x} f, D y :=
                  Real.sq_sqrt (Finset.sum_nonneg fun y _ ↦ hD_nn y)
                have hsqRHS : (2 * Real.sqrt 3 * (Real.sqrt 3) ^ (k * (r - 1)) *
                    ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) *
                    Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) ^ 2 =
                    4 * (3 : ℝ) ^ (1 + k * (r - 1)) *
                      ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) ^ 2 *
                      ∑ y ∈ causalUnionOp {x} f, D y := by
                  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hsq3, hsqD,
                    Real.sq_sqrt (by norm_num), pow_add, pow_one]
                  ring
                rw [hsqRHS]
                have hop_sq : (opNorm (iterComm h f (pauliSite x α.succ))) ^ 2 ≤
                    ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) ^ 2 := by
                  nlinarith [hop1, opNorm_nonneg (iterComm h f (pauliSite x α.succ))]
                have hsumD_nn : 0 ≤ ∑ y ∈ causalUnionOp {x} f, D y :=
                  Finset.sum_nonneg fun y _ ↦ hD_nn y
                calc prodDepolNormSq s s' (matComm A (iterComm h f (pauliSite x α.succ)))
                    ≤ 4 * (3 : ℝ) ^ (causalUnionOp {x} f).card *
                        (opNorm (iterComm h f (pauliSite x α.succ))) ^ 2 *
                        ∑ y ∈ causalUnionOp {x} f, D y := hcond
                  _ ≤ 4 * (3 : ℝ) ^ (1 + k * (r - 1)) *
                        ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) ^ 2 *
                        ∑ y ∈ causalUnionOp {x} f, D y := by
                      apply mul_le_mul_of_nonneg_right _ hsumD_nn
                      apply mul_le_mul
                        (mul_le_mul_of_nonneg_left h3pow (by norm_num))
                        hop_sq (sq_nonneg _) (by positivity)
              have hfac : ((β / 4) ^ k / (k.factorial : ℝ)) *
                  (2 * Real.sqrt 3 * (Real.sqrt 3) ^ (k * (r - 1)) *
                    ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) *
                    Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) =
                  2 * Real.sqrt 3 * (W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) := by
                dsimp only [W]
                have h2b : (β / 4) ^ k * (2 : ℝ) ^ k = (β / 2) ^ k := by
                  rw [← mul_pow]; congr 1; ring
                calc ((β / 4) ^ k / (k.factorial : ℝ)) *
                      (2 * Real.sqrt 3 * (Real.sqrt 3) ^ (k * (r - 1)) *
                        ((2 : ℝ) ^ k * ∏ j : Fin k, opNorm (h (f j))) *
                        Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y))
                    = 2 * Real.sqrt 3 * ((((β / 4) ^ k * (2 : ℝ) ^ k) / (k.factorial : ℝ)) *
                        (Real.sqrt 3) ^ (k * (r - 1)) * (∏ j : Fin k, opNorm (h (f j))) *
                        Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) := by ring
                  _ = _ := by rw [h2b]
              rw [← hfac]
              exact mul_le_mul_of_nonneg_left hsqrt_le
                (div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
          _ = 2 * Real.sqrt 3 * ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) := by rw [← Finset.mul_sum]
      -- Summability of the geometric majorants `q ^ k`
      have hW_sum_le : ∀ k : ℕ,
          ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f ≤ q ^ k := by
        intro k
        have h1 : ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f =
            ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
              fwdCausalSum E (fun X ↦ opNorm (h X)) k {x} := by
          dsimp only [W, fwdCausalSum]; rw [Finset.mul_sum]
        rw [h1]
        have hfwd := fwdCausalSum_le hr E hcard (fun X ↦ opNorm (h X)) (fun _ _ ↦ opNorm_nonneg _)
          hJ hsite_J x k
        have hfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
        calc ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
              fwdCausalSum E (fun X ↦ opNorm (h X)) k {x}
            ≤ ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
              ((k.factorial : ℝ) * ((r : ℝ) * J) ^ k) :=
              mul_le_mul_of_nonneg_left hfwd (by positivity)
          _ = ((β / 2) * (Real.sqrt 3) ^ (r - 1) * ((r : ℝ) * J)) ^ k := by
              simp only [mul_pow, ← pow_mul, mul_comm (r - 1) k]
              field_simp [hfac_ne]
          _ = q ^ k := by dsimp only [q]; congr 1; ring
      let Dtot : ℝ := ∑ y : Fin N, D y
      have hDtot_nn : 0 ≤ Dtot := Finset.sum_nonneg fun y _ ↦ hD_nn y
      have hsumm_W : Summable (fun k : ℕ ↦
          ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f) :=
        Summable.of_nonneg_of_le
          (fun k ↦ Finset.sum_nonneg fun f _ ↦ hW_nn k f) hW_sum_le
          (summable_geometric_of_lt_one hq_nn hq_lt1)
      have hsumm_WD : Summable (fun k : ℕ ↦
          ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y) := by
        refine Summable.of_nonneg_of_le
          (fun k ↦ Finset.sum_nonneg fun f _ ↦ mul_nonneg (hW_nn k f) (Finset.sum_nonneg fun y _ ↦ hD_nn y))
          (fun k ↦ ?_) ((summable_geometric_of_lt_one hq_nn hq_lt1).mul_right Dtot)
        calc ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * ∑ y ∈ causalUnionOp {x} f, D y
            ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f * Dtot := by
              apply Finset.sum_le_sum; intro f _
              exact mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ ↦ hD_nn y)
                (hW_nn k f)
          _ = (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f) * Dtot := by
              rw [← Finset.sum_mul]
          _ ≤ q ^ k * Dtot := mul_le_mul_of_nonneg_right (hW_sum_le k) hDtot_nn
      -- Cauchy–Schwarz on finite partial sums `F : Finset ℕ`
      let S_W : ℝ := ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f
      let S_WD : ℝ := ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
        W k f * ∑ y ∈ causalUnionOp {x} f, D y
      have hS_W_le : S_W ≤ 2 := by
        calc S_W ≤ ∑' k : ℕ, q ^ k :=
              hsumm_W.tsum_le_tsum hW_sum_le (summable_geometric_of_lt_one hq_nn hq_lt1)
          _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq_nn hq_lt1
          _ ≤ 2 := by
              rw [inv_le_iff_one_le_mul₀ (by linarith)]
              dsimp only [q]; linarith
      have hS_W_nn : 0 ≤ S_W := tsum_nonneg fun k ↦ Finset.sum_nonneg fun f _ ↦ hW_nn k f
      have hS_WD_nn : 0 ≤ S_WD := tsum_nonneg fun k ↦
        Finset.sum_nonneg fun f _ ↦ mul_nonneg (hW_nn k f) (Finset.sum_nonneg fun y _ ↦ hD_nn y)
      have hpartial_le : ∀ F : Finset ℕ,
          Real.sqrt (prodDepolNormSq s s'
            (∑ k ∈ F, ((Complex.I * z) ^ k / (k.factorial : ℂ)) • matComm A (adPowMat H k (pauliSite x α.succ)))) ≤
          2 * Real.sqrt 3 * Real.sqrt (S_W * S_WD) := by
        intro F
        have htri := sqrt_prodDepolNormSq_sum_le s s' F
          (fun k ↦ ((Complex.I * z) ^ k / (k.factorial : ℂ)) • matComm A (adPowMat H k (pauliSite x α.succ)))
        have hstep1 : ∑ k ∈ F, Real.sqrt (prodDepolNormSq s s'
            (((Complex.I * z) ^ k / (k.factorial : ℂ)) • matComm A (adPowMat H k (pauliSite x α.succ)))) ≤
            2 * Real.sqrt 3 * ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun k _ ↦ hterm_le k
        -- Cauchy–Schwarz: `(∑_{k ∈ F, f} W k f * √(D_f)) ^ 2 ≤ (∑_{k ∈ F, f} W k f) * (∑_{k ∈ F, f} W k f * D_f)`
        have hcs : (∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) ^ 2 ≤
            (∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f) *
            (∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * ∑ y ∈ causalUnionOp {x} f, D y) := by
          let idx := F.sigma (fun k ↦ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}))
          have h1 : ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y) =
              ∑ p ∈ idx, Real.sqrt (W p.1 p.2) * (Real.sqrt (W p.1 p.2) * Real.sqrt (∑ y ∈ causalUnionOp {x} p.2, D y)) := by
            rw [Finset.sum_sigma]
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro f _
            rw [← mul_assoc, Real.mul_self_sqrt (hW_nn k f)]
          rw [h1]
          have h2 := Finset.sum_mul_sq_le_sq_mul_sq idx
            (fun p ↦ Real.sqrt (W p.1 p.2))
            (fun p ↦ Real.sqrt (W p.1 p.2) * Real.sqrt (∑ y ∈ causalUnionOp {x} p.2, D y))
          refine le_trans h2 ?_
          have hA : ∑ p ∈ idx, (Real.sqrt (W p.1 p.2)) ^ 2 =
              ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f := by
            rw [Finset.sum_sigma]; apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro f _; exact Real.sq_sqrt (hW_nn k f)
          have hB : ∑ p ∈ idx, (Real.sqrt (W p.1 p.2) * Real.sqrt (∑ y ∈ causalUnionOp {x} p.2, D y)) ^ 2 =
              ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                W k f * ∑ y ∈ causalUnionOp {x} f, D y := by
            rw [Finset.sum_sigma]; apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro f _
            rw [mul_pow, Real.sq_sqrt (hW_nn k f),
              Real.sq_sqrt (Finset.sum_nonneg fun y _ ↦ hD_nn y)]
          rw [hA, hB]
        have hF_W : ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f ≤ S_W :=
          hsumm_W.sum_le_tsum F fun k _ ↦ Finset.sum_nonneg fun f _ ↦ hW_nn k f
        have hF_WD : ∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y ≤ S_WD :=
          hsumm_WD.sum_le_tsum F fun k _ ↦
            Finset.sum_nonneg fun f _ ↦ mul_nonneg (hW_nn k f) (Finset.sum_nonneg fun y _ ↦ hD_nn y)
        have hprod_le : (∑ k ∈ F, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * Real.sqrt (∑ y ∈ causalUnionOp {x} f, D y)) ≤ Real.sqrt (S_W * S_WD) := by
          rw [Real.le_sqrt (Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun f _ ↦
            mul_nonneg (hW_nn k f) (Real.sqrt_nonneg _)) (mul_nonneg hS_W_nn hS_WD_nn)]
          exact le_trans hcs (mul_le_mul hF_W hF_WD
            (Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun f _ ↦
              mul_nonneg (hW_nn k f) (Finset.sum_nonneg fun y _ ↦ hD_nn y)) hS_W_nn)
        exact le_trans (le_trans htri hstep1) (mul_le_mul_of_nonneg_left hprod_le (by positivity))
      have hlim := le_of_tendsto (hcont_norm.continuousAt.tendsto.comp hhas_comm)
        (Filter.Eventually.of_forall hpartial_le)
      have hsq : prodDepolNormSq s s' (matComm A (heisenbergEvol hH z (pauliSite x α.succ))) ≤
          (2 * Real.sqrt 3 * Real.sqrt (S_W * S_WD)) ^ 2 := by
        have h0 : (Real.sqrt (prodDepolNormSq s s' (matComm A (heisenbergEvol hH z (pauliSite x α.succ))))) ^ 2 ≤
            (2 * Real.sqrt 3 * Real.sqrt (S_W * S_WD)) ^ 2 := by
          nlinarith [hlim, Real.sqrt_nonneg (prodDepolNormSq s s' (matComm A (heisenbergEvol hH z (pauliSite x α.succ))))]
        rwa [Real.sq_sqrt (prodDepolNormSq_nonneg s s' _)] at h0
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (mul_nonneg hS_W_nn hS_WD_nn)] at hsq
      calc prodDepolNormSq s s' (matComm A (heisenbergEvol hH z (pauliSite x α.succ)))
          ≤ 2 ^ 2 * 3 * (S_W * S_WD) := hsq
        _ ≤ 2 ^ 2 * 3 * (2 * S_WD) := by
            apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS_W_le hS_WD_nn) (by norm_num)
        _ = 24 * S_WD := by ring
    -- Sum `hxa` over `x : Fin N` and `α : Fin 3`, then apply `revCausalSum_le`
    have hsumm_all : ∀ x : Fin N, Summable (fun k : ℕ ↦
        ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
          W k f * ∑ y ∈ causalUnionOp {x} f, D y) := by
      intro x
      let Dtot : ℝ := ∑ y : Fin N, D y
      have hDtot_nn : 0 ≤ Dtot := Finset.sum_nonneg fun y _ ↦ hD_nn y
      refine Summable.of_nonneg_of_le
        (fun k ↦ Finset.sum_nonneg fun f _ ↦ mul_nonneg (hW_nn k f) (Finset.sum_nonneg fun y _ ↦ hD_nn y))
        (fun k ↦ ?_) ((summable_geometric_of_lt_one hq_nn hq_lt1).mul_right Dtot)
      calc ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y
          ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f * Dtot := by
            apply Finset.sum_le_sum; intro f _
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ ↦ hD_nn y)
              (hW_nn k f)
        _ = (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f) * Dtot := by
            rw [← Finset.sum_mul]
        _ ≤ q ^ k * Dtot := by
            apply mul_le_mul_of_nonneg_right _ hDtot_nn
            have h1 : ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}), W k f =
                ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
                  fwdCausalSum E (fun X ↦ opNorm (h X)) k {x} := by
              dsimp only [W, fwdCausalSum]; rw [Finset.mul_sum]
            rw [h1]
            have hfwd := fwdCausalSum_le hr E hcard (fun X ↦ opNorm (h X)) (fun _ _ ↦ opNorm_nonneg _)
              hJ hsite_J x k
            have hfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
            calc ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
                  fwdCausalSum E (fun X ↦ opNorm (h X)) k {x}
                ≤ ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
                  ((k.factorial : ℝ) * ((r : ℝ) * J) ^ k) :=
                  mul_le_mul_of_nonneg_left hfwd (by positivity)
              _ = q ^ k := by
                  dsimp only [q]; simp only [mul_pow, ← pow_mul, mul_comm (r - 1) k]
                  field_simp [hfac_ne]
    have hsum_xa : (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
          prodDepolNormSq s s' (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
            (pauliSite x α.succ))) ≤
        9 * ∑' k : ℕ, ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
          W k f * ∑ y ∈ causalUnionOp {x} f, D y := by
      have h1 : ∑ x : Fin N, ∑ α : Fin 3,
            prodDepolNormSq s s' (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
              (pauliSite x α.succ))) ≤
          72 * ∑ x : Fin N, ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro x _
        calc ∑ α : Fin 3, prodDepolNormSq s s' (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
                (pauliSite x α.succ)))
            ≤ ∑ _α : Fin 3, (24 * ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                W k f * ∑ y ∈ causalUnionOp {x} f, D y) := Finset.sum_le_sum fun α _ ↦ hxa x α
          _ = 72 * ∑' k : ℕ, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
                W k f * ∑ y ∈ causalUnionOp {x} f, D y := by simp [Finset.sum_const]; ring
      rw [← Summable.tsum_finsetSum (fun x _ ↦ hsumm_all x)] at h1
      linarith
    -- Swap `∑ x, ∑ f` with `∑ y` at each `k` and apply `revCausalSum_le`
    have hk_bound : ∀ k : ℕ,
        ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
          W k f * ∑ y ∈ causalUnionOp {x} f, D y ≤
        (((k + 1 : ℕ) : ℝ) * q ^ k) * ∑ y : Fin N, D y := by
      intro k
      have hswap : ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y =
          ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
            ∑ y : Fin N, D y * revCausalSum E (fun X ↦ opNorm (h X)) k y := by
        have hstep1 : ∀ x : Fin N,
            ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * ∑ y ∈ causalUnionOp {x} f, D y =
            ∑ y : Fin N, D y * ∑ f ∈ ((Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x})).filter
              (fun f ↦ y ∈ causalUnionOp {x} f), W k f := by
          intro x
          have h1 : ∀ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * ∑ y ∈ causalUnionOp {x} f, D y =
              ∑ y : Fin N, if y ∈ causalUnionOp {x} f then D y * W k f else 0 := by
            intro f _
            rw [Finset.mul_sum, ← Finset.sum_filter]
            have hfeq : Finset.univ.filter (fun y ↦ y ∈ causalUnionOp {x} f) = causalUnionOp {x} f := by
              ext y; simp
            rw [hfeq]; apply Finset.sum_congr rfl; intro y _; ring
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.mul_sum, ← Finset.sum_filter]
        simp_rw [hstep1]
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        dsimp only [revCausalSum, W]
        simp_rw [← Finset.mul_sum]
        ring
      rw [hswap]
      have hrev_sum : ∑ y : Fin N, D y * revCausalSum E (fun X ↦ opNorm (h X)) k y ≤
          (((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) * ∑ y : Fin N, D y := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro y _
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (revCausalSum_le hr E hcard (fun X ↦ opNorm (h X)) (fun _ _ ↦ opNorm_nonneg _) hJ hsite_J k y)
          (hD_nn y)
      have hfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      calc ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
            ∑ y : Fin N, D y * revCausalSum E (fun X ↦ opNorm (h X)) k y
          ≤ ((β / 2) ^ k / (k.factorial : ℝ)) * (Real.sqrt 3) ^ (k * (r - 1)) *
            ((((k + 1).factorial : ℝ) * ((r : ℝ) * J) ^ k) * ∑ y : Fin N, D y) :=
            mul_le_mul_of_nonneg_left hrev_sum (by positivity)
        _ = (((k + 1 : ℕ) : ℝ) * q ^ k) * ∑ y : Fin N, D y := by
            dsimp only [q]
            rw [Nat.factorial_succ, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm (r - 1) k]
            push_cast; field_simp [hfac_ne]
    -- Bound `∑' k, (k + 1) * q^k ≤ 4` for `q ≤ 1/2` (since `(k + 1) * (1/2)^k ≤ 4` total sum = 4!)
    have hsum_k1_q : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * q ^ k) ∧
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * q ^ k ≤ 4 := by
      have hhalf_lt : (1 / 2 : ℝ) < 1 := by norm_num
      have hhalf_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
      have hgeom := summable_geometric_of_lt_one hhalf_nn hhalf_lt
      have hgeom_val : ∑' k : ℕ, (1 / 2 : ℝ) ^ k = 2 := by
        rw [tsum_geometric_of_lt_one hhalf_nn hhalf_lt]; norm_num
      -- `∑' k, (k + 1) * (1/2)^k = 4` by shifting: `S - (1/2) S = ∑' k, (1/2)^k = 2`
      have hsumm_half : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
        have h34 : Summable (fun k : ℕ ↦ (3 / 4 : ℝ) ^ k) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) (h34.mul_left 4)
        -- `(k + 1) * (1/2)^k ≤ 4 * (3/4)^k ↔ (k + 1) ≤ 4 * (3/2)^k`
        have hind : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ 4 * (3 / 2 : ℝ) ^ n := by
          intro n; induction n with
          | zero => norm_num
          | succ n ihn =>
            rw [pow_succ]; push_cast at ihn ⊢
            have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
            linarith
        have hpow : (3 / 4 : ℝ) ^ k = (3 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
          rw [← mul_pow]; congr 1; norm_num
        rw [hpow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hind k) (by positivity)
      have hval_half : ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k = 4 := by
        have hshift := hsumm_half.tsum_eq_zero_add
        have hdiff : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) -
            (1 / 2 : ℝ) * (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) =
            ∑' k : ℕ, (1 / 2 : ℝ) ^ k := by
          rw [← tsum_mul_left, hshift]
          have hsub := ((summable_nat_add_iff 1).mpr hsumm_half).tsum_sub
            (hsumm_half.mul_left (1 / 2 : ℝ))
          have hterm : ∀ k : ℕ,
              (((k + 1 + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (k + 1) -
                (1 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k)) = (1 / 2 : ℝ) ^ (k + 1) := by
            intro k; rw [pow_succ]; push_cast; ring
          have hshift_g := hgeom.tsum_eq_zero_add
          rw [hshift_g]
          have h0 : (((0 + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 0) = (1 / 2 : ℝ) ^ 0 := by norm_num
          linarith [hsub.symm.trans (tsum_congr hterm)]
        linarith [hgeom_val]
      have hq_le_half : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * q ^ k ≤ ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k :=
        fun k ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq_nn hq k) (Nat.cast_nonneg _)
      have hsumm_q : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * q ^ k) :=
        Summable.of_nonneg_of_le (fun _ ↦ by positivity) hq_le_half hsumm_half
      exact ⟨hsumm_q, le_trans (hsumm_q.tsum_le_tsum hq_le_half hsumm_half) hval_half.le⟩
    have htsum_le : ∑' k : ℕ, ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
          W k f * ∑ y ∈ causalUnionOp {x} f, D y ≤
        4 * ∑ y : Fin N, D y := by
      have hsumm_lhs : Summable (fun k : ℕ ↦
          ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
            W k f * ∑ y ∈ causalUnionOp {x} f, D y) :=
        summable_sum fun x _ ↦ hsumm_all x
      calc ∑' k : ℕ, ∑ x : Fin N, ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp {x}),
              W k f * ∑ y ∈ causalUnionOp {x} f, D y
          ≤ ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) * q ^ k) * ∑ y : Fin N, D y :=
            hsumm_lhs.tsum_le_tsum hk_bound (hsum_k1_q.1.mul_right _)
        _ = (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * q ^ k) * ∑ y : Fin N, D y := tsum_mul_right
        _ ≤ 4 * ∑ y : Fin N, D y :=
            mul_le_mul_of_nonneg_right hsum_k1_q.2 (Finset.sum_nonneg fun y _ ↦ hD_nn y)
    have hDsum_nn : 0 ≤ ∑ y : Fin N, D y := Finset.sum_nonneg fun y _ ↦ hD_nn y
    linarith
  -- Average `hper_ss` over `π s * π s'` and finish via `lemma_7_3_operator_filtration_identity` + `wightmanProj_convex_mixture_ge`
  have hQ_expand : ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
        π s * π s' * ∑ y : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A ≤
      (gibbsWightmanInner G A (wightmanQ G A)).re := by
    have hfilt_eq : ∀ s s' : Fin N → Fin 6,
        ∑ y : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A =
        ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A :=
      fun s s' ↦ lemma_7_3_operator_filtration_identity s s' A
    simp_rw [hfilt_eq]
    have hswap_k : ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A =
        ∑ k ∈ Finset.range N, ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * prodDepolDistSq s s' (filtrationSubmodule N k) A := by
      have h2 : ∀ s : Fin N → Fin 6,
          (∑ s' : Fin N → Fin 6, π s * π s' *
            ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A) =
          ∑ k ∈ Finset.range N, ∑ s' : Fin N → Fin 6,
            π s * π s' * prodDepolDistSq s s' (filtrationSubmodule N k) A := fun s ↦ by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      simp_rw [h2]; exact Finset.sum_comm
    rw [hswap_k, wightmanQ_eq_sum_distSq]
    apply Finset.sum_le_sum; intro k _
    have h1 := wightmanProj_convex_mixture_ge G π (fun s ↦ (hπ_pos s).le) hρHalf (filtrationSubmodule N k) A
    rw [wightmanSubspaceProj_eq_distSq] at h1
    exact h1
  unfold otocI
  dsimp only [G] at hnorm_expand
  simp_rw [hnorm_expand]
  have hswap_otoc : (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
        ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ))) =
      ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
        π s * π s' * ((1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
          prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)))) := by
    simp_rw [Finset.mul_sum]
    have h1 : ∀ x : Fin N,
        ∑ α : Fin 3, ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          (1 / 8 : ℝ) * (π s * π s' * prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)))) =
        ∑ s : Fin N → Fin 6, ∑ α : Fin 3, ∑ s' : Fin N → Fin 6,
          (1 / 8 : ℝ) * (π s * π s' * prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)))) :=
      fun _ ↦ Finset.sum_comm
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    have h2 : ∀ x : Fin N,
        ∑ α : Fin 3, ∑ s' : Fin N → Fin 6,
          (1 / 8 : ℝ) * (π s * π s' * prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)))) =
        ∑ s' : Fin N → Fin 6, ∑ α : Fin 3,
          (1 / 8 : ℝ) * (π s * π s' * prodDepolNormSq s s'
            (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)))) :=
      fun _ ↦ Finset.sum_comm
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s' _
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro α _; ring
  rw [hswap_otoc]
  calc ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * ((1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
            prodDepolNormSq s s'
              (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ))))
      ≤ ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * (216 * ∑ y : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A) := by
        apply Finset.sum_le_sum; intro s _
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hper_ss s s')
          (mul_nonneg (hπ_pos s).le (hπ_pos s').le)
    _ = 216 * ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
          π s * π s' * ∑ y : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s' _; ring
    _ ≤ 216 * (gibbsWightmanInner G A (wightmanQ G A)).re :=
        mul_le_mul_of_nonneg_left hQ_expand (by norm_num)

/-- **End-to-End Concrete Dynamical Bound (Theorem 1.3(c) Finite-Volume Core)**:
Combines unconditional `theorem_1_3b_otocI_unconditional` with concrete Lanczos truncation
`theorem_1_1b_concrete_operator` directly on `heisenbergEvol hH (t : ℂ) O`:
for any `r`-local Hamiltonian `H = ∑ X ∈ E, h X` in the high-temperature regime,
`otocI hH β (heisenbergEvol hH (t : ℂ) O)` is bounded directly by the static truncation
filtration size `s_M` and the concrete Lanczos remainder `R_M = O(t) - A_M(t)` with ZERO
scalar-wrapper hypotheses. -/
theorem theorem_1_3c_concrete_end_to_end {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c J : ℝ} (hβ : 0 ≤ β) (hc : 0 < c) (hJ : 0 ≤ J)
    (hsite_kp : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c)
    (hsite_J : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    (hq : (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * J ≤ 1 / 2)
    (O : QubitOp N) (s₀ M : ℕ) (hM : 1 ≤ M) (t : ℝ)
    (hO : O ∈ filtrationSubmodule N s₀)
    (hH_filt : (∑ X ∈ E, h X) ∈ filtrationSubmodule N r) :
    let G := concreteGibbsData hH β
    let A_M := lanczosTrunc hH β O M t
    let R_M := heisenbergEvol hH (t : ℂ) O - A_M
    let s_M : ℕ := s₀ + (M - 1) * (r - 1)
    otocI hH β (heisenbergEvol hH (t : ℂ) O) ≤
      216 * ((s_M : ℝ) * gibbsWightmanNormSq G A_M +
        2 * Real.sqrt ((s_M : ℝ) * gibbsWightmanNormSq G A_M) *
            Real.sqrt ((N : ℝ) * gibbsWightmanNormSq G R_M) +
        (N : ℝ) * gibbsWightmanNormSq G R_M) := by
  have h13b := theorem_1_3b_otocI_unconditional hr E hne hcard h hsupp hH hβ hc hJ
    hsite_kp hkp_param hsite_J hq (heisenbergEvol hH (t : ℂ) O)
  have h11b := lemma_4_2_concrete_operator hr hM hH β t hH_filt hO
  exact le_trans h13b (mul_le_mul_of_nonneg_left h11b (by norm_num))

end CausalExpansionAndThm13bOtocI

end KrylovChaos
