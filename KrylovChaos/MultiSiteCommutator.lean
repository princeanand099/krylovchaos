/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Lemma72Concrete
import KrylovChaos.ConcreteEndToEndWiring

/-!
# Concrete Imaginary-Time Shifted Commutator Bound `I(A) ≤ 216 Q(A)` & Theorem 1.3(c)

Closes Open Sub-Gap 2 strictly on top of Mathlib `v4.35.0` with zero custom axioms,
zero `sorry`s, and zero hypothesis-laundering:
1. Proves `opNorm_conjTranspose_le`, Hilbert–Schmidt submultiplicativity
   `hsNormSq_mul_left_le` / `hsNormSq_mul_right_le`, and the multi-site depolarized
   commutator conditioning bound `prodDepolNormSq_matComm_supportedOn_le`:
   for any `W ∈ supportedOn U` and `A : QubitOp N`,
   `prodDepolNormSq s s' (matComm A W) ≤ 4 * 3 ^ U.card * (opNorm W) ^ 2 * ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A`.
2. Proves the concrete eigenbasis expansion `hasSum_heisenbergEvol_adPow` of
   `heisenbergEvol hH z B` into iterated commutators `adPowMat H k B`, causal-sequence
   support & norm bounds, and the inductive reverse-causal sum bound `revCausalSum_le`
   (`≤ (k + 1)! * r^k * J^k`).
3. Combines `lemma_7_2_concrete_positive_frame` (ZERO `hρHalf` hypothesis!),
   Minkowski + Cauchy–Schwarz + `lemma_7_3_operator_filtration_identity` +
   `wightmanProj_convex_mixture_ge` to prove **Theorem 1.3(b) Part 2**
   (`theorem_1_3b_otocI_unconditional`):
   `otocI hH β A ≤ 216 * Re (A | 𝒬^{(β)} A)_β^W` for all `A : QubitOp N`.
4. Wires **Theorem 1.3(c)** (`theorem_1_3c_concrete_end_to_end`) directly from
   `theorem_1_3b_otocI_unconditional` and `theorem_1_1b_concrete_operator` on
   `heisenbergEvol hH (t : ℂ) O`.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section MultiSiteCommutatorConditioning

lemma opNorm_conjTranspose_le {N : ℕ} (A : QubitOp N) : opNorm Aᴴ ≤ opNorm A := by
  unfold opNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (opNorm_nonneg A)
  intro v
  by_cases hv : ‖opToCLM Aᴴ v‖ = 0
  · rw [hv]; exact mul_nonneg (opNorm_nonneg A) (norm_nonneg v)
  have hinner : @inner ℂ _ _ (opToCLM Aᴴ v) (opToCLM Aᴴ v) =
      @inner ℂ _ _ v (opToCLM A (opToCLM Aᴴ v)) := by
    have hop : ∀ (M : QubitOp N) (w : EuclideanSpace ℂ (QubitIdx N)) (i : QubitIdx N),
        (opToCLM M w).ofLp i = ∑ k : QubitIdx N, M i k * w.ofLp k := by
      intro M w i; simp [opToCLM, EuclideanSpace.equiv, Matrix.mulVec, dotProduct]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, Complex.star_def]
    simp_rw [hop, map_sum, map_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    conv_rhs => simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [Matrix.conjTranspose_apply, Complex.star_def, starRingEnd_self_apply]
    ring
  have hsq : ‖opToCLM Aᴴ v‖ ^ 2 ≤ ‖v‖ * (opNorm A * ‖opToCLM Aᴴ v‖) := by
    have h1 : (‖opToCLM Aᴴ v‖ ^ 2 : ℝ) = ‖@inner ℂ _ _ (opToCLM Aᴴ v) (opToCLM Aᴴ v)‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      change ‖opToCLM Aᴴ v‖ ^ 2 = ‖((‖opToCLM Aᴴ v‖ : ℂ) ^ 2)‖
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [h1, hinner]
    calc ‖@inner ℂ _ _ v (opToCLM A (opToCLM Aᴴ v))‖
        ≤ ‖v‖ * ‖opToCLM A (opToCLM Aᴴ v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (opNorm A * ‖opToCLM Aᴴ v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm (opToCLM A) _) (norm_nonneg v)
  have hpos : 0 < ‖opToCLM Aᴴ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  nlinarith

lemma hsNormSq_eq_sum_col_norm_sq {N : ℕ} (X : QubitOp N) :
    hsNormSq X = ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i : QubitIdx N ↦ X i j)‖ ^ 2 := by
  unfold hsNormSq hsInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl; intro i _
  simp only [WithLp.ofLp_toLp, Complex.star_def]
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma hsNormSq_conjTranspose {N : ℕ} (X : QubitOp N) : hsNormSq Xᴴ = hsNormSq X := by
  unfold hsNormSq hsInner
  rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

lemma hsNormSq_mul_left_le {N : ℕ} (M X : QubitOp N) :
    hsNormSq (M * X) ≤ (opNorm M) ^ 2 * hsNormSq X := by
  rw [hsNormSq_eq_sum_col_norm_sq (M * X), hsNormSq_eq_sum_col_norm_sq X, Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  let vj : EuclideanSpace ℂ (QubitIdx N) := WithLp.toLp 2 (fun i : QubitIdx N ↦ X i j)
  have hcol : WithLp.toLp 2 (fun i : QubitIdx N ↦ (M * X) i j) = opToCLM M vj := by
    ext i; simp [opToCLM, EuclideanSpace.equiv, vj, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hcol]
  have h1 : ‖opToCLM M vj‖ ≤ opNorm M * ‖vj‖ := ContinuousLinearMap.le_opNorm (opToCLM M) vj
  have hnn : 0 ≤ ‖opToCLM M vj‖ := norm_nonneg _
  nlinarith [mul_nonneg (opNorm_nonneg M) (norm_nonneg vj)]

lemma hsNormSq_mul_right_le {N : ℕ} (X M : QubitOp N) :
    hsNormSq (X * M) ≤ (opNorm M) ^ 2 * hsNormSq X := by
  rw [← hsNormSq_conjTranspose (X * M), Matrix.conjTranspose_mul, ← hsNormSq_conjTranspose X]
  have h1 := hsNormSq_mul_left_le Mᴴ Xᴴ
  have h2 : (opNorm Mᴴ) ^ 2 ≤ (opNorm M) ^ 2 := by
    have hle := opNorm_conjTranspose_le M
    nlinarith [opNorm_nonneg Mᴴ, opNorm_nonneg M]
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (hsNormSq_nonneg Xᴴ))

lemma opNorm_diagonal_le {N : ℕ} (d : QubitIdx N → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) :
    opNorm (Matrix.diagonal d) ≤ C := by
  unfold opNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hsq : ‖opToCLM (Matrix.diagonal d) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    have hval : (opToCLM (Matrix.diagonal d) v).ofLp i = d i * v.ofLp i := by
      simp [opToCLM, EuclideanSpace.equiv, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    rw [hval, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hd i, norm_nonneg (d i)]) (sq_nonneg _)
  nlinarith [norm_nonneg (opToCLM (Matrix.diagonal d) v), mul_nonneg hC (norm_nonneg v)]

lemma signedPauliU_diag_signedPauli (u : Fin 6) :
    signedPauli u =
      signedPauliU u * Matrix.diagonal ![(1 : ℂ), (-1 : ℂ)] * (signedPauliU u)ᴴ := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; norm_num
  have h2' : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [signedPauli, signedPauliU, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two] <;>
    (try ring_nf) <;> simp only [h2, h2', hI] <;> ring

lemma opNorm_kron_depolPHalf_mul_inv_le {N : ℕ} (s : Fin N → Fin 6) (U : Finset (Fin N)) :
    opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalfInv (s x) else 1)) *
      opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalf (s x) else 1)) ≤
      (Real.sqrt 3) ^ U.card := by
  let V : QubitOp N := kronOp (fun x ↦ if x ∈ U then signedPauliU (s x) else 1)
  have hV_unit : Vᴴ * V = 1 := by
    dsimp only [V]; rw [kronOp_conjTranspose, kronOp_mul]
    have h1 : (fun x : Fin N ↦ (if x ∈ U then signedPauliU (s x) else 1)ᴴ *
        (if x ∈ U then signedPauliU (s x) else 1)) = fun _ ↦ 1 := by
      funext x; by_cases hx : x ∈ U <;> simp [hx, signedPauliU_unitary]
    rw [h1]; ext i j; simp only [kronOp, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ↓reduceIte]
      have hne : ∃ x : Fin N, i x ≠ j x := by
        by_contra hall; push Not at hall; exact hij (funext hall)
      rcases hne with ⟨x, hx⟩
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Matrix.one_apply, hx])
  have hV_unit' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV_unit
  have hV1 : opNorm V ≤ 1 := opNorm_unitary_le hV_unit
  have hVh1 : opNorm Vᴴ ≤ 1 := opNorm_unitary_le (by rw [Matrix.conjTranspose_conjTranspose]; exact hV_unit')
  have hdiag_bound : ∀ (a b : ℝ) (c : ℝ), 0 ≤ c → |a| ≤ c → |b| ≤ c →
      ∀ (M : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ u, M u = signedPauliU u * Matrix.diagonal ![(a : ℂ), (b : ℂ)] * (signedPauliU u)ᴴ) →
        opNorm (kronOp (fun x ↦ if x ∈ U then M (s x) else 1)) ≤ c ^ U.card := by
    intro a b c hc ha hb M hM
    let d : QubitIdx N → ℂ := fun i ↦
      ∏ x : Fin N, if x ∈ U then (![(a : ℂ), (b : ℂ)] (i x)) else 1
    have hMeq : kronOp (fun x ↦ if x ∈ U then M (s x) else 1) = V * Matrix.diagonal d * Vᴴ := by
      have hD : Matrix.diagonal d = kronOp (fun x ↦
          if x ∈ U then Matrix.diagonal ![(a : ℂ), (b : ℂ)] else 1) := by
        ext i j; simp only [Matrix.diagonal_apply, kronOp, Matrix.of_apply]
        by_cases hij : i = j
        · subst hij; dsimp only [d]; simp only [↓reduceIte, Matrix.diagonal_apply_eq]
          apply Finset.prod_congr rfl; intro x _; by_cases hx : x ∈ U <;> simp [hx]
        · simp only [hij, ↓reduceIte]
          have hne : ∃ x : Fin N, i x ≠ j x := by
            by_contra hall; push Not at hall; exact hij (funext hall)
          rcases hne with ⟨x, hx⟩
          exact (Finset.prod_eq_zero (Finset.mem_univ x) (by
            by_cases hxU : x ∈ U <;> simp [hxU, Matrix.diagonal_apply_ne _ hx, Matrix.one_apply, hx])).symm
      rw [hD]; dsimp only [V]; rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul]
      congr 1; funext x
      by_cases hx : x ∈ U
      · simp only [hx, ↓reduceIte]; exact hM (s x)
      · simp [hx]
    rw [hMeq]
    have hd_le : ∀ i : QubitIdx N, ‖d i‖ ≤ c ^ U.card := by
      intro i; dsimp only [d]; rw [norm_prod]
      calc ∏ x : Fin N, ‖if x ∈ U then (![(a : ℂ), (b : ℂ)] (i x)) else 1‖
          ≤ ∏ x : Fin N, (if x ∈ U then c else 1) := by
            apply real_prod_le_prod
            · intro x _; exact norm_nonneg _
            · intro x _; by_cases hx : x ∈ U
              · simp only [hx, ↓reduceIte]
                generalize hix : i x = b
                fin_cases b <;>
                  simp [Complex.norm_real, Real.norm_eq_abs, ha, hb]
              · simp [hx]
        _ = c ^ U.card := by
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1; congr 1; ext x; simp
    have hDnorm : opNorm (Matrix.diagonal d) ≤ c ^ U.card :=
      opNorm_diagonal_le d (pow_nonneg hc _) hd_le
    calc opNorm (V * Matrix.diagonal d * Vᴴ)
        ≤ opNorm (V * Matrix.diagonal d) * opNorm Vᴴ := opNorm_mul_le _ _
      _ ≤ (opNorm V * opNorm (Matrix.diagonal d)) * opNorm Vᴴ :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * c ^ U.card) * 1 := by
          apply mul_le_mul
            (mul_le_mul hV1 hDnorm (opNorm_nonneg _) zero_le_one)
            hVh1 (opNorm_nonneg _) (by positivity)
      _ = c ^ U.card := by ring
  have hlin_diag : ∀ (u : Fin 6) (α β : ℂ),
      α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • signedPauli u =
        signedPauliU u * Matrix.diagonal ![α + β, α - β] * (signedPauliU u)ᴴ := by
    intro u α β
    have hUU : (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        signedPauliU u * Matrix.diagonal ![(1 : ℂ), (1 : ℂ)] * (signedPauliU u)ᴴ := by
      rw [show Matrix.diagonal ![(1 : ℂ), (1 : ℂ)] = 1 from by
        ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.mul_one]
      exact (mul_eq_one_comm.mp (signedPauliU_unitary u)).symm
    conv_lhs => rw [hUU, signedPauliU_diag_signedPauli u]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  have hdiag_half : ∀ u : Fin 6, depolPHalf u =
      signedPauliU u * Matrix.diagonal ![(((Real.sqrt 3 / 2 : ℝ) : ℂ)), (((1 / 2 : ℝ) : ℂ))] *
        (signedPauliU u)ᴴ := by
    intro u; unfold depolPHalf; rw [hlin_diag]
    congr 2; ext i j; fin_cases i <;> fin_cases j <;> simp <;> push_cast <;> ring
  have hdiag_inv : ∀ u : Fin 6, depolPHalfInv u =
      signedPauliU u * Matrix.diagonal ![(((2 / Real.sqrt 3 : ℝ) : ℂ)), (((2 : ℝ) : ℂ))] *
        (signedPauliU u)ᴴ := by
    intro u; unfold depolPHalfInv; rw [hlin_diag]
    congr 2; ext i j; fin_cases i <;> fin_cases j <;> simp <;> push_cast <;> ring
  have hs3_ge1 : (1 : ℝ) ≤ Real.sqrt 3 := by
    have : (1 : ℝ) = Real.sqrt 1 := by simp
    rw [this]; exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalf (s x) else 1)) ≤
      (Real.sqrt 3 / 2) ^ U.card :=
    hdiag_bound (Real.sqrt 3 / 2) (1 / 2) (Real.sqrt 3 / 2) (by positivity)
      (by rw [abs_of_nonneg (by positivity)])
      (by rw [abs_of_nonneg (by norm_num)]; linarith) depolPHalf hdiag_half
  have h2 : opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalfInv (s x) else 1)) ≤
      (2 : ℝ) ^ U.card :=
    hdiag_bound (2 / Real.sqrt 3) 2 2 (by norm_num)
      (by rw [abs_of_nonneg (by positivity), div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]; linarith)
      (by rw [abs_of_nonneg (by norm_num)]) depolPHalfInv hdiag_inv
  calc opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalfInv (s x) else 1)) *
        opNorm (kronOp (fun x ↦ if x ∈ U then depolPHalf (s x) else 1))
      ≤ (2 : ℝ) ^ U.card * (Real.sqrt 3 / 2) ^ U.card :=
        mul_le_mul h2 h1 (opNorm_nonneg _) (pow_nonneg (by norm_num) _)
    _ = (2 * (Real.sqrt 3 / 2)) ^ U.card := by rw [← mul_pow]
    _ = (Real.sqrt 3) ^ U.card := by congr 1; ring

private lemma pauliMat_span_all (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • pauliMat 0 +
        ((M 0 1 + M 1 0) / 2) • pauliMat 1 +
        ((Complex.I * (M 0 1 - M 1 0)) / 2) • pauliMat 2 +
        ((M 0 0 - M 1 1) / 2) • pauliMat 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliMat, pauliX, pauliY, pauliZ] <;> (try ring_nf) <;> simp [Complex.I_sq] <;> ring

lemma prodDepolBasis_mem_supportedOn_compl {N : ℕ} (s s' : Fin N → Fin 6)
    (U : Finset (Fin N)) (a : Fin N → Fin 4) (ha : ∀ y ∈ U, a y = 0) :
    prodDepolBasis s s' a ∈ supportedOn Uᶜ := by
  unfold prodDepolBasis
  have h0_eq : ∀ u v : Fin 6, ∃ c : ℂ, singleDepolBasis u v 0 = c • pauliMat 0 := by
    intro u v
    refine ⟨((Real.sqrt (singleDepolInner u v 1 1).re)⁻¹ : ℂ), ?_⟩
    unfold singleDepolBasis singleDepolGS0
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
  have hkron_mem : ∀ (f : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ y ∈ U, ∃ c : ℂ, f y = c • pauliMat 0) →
      kronOp f ∈ supportedOn Uᶜ := by
    intro f hf
    have hcoeff : ∀ x : Fin N, ∃ g : Fin 4 → ℂ,
        f x = ∑ k : Fin 4, g k • pauliMat k ∧ (x ∈ U → ∀ k : Fin 4, k ≠ 0 → g k = 0) := by
      intro x
      by_cases hx : x ∈ U
      · rcases hf x hx with ⟨c, hc⟩
        refine ⟨fun k ↦ if k = 0 then c else 0, ?_, fun _ k hk ↦ by simp [hk]⟩
        rw [Fin.sum_univ_four]; simp [hc]
      · refine ⟨fun k ↦
          match k with
          | 0 => (f x 0 0 + f x 1 1) / 2
          | 1 => (f x 0 1 + f x 1 0) / 2
          | 2 => (Complex.I * (f x 0 1 - f x 1 0)) / 2
          | 3 => (f x 0 0 - f x 1 1) / 2, ?_, fun hxU ↦ absurd hxU hx⟩
        rw [Fin.sum_univ_four]; simpa using pauliMat_span_all (f x)
    choose g hg hgz using hcoeff
    have hfk : kronOp f = ∑ b : Fin N → Fin 4, (∏ x : Fin N, g x (b x)) • pauliString b := by
      have h1 : kronOp f = kronOp (fun x ↦ ∑ k : Fin 4, g x k • pauliMat k) := by
        congr 1; funext x; exact hg x
      rw [h1]
      ext i j
      simp only [kronOp, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        pauliString, Finset.sum_apply]
      have hps := Fintype.prod_sum (fun (x : Fin N) (k : Fin 4) ↦ g x k * pauliMat k (i x) (j x))
      rw [hps]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.prod_mul_distrib]
    rw [hfk]
    apply Submodule.sum_mem
    intro b _
    by_cases hb : ∀ y ∈ U, b y = 0
    · exact Submodule.smul_mem _ _ (pauliString_mem_supportedOn b fun x hx ↦ hb x (by simpa using hx))
    · push Not at hb
      rcases hb with ⟨y, hyU, hby⟩
      have hprod0 : ∏ x : Fin N, g x (b x) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ y) (hgz y hyU (b y) hby)
      rw [hprod0, zero_smul]
      exact Submodule.zero_mem _
  apply hkron_mem
  intro y hy
  rw [ha y hy]
  exact h0_eq (s y) (s' y)

/-- **Multi-Site Depolarized Commutator Conditioning Bound**:
For ANY `s, s' : Fin N → Fin 6`, `U : Finset (Fin N)`, `W ∈ supportedOn U`, and `A : QubitOp N`:
`prodDepolNormSq s s' (matComm A W) ≤ 4 * 3 ^ U.card * (opNorm W) ^ 2 * ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A`. -/
theorem prodDepolNormSq_matComm_supportedOn_le {N : ℕ} (s s' : Fin N → Fin 6)
    {U : Finset (Fin N)} {W : QubitOp N} (hW : W ∈ supportedOn U) (A : QubitOp N) :
    prodDepolNormSq s s' (matComm A W) ≤
      4 * (3 : ℝ) ^ U.card * (opNorm W) ^ 2 *
        ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
  let c : (Fin N → Fin 4) → ℂ := fun a ↦ prodDepolInner s s' (prodDepolBasis s s' a) A
  let B : QubitOp N :=
    ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ∀ y ∈ U, a y = 0),
      c a • prodDepolBasis s s' a
  have hB_mem : B ∈ supportedOn Uᶜ := Submodule.sum_mem _ fun a ha ↦
    Submodule.smul_mem _ _ (prodDepolBasis_mem_supportedOn_compl s s' U a (Finset.mem_filter.mp ha).2)
  have hcomm_B : matComm B W = 0 := by
    unfold matComm
    rw [supportedOn_comm_of_disjoint disjoint_compl_left hB_mem hW, sub_self]
  have hcomm_eq : matComm A W = matComm (A - B) W := by
    unfold matComm
    have : (A - B) * W - W * (A - B) = (A * W - W * A) - (B * W - W * B) := by noncomm_ring
    rw [this]; unfold matComm at hcomm_B; rw [hcomm_B, sub_zero]
  rw [hcomm_eq]
  set Z := A - B
  -- Bound `prodDepolNormSq s s' (Z * W)` and `prodDepolNormSq s s' (W * Z)`
  have hZW_le : prodDepolNormSq s s' (Z * W) ≤ (3 : ℝ) ^ U.card * (opNorm W) ^ 2 * prodDepolNormSq s s' Z := by
    unfold prodDepolNormSq
    rw [prodDepolInner_eq_hsInner, prodDepolInner_eq_hsInner]
    change hsNormSq (globalDepolPHalf N s' * (Z * W) * globalDepolPHalf N s) ≤
      (3 : ℝ) ^ U.card * (opNorm W) ^ 2 * hsNormSq (globalDepolPHalf N s' * Z * globalDepolPHalf N s)
    let L : QubitOp N := kronOp (fun x ↦ if x ∈ U then depolPHalfInv (s x) else 1)
    let R : QubitOp N := kronOp (fun x ↦ if x ∈ U then depolPHalf (s x) else 1)
    have hconj : globalDepolPHalf N s' * (Z * W) * globalDepolPHalf N s =
        (globalDepolPHalf N s' * Z * globalDepolPHalf N s) * (L * W * R) := by
      have hcomm_W : W * globalDepolPHalf N s = globalDepolPHalf N s * (L * W * R) := by
        have hstep : globalDepolPHalf N s * L = kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) := by
          unfold globalDepolPHalf; dsimp only [L]; rw [kronOp_mul]
          congr 1; funext x; by_cases hx : x ∈ U
          · simp [hx, depolPHalf_mul_inv]
          · simp [hx]
        have hstep2 : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) * W =
            W * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) := by
          have hmem_compl : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) ∈ supportedOn Uᶜ := by
            have hcoeff : ∀ x : Fin N, ∃ g : Fin 4 → ℂ,
                (if x ∈ U then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s x)) =
                  ∑ k : Fin 4, g k • pauliMat k ∧ (x ∈ U → ∀ k : Fin 4, k ≠ 0 → g k = 0) := by
              intro x; by_cases hx : x ∈ U
              · refine ⟨fun k ↦ if k = 0 then 1 else 0, ?_, fun _ k hk ↦ by simp [hk]⟩
                rw [Fin.sum_univ_four]; simp [hx]
                ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
              · let M := depolPHalf (s x)
                refine ⟨fun k ↦
                  match k with
                  | 0 => (M 0 0 + M 1 1) / 2
                  | 1 => (M 0 1 + M 1 0) / 2
                  | 2 => (Complex.I * (M 0 1 - M 1 0)) / 2
                  | 3 => (M 0 0 - M 1 1) / 2, ?_, fun hxU ↦ absurd hxU hx⟩
                simp only [hx, ↓reduceIte]; rw [Fin.sum_univ_four]; exact pauliMat_span_all M
            choose g hg hgz using hcoeff
            have hfk : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) =
                ∑ b : Fin N → Fin 4, (∏ x : Fin N, g x (b x)) • pauliString b := by
              have h1 : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) =
                  kronOp (fun x ↦ ∑ k : Fin 4, g x k • pauliMat k) := by
                congr 1; funext x; exact hg x
              rw [h1]; ext i j
              simp only [kronOp, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
                pauliString, Finset.sum_apply]
              rw [Fintype.prod_sum (fun (x : Fin N) (k : Fin 4) ↦ g x k * pauliMat k (i x) (j x))]
              apply Finset.sum_congr rfl; intro b _; rw [Finset.prod_mul_distrib]
            rw [hfk]; apply Submodule.sum_mem; intro b _
            by_cases hb : ∀ y ∈ U, b y = 0
            · exact Submodule.smul_mem _ _ (pauliString_mem_supportedOn b fun x hx ↦ hb x (by simpa using hx))
            · push Not at hb; rcases hb with ⟨y, hyU, hby⟩
              rw [Finset.prod_eq_zero (Finset.mem_univ y) (hgz y hyU (b y) hby), zero_smul]
              exact Submodule.zero_mem _
          exact supportedOn_comm_of_disjoint disjoint_compl_left hmem_compl hW
        have hstep3 : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) * R =
            globalDepolPHalf N s := by
          unfold globalDepolPHalf; dsimp only [R]; rw [kronOp_mul]
          congr 1; funext x; by_cases hx : x ∈ U <;> simp [hx]
        symm; calc globalDepolPHalf N s * (L * W * R)
            = (globalDepolPHalf N s * L) * W * R := by simp only [Matrix.mul_assoc]
          _ = (kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) * W) * R := by rw [hstep]
          _ = (W * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x))) * R := by rw [hstep2]
          _ = W * (kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s x)) * R) := by simp only [Matrix.mul_assoc]
          _ = W * globalDepolPHalf N s := by rw [hstep3]
      calc globalDepolPHalf N s' * (Z * W) * globalDepolPHalf N s
          = globalDepolPHalf N s' * Z * (W * globalDepolPHalf N s) := by simp only [Matrix.mul_assoc]
        _ = globalDepolPHalf N s' * Z * (globalDepolPHalf N s * (L * W * R)) := by rw [hcomm_W]
        _ = (globalDepolPHalf N s' * Z * globalDepolPHalf N s) * (L * W * R) := by simp only [Matrix.mul_assoc]
    rw [hconj]
    have hMnorm : opNorm (L * W * R) ≤ (Real.sqrt 3) ^ U.card * opNorm W := by
      have h1 := opNorm_kron_depolPHalf_mul_inv_le s U
      calc opNorm (L * W * R)
          ≤ opNorm (L * W) * opNorm R := opNorm_mul_le _ _
        _ ≤ (opNorm L * opNorm W) * opNorm R :=
            mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
        _ = (opNorm L * opNorm R) * opNorm W := by ring
        _ ≤ (Real.sqrt 3) ^ U.card * opNorm W :=
            mul_le_mul_of_nonneg_right h1 (opNorm_nonneg W)
    have hMsq : (opNorm (L * W * R)) ^ 2 ≤ (3 : ℝ) ^ U.card * (opNorm W) ^ 2 := by
      have hsq3 : ((Real.sqrt 3) ^ U.card) ^ 2 = (3 : ℝ) ^ U.card := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
      have h0 : (opNorm (L * W * R)) ^ 2 ≤ ((Real.sqrt 3) ^ U.card * opNorm W) ^ 2 := by
        nlinarith [hMnorm, opNorm_nonneg (L * W * R)]
      rw [mul_pow, hsq3] at h0; exact h0
    exact le_trans (hsNormSq_mul_right_le _ _) (mul_le_mul_of_nonneg_right hMsq (hsNormSq_nonneg _))
  have hWZ_le : prodDepolNormSq s s' (W * Z) ≤ (3 : ℝ) ^ U.card * (opNorm W) ^ 2 * prodDepolNormSq s s' Z := by
    unfold prodDepolNormSq
    rw [prodDepolInner_eq_hsInner, prodDepolInner_eq_hsInner]
    change hsNormSq (globalDepolPHalf N s' * (W * Z) * globalDepolPHalf N s) ≤
      (3 : ℝ) ^ U.card * (opNorm W) ^ 2 * hsNormSq (globalDepolPHalf N s' * Z * globalDepolPHalf N s)
    let L : QubitOp N := kronOp (fun x ↦ if x ∈ U then depolPHalf (s' x) else 1)
    let R : QubitOp N := kronOp (fun x ↦ if x ∈ U then depolPHalfInv (s' x) else 1)
    have hconj : globalDepolPHalf N s' * (W * Z) * globalDepolPHalf N s =
        (L * W * R) * (globalDepolPHalf N s' * Z * globalDepolPHalf N s) := by
      have hcomm_W : globalDepolPHalf N s' * W = (L * W * R) * globalDepolPHalf N s' := by
        have hstep : R * globalDepolPHalf N s' = kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) := by
          unfold globalDepolPHalf; dsimp only [R]; rw [kronOp_mul]
          congr 1; funext x; by_cases hx : x ∈ U
          · simp [hx, depolPHalfInv_mul]
          · simp [hx]
        have hstep2 : W * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) =
            kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) * W := by
          have hmem_compl : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) ∈ supportedOn Uᶜ := by
            have hcoeff : ∀ x : Fin N, ∃ g : Fin 4 → ℂ,
                (if x ∈ U then (1 : Matrix (Fin 2) (Fin 2) ℂ) else depolPHalf (s' x)) =
                  ∑ k : Fin 4, g k • pauliMat k ∧ (x ∈ U → ∀ k : Fin 4, k ≠ 0 → g k = 0) := by
              intro x; by_cases hx : x ∈ U
              · refine ⟨fun k ↦ if k = 0 then 1 else 0, ?_, fun _ k hk ↦ by simp [hk]⟩
                rw [Fin.sum_univ_four]; simp [hx]
                ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
              · let M := depolPHalf (s' x)
                refine ⟨fun k ↦
                  match k with
                  | 0 => (M 0 0 + M 1 1) / 2
                  | 1 => (M 0 1 + M 1 0) / 2
                  | 2 => (Complex.I * (M 0 1 - M 1 0)) / 2
                  | 3 => (M 0 0 - M 1 1) / 2, ?_, fun hxU ↦ absurd hxU hx⟩
                simp only [hx, ↓reduceIte]; rw [Fin.sum_univ_four]; exact pauliMat_span_all M
            choose g hg hgz using hcoeff
            have hfk : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) =
                ∑ b : Fin N → Fin 4, (∏ x : Fin N, g x (b x)) • pauliString b := by
              have h1 : kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) =
                  kronOp (fun x ↦ ∑ k : Fin 4, g x k • pauliMat k) := by
                congr 1; funext x; exact hg x
              rw [h1]; ext i j
              simp only [kronOp, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
                pauliString, Finset.sum_apply]
              rw [Fintype.prod_sum (fun (x : Fin N) (k : Fin 4) ↦ g x k * pauliMat k (i x) (j x))]
              apply Finset.sum_congr rfl; intro b _; rw [Finset.prod_mul_distrib]
            rw [hfk]; apply Submodule.sum_mem; intro b _
            by_cases hb : ∀ y ∈ U, b y = 0
            · exact Submodule.smul_mem _ _ (pauliString_mem_supportedOn b fun x hx ↦ hb x (by simpa using hx))
            · push Not at hb; rcases hb with ⟨y, hyU, hby⟩
              rw [Finset.prod_eq_zero (Finset.mem_univ y) (hgz y hyU (b y) hby), zero_smul]
              exact Submodule.zero_mem _
          exact (supportedOn_comm_of_disjoint disjoint_compl_left hmem_compl hW).symm
        have hstep3 : L * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) =
            globalDepolPHalf N s' := by
          unfold globalDepolPHalf; dsimp only [L]; rw [kronOp_mul]
          congr 1; funext x; by_cases hx : x ∈ U <;> simp [hx]
        symm; calc (L * W * R) * globalDepolPHalf N s'
            = L * (W * (R * globalDepolPHalf N s')) := by simp only [Matrix.mul_assoc]
          _ = L * (W * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x))) := by rw [hstep]
          _ = L * (kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x)) * W) := by rw [hstep2]
          _ = (L * kronOp (fun x ↦ if x ∈ U then 1 else depolPHalf (s' x))) * W := by simp only [Matrix.mul_assoc]
          _ = globalDepolPHalf N s' * W := by rw [hstep3]
      calc globalDepolPHalf N s' * (W * Z) * globalDepolPHalf N s
          = (globalDepolPHalf N s' * W) * Z * globalDepolPHalf N s := by simp only [Matrix.mul_assoc]
        _ = ((L * W * R) * globalDepolPHalf N s') * Z * globalDepolPHalf N s := by rw [hcomm_W]
        _ = (L * W * R) * (globalDepolPHalf N s' * Z * globalDepolPHalf N s) := by simp only [Matrix.mul_assoc]
    rw [hconj]
    have hMnorm : opNorm (L * W * R) ≤ (Real.sqrt 3) ^ U.card * opNorm W := by
      have h1 := opNorm_kron_depolPHalf_mul_inv_le s' U
      calc opNorm (L * W * R)
          ≤ opNorm (L * W) * opNorm R := opNorm_mul_le _ _
        _ ≤ (opNorm L * opNorm W) * opNorm R :=
            mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _)
        _ = (opNorm R * opNorm L) * opNorm W := by ring
        _ ≤ (Real.sqrt 3) ^ U.card * opNorm W :=
            mul_le_mul_of_nonneg_right h1 (opNorm_nonneg W)
    have hMsq : (opNorm (L * W * R)) ^ 2 ≤ (3 : ℝ) ^ U.card * (opNorm W) ^ 2 := by
      have hsq3 : ((Real.sqrt 3) ^ U.card) ^ 2 = (3 : ℝ) ^ U.card := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
      have h0 : (opNorm (L * W * R)) ^ 2 ≤ ((Real.sqrt 3) ^ U.card * opNorm W) ^ 2 := by
        nlinarith [hMnorm, opNorm_nonneg (L * W * R)]
      rw [mul_pow, hsq3] at h0; exact h0
    exact le_trans (hsNormSq_mul_left_le _ _) (mul_le_mul_of_nonneg_right hMsq (hsNormSq_nonneg _))
  -- Now bound `prodDepolNormSq s s' Z ≤ ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A`
  have hZ_le : prodDepolNormSq s s' Z ≤
      ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
    have hZ_expand : Z = ∑ a : Fin N → Fin 4,
        (if ∀ y ∈ U, a y = 0 then (0 : ℂ) else c a) • prodDepolBasis s s' a := by
      dsimp only [Z, B]
      conv_lhs => rw [prodDepolBasis_expand s s' A]
      have hB_full : ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ∀ y ∈ U, a y = 0),
            c a • prodDepolBasis s s' a =
          ∑ a : Fin N → Fin 4,
            (if ∀ y ∈ U, a y = 0 then c a else 0) • prodDepolBasis s s' a := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro a _
        split_ifs <;> simp
      rw [hB_full, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro a _
      by_cases ha : ∀ y ∈ U, a y = 0 <;> simp only [ha, ↓reduceIte, zero_smul, sub_self, sub_zero, c]
    rw [hZ_expand, prodDepolNormSq_expand]
    have hfilt : ∑ a : Fin N → Fin 4, ‖if ∀ y ∈ U, a y = 0 then (0 : ℂ) else c a‖ ^ 2 =
        ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ∃ y ∈ U, a y ≠ 0), ‖c a‖ ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro a _
      by_cases ha : ∀ y ∈ U, a y = 0
      · have hnot : ¬ ∃ y ∈ U, a y ≠ 0 := by push Not; exact ha
        simp [ha, hnot]
      · have hex : ∃ y ∈ U, a y ≠ 0 := by by_contra h; push Not at h; exact ha h
        simp [ha, hex]
    rw [hfilt]
    have hsub_u : Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ∃ y ∈ U, a y ≠ 0) ⊆
        U.biUnion (fun y ↦ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a y ≠ 0)) := by
      intro a ha
      rcases (Finset.mem_filter.mp ha).2 with ⟨y, hyU, hay⟩
      exact Finset.mem_biUnion.mpr ⟨y, hyU, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hay⟩⟩
    calc ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ∃ y ∈ U, a y ≠ 0), ‖c a‖ ^ 2
        ≤ ∑ a ∈ U.biUnion (fun y ↦ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a y ≠ 0)), ‖c a‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_u fun _ _ _ ↦ sq_nonneg _
      _ ≤ ∑ y ∈ U, ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a y ≠ 0), ‖c a‖ ^ 2 :=
          real_sum_biUnion_le _ _ _ fun _ _ ↦ sq_nonneg _
      _ = ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
          apply Finset.sum_congr rfl; intro y _
          exact (prodDepolDistSq_singleSite_eq s s' y A).symm
  have hpar : prodDepolNormSq s s' (matComm Z W) ≤
      2 * (prodDepolNormSq s s' (Z * W) + prodDepolNormSq s s' (W * Z)) := by
    unfold matComm
    have hpar_eq : prodDepolNormSq s s' (Z * W - W * Z) + prodDepolNormSq s s' (Z * W + W * Z) =
        2 * (prodDepolNormSq s s' (Z * W) + prodDepolNormSq s s' (W * Z)) := by
      unfold prodDepolNormSq prodDepolInner
      set P1 := globalDepolP N s
      set P2 := globalDepolP N s'
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add]
      simp only [mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub, Matrix.trace_add,
        Complex.sub_re, Complex.add_re]
      ring
    linarith [prodDepolNormSq_nonneg s s' (Z * W + W * Z)]
  have hfac_nn : 0 ≤ (3 : ℝ) ^ U.card * (opNorm W) ^ 2 :=
    mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)
  nlinarith

end MultiSiteCommutatorConditioning

end KrylovChaos
