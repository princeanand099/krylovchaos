/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.DoubleWellTunneling
import KrylovChaos.ConcreteEndToEndWiring
import Mathlib.Tactic

/-!
# Proposition 9.1(2): Full-Rank Bimodal Perturbation `ρ_ε = (1 - ε) ρ + ε I / 2^N`

Instantiates `GibbsData N` for the full-rank bimodal perturbation
`ρ_ε = (1 - ε) ((1/2) |0⋯0⟩⟨0⋯0| + (1/2) I / 2^N) + ε I / 2^N` (`ε ∈ (0, 1)`) and proves
directly on `lambdaMSS (bimodalPerturbedGibbs N hε0 hε1) 1` that Hypothesis (H2) is violated
for every `δ ∈ [0, 1)` and every `C₁, C₂ ≥ 0`:
1. `bimodalPerturbedGibbs`: constructs a full-rank `GibbsData N` for every `N` and `ε ∈ (0, 1)`.
2. `bimodalPerturbed_mssThermalSize_lower`: computes the exact diagonal site-size difference for
   the normalized 1-local Hermitian operator `A = (3 - ε)^{-1/2} (1 + Z_{x₀}) ∈ filtrationSubmodule N 1`,
   proving `mssThermalSize G A ≥ (N - 1) / 96 - 1 / 2` for `N ≥ 4` and `ε ∈ (0, 1/2]`.
3. `prop_9_1_part2_full_rank_lambdaMSS_violates_H2`: proves `lambdaMSS G 1 ≥ (N - 1) / 96 - 1 / 2`
   and deduces `C₁ * 1 + C₂ * N^δ * 1^(1 - δ) < lambdaMSS (bimodalPerturbedGibbs N hε0 hε1) 1`
   for all sufficiently large `N` and all `ε ∈ (0, 1/2]`.
-/

namespace KrylovChaos

open Matrix Filter Topology

section FullRankBimodalGibbs

/-- All-zero computational basis string `0⋯0 : QubitIdx N`. -/
def allZeroIdx (N : ℕ) : QubitIdx N := fun _ ↦ 0

/-- Bit-flip of `s : QubitIdx N` at site `x : Fin N`. -/
private def bmFlip {N : ℕ} (x : Fin N) (s : QubitIdx N) : QubitIdx N :=
  Function.update s x (1 - s x)

private lemma bmFlip_bmFlip {N : ℕ} (x : Fin N) (s : QubitIdx N) :
    bmFlip x (bmFlip x s) = s := by
  ext y
  unfold bmFlip
  by_cases hy : y = x
  · subst hy
    simp only [Function.update_self]
    generalize hb : s y = b; fin_cases b <;> decide
  · simp [Function.update_of_ne hy]

private lemma bmFlip_ne_self {N : ℕ} (x : Fin N) (s : QubitIdx N) :
    bmFlip x s ≠ s := by
  intro h
  have hx := congrFun h x
  unfold bmFlip at hx
  simp only [Function.update_self] at hx
  generalize hb : s x = b; rw [hb] at hx; fin_cases b <;> simp at hx

/-- Diagonal probabilities of `ρ_ε = (1 - ε) ((1/2)|0⋯0⟩⟨0⋯0| + (1/2) I / 2^N) + ε I / 2^N`. -/
noncomputable def bimodalPerturbedProb (N : ℕ) (ε : ℝ) (s : QubitIdx N) : ℝ :=
  (1 - ε) * (if s = allZeroIdx N then (1 / 2 : ℝ) else 0) + (1 + ε) / (2 ^ (N + 1) : ℝ)

lemma bimodalPerturbedProb_pos {N : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (s : QubitIdx N) :
    0 < bimodalPerturbedProb N ε s := by
  unfold bimodalPerturbedProb
  have h1 : 0 ≤ (1 - ε) * (if s = allZeroIdx N then (1 / 2 : ℝ) else 0) := by
    split_ifs <;> linarith
  have h2 : 0 < (1 + ε) / (2 ^ (N + 1) : ℝ) := by positivity
  linarith

lemma bimodalPerturbedProb_sum {N : ℕ} (ε : ℝ) :
    ∑ s : QubitIdx N, bimodalPerturbedProb N ε s = 1 := by
  unfold bimodalPerturbedProb
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ]
  have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp [h2N]
  ring

/-- Full-rank `GibbsData N` for `ρ_ε = (1 - ε) ρ_bimodal + ε I / 2^N` (`ε ∈ (0, 1)`). -/
noncomputable def bimodalPerturbedGibbs (N : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    GibbsData N where
  ρβ := Matrix.diagonal (fun s ↦ (bimodalPerturbedProb N ε s : ℂ))
  ρHalf := Matrix.diagonal (fun s ↦ (Real.sqrt (bimodalPerturbedProb N ε s) : ℂ))
  ρQuarter := Matrix.diagonal (fun s ↦ (Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) : ℂ))
  ρQuarterInv := Matrix.diagonal (fun s ↦ ((Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)))⁻¹ : ℂ))
  ρβ_herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρHalf_herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρQuarter_herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  ρQuarterInv_herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  sq_quarter := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  sq_half := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (bimodalPerturbedProb_pos hε0 hε1 s).le]
  inv_left := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀]
      · simp
      · exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (bimodalPerturbedProb_pos hε0 hε1 i))).ne'
    · rfl
  inv_right := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀]
      · simp
      · exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (bimodalPerturbedProb_pos hε0 hε1 i))).ne'
    · rfl
  trace_one := by
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, bimodalPerturbedProb_sum ε, Complex.ofReal_one]

/-- Entrywise formula for `pauliSite x k`. -/
private lemma pauliSite_entry {N : ℕ} (x : Fin N) (k : Fin 4) (a b : QubitIdx N) :
    pauliSite x k a b =
      ∏ y : Fin N, if y = x then pauliMat k (a y) (b y) else if a y = b y then 1 else 0 := by
  unfold pauliSite pauliString kronOp
  simp only [Matrix.of_apply]
  apply Finset.prod_congr rfl; intro y _
  by_cases hy : y = x
  · subst hy; simp
  · rw [if_neg hy, Function.update_of_ne hy]
    generalize ha : a y = ay; generalize hb : b y = by_
    fin_cases ay <;> fin_cases by_ <;> simp [pauliMat]

/-- Equivalent 3-Pauli-commutator form of `siteSizeOp x M`. -/
private lemma siteSizeOp_eq_three_avg {N : ℕ} (x : Fin N) (M : QubitOp N) :
    siteSizeOp x M =
      (1 / 4 : ℂ) • ∑ α : Fin 3, (M - pauliSite x α.succ * M * pauliSite x α.succ) := by
  have h0 : pauliSite x 0 = 1 := by
    unfold pauliSite pauliString
    have hfun : (fun y : Fin N ↦ pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x 0 y)) =
        fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext y
      by_cases hy : y = x
      · subst hy; simp [pauliMat]
      · rw [Function.update_of_ne hy]; simp [pauliMat]
    rw [hfun, kronOp_one]
  unfold siteSizeOp partialTraceSite
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  have hs2 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := by decide
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hs2, h0, Matrix.one_mul, Matrix.mul_one]
  ext s t
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- Exact action of `pauliSite x 3` (`Z_x`) on a computational-basis diagonal matrix. -/
private lemma pauliSite_conj_diagonal_Z {N : ℕ} (x : Fin N) (d : QubitIdx N → ℂ) :
    pauliSite x 3 * Matrix.diagonal d * pauliSite x 3 = Matrix.diagonal d := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [pauliSite_entry]
  have h1 : ∀ a b : QubitIdx N,
      (∏ y : Fin N, if y = x then pauliMat 3 (a y) (b y) else if a y = b y then 1 else 0) =
      if a = b then pauliMat 3 (a x) (a x) else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      calc ∏ y : Fin N, (if y = x then pauliMat 3 (a y) (a y) else if a y = a y then 1 else 0)
          = ∏ y : Fin N, (if y = x then pauliMat 3 (a y) (a y) else 1) := by
            apply Finset.prod_congr rfl; intro y _; by_cases hy : y = x <;> simp [hy]
        _ = pauliMat 3 (a x) (a x) := by rw [Finset.prod_ite_eq']; simp
    · rw [if_neg hab]
      obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin N, a y₀ ≠ b y₀ := by
        by_contra h; push Not at h; exact hab (funext h)
      apply Finset.prod_eq_zero (Finset.mem_univ y₀)
      by_cases hyx : y₀ = x
      · subst hyx; rw [if_pos rfl]
        generalize ha : a y₀ = ay at hy₀ ⊢; generalize hb : b y₀ = by_ at hy₀ ⊢
        fin_cases ay <;> fin_cases by_ <;> first | exact absurd rfl hy₀ | simp [pauliMat]
      · rw [if_neg hyx, if_neg hy₀]
  simp only [h1]
  have hsum : ∑ u : QubitIdx N, (if s = u then pauliMat 3 (s x) (s x) else 0) * d u *
      (if u = t then pauliMat 3 (u x) (u x) else 0) =
      if s = t then pauliMat 3 (s x) (s x) * d s * pauliMat 3 (s x) (s x) else 0 := by
    rw [Finset.sum_eq_single s]
    · simp only [↓reduceIte]; split_ifs <;> ring
    · intro u _ hus; rw [if_neg hus.symm, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ s) h
  have hzsq : pauliMat 3 (s x) (s x) * pauliMat 3 (s x) (s x) = 1 := by
    generalize hb : s x = b; fin_cases b <;> simp [pauliMat]
  calc (∑ u : QubitIdx N, (if s = u then pauliMat 3 (s x) (s x) else 0) * d u *
        (if u = t then pauliMat 3 (u x) (u x) else 0))
      = if s = t then pauliMat 3 (s x) (s x) * d s * pauliMat 3 (s x) (s x) else 0 := hsum
    _ = if s = t then d s else 0 := by
        split_ifs
        · calc pauliMat 3 (s x) (s x) * d s * pauliMat 3 (s x) (s x)
              = (pauliMat 3 (s x) (s x) * pauliMat 3 (s x) (s x)) * d s := by ring
            _ = d s := by rw [hzsq, one_mul]
        · rfl

/-- Exact action of `pauliSite x 1` (`X_x`) and `pauliSite x 2` (`Y_x`) on a diagonal matrix. -/
private lemma pauliSite_conj_diagonal_XY {N : ℕ} (x : Fin N) (α : Fin 4)
    (hα : α = 1 ∨ α = 2) (d : QubitIdx N → ℂ) :
    pauliSite x α * Matrix.diagonal d * pauliSite x α =
      Matrix.diagonal (fun s ↦ d (bmFlip x s)) := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [pauliSite_entry]
  have h1 : ∀ a b : QubitIdx N,
      (∏ y : Fin N, if y = x then pauliMat α (a y) (b y) else if a y = b y then 1 else 0) =
      if b = bmFlip x a then pauliMat α (a x) (1 - a x) else 0 := by
    intro a b
    by_cases hab : b = bmFlip x a
    · subst hab
      rw [if_pos rfl]
      calc ∏ y : Fin N, (if y = x then pauliMat α (a y) (bmFlip x a y)
              else if a y = bmFlip x a y then 1 else 0)
          = ∏ y : Fin N, (if y = x then pauliMat α (a x) (1 - a x) else 1) := by
            apply Finset.prod_congr rfl; intro y _
            by_cases hyx : y = x
            · subst hyx; simp [bmFlip]
            · simp [hyx, bmFlip, Function.update_of_ne hyx]
        _ = pauliMat α (a x) (1 - a x) := by rw [Finset.prod_ite_eq']; simp
    · rw [if_neg hab]
      obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin N, b y₀ ≠ bmFlip x a y₀ := by
        by_contra h; push Not at h; exact hab (funext h)
      apply Finset.prod_eq_zero (Finset.mem_univ y₀)
      by_cases hyx : y₀ = x
      · subst hyx; rw [if_pos rfl]
        simp only [bmFlip, Function.update_self] at hy₀
        generalize ha : a y₀ = ay at hy₀ ⊢; generalize hb : b y₀ = by_ at hy₀ ⊢
        rcases hα with rfl | rfl <;> fin_cases ay <;> fin_cases by_ <;>
          first | exact absurd rfl hy₀ | simp [pauliMat]
      · rw [if_neg hyx]
        simp only [bmFlip, Function.update_of_ne hyx] at hy₀
        rw [if_neg (Ne.symm hy₀)]
  simp only [h1]
  rw [Finset.sum_eq_single (bmFlip x s)]
  · simp only [↓reduceIte]
    have hflip_eq : (t = bmFlip x (bmFlip x s)) ↔ (s = t) := by
      rw [bmFlip_bmFlip]; exact eq_comm
    have hmul_one : pauliMat α (s x) (1 - s x) * pauliMat α (bmFlip x s x) (1 - bmFlip x s x) = 1 := by
      simp only [bmFlip, Function.update_self]
      rcases hα with rfl | rfl <;> generalize hb : s x = b <;> fin_cases b <;> simp [pauliMat]
    by_cases hst : s = t
    · rw [if_pos (hflip_eq.mpr hst), if_pos hst]
      calc pauliMat α (s x) (1 - s x) * d (bmFlip x s) *
            pauliMat α (bmFlip x s x) (1 - bmFlip x s x)
          = (pauliMat α (s x) (1 - s x) *
            pauliMat α (bmFlip x s x) (1 - bmFlip x s x)) * d (bmFlip x s) := by ring
        _ = d (bmFlip x s) := by rw [hmul_one, one_mul]
    · rw [if_neg (fun h ↦ hst (hflip_eq.mp h)), if_neg hst, mul_zero]
  · intro u _ hus; rw [if_neg hus, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Exact Hilbert–Schmidt single-site size formula for any real diagonal operator
`M = Matrix.diagonal (fun s ↦ (d s : ℂ))`. -/
lemma hsInner_siteSizeOp_real_diagonal {N : ℕ} (x : Fin N) (d : QubitIdx N → ℝ) :
    let M : QubitOp N := Matrix.diagonal (fun s ↦ (d s : ℂ))
    (hsInner M (siteSizeOp x M)).re =
      (1 / 2 : ℝ) * ∑ s : QubitIdx N, (d s ^ 2 - d s * d (bmFlip x s)) := by
  intro M
  have hMh : Mᴴ = M := by
    ext i j
    simp only [M, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  have hsite : siteSizeOp x M =
      ((1 / 2 : ℂ)) • (M - Matrix.diagonal (fun s ↦ (d (bmFlip x s) : ℂ))) := by
    rw [siteSizeOp_eq_three_avg, Fin.sum_univ_three]
    change (1 / 4 : ℂ) • ((M - pauliSite x 1 * M * pauliSite x 1) +
      (M - pauliSite x 2 * M * pauliSite x 2) +
      (M - pauliSite x 3 * M * pauliSite x 3)) = _
    rw [pauliSite_conj_diagonal_XY x 1 (Or.inl rfl),
        pauliSite_conj_diagonal_XY x 2 (Or.inr rfl),
        pauliSite_conj_diagonal_Z x]
    ext s t
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  unfold hsInner
  rw [hMh, hsite, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sub]
  have hM2 : M * M = Matrix.diagonal (fun s ↦ ((d s ^ 2 : ℝ) : ℂ)) := by
    dsimp only [M]; rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext s; push_cast; ring
  have hMflip : M * Matrix.diagonal (fun s ↦ (d (bmFlip x s) : ℂ)) =
      Matrix.diagonal (fun s ↦ ((d s * d (bmFlip x s) : ℝ) : ℂ)) := by
    dsimp only [M]; rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext s; push_cast; rfl
  rw [hM2, hMflip, Matrix.trace_sub, Matrix.trace_diagonal, Matrix.trace_diagonal,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← Finset.sum_sub_distrib]

/-- Non-negativity of `(hsInner M (siteSizeOp x M)).re` for any real diagonal operator `M`. -/
lemma hsInner_siteSizeOp_real_diagonal_nonneg {N : ℕ} (x : Fin N) (d : QubitIdx N → ℝ) :
    0 ≤ (hsInner (Matrix.diagonal (fun s ↦ (d s : ℂ)))
      (siteSizeOp x (Matrix.diagonal (fun s ↦ (d s : ℂ))))).re := by
  rw [hsInner_siteSizeOp_real_diagonal]
  have hflip_sum : ∑ s : QubitIdx N, d (bmFlip x s) ^ 2 = ∑ s : QubitIdx N, d s ^ 2 :=
    Fintype.sum_equiv (Function.Involutive.toPerm (bmFlip x) (bmFlip_bmFlip x)) _ _ fun _ ↦ rfl
  have hsq : 0 ≤ ∑ s : QubitIdx N, (d s - d (bmFlip x s)) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hexp : ∑ s : QubitIdx N, (d s - d (bmFlip x s)) ^ 2 =
      2 * ∑ s : QubitIdx N, (d s ^ 2 - d s * d (bmFlip x s)) := by
    have h1 : ∀ s, (d s - d (bmFlip x s)) ^ 2 =
        d s ^ 2 + d (bmFlip x s) ^ 2 - 2 * (d s * d (bmFlip x s)) := fun s ↦ by ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  linarith

/-- Normalized 1-local Hermitian witness `A = (3 - ε)^{-1/2} (1 + Z_{x₀})`. -/
noncomputable def bimodalWitnessOp {N : ℕ} (x₀ : Fin N) (ε : ℝ) : QubitOp N :=
  (((Real.sqrt (3 - ε))⁻¹ : ℝ) : ℂ) • ((1 : QubitOp N) + pauliSite x₀ 3)

lemma bimodalWitnessOp_mem_filtration {N : ℕ} (x₀ : Fin N) (ε : ℝ) :
    bimodalWitnessOp x₀ ε ∈ filtrationSubmodule N 1 := by
  unfold bimodalWitnessOp
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · exact Submodule.subset_span ⟨0, by simp [stringWeight], by
      ext s t
      simp only [pauliString, kronOp, Matrix.of_apply, Matrix.one_apply]
      by_cases h : s = t
      · subst h; rw [if_pos rfl]; symm; apply Finset.prod_eq_one; intro y _; simp [pauliMat]
      · rw [if_neg h]
        obtain ⟨y₀, hy₀⟩ : ∃ y₀, s y₀ ≠ t y₀ := by by_contra h0; push Not at h0; exact h (funext h0)
        symm; apply Finset.prod_eq_zero (Finset.mem_univ y₀)
        generalize ha : s y₀ = sy at hy₀ ⊢; generalize hb : t y₀ = ty at hy₀ ⊢
        fin_cases sy <;> fin_cases ty <;> first | exact absurd rfl hy₀ | simp [pauliMat]⟩
  · refine Submodule.subset_span ⟨Function.update 0 x₀ 3, ?_, ?_⟩
    · have hle : (Finset.univ.filter fun y : Fin N ↦ Function.update (0 : Fin N → Fin 4) x₀ 3 y ≠ 0).card ≤
          ({x₀} : Finset (Fin N)).card := by
        apply Finset.card_le_card; intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [Finset.mem_singleton]
        by_contra hne; exact hy (by simp [Function.update_of_ne hne])
      simpa [stringWeight] using hle
    · rfl

private lemma one_add_pauliSiteZ_eq_diagonal {N : ℕ} (x₀ : Fin N) :
    (1 : QubitOp N) + pauliSite x₀ 3 =
      Matrix.diagonal (fun s : QubitIdx N ↦ if s x₀ = 0 then (2 : ℂ) else 0) := by
  ext s t
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply, pauliSite_entry]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl, if_pos rfl]
    have hprod : (∏ y : Fin N, if y = x₀ then pauliMat 3 (s y) (s y) else if s y = s y then 1 else 0) =
        pauliMat 3 (s x₀) (s x₀) := by
      calc ∏ y : Fin N, (if y = x₀ then pauliMat 3 (s y) (s y) else if s y = s y then 1 else 0)
          = ∏ y : Fin N, (if y = x₀ then pauliMat 3 (s y) (s y) else 1) := by
            apply Finset.prod_congr rfl; intro y _; by_cases hy : y = x₀ <;> simp [hy]
        _ = pauliMat 3 (s x₀) (s x₀) := by rw [Finset.prod_ite_eq']; simp
    rw [hprod]
    generalize hb : s x₀ = b; fin_cases b <;> simp [pauliMat] <;> norm_num
  · rw [if_neg hst, if_neg hst, zero_add]
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, s y₀ ≠ t y₀ := by by_contra h0; push Not at h0; exact hst (funext h0)
    apply Finset.prod_eq_zero (Finset.mem_univ y₀)
    by_cases hyx : y₀ = x₀
    · subst hyx; rw [if_pos rfl]
      generalize ha : s y₀ = sy at hy₀ ⊢; generalize hb : t y₀ = ty at hy₀ ⊢
      fin_cases sy <;> fin_cases ty <;> first | exact absurd rfl hy₀ | simp [pauliMat]
    · rw [if_neg hyx, if_neg hy₀]

/-- Exact Wightman normalization:
`gibbsWightmanNormSq (bimodalPerturbedGibbs N hε0 hε1) (bimodalWitnessOp x₀ ε) = 1`. -/
lemma bimodalWitnessOp_wightmanNormSq {N : ℕ} (hN : 1 ≤ N) (x₀ : Fin N)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gibbsWightmanNormSq (bimodalPerturbedGibbs N hε0 hε1) (bimodalWitnessOp x₀ ε) = 1 := by
  let G := bimodalPerturbedGibbs N hε0 hε1
  have h3m : 0 < 3 - ε := by linarith
  have hA_diag : bimodalWitnessOp x₀ ε =
      Matrix.diagonal (fun s : QubitIdx N ↦
        ((if s x₀ = 0 then 2 / Real.sqrt (3 - ε) else 0 : ℝ) : ℂ)) := by
    unfold bimodalWitnessOp
    rw [one_add_pauliSiteZ_eq_diagonal]
    ext s t
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp [div_eq_inv_mul]
  have hjA : jBeta G.ρQuarter (bimodalWitnessOp x₀ ε) =
      Matrix.diagonal (fun s : QubitIdx N ↦
        ((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℂ)) := by
    unfold jBeta
    rw [hA_diag]
    dsimp only [G, bimodalPerturbedGibbs]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext s
    split_ifs
    · have hsq : Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) *
          Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) =
          Real.sqrt (bimodalPerturbedProb N ε s) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      calc Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) * (2 / Real.sqrt (3 - ε)) *
            Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s))
          = (2 / Real.sqrt (3 - ε)) * (Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) *
              Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s))) := by ring
        _ = (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) := by rw [hsq]
    · simp
  have hiso := (prop_2_2_lanczos_invariance G 0 (by simp)).1 (bimodalWitnessOp x₀ ε) (bimodalWitnessOp x₀ ε)
  unfold gibbsWightmanNormSq
  rw [hiso, hjA]
  unfold hsInner
  have hdiag_h : (Matrix.diagonal (fun s : QubitIdx N ↦
      ((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℂ)))ᴴ =
      Matrix.diagonal (fun s : QubitIdx N ↦
      ((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℂ)) := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  rw [hdiag_h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have hcast_eq : (∑ s : QubitIdx N,
      ((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℂ) *
      ((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℂ)) =
      ∑ s : QubitIdx N,
      (((if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) *
        (if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0 : ℝ) : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl; intro s _; push_cast; rfl
  have hhalf_card : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card = 2 ^ (N - 1) := by
    have hsplit : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card +
        (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ ≠ 0)).card = 2 ^ N := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
    have hbij : (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0)).card =
        (Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ ≠ 0)).card := by
      refine Finset.card_bij (fun s _ ↦ bmFlip x₀ s) ?_ ?_ ?_
      · intro s hs
        have h0 : s x₀ = 0 := (Finset.mem_filter.mp hs).2
        simp [bmFlip, h0]
      · intro s₁ _ s₂ _ h
        have := congrArg (bmFlip x₀) h
        rwa [bmFlip_bmFlip, bmFlip_bmFlip] at this
      · intro t ht
        have hne : t x₀ ≠ 0 := (Finset.mem_filter.mp ht).2
        refine ⟨bmFlip x₀ t, ?_, bmFlip_bmFlip x₀ t⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, bmFlip, Function.update_self]
        generalize hb : t x₀ = b; rw [hb] at hne; fin_cases b <;> simp_all
    have h2N : 2 ^ N = 2 * 2 ^ (N - 1) := by
      conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
      ring
    omega
  have hprob_half : ∑ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0),
      bimodalPerturbedProb N ε s = (3 - ε) / 4 := by
    unfold bimodalPerturbedProb
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      if_pos (by simp [allZeroIdx]), Finset.sum_const, hhalf_card, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (2 : ℝ) ^ (N + 1) = 4 * (2 : ℝ) ^ (N - 1) := by
      have : N + 1 = (N - 1) + 2 := by omega
      rw [this, pow_add]; norm_num; ring
    rw [hpow]
    have h2pos : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
    field_simp [h2pos]
    ring
  rw [hcast_eq, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hsum_eq : (∑ s : QubitIdx N,
      (if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0) *
      (if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0)) =
      (4 / (3 - ε)) * ∑ s ∈ Finset.univ.filter (fun s : QubitIdx N ↦ s x₀ = 0),
        bimodalPerturbedProb N ε s := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro s _
    split_ifs
    · rw [show (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) *
          ((2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s)) =
          (2 / Real.sqrt (3 - ε)) ^ 2 * (Real.sqrt (bimodalPerturbedProb N ε s) *
            Real.sqrt (bimodalPerturbedProb N ε s)) by ring,
        div_pow, Real.sq_sqrt h3m.le,
        Real.mul_self_sqrt (bimodalPerturbedProb_pos hε0 hε1 s).le]
      norm_num
    · ring
  rw [hsum_eq, hprob_half]
  field_simp [h3m.ne']

/-- **Quantitative Lower Bound on `mssThermalSize` for Full-Rank `ρ_ε`**:
For `N ≥ 4` and `ε ∈ (0, 1/2]`:
`mssThermalSize (bimodalPerturbedGibbs N hε0 hε1) (bimodalWitnessOp x₀ ε) ≥ (N - 1) / 96 - 1 / 2`. -/
theorem bimodalPerturbed_mssThermalSize_lower {N : ℕ} (hN : 4 ≤ N) (x₀ : Fin N)
    {ε : ℝ} (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2) :
    ((N : ℝ) - 1) / 96 - 1 / 2 ≤
      mssThermalSize (bimodalPerturbedGibbs N hε0 (by linarith)) (bimodalWitnessOp x₀ ε) := by
  have hε1 : ε < 1 := by linarith
  let G := bimodalPerturbedGibbs N hε0 hε1
  have h3m : 0 < 3 - ε := by linarith
  let d₀ : QubitIdx N → ℝ := fun s ↦ Real.sqrt (bimodalPerturbedProb N ε s)
  let dA : QubitIdx N → ℝ := fun s ↦
    if s x₀ = 0 then (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) else 0
  have hjA : jBeta G.ρQuarter (bimodalWitnessOp x₀ ε) =
      Matrix.diagonal (fun s : QubitIdx N ↦ (dA s : ℂ)) := by
    unfold jBeta bimodalWitnessOp
    rw [one_add_pauliSiteZ_eq_diagonal]
    dsimp only [G, bimodalPerturbedGibbs]
    have hsmul : (((Real.sqrt (3 - ε))⁻¹ : ℝ) : ℂ) •
        Matrix.diagonal (fun s : QubitIdx N ↦ if s x₀ = 0 then (2 : ℂ) else 0) =
        Matrix.diagonal (fun s : QubitIdx N ↦ ((if s x₀ = 0 then 2 / Real.sqrt (3 - ε) else 0 : ℝ) : ℂ)) := by
      ext s t; simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
      split_ifs <;> simp [div_eq_inv_mul]
    rw [hsmul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext s
    dsimp only [dA]
    split_ifs
    · have hsq : Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) *
          Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) =
          Real.sqrt (bimodalPerturbedProb N ε s) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      calc Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) * (2 / Real.sqrt (3 - ε)) *
            Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s))
          = (2 / Real.sqrt (3 - ε)) * (Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s)) *
              Real.sqrt (Real.sqrt (bimodalPerturbedProb N ε s))) := by ring
        _ = (2 / Real.sqrt (3 - ε)) * Real.sqrt (bimodalPerturbedProb N ε s) := by rw [hsq]
    · simp
  have htotal_split : ∀ M : QubitOp N,
      (hsInner M (totalSizeOp M)).re = ∑ x : Fin N, (hsInner M (siteSizeOp x M)).re := by
    intro M
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  unfold mssThermalSize
  rw [htotal_split, htotal_split, hjA, ← Finset.sum_sub_distrib]
  let a := bimodalPerturbedProb N ε (allZeroIdx N)
  let b := (1 + ε) / (2 ^ (N + 1) : ℝ)
  have hsite_ρ : ∀ x : Fin N,
      (hsInner G.ρHalf (siteSizeOp x G.ρHalf)).re = (1 / 2 : ℝ) * (Real.sqrt a - Real.sqrt b) ^ 2 := by
    intro x
    change (hsInner (Matrix.diagonal (fun s ↦ (d₀ s : ℂ)))
      (siteSizeOp x (Matrix.diagonal (fun s ↦ (d₀ s : ℂ))))).re = _
    rw [hsInner_siteSizeOp_real_diagonal]
    have hpair : {allZeroIdx N, bmFlip x (allZeroIdx N)} ⊆ (Finset.univ : Finset (QubitIdx N)) :=
      Finset.subset_univ _
    rw [← Finset.sum_subset hpair]
    · rw [Finset.sum_pair (bmFlip_ne_self x (allZeroIdx N)).symm, bmFlip_bmFlip]
      have hd_zero : d₀ (allZeroIdx N) = Real.sqrt a := rfl
      have hd_flip : d₀ (bmFlip x (allZeroIdx N)) = Real.sqrt b := by
        dsimp only [d₀, bimodalPerturbedProb, b]
        rw [if_neg (bmFlip_ne_self x (allZeroIdx N)), mul_zero, zero_add]
      rw [hd_zero, hd_flip]; ring
    · intro s _ hnot
      have hs0 : s ≠ allZeroIdx N := fun h ↦ hnot (by simp [h])
      have hs1 : bmFlip x s ≠ allZeroIdx N := fun h ↦ by
        apply hnot
        have : s = bmFlip x (allZeroIdx N) := by rw [← h, bmFlip_bmFlip]
        simp [this]
      have h1 : d₀ s = Real.sqrt b := by
        dsimp only [d₀, bimodalPerturbedProb, b]; rw [if_neg hs0, mul_zero, zero_add]
      have h2 : d₀ (bmFlip x s) = Real.sqrt b := by
        dsimp only [d₀, bimodalPerturbedProb, b]; rw [if_neg hs1, mul_zero, zero_add]
      rw [h1, h2]; ring
  have hsite_A_ne : ∀ x : Fin N, x ≠ x₀ →
      (hsInner (Matrix.diagonal (fun s ↦ (dA s : ℂ)))
        (siteSizeOp x (Matrix.diagonal (fun s ↦ (dA s : ℂ))))).re =
      (4 / (3 - ε)) * ((1 / 2 : ℝ) * (Real.sqrt a - Real.sqrt b) ^ 2) := by
    intro x hne
    rw [hsInner_siteSizeOp_real_diagonal]
    have hpair : {allZeroIdx N, bmFlip x (allZeroIdx N)} ⊆ (Finset.univ : Finset (QubitIdx N)) :=
      Finset.subset_univ _
    rw [← Finset.sum_subset hpair]
    · rw [Finset.sum_pair (bmFlip_ne_self x (allZeroIdx N)).symm, bmFlip_bmFlip]
      have hx0_zero : allZeroIdx N x₀ = 0 := rfl
      have hx0_flip : bmFlip x (allZeroIdx N) x₀ = 0 := by
        simp [bmFlip, Function.update_of_ne hne.symm, allZeroIdx]
      have hdA_zero : dA (allZeroIdx N) = (2 / Real.sqrt (3 - ε)) * Real.sqrt a := by
        dsimp only [dA]; rw [if_pos hx0_zero]
      have hdA_flip : dA (bmFlip x (allZeroIdx N)) = (2 / Real.sqrt (3 - ε)) * Real.sqrt b := by
        dsimp only [dA, bimodalPerturbedProb, b]
        rw [if_pos hx0_flip, if_neg (bmFlip_ne_self x (allZeroIdx N)), mul_zero, zero_add]
      rw [hdA_zero, hdA_flip]
      have hsq : (2 / Real.sqrt (3 - ε)) ^ 2 = 4 / (3 - ε) := by
        rw [div_pow, Real.sq_sqrt h3m.le]; norm_num
      nlinarith [hsq]
    · intro s _ hnot
      have hs0 : s ≠ allZeroIdx N := fun h ↦ hnot (by simp [h])
      have hs1 : bmFlip x s ≠ allZeroIdx N := fun h ↦ by
        apply hnot
        have : s = bmFlip x (allZeroIdx N) := by rw [← h, bmFlip_bmFlip]
        simp [this]
      have hsame : bmFlip x s x₀ = s x₀ := by simp [bmFlip, Function.update_of_ne hne.symm]
      dsimp only [dA]
      rw [hsame]
      split_ifs
      · have h1 : bimodalPerturbedProb N ε s = b := by
          unfold bimodalPerturbedProb; rw [if_neg hs0, mul_zero, zero_add]
        have h2 : bimodalPerturbedProb N ε (bmFlip x s) = b := by
          unfold bimodalPerturbedProb; rw [if_neg hs1, mul_zero, zero_add]
        rw [h1, h2]; ring
      · ring
  have ha_ge : (1 / 4 : ℝ) ≤ a := by
    dsimp only [a, bimodalPerturbedProb]
    rw [if_pos rfl]
    have hb_pos : 0 < (1 + ε) / (2 ^ (N + 1) : ℝ) := by positivity
    linarith
  have hsqa_ge : (1 / 2 : ℝ) ≤ Real.sqrt a := by
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by norm_num
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt ha_ge
  have hb_le : b ≤ 1 / 16 := by
    dsimp only [b]
    have h2pow : (32 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      have h5 : 5 ≤ N + 1 := by omega
      calc (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
        _ ≤ (2 : ℝ) ^ (N + 1) := pow_le_pow_right₀ (by norm_num) h5
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsqb_le : Real.sqrt b ≤ 1 / 4 := by
    calc Real.sqrt b ≤ Real.sqrt (1 / 16) := Real.sqrt_le_sqrt hb_le
      _ = 1 / 4 := by norm_num
  have hgap_sq : (1 / 16 : ℝ) ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by nlinarith
  have hcoeff_ge : (1 / 3 : ℝ) ≤ 4 / (3 - ε) - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ h3m]; linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  have hx0_lb : -(1 / 2 : ℝ) ≤
      (hsInner (Matrix.diagonal (fun s ↦ (dA s : ℂ)))
        (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (dA s : ℂ))))).re -
      (hsInner G.ρHalf (siteSizeOp x₀ G.ρHalf)).re := by
    have hnn := hsInner_siteSizeOp_real_diagonal_nonneg x₀ dA
    rw [hsite_ρ x₀]
    have ha_le : a ≤ 1 := by
      have hle := Finset.single_le_sum (f := bimodalPerturbedProb N ε)
        (fun s _ ↦ (bimodalPerturbedProb_pos hε0 hε1 s).le) (Finset.mem_univ (allZeroIdx N))
      rw [bimodalPerturbedProb_sum] at hle; exact hle
    have hsqa_le : Real.sqrt a ≤ 1 := by
      calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha_le
        _ = 1 := Real.sqrt_one
    have hsqb_nn : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
    have hdiff_le : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hne_lb : ((N : ℝ) - 1) / 96 ≤
      ∑ x ∈ Finset.univ.erase x₀,
        ((hsInner (Matrix.diagonal (fun s ↦ (dA s : ℂ)))
          (siteSizeOp x (Matrix.diagonal (fun s ↦ (dA s : ℂ))))).re -
         (hsInner G.ρHalf (siteSizeOp x G.ρHalf)).re) := by
    calc ((N : ℝ) - 1) / 96
        = ((Finset.univ.erase x₀).card : ℝ) * (1 / 96 : ℝ) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, Fintype.card_fin,
            Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]; ring
      _ = ∑ _x ∈ Finset.univ.erase x₀, (1 / 96 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Finset.univ.erase x₀,
            ((hsInner (Matrix.diagonal (fun s ↦ (dA s : ℂ)))
              (siteSizeOp x (Matrix.diagonal (fun s ↦ (dA s : ℂ))))).re -
             (hsInner G.ρHalf (siteSizeOp x G.ρHalf)).re) := by
          apply Finset.sum_le_sum; intro x hx
          have hne : x ≠ x₀ := (Finset.mem_erase.mp hx).1
          rw [hsite_A_ne x hne, hsite_ρ x]
          nlinarith
  linarith

/-- Elementary Hilbert–Schmidt bound: for any Hermitian unitary `P` (`Pᴴ = P`, `P * P = 1`),
`Re ⟨M, M - P M P⟩_HS ≤ 2 Re ⟨M, M⟩_HS`. -/
private lemma hsInner_sub_conj_le_two {N : ℕ} (P M : QubitOp N)
    (hPh : Pᴴ = P) (hP2 : P * P = 1) :
    (hsInner M (M - P * M * P)).re ≤ 2 * (hsInner M M).re := by
  have hnn : 0 ≤ (hsInner (M + P * M * P) (M + P * M * P)).re := by
    have hgen : ∀ K : QubitOp N, 0 ≤ (hsInner K K).re := by
      intro K; unfold hsInner
      have htr : (Kᴴ * K).trace.re = ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖K j i‖ ^ 2 := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.re_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [htr]
      exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    exact hgen (M + P * M * P)
  have hPMP_norm : hsInner (P * M * P) (P * M * P) = hsInner M M := by
    unfold hsInner
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh]
    calc (P * Mᴴ * P * (P * M * P)).trace
        = (P * Mᴴ * (P * P) * M * P).trace := by simp only [Matrix.mul_assoc]
      _ = (P * Mᴴ * M * P).trace := by rw [hP2, Matrix.mul_one]
      _ = (P * P * Mᴴ * M).trace := by
          rw [Matrix.trace_mul_comm (P * Mᴴ * M) P]; simp only [Matrix.mul_assoc]
      _ = (Mᴴ * M).trace := by rw [hP2, Matrix.one_mul]
  have hcross_eq : (hsInner (P * M * P) M).re = (hsInner M (P * M * P)).re := by
    unfold hsInner
    have h1 : ((P * M * P)ᴴ * M).trace = star ((Mᴴ * (P * M * P)).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [h1, Complex.star_def, Complex.conj_re]
  have hexp : hsInner (M + P * M * P) (M + P * M * P) =
      hsInner M M + hsInner M (P * M * P) + hsInner (P * M * P) M + hsInner (P * M * P) (P * M * P) := by
    unfold hsInner
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
    ring
  rw [hexp, hPMP_norm] at hnn
  simp only [Complex.add_re] at hnn
  have hsub : (hsInner M (M - P * M * P)).re = (hsInner M M).re - (hsInner M (P * M * P)).re := by
    unfold hsInner; rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

/-- Uniform upper bound on `mssThermalSize G B` for unit-norm `B`, giving `BddAbove` for `lambdaMSS`. -/
private lemma mssThermalSize_bddAbove_unit {N : ℕ} (G : GibbsData N) (s : ℕ) :
    BddAbove { r : ℝ | ∃ A ∈ filtrationSubmodule N s,
      gibbsWightmanNormSq G A = 1 ∧ r = mssThermalSize G A } := by
  refine ⟨(3 / 2 : ℝ) * (N : ℝ) + |(hsInner G.ρHalf (totalSizeOp G.ρHalf)).re|, ?_⟩
  rintro r ⟨A, _, hnorm, rfl⟩
  unfold mssThermalSize
  have hM_norm : (hsInner (jBeta G.ρQuarter A) (jBeta G.ρQuarter A)).re = 1 := by
    have hiso := (prop_2_2_lanczos_invariance G 0 (by simp)).1 A A
    unfold gibbsWightmanNormSq at hnorm
    rw [← hiso]; exact hnorm
  have htotal : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re =
      ∑ x : Fin N, (hsInner (jBeta G.ρQuarter A) (siteSizeOp x (jBeta G.ρQuarter A))).re := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  have hle : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re ≤
      (3 / 2 : ℝ) * (N : ℝ) := by
    rw [htotal]
    calc ∑ x : Fin N, (hsInner (jBeta G.ρQuarter A) (siteSizeOp x (jBeta G.ρQuarter A))).re
        ≤ ∑ _x : Fin N, (3 / 2 : ℝ) := by
          apply Finset.sum_le_sum; intro x _
          rw [siteSizeOp_eq_three_avg]
          unfold hsInner
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum]
          rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
            Complex.re_sum]
          have hsum3 : ∑ α : Fin 3,
              ((jBeta G.ρQuarter A)ᴴ *
                (jBeta G.ρQuarter A - pauliSite x α.succ * jBeta G.ρQuarter A * pauliSite x α.succ)).trace.re ≤
              ∑ _α : Fin 3, (2 : ℝ) := by
            apply Finset.sum_le_sum; intro α _
            have h1 := hsInner_sub_conj_le_two (pauliSite x α.succ) (jBeta G.ρQuarter A)
              (pauliSite_herm x α.succ) (pauliSite_sq x α.succ)
            unfold hsInner at h1 hM_norm
            linarith
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum3
          norm_num at hsum3
          linarith
      _ = (3 / 2 : ℝ) * (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith [neg_abs_le (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re]

/-- **Lower Bound on `lambdaMSS (bimodalPerturbedGibbs N hε0 hε1) 1`**:
For every `N ≥ 4` and `ε ∈ (0, 1/2]`:
`((N : ℝ) - 1) / 96 - 1 / 2 ≤ lambdaMSS (bimodalPerturbedGibbs N hε0 hε1) 1`. -/
theorem bimodalPerturbed_lambdaMSS_lower {N : ℕ} (hN : 4 ≤ N)
    {ε : ℝ} (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2) :
    ((N : ℝ) - 1) / 96 - 1 / 2 ≤ lambdaMSS (bimodalPerturbedGibbs N hε0 (by linarith)) 1 := by
  have hε1 : ε < 1 := by linarith
  let G := bimodalPerturbedGibbs N hε0 hε1
  let x₀ : Fin N := ⟨0, by omega⟩
  have hmem : mssThermalSize G (bimodalWitnessOp x₀ ε) ∈
      { r : ℝ | ∃ A ∈ filtrationSubmodule N 1,
        gibbsWightmanNormSq G A = 1 ∧ r = mssThermalSize G A } :=
    ⟨bimodalWitnessOp x₀ ε, bimodalWitnessOp_mem_filtration x₀ ε,
      bimodalWitnessOp_wightmanNormSq (by omega) x₀ hε0 hε1, rfl⟩
  exact le_trans (bimodalPerturbed_mssThermalSize_lower hN x₀ hε0 hε_half)
    (le_csSup (mssThermalSize_bddAbove_unit G 1) hmem)

/-- **Proposition 9.1(2) (Full-Rank Perturbation Direct Violation of Hypothesis (H2))**:
For EVERY `δ ∈ [0, 1)` and ANY constants `C₁, C₂ ≥ 0`, there exists `N₀ ≥ 4` such that for ALL
`N ≥ N₀` and ALL full-rank perturbations `ε ∈ (0, 1/2]`, the full-rank `GibbsData N` state
`G = bimodalPerturbedGibbs N hε0 hε1` (`ρ_ε = (1 - ε) ρ + ε I / 2^N`) directly violates
Hypothesis (H2) in the exact `lambdaMSS` signature of Theorem 1.1(b):
`C₁ * 1 + C₂ * (N : ℝ) ^ δ * (1 : ℝ) ^ (1 - δ) < lambdaMSS G 1`. -/
theorem prop_9_1_part2_full_rank_lambdaMSS_violates_H2 {δ C₁ C₂ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ (N₀ : ℕ) (hN₀ : 4 ≤ N₀), ∀ (N : ℕ) (hN : N₀ ≤ N)
      {ε : ℝ} (hε0 : 0 < ε) (hε_half : ε ≤ 1 / 2),
      C₁ * (1 : ℝ) + C₂ * (N : ℝ) ^ δ * (1 : ℝ) ^ (1 - δ) <
        lambdaMSS (bimodalPerturbedGibbs N hε0 (by linarith)) 1 := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 - δ)) atTop atTop :=
    (tendsto_rpow_atTop h1mδ).comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ δ / (N : ℝ)) atTop (nhds 0) := by
    have heq : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ δ / (N : ℝ) = ((N : ℝ) ^ (1 - δ))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      rw [← Real.rpow_neg hNpos.le, neg_sub, Real.rpow_sub hNpos, Real.rpow_one]
    exact (tendsto_inv_atTop_zero.comp hpow).congr' (heq.mono fun _ h ↦ h.symm)
  have hratio : Tendsto (fun N : ℕ ↦ (C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ (C₁ + 1) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ ↦ C₂ * ((N : ℝ) ^ δ / (N : ℝ))) atTop (nhds (C₂ * 0)) :=
      tendsto_const_nhds.mul hdiv
    rw [mul_zero] at h2
    simpa using h1.add h2
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hratio) (1 / 192) (by norm_num)
  refine ⟨max N₁ 4, le_max_right _ _, fun N hN ε hε0 hε_half ↦ ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlt := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  have hmul : ((C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ))) * (N : ℝ) < (1 / 192 : ℝ) * (N : ℝ) :=
    mul_lt_mul_of_pos_right hlt hNpos
  have hlhs : ((C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ))) * (N : ℝ) =
      C₁ + 1 + C₂ * (N : ℝ) ^ δ := by
    field_simp [hNpos.ne']
  rw [hlhs] at hmul
  have hlb := bimodalPerturbed_lambdaMSS_lower hN4 hε0 hε_half
  rw [Real.one_rpow, mul_one, mul_one]
  linarith

end FullRankBimodalGibbs

end KrylovChaos
