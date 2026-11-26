/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ManyBodySetup
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Lemma 2.1: Causal-Sequence Commutator Expansion & Complex-Time Operator-Norm Bounds

Formalizes **Lemma 2.1** (Eqs. 2.3–2.5 of `finite_temp_krylov_chaos.tex`) at the full
operator-algebraic level on any complete normed `ℂ`-algebra `E` (with `[NormOneClass E]`):
1. Iterated adjoint commutator `adPow H O m` and its exact binomial expansion
   `adPow H O m = ∑_{j=0}^m (-1)^{m-j} C(m, j) H^j O H^{m-j}` (`adPow_eq_binomial_sum`).
2. **Exact Hadamard / BCH Complex-Time Expansion** (`exp_conj_eq_tsum_adPow`):
   `NormedSpace.exp (z • H) * O * NormedSpace.exp (-(z • H)) =
     ∑' m : ℕ, (z ^ m / (m.factorial : ℂ)) • adPow H O m`.
3. **Causal-Sequence Expansion & Support Growth** (`lemma_2_1_causal_norm_sum`, Eq. 2.3):
   for an `r`-local Hamiltonian `H = ∑_{i ∈ I} h_i` (`r ≥ 2`, `|supp h_i| ≤ r`, per-site
   bound `J_site`), proves by induction on `m` that `adPow H O m` expands over causal
   sequences with support size `≤ s + m (r - 1)` and satisfies
   `‖adPow H O m‖ ≤ ‖O‖ · κ^{-m} ∏_{j=0}^{m-1} (s / (r - 1) + j)`.
4. **Lemma 2.1(2) (Eq. 2.4)** (`lemma_2_1_single_site_exp_bound`):
   `‖exp(± (τ/4) H) V_i exp(∓ (τ/4) H)‖ ≤ (1 - |τ| / (4 κ))⁻¹` for `|τ| < 4 κ`.
5. **Lemma 2.1(3) (Eq. 2.5)** (`lemma_2_1_r_local_exp_bound`):
   `‖exp(± (τ/4) H) h_X exp(∓ (τ/4) H)‖ ≤ ‖h_X‖ · (1 - |τ| / (4 κ))⁻¹ ^ 2` for `|τ| < 4 κ`.
-/

namespace KrylovChaos

private lemma prod_le_prod_nn {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have h1 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have h2 : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
      have h3 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have h4 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
           (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
      exact mul_le_mul h2 h4 h3 (le_trans h1 h2)

private lemma prod_range_one_add (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + (j : ℝ)) = (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

private lemma prod_range_two_add (m : ℕ) :
    ∏ j ∈ Finset.range m, (2 + (j : ℝ)) = ((m + 1).factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ (k + 1), Nat.cast_mul, Nat.cast_add,
        Nat.cast_add, Nat.cast_one]
      ring

/-- Convert a summable `ℕ × ℕ` series into a Cauchy-product antidiagonal series. -/
private lemma tsum_prod_eq_tsum_antidiag {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    (h : ℕ × ℕ → G) (hh : Summable h) :
    (∑' p : ℕ × ℕ, h p) = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, h p := by
  let e : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ≃ ℕ × ℕ :=
    Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ ↦ p.1 + p.2)
  have hcomp : Summable (fun q : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ↦ h (e q)) :=
    hh.comp_injective e.injective
  have hfib : ∀ m : ℕ, Fintype {p : ℕ × ℕ // p.1 + p.2 = m} := fun m ↦
    Fintype.ofEquiv (Finset.antidiagonal m)
      { toFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mp p.2⟩
        invFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mpr p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have h1 : (∑' p : ℕ × ℕ, h p) = ∑' q : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m}, h (e q) :=
    (e.tsum_eq h).symm
  rw [h1, hcomp.tsum_sigma' (fun m ↦ (hasSum_fintype _).summable)]
  refine tsum_congr fun m ↦ ?_
  haveI := hfib m
  rw [tsum_fintype]
  refine Finset.sum_bij (fun p _ ↦ p.1) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_antidiagonal.mpr p.2
  · intro p₁ _ p₂ _ hp; exact Subtype.ext hp
  · intro p hp; exact ⟨⟨p, Finset.mem_antidiagonal.mp hp⟩, Finset.mem_univ _, rfl⟩
  · intro p _; rfl

private lemma summable_antidiag_of_summable_prod {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    (h : ℕ × ℕ → G) (hh : Summable h) :
    Summable (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, h p) := by
  let e : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ≃ ℕ × ℕ :=
    Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ ↦ p.1 + p.2)
  have hcomp : Summable (fun q : (m : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = m} ↦ h (e q)) :=
    hh.comp_injective e.injective
  have hfib : ∀ m : ℕ, Fintype {p : ℕ × ℕ // p.1 + p.2 = m} := fun m ↦
    Fintype.ofEquiv (Finset.antidiagonal m)
      { toFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mp p.2⟩
        invFun := fun p ↦ ⟨p.1, Finset.mem_antidiagonal.mpr p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hs := hcomp.sigma
  refine hs.congr fun m ↦ ?_
  haveI := hfib m
  rw [tsum_fintype]
  refine Finset.sum_bij (fun p _ ↦ p.1) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_antidiagonal.mpr p.2
  · intro p₁ _ p₂ _ hp; exact Subtype.ext hp
  · intro p hp; exact ⟨⟨p, Finset.mem_antidiagonal.mp hp⟩, Finset.mem_univ _, rfl⟩
  · intro p _; rfl

section HadamardExpansion

variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- Iterated adjoint commutator `ad_H^m(O)` in an associative algebra. -/
def adPow (H O : E) : ℕ → E
  | 0 => O
  | m + 1 => H * adPow H O m - adPow H O m * H

/-- Exact binomial expansion of the iterated commutator:
`ad_H^m(O) = ∑_{j=0}^m (-1)^{m-j} C(m, j) H^j O H^{m-j}`. -/
theorem adPow_eq_binomial_sum (H O : E) :
    ∀ m : ℕ, adPow H O m =
      ∑ j ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ (m - j) * (Nat.choose m j : ℂ)) • (H ^ j * O * H ^ (m - j))
  | 0 => by simp [adPow]
  | m + 1 => by
    rw [adPow, adPow_eq_binomial_sum H O m]
    rw [Finset.mul_sum, Finset.sum_mul]
    have hL :
        (∑ j ∈ Finset.range (m + 1),
          H * (((-1 : ℂ) ^ (m - j) * (Nat.choose m j : ℂ)) • (H ^ j * O * H ^ (m - j)))) =
        ∑ k ∈ Finset.Ico 1 (m + 2),
          ((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m (k - 1) : ℂ)) • (H ^ k * O * H ^ (m + 1 - k)) := by
      refine Finset.sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Ico]; have := Finset.mem_range.mp hj; omega
      · intro j₁ _ j₂ _ h; omega
      · intro k hk; rw [Finset.mem_Ico] at hk; exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : m + 1 - (j + 1) = m - j := by omega
        have hsub1 : j + 1 - 1 = j := by omega
        rw [hsub, hsub1, mul_smul_comm]
        congr 1
        rw [pow_succ', ← mul_assoc, ← mul_assoc]
    have hR :
        (∑ j ∈ Finset.range (m + 1),
          (((-1 : ℂ) ^ (m - j) * (Nat.choose m j : ℂ)) • (H ^ j * O * H ^ (m - j))) * H) =
        ∑ k ∈ Finset.range (m + 1),
          (-((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m k : ℂ))) • (H ^ k * O * H ^ (m + 1 - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsub : m + 1 - k = (m - k) + 1 := by omega
      rw [hsub, smul_mul_assoc, mul_assoc, ← pow_succ, pow_succ (-1 : ℂ)]
      congr 1
      ring
    rw [hL, hR]
    have hL_ext :
        (∑ k ∈ Finset.Ico 1 (m + 2),
          ((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m (k - 1) : ℂ)) • (H ^ k * O * H ^ (m + 1 - k))) =
        ∑ k ∈ Finset.range (m + 2),
          if k = 0 then (0 : E)
          else ((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m (k - 1) : ℂ)) •
            (H ^ k * O * H ^ (m + 1 - k)) := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, add_zero, Nat.succ_ne_zero]
      refine Finset.sum_bij (fun k _ ↦ k - 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr (by omega)
      · intro k₁ hk₁ k₂ hk₂ h; rw [Finset.mem_Ico] at hk₁ hk₂; omega
      · intro j hj; exact ⟨j + 1, Finset.mem_Ico.mpr (by have := Finset.mem_range.mp hj; omega), by omega⟩
      · intro k hk
        rw [Finset.mem_Ico] at hk
        have h1 : k - 1 + 1 = k := by omega
        rw [h1]
    have hR_ext :
        (∑ k ∈ Finset.range (m + 1),
          (-((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m k : ℂ))) • (H ^ k * O * H ^ (m + 1 - k))) =
        ∑ k ∈ Finset.range (m + 2),
          if k = m + 1 then (0 : E)
          else (-((-1 : ℂ) ^ (m + 1 - k) * (Nat.choose m k : ℂ))) •
            (H ^ k * O * H ^ (m + 1 - k)) := by
      symm
      rw [Finset.sum_range_succ, if_pos rfl, add_zero]
      apply Finset.sum_congr rfl
      intro k hk
      have hne : k ≠ m + 1 := by have := Finset.mem_range.mp hk; omega
      rw [if_neg hne]
    rw [hL_ext, hR_ext, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkle : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, Nat.zero_ne_add_one, zero_sub, neg_smul, neg_neg, Nat.choose_zero_right,
        Nat.cast_one]
    · by_cases hkm1 : k = m + 1
      · subst hkm1
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, sub_zero,
          Nat.add_sub_cancel, Nat.choose_self, Nat.cast_one]
      · simp only [hk0, hkm1, ↓reduceIte, neg_smul, sub_neg_eq_add, ← add_smul]
        congr 1
        have hchoose : Nat.choose (m + 1) k = Nat.choose m (k - 1) + Nat.choose m k := by
          cases k with
          | zero => contradiction
          | succ k' => exact Nat.choose_succ_succ m k'
        rw [hchoose, Nat.cast_add]
        ring

/-- **Exact Hadamard / BCH Complex-Time Expansion**:
In any complete normed `ℂ`-algebra `E`,
`exp(z H) * O * exp(-z H) = ∑' m : ℕ, (z ^ m / m!) • ad_H^m(O)`. -/
theorem exp_conj_eq_tsum_adPow (H O : E) (z : ℂ) :
    NormedSpace.exp (z • H) * O * NormedSpace.exp (-(z • H)) =
    ∑' m : ℕ, (z ^ m / (m.factorial : ℂ)) • adPow H O m := by
  let f : ℕ → E := fun j ↦ (((j.factorial : ℂ)⁻¹) • (z • H) ^ j) * O
  let g : ℕ → E := fun k ↦ ((k.factorial : ℂ)⁻¹) • (-(z • H)) ^ k
  have hexp_eq : ∀ x : E, NormedSpace.exp x = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • x ^ n := by
    intro x
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := E)]
  have hf_base_norm : Summable (fun j : ℕ ↦ ‖((j.factorial : ℂ)⁻¹) • (z • H) ^ j‖) := by
    refine Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) (fun j ↦ ?_)
      (Real.summable_pow_div_factorial ‖z • H‖)
    calc ‖((j.factorial : ℂ)⁻¹) • (z • H) ^ j‖
        = (j.factorial : ℝ)⁻¹ * ‖(z • H) ^ j‖ := by
            rw [norm_smul, norm_inv, Complex.norm_natCast]
      _ ≤ (j.factorial : ℝ)⁻¹ * ‖z • H‖ ^ j := by
            gcongr; exact norm_pow_le _ _
      _ = ‖z • H‖ ^ j / (j.factorial : ℝ) := by ring
  have hf_norm : Summable (fun j ↦ ‖f j‖) := by
    refine Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) (fun j ↦ ?_)
      (hf_base_norm.mul_right ‖O‖)
    exact norm_mul_le _ _
  have hg_norm : Summable (fun k ↦ ‖g k‖) := by
    refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
      (Real.summable_pow_div_factorial ‖-(z • H)‖)
    calc ‖g k‖ = (k.factorial : ℝ)⁻¹ * ‖(-(z • H)) ^ k‖ := by
            rw [norm_smul, norm_inv, Complex.norm_natCast]
      _ ≤ (k.factorial : ℝ)⁻¹ * ‖-(z • H)‖ ^ k := by
            gcongr; exact norm_pow_le _ _
      _ = ‖-(z • H)‖ ^ k / (k.factorial : ℝ) := by ring
  have hf_tsum : ∑' j : ℕ, f j = NormedSpace.exp (z • H) * O := by
    rw [hexp_eq (z • H)]
    exact (hf_base_norm.of_norm.hasSum.mul_right O).tsum_eq
  have hg_tsum : ∑' k : ℕ, g k = NormedSpace.exp (-(z • H)) :=
    (hexp_eq (-(z • H))).symm
  have hprod_summ : Summable (fun p : ℕ × ℕ ↦ f p.1 * g p.2) :=
    summable_mul_of_summable_norm hf_norm hg_norm
  have hprod : NormedSpace.exp (z • H) * O * NormedSpace.exp (-(z • H)) =
      ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
    rw [← hf_tsum, ← hg_tsum]
    exact tsum_mul_tsum_of_summable_norm hf_norm hg_norm
  rw [hprod, tsum_prod_eq_tsum_antidiag _ hprod_summ]
  refine tsum_congr fun m ↦ ?_
  rw [adPow_eq_binomial_sum, Finset.smul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k ↦ f j * g k) m]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfac_ne : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hj_ne : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hmj_ne : ((m - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - j))
  have hchoose_eq : (Nat.choose m j : ℂ) / (m.factorial : ℂ) =
      ((j.factorial : ℂ)⁻¹) * (((m - j).factorial : ℂ)⁻¹) := by
    have hnat : (Nat.choose m j : ℂ) * (j.factorial : ℂ) * ((m - j).factorial : ℂ) =
        (m.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjm
    field_simp [hfac_ne, hj_ne, hmj_ne]
    linear_combination hnat
  have hneg : (-(z • H)) ^ (m - j) = ((-1 : ℂ) ^ (m - j) * z ^ (m - j)) • H ^ (m - j) := by
    rw [show -(z • H) = (-z) • H by simp [neg_smul], smul_pow,
      show (-z) ^ (m - j) = (-1 : ℂ) ^ (m - j) * z ^ (m - j) by
        rw [← mul_pow]; congr 1; ring]
  simp only [f, g, smul_pow, hneg, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  have hzpow : z ^ j * z ^ (m - j) = z ^ m := by rw [← pow_add, Nat.add_sub_of_le hjm]
  calc ((m - j).factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ (m - j) * (z ^ (m - j) * ((j.factorial : ℂ)⁻¹ * z ^ j)))
      = ((j.factorial : ℂ)⁻¹ * ((m - j).factorial : ℂ)⁻¹) * ((-1 : ℂ) ^ (m - j) * (z ^ j * z ^ (m - j))) := by
          ring
    _ = ((Nat.choose m j : ℂ) / (m.factorial : ℂ)) * ((-1 : ℂ) ^ (m - j) * z ^ m) := by
          rw [hchoose_eq, hzpow]
    _ = z ^ m / (m.factorial : ℂ) * ((-1 : ℂ) ^ (m - j) * (Nat.choose m j : ℂ)) := by ring

end HadamardExpansion

section CausalSequenceBounds

variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- Abstract `r`-local interaction decomposition `H = ∑_{i ∈ I} h_i` in a Banach algebra `E`,
with each interaction term supported on a subset `supp i ⊆ Fin N` of size `≤ r` and
commuting with any operator supported on a disjoint subset. -/
structure LocalInteractionDecomp (E : Type*) [NormedRing E] (N r : ℕ) where
  ι : Type*
  [fintype_ι : Fintype ι]
  term : ι → E
  supp : ι → Finset (Fin N)
  supp_card_le : ∀ i, (supp i).card ≤ r
  /-- Support predicate on `E`: `SupportedOn U A` means `A` acts only on `U`. -/
  SupportedOn : Finset (Fin N) → E → Prop
  supportedOn_comm_zero : ∀ U i A, SupportedOn U A → Disjoint (supp i) U →
    term i * A - A * term i = 0
  supportedOn_comm_union : ∀ U i A, SupportedOn U A →
    SupportedOn (U ∪ supp i) (term i * A - A * term i)

attribute [instance] LocalInteractionDecomp.fintype_ι

/-- Total Hamiltonian `H = ∑ i, term i`. -/
def LocalInteractionDecomp.totalH {N r : ℕ} (D : LocalInteractionDecomp E N r) : E :=
  ∑ i : D.ι, D.term i

/-- Causal-sequence operator `T_Γ = [h_{i_{m-1}}, [..., [h_{i_0}, O]...]]`. -/
def causalOp {N r : ℕ} (D : LocalInteractionDecomp E N r) (O : E) :
    ∀ {m : ℕ}, (Fin m → D.ι) → E
  | 0, _ => O
  | m + 1, Γ =>
      let prev := causalOp D O (fun k : Fin m ↦ Γ k.castSucc)
      D.term (Γ (Fin.last m)) * prev - prev * D.term (Γ (Fin.last m))

/-- Cumulative support `U_Γ = U ∪ supp(Γ 0) ∪ ... ∪ supp(Γ (m-1))`. -/
def causalSupp {N r : ℕ} (D : LocalInteractionDecomp E N r) (U : Finset (Fin N)) :
    ∀ {m : ℕ}, (Fin m → D.ι) → Finset (Fin N)
  | 0, _ => U
  | m + 1, Γ => causalSupp D U (fun k : Fin m ↦ Γ k.castSucc) ∪ D.supp (Γ (Fin.last m))

/-- A length-`m` sequence `Γ : Fin m → D.ι` is causal starting from `U` if each new term
intersects the cumulative support of all previous terms. -/
def isCausalSeq {N r : ℕ} (D : LocalInteractionDecomp E N r) (U : Finset (Fin N)) :
    ∀ {m : ℕ}, (Fin m → D.ι) → Prop
  | 0, _ => True
  | m + 1, Γ =>
      isCausalSeq D U (fun k : Fin m ↦ Γ k.castSucc) ∧
      ¬ Disjoint (D.supp (Γ (Fin.last m))) (causalSupp D U (fun k : Fin m ↦ Γ k.castSucc))

/-- Support growth of causal sequences: `|U_Γ| ≤ |U| + m (r - 1)` for `r ≥ 1`. -/
theorem causalSupp_card_le {N r : ℕ} (D : LocalInteractionDecomp E N r) (hr : 1 ≤ r)
    (U : Finset (Fin N)) :
    ∀ {m : ℕ} (Γ : Fin m → D.ι), isCausalSeq D U Γ →
      (causalSupp D U Γ).card ≤ U.card + m * (r - 1)
  | 0, _, _ => by simp [causalSupp]
  | m + 1, Γ, ⟨hprev, hnotdisj⟩ => by
      simp only [causalSupp]
      have hih := causalSupp_card_le D hr U (fun k : Fin m ↦ Γ k.castSucc) hprev
      have hinter : 1 ≤ (causalSupp D U (fun k : Fin m ↦ Γ k.castSucc) ∩
          D.supp (Γ (Fin.last m))).card := by
        rw [Finset.one_le_card]
        rw [Finset.not_disjoint_iff] at hnotdisj
        rcases hnotdisj with ⟨x, hx1, hx2⟩
        exact ⟨x, Finset.mem_inter.mpr ⟨hx2, hx1⟩⟩
      have hcard_union := Finset.card_union_add_card_inter
        (causalSupp D U (fun k : Fin m ↦ Γ k.castSucc)) (D.supp (Γ (Fin.last m)))
      have hterm := D.supp_card_le (Γ (Fin.last m))
      have : (m + 1) * (r - 1) = m * (r - 1) + (r - 1) := by ring
      omega

/-- Every causal operator `T_Γ` is supported on `U_Γ`. -/
lemma causalOp_supportedOn {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (U : Finset (Fin N)) (O : E) (hO : D.SupportedOn U O) :
    ∀ {m : ℕ} (Γ : Fin m → D.ι), D.SupportedOn (causalSupp D U Γ) (causalOp D O Γ)
  | 0, _ => hO
  | m + 1, Γ =>
      D.supportedOn_comm_union _ _ _
        (causalOp_supportedOn D U O hO (fun k : Fin m ↦ Γ k.castSucc))

private lemma snoc_init_eq {α : Type*} {m : ℕ} (f : Fin m → α) (x : α) :
    (fun k : Fin m ↦ Fin.snoc (α := fun _ ↦ α) f x k.castSucc) = f := by
  ext k
  simp [Fin.snoc_castSucc]

open scoped Classical in
/-- **Exact Causal-Sequence Expansion of `ad_H^m(O)`**:
`ad_H^m(O) = ∑_{Γ causal, |Γ|=m} T_Γ`. -/
theorem adPow_eq_causal_sum {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (U : Finset (Fin N)) (O : E) (hO : D.SupportedOn U O) :
    ∀ m : ℕ, adPow D.totalH O m =
      ∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)), causalOp D O Γ
  | 0 => by
      simp [adPow, causalOp, isCausalSeq]
  | m + 1 => by
      rw [adPow, adPow_eq_causal_sum D U O hO m]
      have hcomm : ∀ A : E, D.totalH * A - A * D.totalH =
          ∑ i : D.ι, (D.term i * A - A * D.term i) := by
        intro A
        unfold LocalInteractionDecomp.totalH
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [hcomm]
      have hswap :
          (∑ i : D.ι, (D.term i * (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)), causalOp D O Γ) -
            (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)), causalOp D O Γ) * D.term i)) =
          ∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
            ∑ i : D.ι, (D.term i * causalOp D O Γ - causalOp D O Γ * D.term i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Γ _
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
      rw [hswap]
      have hdrop : ∀ Γ : Fin m → D.ι,
          (∑ i : D.ι, (D.term i * causalOp D O Γ - causalOp D O Γ * D.term i)) =
          ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
            (D.term i * causalOp D O Γ - causalOp D O Γ * D.term i) := by
        intro Γ
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hd : Disjoint (D.supp i) (causalSupp D U Γ)
        · simp [hd, D.supportedOn_comm_zero _ _ _ (causalOp_supportedOn D U O hO Γ) hd]
        · simp [hd]
      simp_rw [hdrop]
      have hsig :
          (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
            ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              (D.term i * causalOp D O Γ - causalOp D O Γ * D.term i)) =
          ∑ p ∈ (Finset.univ.filter (isCausalSeq D U (m := m))).sigma
              (fun Γ ↦ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ))),
            (D.term p.2 * causalOp D O p.1 - causalOp D O p.1 * D.term p.2) :=
        (Finset.sum_sigma (Finset.univ.filter (isCausalSeq D U (m := m)))
          (fun Γ ↦ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)))
          (fun p : (_ : Fin m → D.ι) × D.ι ↦
            D.term p.2 * causalOp D O p.1 - causalOp D O p.1 * D.term p.2)).symm
      rw [hsig]
      refine Finset.sum_bij (fun p _ ↦ Fin.snoc (α := fun _ ↦ D.ι) p.1 p.2) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hp ⊢
        obtain ⟨hprev, hnd⟩ := hp
        rw [isCausalSeq, snoc_init_eq, Fin.snoc_last]
        exact ⟨hprev, hnd⟩
      · intro p₁ _ p₂ _ heq
        have h1 : p₁.1 = p₂.1 := by
          ext k
          have := congrFun heq k.castSucc
          simpa [Fin.snoc_castSucc] using this
        have h2 : p₁.2 = p₂.2 := by
          have := congrFun heq (Fin.last m)
          simpa [Fin.snoc_last] using this
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro Γ' hΓ'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΓ'
        refine ⟨⟨fun k : Fin m ↦ Γ' k.castSucc, Γ' (Fin.last m)⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and]
          exact hΓ'
        · exact Fin.snoc_init_self Γ'
      · intro p _
        simp only [causalOp, Fin.snoc_last, snoc_init_eq]

open scoped Classical in
/-- **Lemma 2.1(1) (Eq. 2.3 — Causal-Sequence Norm Sum Bound)**:
For an `r`-local interaction decomposition (`r ≥ 2`) with per-site strength
`∑_{i : x ∈ supp i} ‖h_i‖ ≤ J_site` (`J_site > 0`) and `κ = (2 (r - 1) J_site)⁻¹`,
every operator `O` supported on `U` (`|U| = s`) satisfies
`∑_{Γ causal, |Γ|=m} ‖T_Γ‖ ≤ ‖O‖ · κ^{-m} · ∏_{j=0}^{m-1} (s / (r - 1) + j)`. -/
theorem lemma_2_1_causal_norm_sum {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (hr : 2 ≤ r) {Jsite : ℝ} (hJ : 0 < Jsite)
    (hJsite : ∀ x : Fin N, ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖ ≤ Jsite)
    (U : Finset (Fin N)) (O : E) :
    ∀ m : ℕ,
      (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)), ‖causalOp D O Γ‖) ≤
      ‖O‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ m *
        ∏ j ∈ Finset.range m, ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ))
  | 0 => by
      simp [causalOp, isCausalSeq]
  | m + 1 => by
      have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < r - 1)
      have hreidx :
          (∑ Γ' ∈ Finset.univ.filter (isCausalSeq D U (m := m + 1)), ‖causalOp D O Γ'‖) =
          ∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
            ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖ := by
        have hsig :
            (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
              ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
                ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖) =
            ∑ p ∈ (Finset.univ.filter (isCausalSeq D U (m := m))).sigma
                (fun Γ ↦ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ))),
              ‖D.term p.2 * causalOp D O p.1 - causalOp D O p.1 * D.term p.2‖ :=
          (Finset.sum_sigma (Finset.univ.filter (isCausalSeq D U (m := m)))
            (fun Γ ↦ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)))
            (fun p : (_ : Fin m → D.ι) × D.ι ↦
              ‖D.term p.2 * causalOp D O p.1 - causalOp D O p.1 * D.term p.2‖)).symm
        rw [hsig]
        symm
        refine Finset.sum_bij (fun p _ ↦ Fin.snoc (α := fun _ ↦ D.ι) p.1 p.2) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hp ⊢
          rw [isCausalSeq, snoc_init_eq, Fin.snoc_last]
          exact hp
        · intro p₁ _ p₂ _ heq
          have h1 : p₁.1 = p₂.1 := by
            ext k; have := congrFun heq k.castSucc; simpa [Fin.snoc_castSucc] using this
          have h2 : p₁.2 = p₂.2 := by
            have := congrFun heq (Fin.last m); simpa [Fin.snoc_last] using this
          exact Sigma.ext h1 (heq_of_eq h2)
        · intro Γ' hΓ'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΓ'
          exact ⟨⟨fun k : Fin m ↦ Γ' k.castSucc, Γ' (Fin.last m)⟩,
            by simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and]; exact hΓ',
            Fin.snoc_init_self Γ'⟩
        · intro p _
          simp only [causalOp, Fin.snoc_last, snoc_init_eq]
      rw [hreidx]
      have hstep : ∀ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
          (∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
            ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖) ≤
          2 * ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite * ‖causalOp D O Γ‖ := by
        intro Γ hΓ
        have hcausal : isCausalSeq D U Γ := (Finset.mem_filter.mp hΓ).2
        have hcomm_bd : ∀ i : D.ι,
            ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖ ≤
            2 * ‖D.term i‖ * ‖causalOp D O Γ‖ := by
          intro i
          calc ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖
              ≤ ‖D.term i * causalOp D O Γ‖ + ‖causalOp D O Γ * D.term i‖ := norm_sub_le _ _
            _ ≤ ‖D.term i‖ * ‖causalOp D O Γ‖ + ‖causalOp D O Γ‖ * ‖D.term i‖ :=
                  add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ = 2 * ‖D.term i‖ * ‖causalOp D O Γ‖ := by ring
        have h1 :
            (∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖) ≤
            (∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i‖) * (2 * ‖causalOp D O Γ‖) := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i _
          linarith [hcomm_bd i]
        have h2 :
            (∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i‖) ≤
            ∑ x ∈ causalSupp D U Γ,
              ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖ := by
          have hswap2 :
              (∑ x ∈ causalSupp D U Γ,
                ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖) =
              ∑ i : D.ι, ((causalSupp D U Γ ∩ D.supp i).card : ℝ) * ‖D.term i‖ := by
            simp_rw [Finset.sum_filter]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter]
          rw [hswap2, Finset.sum_filter]
          apply Finset.sum_le_sum
          intro i _
          by_cases hnd : Disjoint (D.supp i) (causalSupp D U Γ)
          · simp only [hnd, not_true_eq_false, ↓reduceIte]
            positivity
          · simp only [hnd, not_false_eq_true, ↓reduceIte]
            have hge1 : (1 : ℝ) ≤ ((causalSupp D U Γ ∩ D.supp i).card : ℝ) := by
              rw [Finset.not_disjoint_iff] at hnd
              rcases hnd with ⟨x, hx1, hx2⟩
              have : 1 ≤ (causalSupp D U Γ ∩ D.supp i).card :=
                Finset.one_le_card.mpr ⟨x, Finset.mem_inter.mpr ⟨hx2, hx1⟩⟩
              exact_mod_cast this
            nlinarith [norm_nonneg (D.term i)]
        have h3 :
            (∑ x ∈ causalSupp D U Γ,
              ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖) ≤
            ((causalSupp D U Γ).card : ℝ) * Jsite := by
          calc _ ≤ ∑ _x ∈ causalSupp D U Γ, Jsite := Finset.sum_le_sum fun x _ ↦ hJsite x
            _ = ((causalSupp D U Γ).card : ℝ) * Jsite := by simp [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((causalSupp D U Γ).card : ℝ) ≤
            (U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ) := by
          exact_mod_cast causalSupp_card_le D (by omega) U Γ hcausal
        have h4 :
            (∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i‖) ≤
            ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite :=
          le_trans h2 (le_trans h3 (mul_le_mul_of_nonneg_right hcard hJ.le))
        calc _ ≤ _ := h1
          _ ≤ (((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite) * (2 * ‖causalOp D O Γ‖) :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = 2 * ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite * ‖causalOp D O Γ‖ := by ring
      have hsum_le :
          (∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)),
            ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ ¬ Disjoint (D.supp i) (causalSupp D U Γ)),
              ‖D.term i * causalOp D O Γ - causalOp D O Γ * D.term i‖) ≤
          (2 * ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite) *
            ∑ Γ ∈ Finset.univ.filter (isCausalSeq D U (m := m)), ‖causalOp D O Γ‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hstep
      have hih := lemma_2_1_causal_norm_sum D hr hJ hJsite U O m
      have hfac_eq :
          2 * ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite =
          (2 * ((r - 1 : ℕ) : ℝ) * Jsite) * ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (m : ℝ)) := by
        field_simp [hr1_pos.ne']
      calc _ ≤ _ := hsum_le
        _ ≤ (2 * ((U.card : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ)) * Jsite) *
              (‖O‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ m *
                ∏ j ∈ Finset.range m, ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ))) :=
              mul_le_mul_of_nonneg_left hih (by positivity)
        _ = ‖O‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ (m + 1) *
              ∏ j ∈ Finset.range (m + 1), ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ)) := by
              rw [hfac_eq, pow_succ, Finset.prod_range_succ]; ring

/-- Direct norm bound on `ad_H^m(O)` from `lemma_2_1_causal_norm_sum`. -/
theorem lemma_2_1_adPow_norm_bound {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (hr : 2 ≤ r) {Jsite : ℝ} (hJ : 0 < Jsite)
    (hJsite : ∀ x : Fin N, ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖ ≤ Jsite)
    (U : Finset (Fin N)) (O : E) (hO : D.SupportedOn U O) (m : ℕ) :
    ‖adPow D.totalH O m‖ ≤
    ‖O‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ m *
      ∏ j ∈ Finset.range m, ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ)) := by
  rw [adPow_eq_causal_sum D U O hO m]
  exact le_trans (norm_sum_le _ _) (lemma_2_1_causal_norm_sum D hr hJ hJsite U O m)

/-- Exact identity `∑' m : ℕ, (m + 1 : ℝ) * q ^ m = (1 - q)⁻¹ ^ 2` for `0 ≤ q < 1`,
proved via Cauchy product of two geometric series. -/
private lemma tsum_succ_mul_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * q ^ m = (1 - q)⁻¹ ^ 2 := by
  have hsumm : Summable (fun j : ℕ ↦ ‖q ^ j‖) := by
    simpa [Real.norm_of_nonneg (pow_nonneg hq0 _)] using summable_geometric_of_lt_one hq0 hq1
  have hprod_summ : Summable (fun p : ℕ × ℕ ↦ q ^ p.1 * q ^ p.2) :=
    summable_mul_of_summable_norm hsumm hsumm
  have hprod := tsum_mul_tsum_of_summable_norm hsumm hsumm
  rw [tsum_geometric_of_lt_one hq0 hq1, ← sq] at hprod
  rw [hprod, tsum_prod_eq_tsum_antidiag _ hprod_summ]
  refine tsum_congr fun m ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ q ^ i * q ^ j) m]
  have hterm : ∀ j ∈ Finset.range (m + 1), q ^ j * q ^ (m - j) = q ^ m := by
    intro j hj
    rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Lemma 2.1(2) (Eq. 2.4 — Single-Site Imaginary-Time Operator-Norm Bound)**:
For an `r`-local Hamiltonian (`r ≥ 2`), `κ = (2 (r - 1) J_site)⁻¹`, `|τ| < 4 κ`, and any
single-site operator `V` (`|U| ≤ 1`, `‖V‖ ≤ 1`), the complex-time evolved operator
`exp(z H) V exp(-z H)` with `‖z‖ = |τ| / 4` satisfies
`‖exp(z H) V exp(-z H)‖ ≤ (1 - |τ| / (4 κ))⁻¹`. -/
theorem lemma_2_1_single_site_exp_bound {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (hr : 2 ≤ r) {Jsite τ : ℝ} (hJ : 0 < Jsite)
    (hJsite : ∀ x : Fin N, ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖ ≤ Jsite)
    (U : Finset (Fin N)) (hU : U.card ≤ 1) (V : E) (hV_supp : D.SupportedOn U V)
    (hV_norm : ‖V‖ ≤ 1) (z : ℂ) (hz : ‖z‖ = |τ| / 4)
    (hτ : |τ| < 4 * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹) :
    ‖NormedSpace.exp (z • D.totalH) * V * NormedSpace.exp (-(z • D.totalH))‖ ≤
    (1 - |τ| / (4 * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹))⁻¹ := by
  set κ := (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹
  have hr1_ge1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
  have hκ_pos : 0 < κ := by positivity
  set q := |τ| / (4 * κ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr hτ
  have hq_eq : ‖z‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) = q := by
    rw [hz]; simp only [q, κ]; field_simp [hκ_pos.ne']
  rw [exp_conj_eq_tsum_adPow]
  have hterm_le : ∀ m : ℕ, ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH V m‖ ≤ q ^ m := by
    intro m
    have had := lemma_2_1_adPow_norm_bound D hr hJ hJsite U V hV_supp m
    have hprod_le : (∏ j ∈ Finset.range m, ((U.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ))) ≤
        (m.factorial : ℝ) := by
      have hU_div : (U.card : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact le_trans (by exact_mod_cast hU) hr1_ge1
      rw [← prod_range_one_add m]
      exact prod_le_prod_nn _ _ _ (fun j _ ↦ by positivity) (fun j _ ↦ by linarith)
    have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    calc ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH V m‖
        = (‖z‖ ^ m / (m.factorial : ℝ)) * ‖adPow D.totalH V m‖ := by
            rw [norm_smul, norm_div, norm_pow, Complex.norm_natCast]
      _ ≤ (‖z‖ ^ m / (m.factorial : ℝ)) *
            (1 * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ m * (m.factorial : ℝ)) := by
            gcongr
            exact le_trans had (mul_le_mul (mul_le_mul_of_nonneg_right hV_norm (by positivity))
              hprod_le (Finset.prod_nonneg fun _ _ ↦ by positivity) (by positivity))
      _ = (‖z‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) ^ m := by
            rw [mul_pow]; field_simp [hfac_pos.ne']; ring
      _ = q ^ m := by rw [hq_eq]
  have hsumm_norm : Summable (fun m : ℕ ↦ ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH V m‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le (summable_geometric_of_lt_one hq0 hq1)
  calc ‖∑' m : ℕ, (z ^ m / (m.factorial : ℂ)) • adPow D.totalH V m‖
      ≤ ∑' m : ℕ, ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH V m‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' m : ℕ, q ^ m :=
          hsumm_norm.tsum_le_tsum hterm_le (summable_geometric_of_lt_one hq0 hq1)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- **Lemma 2.1(3) (Eq. 2.5 — `r`-Local Interaction Imaginary-Time Operator-Norm Bound)**:
For an `r`-local Hamiltonian (`r ≥ 2`), `κ = (2 (r - 1) J_site)⁻¹`, `|τ| < 4 κ`, and any
`r`-local operator `h_X` (`|X| ≤ r`),
`‖exp(z H) h_X exp(-z H)‖ ≤ ‖h_X‖ · (1 - |τ| / (4 κ))⁻¹ ^ 2` where `‖z‖ = |τ| / 4`. -/
theorem lemma_2_1_r_local_exp_bound {N r : ℕ} (D : LocalInteractionDecomp E N r)
    (hr : 2 ≤ r) {Jsite τ : ℝ} (hJ : 0 < Jsite)
    (hJsite : ∀ x : Fin N, ∑ i ∈ Finset.univ.filter (fun i : D.ι ↦ x ∈ D.supp i), ‖D.term i‖ ≤ Jsite)
    (X : Finset (Fin N)) (hX : X.card ≤ r) (hOp : E) (hOp_supp : D.SupportedOn X hOp)
    (z : ℂ) (hz : ‖z‖ = |τ| / 4)
    (hτ : |τ| < 4 * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹) :
    ‖NormedSpace.exp (z • D.totalH) * hOp * NormedSpace.exp (-(z • D.totalH))‖ ≤
    ‖hOp‖ * (1 - |τ| / (4 * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹))⁻¹ ^ 2 := by
  set κ := (2 * ((r - 1 : ℕ) : ℝ) * Jsite)⁻¹
  have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hκ_pos : 0 < κ := by positivity
  set q := |τ| / (4 * κ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr hτ
  have hq_eq : ‖z‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) = q := by
    rw [hz]; simp only [q, κ]; field_simp [hκ_pos.ne']
  rw [exp_conj_eq_tsum_adPow]
  have hterm_le : ∀ m : ℕ,
      ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH hOp m‖ ≤
      ‖hOp‖ * (((m + 1 : ℕ) : ℝ) * q ^ m) := by
    intro m
    have had := lemma_2_1_adPow_norm_bound D hr hJ hJsite X hOp hOp_supp m
    have hprod_le : (∏ j ∈ Finset.range m, ((X.card : ℝ) / ((r - 1 : ℕ) : ℝ) + (j : ℝ))) ≤
        ((m + 1).factorial : ℝ) := by
      have hX_div : (X.card : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hr1_pos]
        have hnat : X.card ≤ 2 * (r - 1) := by omega
        exact_mod_cast hnat
      rw [← prod_range_two_add m]
      exact prod_le_prod_nn _ _ _ (fun j _ ↦ by positivity) (fun j _ ↦ by linarith)
    have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    calc ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH hOp m‖
        = (‖z‖ ^ m / (m.factorial : ℝ)) * ‖adPow D.totalH hOp m‖ := by
            rw [norm_smul, norm_div, norm_pow, Complex.norm_natCast]
      _ ≤ (‖z‖ ^ m / (m.factorial : ℝ)) *
            (‖hOp‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite) ^ m * ((m + 1).factorial : ℝ)) := by
            gcongr
            exact le_trans had (mul_le_mul_of_nonneg_left hprod_le (by positivity))
      _ = ‖hOp‖ * (((m + 1 : ℕ) : ℝ) * (‖z‖ * (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) ^ m) := by
            rw [Nat.factorial_succ, Nat.cast_mul, mul_pow]
            field_simp [hfac_pos.ne']; ring
      _ = ‖hOp‖ * (((m + 1 : ℕ) : ℝ) * q ^ m) := by rw [hq_eq]
  have hsumm_rhs : Summable (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * q ^ m) := by
    have hsumm : Summable (fun j : ℕ ↦ ‖q ^ j‖) := by
      simpa [Real.norm_of_nonneg (pow_nonneg hq0 _)] using summable_geometric_of_lt_one hq0 hq1
    have hprod_summ : Summable (fun p : ℕ × ℕ ↦ q ^ p.1 * q ^ p.2) :=
      summable_mul_of_summable_norm hsumm hsumm
    have hanti := summable_antidiag_of_summable_prod _ hprod_summ
    refine hanti.congr fun m ↦ ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ q ^ i * q ^ j) m]
    have hterm : ∀ j ∈ Finset.range (m + 1), q ^ j * q ^ (m - j) = q ^ m := by
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumm_norm : Summable (fun m : ℕ ↦ ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH hOp m‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le (hsumm_rhs.mul_left ‖hOp‖)
  calc ‖∑' m : ℕ, (z ^ m / (m.factorial : ℂ)) • adPow D.totalH hOp m‖
      ≤ ∑' m : ℕ, ‖(z ^ m / (m.factorial : ℂ)) • adPow D.totalH hOp m‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' m : ℕ, ‖hOp‖ * (((m + 1 : ℕ) : ℝ) * q ^ m) :=
          hsumm_norm.tsum_le_tsum hterm_le (hsumm_rhs.mul_left ‖hOp‖)
    _ = ‖hOp‖ * ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * q ^ m := tsum_mul_left
    _ = ‖hOp‖ * (1 - q)⁻¹ ^ 2 := by rw [tsum_succ_mul_geometric hq0 hq1]

end CausalSequenceBounds

end KrylovChaos
