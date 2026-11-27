/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.ProductState
import KrylovChaos.ProductStateDerivation
import KrylovChaos.ProductStateMultiSite
import KrylovChaos.ConcreteEndToEndWiring
import Mathlib.Tactic

/-!
# Proposition 4.3: Full `Λ_ρ^{MSS}(s)` Bound & N-Qubit Local Unitary Invariance (Item #13)

Closes all remaining gaps in Proposition 4.3 (`ProductStateMultiSite.lean`):
1. **Exact Filtration Span Equivalence (`filtrationSubmodule_eq_span_prodGSBasis`)**:
   For every `m : Fin N → ℝ` with `∀ x, |m x| < 1` and every `s : ℕ`,
   `filtrationSubmodule N s = Submodule.span ℂ { M | ∃ a, stringWeight a ≤ s ∧ M = prodGSBasis m a }`.
2. **Static Supremum Bound (`prop_4_3_lambdaMSS_product_state`)**:
   `lambdaMSS (prodGibbsData m hm) s ≤ (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ))`
   with ZERO assumed expansion coefficients.
3. **Full `N`-Qubit Local Unitary Invariance Lift (`prop_4_3_lambdaMSS_general_product_state`)**:
   For ANY local unitary rotation `U = ⨂_{x=1}^N u_x` (`u_xᴴ u_x = u_x u_xᴴ = 1`),
   proves that `A ↦ Uᴴ A U` preserves `filtrationSubmodule N s`, `gibbsWightmanNormSq`,
   and `mssThermalSize`, hence
   `lambdaMSS (rotatedProdGibbsData u hu m hm) s ≤ (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ))`
   for EVERY general `N`-qubit product state `ρ = ⨂_x u_x ((I + m_x Z)/2) u_xᴴ`.
-/

namespace KrylovChaos

open Matrix

private abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

section KroneckerMultilinearity

private lemma kronOp_update_zero {N : ℕ} (F : Fin N → Mat2) (x : Fin N) :
    kronOp (Function.update F x 0) = 0 := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)

private lemma kronOp_update_add {N : ℕ} (F : Fin N → Mat2) (x : Fin N) (M₁ M₂ : Mat2) :
    kronOp (Function.update F x (M₁ + M₂)) =
      kronOp (Function.update F x M₁) + kronOp (Function.update F x M₂) := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.add_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  have hrest : ∀ M : Mat2,
      (∏ y ∈ Finset.univ.erase x, (Function.update F x M) y (i y) (j y)) =
        ∏ y ∈ Finset.univ.erase x, F y (i y) (j y) := by
    intro M
    apply Finset.prod_congr rfl; intro y hy
    simp [Function.update_of_ne (Finset.mem_erase.mp hy).1]
  rw [hrest, hrest, hrest]
  simp only [Function.update_self, Matrix.add_apply]
  ring

private lemma kronOp_update_smul {N : ℕ} (F : Fin N → Mat2) (x : Fin N) (c : ℂ) (M : Mat2) :
    kronOp (Function.update F x (c • M)) = c • kronOp (Function.update F x M) := by
  ext i j
  simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  have hrest : ∀ B : Mat2,
      (∏ y ∈ Finset.univ.erase x, (Function.update F x B) y (i y) (j y)) =
        ∏ y ∈ Finset.univ.erase x, F y (i y) (j y) := by
    intro B
    apply Finset.prod_congr rfl; intro y hy
    simp [Function.update_of_ne (Finset.mem_erase.mp hy).1]
  rw [hrest, hrest]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Multilinear Kronecker-product span lemma: if on every site `x ∈ S`, `F x` lies in
`span { B x i | P x i }`, and outside `S`, `F x = B x i` with `P x i`, then `kronOp F`
lies in `span { kronOp (fun x ↦ B x (b x)) | ∀ x, P x (b x) }`. -/
lemma kronOp_mem_span_of_site_span {N : ℕ}
    (B : Fin N → Fin 4 → Mat2) (P : Fin N → Fin 4 → Prop)
    (S : Finset (Fin N)) :
    ∀ F : Fin N → Mat2,
      (∀ x ∉ S, ∃ i : Fin 4, P x i ∧ F x = B x i) →
      (∀ x ∈ S, F x ∈ Submodule.span ℂ { M : Mat2 | ∃ i : Fin 4, P x i ∧ M = B x i }) →
      kronOp F ∈ Submodule.span ℂ
        { M : QubitOp N | ∃ b : Fin N → Fin 4, (∀ x, P x (b x)) ∧ M = kronOp (fun x ↦ B x (b x)) } := by
  induction S using Finset.induction_on with
  | empty =>
    intro F hOut _
    have hch : ∀ x : Fin N, ∃ i : Fin 4, P x i ∧ F x = B x i := fun x ↦ hOut x (by simp)
    choose b hbP hbF using hch
    apply Submodule.subset_span
    exact ⟨b, hbP, by congr 1; funext x; exact hbF x⟩
  | @insert x₀ S' hx₀ ih =>
    intro F hOut hIn
    have hFx₀ : F x₀ ∈ Submodule.span ℂ { M : Mat2 | ∃ i : Fin 4, P x₀ i ∧ M = B x₀ i } :=
      hIn x₀ (Finset.mem_insert_self x₀ S')
    have hupd : F = Function.update F x₀ (F x₀) := (Function.update_eq_self x₀ F).symm
    rw [hupd]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hFx₀
    · rintro M ⟨i, hiP, rfl⟩
      apply ih (Function.update F x₀ (B x₀ i))
      · intro x hx
        by_cases hxx : x = x₀
        · subst hxx; exact ⟨i, hiP, by simp⟩
        · have hx' : x ∉ insert x₀ S' := by simp [hxx, hx]
          rcases hOut x hx' with ⟨j, hjP, hjF⟩
          exact ⟨j, hjP, by simp [Function.update_of_ne hxx, hjF]⟩
      · intro x hx
        have hxx : x ≠ x₀ := fun h ↦ hx₀ (h ▸ hx)
        simpa [Function.update_of_ne hxx] using hIn x (Finset.mem_insert_of_mem hx)
    · rw [kronOp_update_zero]; exact Submodule.zero_mem _
    · intro M₁ M₂ _ _ h₁ h₂
      rw [kronOp_update_add]; exact Submodule.add_mem _ h₁ h₂
    · intro c M _ hM
      rw [kronOp_update_smul]; exact Submodule.smul_mem _ c hM

lemma stringWeight_le_of_zero_imp {N : ℕ} {a b : Fin N → Fin 4}
    (h : ∀ x : Fin N, a x = 0 → b x = 0) :
    stringWeight b ≤ stringWeight a := by
  unfold stringWeight
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro ha0
  exact hx (h x ha0)

end KroneckerMultilinearity

section ProductStateFiltrationSpan

private lemma pauliMat_eq_gsBasis_comb {m : ℝ} (hm : |m| < 1) (a : Fin 4) :
    pauliMat a ∈ Submodule.span ℂ
      { M : Mat2 | ∃ i : Fin 4, (a = 0 → i = 0) ∧ M = gsBasis m i } := by
  have hlt := abs_lt.mp hm
  have hσ : 0 < prodSigma m := Real.sqrt_pos.mpr (by nlinarith)
  have hσ_ne : (prodSigma m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hsq_ne : (Real.sqrt (prodSigma m) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hσ).ne'
  fin_cases a <;> dsimp only
  · apply Submodule.subset_span
    refine ⟨0, fun _ ↦ rfl, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis]
  · have h1 : pauliMat 1 = (Real.sqrt (prodSigma m) : ℂ) • gsBasis m 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis, mul_inv_cancel₀ hsq_ne]
    change pauliMat 1 ∈ _
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp, rfl⟩)
  · have h2 : pauliMat 2 = (Real.sqrt (prodSigma m) : ℂ) • gsBasis m 2 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis] <;> field_simp [hsq_ne]
    change pauliMat 2 ∈ _
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp, rfl⟩)
  · have h3 : pauliMat 3 = (prodSigma m : ℂ) • gsBasis m 3 + (m : ℂ) • gsBasis m 0 := by
      have hgs3 := gsBasis_three_eq m
      have hgs0 : gsBasis m 0 = pauliMat 0 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis]
      rw [hgs3, hgs0, smul_smul, mul_inv_cancel₀ hσ_ne, one_smul, sub_add_cancel]
    change pauliMat 3 ∈ _
    rw [h3]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, by simp, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, rfl⟩))

private lemma gsBasis_eq_pauliMat_comb {m : ℝ} (a : Fin 4) :
    gsBasis m a ∈ Submodule.span ℂ
      { M : Mat2 | ∃ i : Fin 4, (a = 0 → i = 0) ∧ M = pauliMat i } := by
  fin_cases a <;> dsimp only
  · apply Submodule.subset_span
    refine ⟨0, fun _ ↦ rfl, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis]
  · have h1 : gsBasis m 1 = ((Real.sqrt (prodSigma m))⁻¹ : ℂ) • pauliMat 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis]
    change gsBasis m 1 ∈ _
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp, rfl⟩)
  · have h2 : gsBasis m 2 = ((Real.sqrt (prodSigma m))⁻¹ : ℂ) • pauliMat 2 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, gsBasis] <;> ring
    change gsBasis m 2 ∈ _
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp, rfl⟩)
  · change gsBasis m 3 ∈ _
    rw [gsBasis_three_eq m]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨3, by simp, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, rfl⟩)))

/-- **Item #13 (Exact Filtration Span Equivalence)**:
For ANY `m : Fin N → ℝ` with `∀ x, |m x| < 1` and ANY `s : ℕ`, the locality filtration
subspace `filtrationSubmodule N s` equals the span of tensor-product Gram–Schmidt basis
operators `prodGSBasis m a` with `stringWeight a ≤ s`. -/
theorem filtrationSubmodule_eq_span_prodGSBasis {N s : ℕ}
    (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) :
    filtrationSubmodule N s =
      Submodule.span ℂ { M : QubitOp N | ∃ a : Fin N → Fin 4,
        stringWeight a ≤ s ∧ M = prodGSBasis m a } := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    have hmem := kronOp_mem_span_of_site_span
      (fun x i ↦ gsBasis (m x) i) (fun x i ↦ a x = 0 → i = 0) Finset.univ
      (fun x ↦ pauliMat (a x)) (by simp) (fun x _ ↦ pauliMat_eq_gsBasis_comb (hm x) (a x))
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, le_trans (stringWeight_le_of_zero_imp hb) ha, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    have hmem := kronOp_mem_span_of_site_span
      (fun _ i ↦ pauliMat i) (fun x i ↦ a x = 0 → i = 0) Finset.univ
      (fun x ↦ gsBasis (m x) (a x)) (by simp) (fun x _ ↦ gsBasis_eq_pauliMat_comb (a x))
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, le_trans (stringWeight_le_of_zero_imp hb) ha, rfl⟩

/-- Every `A ∈ filtrationSubmodule N s` admits an explicit expansion `A = ∑ a, c a • prodGSBasis m a`
with `c a = 0` for all `stringWeight a > s`. -/
lemma exists_prodGSBasis_expansion_of_mem_filtration {N s : ℕ}
    (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) {A : QubitOp N}
    (hA : A ∈ filtrationSubmodule N s) :
    ∃ c : (Fin N → Fin 4) → ℂ,
      (∀ a, s < stringWeight a → c a = 0) ∧
      A = ∑ a : Fin N → Fin 4, c a • prodGSBasis m a := by
  rw [filtrationSubmodule_eq_span_prodGSBasis m hm] at hA
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a₀, ha₀, rfl⟩
    refine ⟨fun a ↦ if a = a₀ then 1 else 0, ?_, ?_⟩
    · intro a hgt
      have hne : a ≠ a₀ := fun h ↦ by subst h; omega
      simp [hne]
    · simp [Finset.sum_ite_eq']
  · exact ⟨fun _ ↦ 0, fun _ _ ↦ rfl, by simp⟩
  · rintro X Y _ _ ⟨c₁, hs₁, hX⟩ ⟨c₂, hs₂, hY⟩
    refine ⟨fun a ↦ c₁ a + c₂ a, fun a hgt ↦ by dsimp only; rw [hs₁ a hgt, hs₂ a hgt, add_zero], ?_⟩
    rw [hX, hY, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; rw [add_smul]
  · rintro r X _ ⟨c, hs, hX⟩
    refine ⟨fun a ↦ r * c a, fun a hgt ↦ by dsimp only; rw [hs a hgt, mul_zero], ?_⟩
    rw [hX, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro a _; rw [smul_smul]

/-- **Proposition 4.3 — Full Concrete `lambdaMSS` Bound for Diagonal Product States (Item #13)**:
For ANY `N`-qubit product state `ρ = ⨂_{x=1}^N (I + m_x Z_x)/2` with `|m_x| ≤ mmax < 1`
and ANY `s : ℕ`:
`lambdaMSS (prodGibbsData m hm) s ≤ (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ))`. -/
theorem prop_4_3_lambdaMSS_product_state {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1) :
    lambdaMSS (prodGibbsData m (fun x ↦ lt_of_le_of_lt (hm_le x) hmmax)) s ≤
      (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  have hm : ∀ x, |m x| < 1 := fun x ↦ lt_of_le_of_lt (hm_le x) hmmax
  unfold lambdaMSS
  apply csSup_le
  · refine ⟨0, 1, ?_, ?_, (mssThermalSize_one _).symm⟩
    · have h1 : (1 : QubitOp N) = pauliString (fun _ ↦ 0) := by
        unfold pauliString
        have h0 : (fun _ : Fin N ↦ pauliMat 0) = (fun _ : Fin N ↦ (1 : Mat2)) := by
          funext _; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
        rw [h0, kronOp_one]
      rw [h1]
      exact Submodule.subset_span ⟨fun _ ↦ 0, by simp [stringWeight], rfl⟩
    · unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_one,
        (prodGibbsData m hm).sq_half, (prodGibbsData m hm).trace_one, Complex.one_re]
  · rintro r ⟨A, hA_mem, hA_norm, rfl⟩
    rcases exists_prodGSBasis_expansion_of_mem_filtration m hm hA_mem with ⟨c, hsupp, rfl⟩
    exact prop_4_3_concrete_product_state_bound m hm_le hmmax c hsupp hA_norm

end ProductStateFiltrationSpan

section LocalUnitaryInvarianceLift

/-- Locally rotated `N`-qubit product state `U ρ Uᴴ` where `U = ⨂_{x=1}^N u_x` is a product
of single-qubit unitaries (`(u x)ᴴ * u x = 1` and `u x * (u x)ᴴ = 1`). Every full-rank
`N`-qubit product state `⨂_x (I + r_x · σ_x)/2` has this exact form! -/
noncomputable def rotatedProdGibbsData {N : ℕ}
    (u : Fin N → Mat2)
    (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) : GibbsData N :=
  let U : QubitOp N := kronOp u
  let G := prodGibbsData m hm
  have hUL : Uᴴ * U = 1 := by
    dsimp only [U]; rw [kronOp_conjTranspose, kronOp_mul]
    have : (fun x ↦ (u x)ᴴ * u x) = fun _ ↦ 1 := funext huL
    rw [this, kronOp_one]
  have hUR : U * Uᴴ = 1 := by
    dsimp only [U]; rw [kronOp_conjTranspose, kronOp_mul]
    have : (fun x ↦ u x * (u x)ᴴ) = fun _ ↦ 1 := funext huR
    rw [this, kronOp_one]
  { ρβ := U * G.ρβ * Uᴴ
    ρHalf := U * G.ρHalf * Uᴴ
    ρQuarter := U * G.ρQuarter * Uᴴ
    ρQuarterInv := U * G.ρQuarterInv * Uᴴ
    ρβ_herm := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        G.ρβ_herm, Matrix.mul_assoc]
    ρHalf_herm := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        G.ρHalf_herm, Matrix.mul_assoc]
    ρQuarter_herm := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        G.ρQuarter_herm, Matrix.mul_assoc]
    ρQuarterInv_herm := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        G.ρQuarterInv_herm, Matrix.mul_assoc]
    sq_quarter := by
      calc U * G.ρQuarter * Uᴴ * (U * G.ρQuarter * Uᴴ)
          = U * G.ρQuarter * (Uᴴ * U) * G.ρQuarter * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * (G.ρQuarter * G.ρQuarter) * Uᴴ := by rw [hUL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * G.ρHalf * Uᴴ := by rw [G.sq_quarter]
    sq_half := by
      calc U * G.ρHalf * Uᴴ * (U * G.ρHalf * Uᴴ)
          = U * G.ρHalf * (Uᴴ * U) * G.ρHalf * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * (G.ρHalf * G.ρHalf) * Uᴴ := by rw [hUL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * G.ρβ * Uᴴ := by rw [G.sq_half]
    inv_left := by
      calc U * G.ρQuarterInv * Uᴴ * (U * G.ρQuarter * Uᴴ)
          = U * G.ρQuarterInv * (Uᴴ * U) * G.ρQuarter * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * (G.ρQuarterInv * G.ρQuarter) * Uᴴ := by rw [hUL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [G.inv_left, Matrix.mul_one, hUR]
    inv_right := by
      calc U * G.ρQuarter * Uᴴ * (U * G.ρQuarterInv * Uᴴ)
          = U * G.ρQuarter * (Uᴴ * U) * G.ρQuarterInv * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * (G.ρQuarter * G.ρQuarterInv) * Uᴴ := by rw [hUL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [G.inv_right, Matrix.mul_one, hUR]
    trace_one := by
      rw [Matrix.trace_mul_cycle, hUL, Matrix.one_mul, G.trace_one] }

private lemma mat2_mem_pauli_span (M : Mat2) :
    M ∈ Submodule.span ℂ { B : Mat2 | ∃ i : Fin 4, B = pauliMat i } := by
  have hdecomp : M =
      ((M 0 0 + M 1 1) / 2) • pauliMat 0 +
      ((M 0 1 + M 1 0) / 2) • pauliMat 1 +
      (Complex.I * (M 0 1 - M 1 0) / 2) • pauliMat 2 +
      ((M 0 0 - M 1 1) / 2) • pauliMat 3 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliMat] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [hdecomp]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))

/-- Local unitary conjugation `A ↦ Uᴴ A U` (`U = ⨂_x u_x`) preserves `filtrationSubmodule N s`. -/
theorem localUnitary_conj_mem_filtration {N s : ℕ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1)
    {A : QubitOp N} (hA : A ∈ filtrationSubmodule N s) :
    (kronOp u)ᴴ * A * kronOp u ∈ filtrationSubmodule N s := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, ha, rfl⟩
    unfold pauliString
    rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul]
    have hmem := kronOp_mem_span_of_site_span
      (fun _ i ↦ pauliMat i) (fun x i ↦ a x = 0 → i = 0) Finset.univ
      (fun x ↦ (u x)ᴴ * pauliMat (a x) * u x) (by simp) (fun x _ ↦ by
        by_cases hax : a x = 0
        · apply Submodule.subset_span
          refine ⟨0, fun _ ↦ rfl, ?_⟩
          have hp0 : pauliMat 0 = (1 : Mat2) := by
            ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
          rw [hax, hp0, Matrix.mul_one, huL x]
        · have hsp := mat2_mem_pauli_span ((u x)ᴴ * pauliMat (a x) * u x)
          refine Submodule.span_mono ?_ hsp
          rintro _ ⟨i, rfl⟩
          exact ⟨i, fun h ↦ absurd h hax, rfl⟩)
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, le_trans (stringWeight_le_of_zero_imp hb) ha, rfl⟩
  · simp [Submodule.zero_mem]
  · intro X Y _ _ hX hY
    rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hX

private lemma singleSite_pauli_twirl_unitary (u : Mat2) (huL : uᴴ * u = 1) (huR : u * uᴴ = 1)
    (M : Mat2) :
    (1 / 4 : ℂ) • ∑ α : Fin 4, pauliMat α * (uᴴ * M * u) * pauliMat α =
      uᴴ * ((1 / 4 : ℂ) • ∑ α : Fin 4, pauliMat α * M * pauliMat α) * u := by
  have htwirl : ∀ B : Mat2,
      (1 / 4 : ℂ) • ∑ α : Fin 4, pauliMat α * B * pauliMat α =
        ((1 / 2 : ℂ) * B.trace) • (1 : Mat2) := by
    intro B
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Fin.sum_univ_four, pauliMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.trace, Matrix.diag]; ring_nf; simp [Complex.I_sq]; try ring)
  rw [htwirl (uᴴ * M * u), htwirl M, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, huL]
  congr 1; congr 1
  rw [Matrix.trace_mul_cycle, huR, Matrix.one_mul]

/-- Local unitary conjugation commutes with `partialTraceSite x`. -/
lemma partialTraceSite_localUnitary_conj {N : ℕ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (x : Fin N) (M : QubitOp N) :
    partialTraceSite x ((kronOp u)ᴴ * M * kronOp u) =
      (kronOp u)ᴴ * partialTraceSite x M * kronOp u := by
  have hspan : M ∈ Submodule.span ℂ { P : QubitOp N | ∃ a : Fin N → Fin 4, P = pauliString a } := by
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun σ _ ↦ Submodule.sum_mem _ fun τ _ ↦ ?_
    have hsingle : Matrix.single σ τ (M σ τ) = M σ τ • Matrix.single σ τ (1 : ℂ) := by
      ext a b
      by_cases h : σ = a ∧ τ = b
      · rcases h with ⟨rfl, rfl⟩; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h]
    rw [hsingle]
    refine Submodule.smul_mem _ _ ?_
    have hkron : Matrix.single σ τ (1 : ℂ) =
        kronOp (fun y : Fin N ↦ Matrix.single (σ y) (τ y) (1 : ℂ)) := by
      ext a b
      unfold kronOp
      by_cases h : σ = a ∧ τ = b
      · rcases h with ⟨rfl, rfl⟩; simp [Matrix.single_apply]
      · simp only [Matrix.single_apply, h, ↓reduceIte]
        have hex : ∃ y : Fin N, ¬(σ y = a y ∧ τ y = b y) := by
          by_contra hall; push Not at hall
          exact h ⟨funext fun y ↦ (hall y).1, funext fun y ↦ (hall y).2⟩
        rcases hex with ⟨y₀, hy₀⟩
        exact (Finset.prod_eq_zero (Finset.mem_univ y₀) (by simp [Matrix.single_apply, hy₀])).symm
    rw [hkron]
    have hmem := kronOp_mem_span_of_site_span (fun _ i ↦ pauliMat i) (fun _ _ ↦ True)
      Finset.univ (fun y ↦ Matrix.single (σ y) (τ y) (1 : ℂ))
      (fun y hy ↦ (hy (Finset.mem_univ y)).elim)
      (fun y _ ↦ by
        refine Submodule.span_mono ?_ (mat2_mem_pauli_span (Matrix.single (σ y) (τ y) (1 : ℂ)))
        rintro _ ⟨i, rfl⟩; exact ⟨i, trivial, rfl⟩)
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩
  have hpt_add : ∀ A B : QubitOp N,
      partialTraceSite x (A + B) = partialTraceSite x A + partialTraceSite x B := by
    intro A B; unfold partialTraceSite
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add]
  have hpt_smul : ∀ (c : ℂ) (A : QubitOp N),
      partialTraceSite x (c • A) = c • partialTraceSite x A := by
    intro c A; unfold partialTraceSite
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]; rw [smul_comm]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨a, rfl⟩
    unfold pauliString
    rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul]
    have hpt_kron : ∀ F : Fin N → Mat2,
        partialTraceSite x (kronOp F) =
          kronOp (fun y ↦ if y = x then (1 / 4 : ℂ) • ∑ α : Fin 4, pauliMat α * F x * pauliMat α else F y) := by
      intro F
      unfold partialTraceSite
      have hp0 : pauliMat 0 = (1 : Mat2) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
      have hconj : ∀ α : Fin 4,
          pauliSite x α * kronOp F * pauliSite x α =
            kronOp (fun y ↦ if y = x then pauliMat α * F x * pauliMat α else F y) := by
        intro α; unfold pauliSite pauliString
        rw [kronOp_mul, kronOp_mul]; congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp
        · simp [hy, hp0]
      simp_rw [hconj]
      ext p q
      simp only [Matrix.smul_apply, Matrix.sum_apply, kronOp, Matrix.of_apply, smul_eq_mul]
      have hfac : ∀ α : Fin 4,
          (∏ y : Fin N, (if y = x then pauliMat α * F x * pauliMat α else F y) (p y) (q y)) =
            (pauliMat α * F x * pauliMat α) (p x) (q x) * ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
        intro α
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
        simp only [↓reduceIte]; congr 1
        apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
      simp_rw [hfac, ← Finset.sum_mul]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      simp only [↓reduceIte, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      have hrest : (∏ y ∈ Finset.univ.erase x,
          (if y = x then (1 / 4 : ℂ) • ∑ α : Fin 4, pauliMat α * F x * pauliMat α else F y) (p y) (q y)) =
          ∏ y ∈ Finset.univ.erase x, F y (p y) (q y) := by
        apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
      rw [hrest]; ring
    rw [hpt_kron, hpt_kron, kronOp_mul, kronOp_mul]
    congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp only [↓reduceIte]
      exact singleSite_pauli_twirl_unitary (u y) (huL y) (huR y) (pauliMat (a y))
    · simp [hy]
  · simp [partialTraceSite]
  · intro A B _ _ hA hB
    rw [Matrix.mul_add, Matrix.add_mul, hpt_add, hpt_add, Matrix.mul_add, Matrix.add_mul, hA, hB]
  · intro c A _ hA
    rw [Matrix.mul_smul, Matrix.smul_mul, hpt_smul, hpt_smul, Matrix.mul_smul, Matrix.smul_mul, hA]

/-- Local unitary conjugation preserves `totalSizeOp`: `S(Uᴴ M U) = Uᴴ S(M) U`. -/
lemma totalSizeOp_localUnitary_conj {N : ℕ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (M : QubitOp N) :
    totalSizeOp ((kronOp u)ᴴ * M * kronOp u) = (kronOp u)ᴴ * totalSizeOp M * kronOp u := by
  unfold totalSizeOp siteSizeOp
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sub, Matrix.sub_mul]
  apply Finset.sum_congr rfl; intro x _
  rw [partialTraceSite_localUnitary_conj u huL huR x M]

private lemma rotatedProdGibbsData_ρHalf {N : ℕ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) :
    (rotatedProdGibbsData u huL huR m hm).ρHalf =
      kronOp u * (prodGibbsData m hm).ρHalf * (kronOp u)ᴴ := rfl

private lemma rotatedProdGibbsData_ρQuarter {N : ℕ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (m : Fin N → ℝ) (hm : ∀ x, |m x| < 1) :
    (rotatedProdGibbsData u huL huR m hm).ρQuarter =
      kronOp u * (prodGibbsData m hm).ρQuarter * (kronOp u)ᴴ := rfl

private lemma lambdaMSS_le_of_unitary_conj {N s : ℕ}
    (G G' : GibbsData N) (U : QubitOp N)
    (hUL : Uᴴ * U = 1) (hUR : U * Uᴴ = 1)
    (hG'half : G'.ρHalf = U * G.ρHalf * Uᴴ)
    (hG'quarter : G'.ρQuarter = U * G.ρQuarter * Uᴴ)
    (hsize : ∀ M : QubitOp N, totalSizeOp (Uᴴ * M * U) = Uᴴ * totalSizeOp M * U)
    (hfilt : ∀ A : QubitOp N, A ∈ filtrationSubmodule N s → Uᴴ * A * U ∈ filtrationSubmodule N s) :
    lambdaMSS G' s ≤ lambdaMSS G s := by
  have hnorm_eq : ∀ A : QubitOp N,
      gibbsWightmanNormSq G' A = gibbsWightmanNormSq G (Uᴴ * A * U) := by
    intro A
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
    rw [hG'half]
    apply congrArg Complex.re
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Matrix.trace (U * G.ρHalf * Uᴴ * Aᴴ * (U * G.ρHalf * Uᴴ) * A)
        = Matrix.trace (U * (G.ρHalf * (Uᴴ * (Aᴴ * U)) * G.ρHalf * (Uᴴ * A))) := by
            apply congrArg Matrix.trace; simp only [mul_assoc]
      _ = Matrix.trace ((G.ρHalf * (Uᴴ * (Aᴴ * U)) * G.ρHalf * (Uᴴ * A)) * U) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G.ρHalf * (Uᴴ * (Aᴴ * U)) * G.ρHalf * (Uᴴ * A * U)) := by
            apply congrArg Matrix.trace; simp only [mul_assoc]
  have hS_eq : ∀ A : QubitOp N,
      mssThermalSize G' A = mssThermalSize G (Uᴴ * A * U) := by
    intro A
    have hhs_unit : ∀ M : QubitOp N,
        hsInner (U * M * Uᴴ) (totalSizeOp (U * M * Uᴴ)) = hsInner M (totalSizeOp M) := by
      intro M
      have hconj := hsize (U * M * Uᴴ)
      have hback : Uᴴ * (U * M * Uᴴ) * U = M := by
        calc Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by simp only [mul_assoc]
          _ = M := by rw [hUL, one_mul, mul_one]
      have hts : totalSizeOp (U * M * Uᴴ) = U * totalSizeOp M * Uᴴ := by
        have h1 : totalSizeOp M = Uᴴ * totalSizeOp (U * M * Uᴴ) * U := by
          rw [← hback]; exact hconj
        calc totalSizeOp (U * M * Uᴴ)
            = (U * Uᴴ) * totalSizeOp (U * M * Uᴴ) * (U * Uᴴ) := by rw [hUR, one_mul, mul_one]
          _ = U * (Uᴴ * totalSizeOp (U * M * Uᴴ) * U) * Uᴴ := by simp only [mul_assoc]
          _ = U * totalSizeOp M * Uᴴ := by rw [← h1]
      rw [hts]
      unfold hsInner
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc Matrix.trace (U * (Mᴴ * Uᴴ) * (U * totalSizeOp M * Uᴴ))
          = Matrix.trace (U * (Mᴴ * (Uᴴ * U) * totalSizeOp M) * Uᴴ) := by
              apply congrArg Matrix.trace; simp only [mul_assoc]
        _ = Matrix.trace (U * (Mᴴ * totalSizeOp M) * Uᴴ) := by rw [hUL, mul_one]
        _ = Matrix.trace (Uᴴ * U * (Mᴴ * totalSizeOp M)) := by
              rw [Matrix.trace_mul_cycle]; apply congrArg Matrix.trace; simp only [mul_assoc]
        _ = Matrix.trace (Mᴴ * totalSizeOp M) := by rw [hUL, one_mul]
    have hj_eq : jBeta G'.ρQuarter A = U * jBeta G.ρQuarter (Uᴴ * A * U) * Uᴴ := by
      unfold jBeta
      rw [hG'quarter]
      simp only [mul_assoc]
    unfold mssThermalSize
    rw [hj_eq, hG'half, hhs_unit, hhs_unit]
  unfold lambdaMSS
  apply csSup_le
  · refine ⟨0, 1, ?_, ?_, (mssThermalSize_one G').symm⟩
    · have h1 : (1 : QubitOp N) = pauliString (fun _ ↦ 0) := by
        unfold pauliString
        have h0 : (fun _ : Fin N ↦ pauliMat 0) = (fun _ : Fin N ↦ (1 : Mat2)) := by
          funext _; ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
        rw [h0, kronOp_one]
      rw [h1]
      exact Submodule.subset_span ⟨fun _ ↦ 0, by simp [stringWeight], rfl⟩
    · unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      rw [Matrix.conjTranspose_one, mul_one, mul_one, G'.sq_half, G'.trace_one,
        Complex.one_re]
  · rintro r ⟨A, hA_mem, hA_norm, rfl⟩
    rw [hS_eq A]
    apply le_csSup
    · refine ⟨(N : ℝ), ?_⟩
      rintro x ⟨B, _, hBnorm, rfl⟩
      unfold mssThermalSize
      have hle := (totalSizeOp_bounds (jBeta G.ρQuarter B)).2
      have hbg := (totalSizeOp_bounds G.ρHalf).1
      have hhs : hsNormSq (jBeta G.ρQuarter B) = 1 := by
        unfold gibbsWightmanNormSq gibbsWightmanInner at hBnorm
        rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter] at hBnorm
        exact hBnorm
      unfold hsNormSq at hhs; rw [hhs, mul_one] at hle; linarith
    · exact ⟨Uᴴ * A * U, hfilt A hA_mem, (hnorm_eq A).symm.trans hA_norm, rfl⟩

/-- **Proposition 4.3 — Full General Product-State Bound via Local Unitary Invariance (Item #13)**:
For ANY local unitary `U = ⨂_{x=1}^N u_x` and ANY Bloch-vector magnitudes `|m_x| ≤ mmax < 1`,
the rotated product state `ρ = U (⨂_x (I + m_x Z_x)/2) Uᴴ` satisfies
`lambdaMSS (rotatedProdGibbsData u huL huR m hm) s ≤ (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ))`. -/
theorem prop_4_3_lambdaMSS_general_product_state {N s : ℕ} {mmax : ℝ}
    (u : Fin N → Mat2) (huL : ∀ x, (u x)ᴴ * u x = 1) (huR : ∀ x, u x * (u x)ᴴ = 1)
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1) :
    lambdaMSS (rotatedProdGibbsData u huL huR m (fun x ↦ lt_of_le_of_lt (hm_le x) hmmax)) s ≤
      (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  have hm : ∀ x, |m x| < 1 := fun x ↦ lt_of_le_of_lt (hm_le x) hmmax
  have hUL : (kronOp u)ᴴ * kronOp u = 1 := by
    rw [kronOp_conjTranspose, kronOp_mul]
    have : (fun x ↦ (u x)ᴴ * u x) = fun _ ↦ 1 := funext huL
    rw [this, kronOp_one]
  have hUR : kronOp u * (kronOp u)ᴴ = 1 := by
    rw [kronOp_conjTranspose, kronOp_mul]
    have : (fun x ↦ u x * (u x)ᴴ) = fun _ ↦ 1 := funext huR
    rw [this, kronOp_one]
  have hle_G : lambdaMSS (rotatedProdGibbsData u huL huR m hm) s ≤
      lambdaMSS (prodGibbsData m hm) s :=
    lambdaMSS_le_of_unitary_conj
      (prodGibbsData m hm) (rotatedProdGibbsData u huL huR m hm) (kronOp u)
      hUL hUR
      (rotatedProdGibbsData_ρHalf u huL huR m hm)
      (rotatedProdGibbsData_ρQuarter u huL huR m hm)
      (totalSizeOp_localUnitary_conj u huL huR)
      (fun _ hA ↦ localUnitary_conj_mem_filtration u huL hA)
  exact le_trans hle_G (prop_4_3_lambdaMSS_product_state m hm_le hmmax)

end LocalUnitaryInvarianceLift

end KrylovChaos
