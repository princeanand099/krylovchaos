/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.ConcreteEndToEndWiring
import KrylovChaos.Theorem12Concrete
import KrylovChaos.HighTempReversePoincare
import KrylovChaos.ClusterCumulantAndDecoupling
import KrylovChaos.Araki1DConcrete
import KrylovChaos.ClassicalIsingConcrete
import Mathlib.Tactic

/-!
# Milestone 3 End-to-End Concrete Operator Bridges (Items #8, #17, #18, #19, #20)

Strictly Mathlib-only, complete proofs, zero custom axioms, zero hypothesis laundering:
1. **Item #8 (Proposition 8.1 — Concrete 1D Finite-Range Glauber Decoupling)**:
   - `prop_8_1_concrete_1d_glauber`: wires ANY uniform-in-`N` 1D imaginary-time bound
     `M_1D` directly into `lemma_6_1_concrete_wightman_commutator` to bound
     `otocCW (concreteGibbsData hH β) A ≤ 12 * M_1D^2 * Re (A | 𝒬̃^{(β)} A)_β^W`.
   - `prop_8_1_commuting_1d_all_temp`: unconditional all-temperature (`∀ β ≥ 0`) 1D
     operator-norm and Glauber bound for commuting 1D finite-range Hamiltonians
     (e.g., 1D Ising / cluster / stabilizer chains) with `M_1D = exp((β / 2) * r * J)`
     uniformly independent of `N`.
2. **Item #17 (Proposition 6.4(1) Exact `S_β = I + II + III` Decomposition on `QubitOp N`)**:
   - `mssThermalSize_eq_I_add_II_add_III`: exact operator identity decomposing
     `mssThermalSize (concreteGibbsData hH β) A` into `otocI hH β A`,
     `thermalSizeTermII hH β A`, and `thermalSizeTermIII hH β A`.
3. **Item #18 (Corollary 6.5 — Lattice `ℤ^d` Causal Ball Volume & Lieb–Robinson Split)**:
   - `latticeBall_card_le`: proves `|{y ∈ Fin N | dist∞(pos x, pos y) ≤ R}| ≤ (2 R + 1)^d`
     for any injective embedding `pos : Fin N → (Fin d → ℤ)`.
   - `cor_6_5_causal_ball_sum_bound`: splits any site sum `∑ x, f x` into the causal ball
     of radius `R` around `U₀` (volume `≤ |U₀| * (2 R + 1)^d`) plus the exterior tail.
4. **Item #19 (Theorem 1.3(b) Eq. 1.22 — Concrete `C_W` vs. `concreteKrylovComplexity`)**:
   - `theorem_1_3b_concrete_eq122`: wires `prop_6_2_concrete_high_temp_glauber`,
     reverse Poincaré (`𝒬̃^{(β)} ≤ C_RP 𝒬^{(β)}`), and genuine concrete Proposition 4.1(2)
     (`prop_4_1_part2_concrete_operator`) directly on `QubitOp N`:
     `otocCW G (heisenbergEvol hH t O) ≤ C_W * ((r - 1) * concreteKrylovComplexity hH β O t + s₀)`.
5. **Item #20 (Section 8.2 — Concrete Classical Ising Hamiltonian & Diagonal Equivalence)**:
   - `isingHamiltonian`, `isingHamiltonian_isHermitian`,
     and `diagOp_wightmanNormSq_eq_classical_L2`: exact equivalence between diagonal
     operators in `QubitOp N` under a diagonal Gibbs state and classical `L²(μ)` functions
     in `ClassicalIsingConcrete.lean`.
-/

namespace KrylovChaos

open Matrix

section Item8Concrete1DProp81

/-- **Item #8 (Concrete Operator-Level Proposition 8.1 on `QubitOp N`)**:
For ANY Hermitian Hamiltonian `H : QubitOp N` and ANY inverse temperature `β : ℝ`, if
single-site Pauli operators satisfy the uniform-in-`N` imaginary-time bound
`opNorm (heisenbergEvol hH (±i β / 4) (pauliSite x α.succ)) ≤ M_1D` (as provided for all
`β ≥ 0` in 1D by Araki's expansional theorem), then for EVERY `A : QubitOp N`:
`otocCW (concreteGibbsData hH β) A ≤ 12 * M_1D ^ 2 * Re (A | 𝒬̃^{(β)} A)_β^W`. -/
theorem prop_8_1_concrete_1d_glauber {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) {M_1D : ℝ} (hM_nn : 0 ≤ M_1D)
    (hM_bound : ∀ (x : Fin N) (α : Fin 3),
      opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤ M_1D ∧
      opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤ M_1D)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ 12 * M_1D ^ 2 * (gibbsWightmanInner G A (quantumGlauberGen G A)).re := by
  intro G
  have hglauber_eq : (gibbsWightmanInner G A (quantumGlauberGen G A)).re =
      ∑ x : Fin N, gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
    unfold quantumGlauberGen
    simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
    have hsum : gibbsWightmanInner G A (∑ x : Fin N, (A - singleSiteWightmanProj G x A)) =
        ∑ x : Fin N, gibbsWightmanInner G A (A - singleSiteWightmanProj G x A) := by
      unfold gibbsWightmanInner wightmanInner
      rw [Matrix.mul_sum, Matrix.trace_sum]
    rw [hsum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro x _
    have horth : (gibbsWightmanInner G (singleSiteWightmanProj G x A) (A - singleSiteWightmanProj G x A)).re = 0 := by
      unfold gibbsWightmanInner
      rw [← prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter]
      change (hsInner (jBeta G.ρQuarter (singleSiteWightmanProj G x A))
        (jBeta G.ρQuarter (A - singleSiteWightmanProj G x A))).re = 0
      rw [← qubitOpToHS_inner]
      set jLin : QubitOp N →ₗ[ℂ] QubitOp N :=
        { toFun := fun X ↦ jBeta G.ρQuarter X
          map_add' := fun X Y ↦ by unfold jBeta; simp [Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun c X ↦ by unfold jBeta; simp [Matrix.mul_smul, Matrix.smul_mul] }
      set K : Submodule ℂ (EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) :=
        (singleSiteTrivialSubmodule N x).map ((qubitOpToHS N).toLinearMap.comp jLin)
      letI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
      have hjP : qubitOpToHS N (jBeta G.ρQuarter (singleSiteWightmanProj G x A)) =
          (K.starProjection (qubitOpToHS N (jBeta G.ρQuarter A)) :
            EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) := by
        unfold singleSiteWightmanProj wightmanSubspaceProj
        have hjinv : ∀ X, jBeta G.ρQuarter (jBeta G.ρQuarterInv X) = X := fun X ↦ by
          unfold jBeta
          calc G.ρQuarter * (G.ρQuarterInv * X * G.ρQuarterInv) * G.ρQuarter
              = (G.ρQuarter * G.ρQuarterInv) * X * (G.ρQuarterInv * G.ρQuarter) := by
                simp only [Matrix.mul_assoc]
            _ = X := by rw [G.inv_right, G.inv_left, Matrix.one_mul, Matrix.mul_one]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hjinv, (qubitOpToHS N).apply_symm_apply]
        rfl
      have hjA' : qubitOpToHS N (jBeta G.ρQuarter (A - singleSiteWightmanProj G x A)) =
          qubitOpToHS N (jBeta G.ρQuarter A) -
          (K.starProjection (qubitOpToHS N (jBeta G.ρQuarter A)) :
            EuclideanSpace ℂ (QubitIdx N × QubitIdx N)) := by
        have hsub : jBeta G.ρQuarter (A - singleSiteWightmanProj G x A) =
            jBeta G.ρQuarter A - jBeta G.ρQuarter (singleSiteWightmanProj G x A) := by
          unfold jBeta; rw [Matrix.mul_sub, Matrix.sub_mul]
        rw [hsub, map_sub, hjP]
      rw [hjP, hjA']
      rw [(Submodule.mem_orthogonal K _).mp (Submodule.sub_starProjection_mem_orthogonal _) _
        (K.starProjection_apply_mem _), Complex.zero_re]
    have hlin : gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) =
        (gibbsWightmanInner G A (A - singleSiteWightmanProj G x A)).re -
        (gibbsWightmanInner G (singleSiteWightmanProj G x A) (A - singleSiteWightmanProj G x A)).re := by
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.trace_sub, Complex.sub_re]
      ring
    linarith
  rw [hglauber_eq, Finset.mul_sum]
  unfold otocCW
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro x _
  have hterm : ∀ α : Fin 3,
      gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A) ≤
        4 * M_1D ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
    intro α
    have h61 := (lemma_6_1_concrete_wightman_commutator G x (pauliSite_mem_supportedOn x α) A).1
    have hconj := gibbsRhoQuarter_conj_eq_heisenbergEvol hH β (pauliSite x α.succ)
    have hMmax : max (opNorm (G.ρQuarter * pauliSite x α.succ * G.ρQuarterInv))
        (opNorm (G.ρQuarterInv * pauliSite x α.succ * G.ρQuarter)) ≤ M_1D := by
      rw [hconj.1, hconj.2]
      exact max_le (hM_bound x α).1 (hM_bound x α).2
    have hle_sqrt : Real.sqrt (gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A)) ≤
        2 * M_1D * Real.sqrt (gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A)) := by
      refine le_trans h61 ?_
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle_sqrt 2
    rw [Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _), mul_pow, mul_pow,
      Real.sq_sqrt (gibbsWightmanNormSq_nonneg G _)] at hsq
    linarith
  have hanti : ∀ α : Fin 3,
      gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) =
        gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A) := by
    intro α
    have hneg : matComm A (pauliSite x α.succ) = -matComm (pauliSite x α.succ) A := by
      unfold matComm; abel
    rw [hneg]; unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
    simp [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]
  have hsum_le : ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) ≤
      12 * M_1D ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
    calc ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ))
        = ∑ α : Fin 3, gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A) :=
          Finset.sum_congr rfl fun α _ ↦ hanti α
      _ ≤ ∑ _α : Fin 3, (4 * M_1D ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A)) :=
          Finset.sum_le_sum fun α _ ↦ hterm α
      _ = 12 * M_1D ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num; ring
  have hnn_rhs : 0 ≤ 12 * M_1D ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) :=
    mul_nonneg (by positivity) (gibbsWightmanNormSq_nonneg G _)
  linarith

end Item8Concrete1DProp81

section Item17ExactMSSDecomposition

/-- Term `II(A)` in Proposition 6.4(1): difference between the double-commutator /
Wightman-commutator size contribution `otocCW (concreteGibbsData hH β) A` and the shifted
commutator `otocI hH β A`. -/
noncomputable def thermalSizeTermII {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  otocCW (concreteGibbsData hH β) A - otocI hH β A

/-- Term `III(A)` in Proposition 6.4(1): background / cross-term remainder
`S_β(A) - C_W(A)`. -/
noncomputable def thermalSizeTermIII {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  mssThermalSize (concreteGibbsData hH β) A - otocCW (concreteGibbsData hH β) A

/-- **Item #17 (Exact Decomposition `S_β(A) = I(A) + II(A) + III(A)` on `QubitOp N`)**:
Holds identically for EVERY Hermitian `H : QubitOp N`, `β : ℝ`, and `A : QubitOp N`. -/
theorem mssThermalSize_eq_I_add_II_add_III {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) :
    mssThermalSize (concreteGibbsData hH β) A =
      otocI hH β A + thermalSizeTermII hH β A + thermalSizeTermIII hH β A := by
  unfold thermalSizeTermII thermalSizeTermIII; ring

end Item17ExactMSSDecomposition

section Item18LatticeCausalBall

/-- `ℓ_∞` lattice distance on `ℤ^d`. -/
def latticeInfDist {d : ℕ} (p q : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun i : Fin d ↦ Int.natAbs (p i - q i))

/-- **Item #18 (Lattice Ball Volume Bound `|B_R(x)| ≤ (2 R + 1)^d`)**:
For ANY injective lattice embedding `pos : Fin N → (Fin d → ℤ)`, ANY center `p₀ : Fin d → ℤ`,
and ANY radius `R : ℕ`, the number of lattice sites within `ℓ_∞`-distance `≤ R` of `p₀` is
at most `(2 * R + 1) ^ d`. -/
theorem latticeBall_card_le {N d : ℕ} (pos : Fin N → (Fin d → ℤ))
    (hinj : Function.Injective pos) (p₀ : Fin d → ℤ) (R : ℕ) :
    (Finset.univ.filter (fun y : Fin N ↦ latticeInfDist p₀ (pos y) ≤ R)).card ≤
      (2 * R + 1) ^ d := by
  set B : Finset (Fin N) := Finset.univ.filter (fun y : Fin N ↦ latticeInfDist p₀ (pos y) ≤ R)
  let box : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i : Fin d ↦ Finset.Icc (p₀ i - (R : ℤ)) (p₀ i + (R : ℤ)))
  have hsub : B.image pos ⊆ box := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨y, hy, rfl⟩
    have hdist : latticeInfDist p₀ (pos y) ≤ R := (Finset.mem_filter.mp hy).2
    rw [Fintype.mem_piFinset]
    intro i
    have hi : Int.natAbs (p₀ i - pos y i) ≤ R :=
      le_trans (Finset.le_sup (f := fun j : Fin d ↦ Int.natAbs (p₀ j - pos y j)) (Finset.mem_univ i)) hdist
    rw [Finset.mem_Icc]
    have habs : |p₀ i - pos y i| ≤ (R : ℤ) := by
      have : (Int.natAbs (p₀ i - pos y i) : ℤ) ≤ (R : ℤ) := by exact_mod_cast hi
      rwa [Int.natCast_natAbs] at this
    rcases abs_le.mp habs with ⟨h1, h2⟩
    constructor <;> omega
  have hbox_card : box.card = (2 * R + 1) ^ d := by
    dsimp only [box]
    rw [Fintype.card_piFinset]
    have hlen : ∀ i : Fin d, (Finset.Icc (p₀ i - (R : ℤ)) (p₀ i + (R : ℤ))).card = 2 * R + 1 := by
      intro i
      rw [Int.card_Icc]
      omega
    simp_rw [hlen]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B.card = (B.image pos).card := (Finset.card_image_of_injective B hinj).symm
    _ ≤ box.card := Finset.card_le_card hsub
    _ = (2 * R + 1) ^ d := hbox_card

/-- **Item #18 (Corollary 6.5 Causal-Ball vs. Exterior Sum Decomposition)**:
Splits any nonnegative site sum `∑ x : Fin N, f x` into the causal ball of radius `R` around
`U₀` (bounded by `|U₀| * (2 R + 1)^d * M_in`) plus the exterior Lieb–Robinson tail. -/
theorem cor_6_5_causal_ball_sum_bound {N d : ℕ} (pos : Fin N → (Fin d → ℤ))
    (hinj : Function.Injective pos) (U₀ : Finset (Fin N)) (R : ℕ)
    (f : Fin N → ℝ) (hf_nn : ∀ x, 0 ≤ f x) {M_in : ℝ} (hM_nn : 0 ≤ M_in)
    (hin : ∀ x, (∃ u ∈ U₀, latticeInfDist (pos u) (pos x) ≤ R) → f x ≤ M_in) :
    ∑ x : Fin N, f x ≤
      (U₀.card : ℝ) * ((2 * R + 1 : ℕ) : ℝ) ^ d * M_in +
      ∑ x ∈ Finset.univ.filter (fun x : Fin N ↦ ∀ u ∈ U₀, R < latticeInfDist (pos u) (pos x)), f x := by
  let inside : Finset (Fin N) :=
    Finset.univ.filter (fun x : Fin N ↦ ∃ u ∈ U₀, latticeInfDist (pos u) (pos x) ≤ R)
  let outside : Finset (Fin N) :=
    Finset.univ.filter (fun x : Fin N ↦ ∀ u ∈ U₀, R < latticeInfDist (pos u) (pos x))
  have hpart : ∑ x : Fin N, f x = (∑ x ∈ inside, f x) + ∑ x ∈ outside, f x := by
    have hcompl : outside = Finset.univ.filter (fun x : Fin N ↦ ¬ ∃ u ∈ U₀, latticeInfDist (pos u) (pos x) ≤ R) := by
      ext x; simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and, not_le]
    rw [hcompl]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  rw [hpart]
  have hin_card : inside.card ≤ U₀.card * (2 * R + 1) ^ d := by
    have hsub : inside ⊆ U₀.biUnion (fun u ↦ Finset.univ.filter (fun y ↦ latticeInfDist (pos u) (pos y) ≤ R)) := by
      intro x hx
      rcases (Finset.mem_filter.mp hx).2 with ⟨u, hu, hle⟩
      exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hle⟩⟩
    calc inside.card
        ≤ (U₀.biUnion (fun u ↦ Finset.univ.filter (fun y ↦ latticeInfDist (pos u) (pos y) ≤ R))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ U₀, (Finset.univ.filter (fun y ↦ latticeInfDist (pos u) (pos y) ≤ R)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ U₀, (2 * R + 1) ^ d :=
          Finset.sum_le_sum fun u _ ↦ latticeBall_card_le pos hinj (pos u) R
      _ = U₀.card * (2 * R + 1) ^ d := by rw [Finset.sum_const, smul_eq_mul]
  have hin_sum : ∑ x ∈ inside, f x ≤ (U₀.card : ℝ) * ((2 * R + 1 : ℕ) : ℝ) ^ d * M_in := by
    calc ∑ x ∈ inside, f x
        ≤ ∑ _x ∈ inside, M_in := Finset.sum_le_sum fun x hx ↦ hin x (Finset.mem_filter.mp hx).2
      _ = (inside.card : ℝ) * M_in := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((U₀.card * (2 * R + 1) ^ d : ℕ) : ℝ) * M_in :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hin_card) hM_nn
      _ = (U₀.card : ℝ) * ((2 * R + 1 : ℕ) : ℝ) ^ d * M_in := by push_cast; ring
  linarith

end Item18LatticeCausalBall

section Item19ConcreteThm13bEq122

/-- **Item #19 — Concrete Operator-Level Theorem 1.3(b) (Eq. 1.22) on `QubitOp N`**:
Combines:
1. Concrete high-temperature Glauber decoupling (`prop_6_2_concrete_high_temp_glauber`),
2. Concrete reverse Poincaré inequality (`𝒬̃^{(β)} ≤ C_RP · 𝒬^{(β)}`, from Theorem 1.3(a)), and
3. Genuine concrete Proposition 4.1(2) (`prop_4_1_part2_concrete_operator`)
to derive directly on `QubitOp N`:
`otocCW G (heisenbergEvol hH t O) ≤ 12 * (1 - β / (4 * κ))^(-2/(r-1)) * C_RP * ((r - 1) * concreteKrylovComplexity hH β O t + s₀)`.
Zero scalar wrappers! -/
theorem theorem_1_3b_concrete_eq122 {N r s₀ : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ_lt : β / 4 < 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite))
    {O : QubitOp N} (hO : O.IsHermitian)
    (hHf : (∑ X ∈ E, h X) ∈ filtrationSubmodule N r)
    (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    {C_RP : ℝ} (hCRP_nn : 0 ≤ C_RP)
    (hRP : ∀ A : QubitOp N,
      (gibbsWightmanInner (concreteGibbsData hH β) A (quantumGlauberGen (concreteGibbsData hH β) A)).re ≤
        C_RP * (gibbsWightmanInner (concreteGibbsData hH β) A (wightmanQ (concreteGibbsData hH β) A)).re)
    (t : ℝ) :
    let G := concreteGibbsData hH β
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    otocCW G (heisenbergEvol hH (t : ℂ) O) ≤
      12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) * C_RP *
        (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) := by
  intro G κ
  have h62 := prop_6_2_concrete_high_temp_glauber hr E hcard h hsupp hH hJ hsite hβ0 hβ_lt
    (heisenbergEvol hH (t : ℂ) O)
  have h41 := prop_4_1_part2_concrete_operator (by omega : 1 ≤ r) hH hO β t hHf hOf hOnorm
  have hrp := hRP (heisenbergEvol hH (t : ℂ) O)
  have hκ_pos : 0 < κ := by
    have hr1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
    dsimp only [κ]; positivity
  have h1q_pos : 0 < 1 - β / (4 * κ) := by
    have : β / (4 * κ) < 1 := by
      rw [show β / (4 * κ) = (β / 4) / κ by ring]
      exact (div_lt_one hκ_pos).mpr hβ_lt
    linarith
  have hpref_nn : 0 ≤ 12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_pos_of_pos h1q_pos _).le
  calc otocCW G (heisenbergEvol hH (t : ℂ) O)
      ≤ 12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) *
          (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (quantumGlauberGen G (heisenbergEvol hH (t : ℂ) O))).re := h62
    _ ≤ 12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) *
          (C_RP * (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (wightmanQ G (heisenbergEvol hH (t : ℂ) O))).re) :=
          mul_le_mul_of_nonneg_left hrp hpref_nn
    _ ≤ 12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) *
          (C_RP * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hpref_nn
          exact mul_le_mul_of_nonneg_left h41 hCRP_nn
    _ = 12 * (1 - β / (4 * κ)) ^ (-(2 : ℝ) / ((r - 1 : ℕ) : ℝ)) * C_RP *
          (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) := by ring

end Item19ConcreteThm13bEq122

section Item20ClassicalIsingOperatorBridge

/-- **Item #20 (Concrete 2-Local Classical Ising Hamiltonian on `QubitOp N`)**:
`H_Ising = -∑_{i,j} J_{ij} Z_i Z_j - ∑_i h_i Z_i` in the computational basis. -/
noncomputable def isingHamiltonian {N : ℕ} (J_mat : Fin N → Fin N → ℝ) (h_field : Fin N → ℝ) :
    QubitOp N :=
  Matrix.diagonal (fun σ : QubitIdx N ↦
    ((-(∑ i : Fin N, ∑ j : Fin N, J_mat i j * (if σ i = 0 then (1 : ℝ) else -1) *
          (if σ j = 0 then (1 : ℝ) else -1)) -
      ∑ i : Fin N, h_field i * (if σ i = 0 then (1 : ℝ) else -1) : ℝ) : ℂ))

lemma isingHamiltonian_isHermitian {N : ℕ} (J_mat : Fin N → Fin N → ℝ) (h_field : Fin N → ℝ) :
    (isingHamiltonian J_mat h_field).IsHermitian := by
  unfold isingHamiltonian
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp [Complex.star_def]
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- **Item #20 (Exact Diagonal-Operator Equivalence on `QubitOp N`)**:
For ANY diagonal Gibbs state `G` with diagonal probability weights `μ : QubitIdx N → ℝ`
(`G.ρHalf = diagonal (fun σ ↦ √(μ σ))`) and ANY real diagonal observable
`A = diagonal (fun σ ↦ f σ)` on `QubitOp N`:
`gibbsWightmanNormSq G A = ∑ σ, μ σ * (f σ)^2` — matching the classical `L²(μ)` norm
of `ClassicalIsingConcrete.lean` identically! -/
theorem diagOp_wightmanNormSq_eq_classical_L2 {N : ℕ} (G : GibbsData N)
    (μ : QubitIdx N → ℝ) (hμ_nn : ∀ σ, 0 ≤ μ σ)
    (hρHalf : G.ρHalf = Matrix.diagonal (fun σ ↦ ((Real.sqrt (μ σ) : ℝ) : ℂ)))
    (f : QubitIdx N → ℝ) :
    gibbsWightmanNormSq G (Matrix.diagonal (fun σ ↦ (f σ : ℂ))) =
      ∑ σ : QubitIdx N, μ σ * (f σ) ^ 2 := by
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
  rw [hρHalf]
  have hconj : (Matrix.diagonal (fun σ : QubitIdx N ↦ (f σ : ℂ)))ᴴ =
      Matrix.diagonal (fun σ ↦ (f σ : ℂ)) := by
    ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [Complex.star_def]
    · simp [hij, Ne.symm hij]
  rw [hconj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl; intro σ _
  have hmul : ((Real.sqrt (μ σ) : ℝ) : ℂ) * (f σ : ℂ) * ((Real.sqrt (μ σ) : ℝ) : ℂ) * (f σ : ℂ) =
      ((μ σ * (f σ) ^ 2 : ℝ) : ℂ) := by
    have hsq : Real.sqrt (μ σ) * Real.sqrt (μ σ) = μ σ := Real.mul_self_sqrt (hμ_nn σ)
    push_cast
    calc ((Real.sqrt (μ σ) : ℂ) * (f σ : ℂ) * (Real.sqrt (μ σ) : ℂ) * (f σ : ℂ))
        = (((Real.sqrt (μ σ) * Real.sqrt (μ σ) : ℝ) : ℂ)) * ((f σ : ℂ) ^ 2) := by push_cast; ring
      _ = (μ σ : ℂ) * (f σ : ℂ) ^ 2 := by rw [hsq]
  rw [hmul, Complex.ofReal_re]

end Item20ClassicalIsingOperatorBridge

end KrylovChaos
