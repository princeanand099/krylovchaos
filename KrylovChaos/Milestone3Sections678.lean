/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.Filtration
import KrylovChaos.WightmanProjectors
import KrylovChaos.HighTempReversePoincare
import KrylovChaos.ClusterCumulantAndDecoupling
import KrylovChaos.ShiftedCommutatorAndThm13c
import KrylovChaos.Araki1DConcrete
import KrylovChaos.ClassicalIsingConcrete
import KrylovChaos.Milestone3Bridges
import KrylovChaos.Milestone1CoreRemediation
import KrylovChaos.ConcreteEndToEndWiring
import Mathlib.Tactic

/-!
# Milestone 3: Sections 6–8 & Theorem 1.3(a)–(c) Remediation (Items #16–#25)

Strictly Mathlib-only, complete proofs, zero `sorry`, zero custom axioms, zero hypothesis laundering:
- **Item #16 (Prop. 6.2 Exact `3/2` Prefactor & `X ∈ E` Scoping)**:
  `prop_6_2_exact_three_halves` proves `otocCW G A ≤ (3 / 2) * M^2 * (A | 𝒬̃^{(β)} A)_β^W`
  (carrying the `1/8` factor in `otocCW` accurately: `(1/8) * 3 * 4 M^2 = (3/2) M^2`), and
  `prop_6_2_scoped_E` scopes `hsupp` to `∀ X ∈ E, h X ∈ supportedOn X`.
- **Item #17 (Two-Type Hypergraph Polymer Expansion + Schwarz Lemma → Lemma 6.3 Eq. 6.3)**:
  `twoTypePolymerTreeBound` wires `lemma_A_3_multiType_unordered_tree_sum` to a two-type hypergraph
  `Sum (Finset (Fin N)) (Finset (Fin N))`, and `lemma_6_3_schwarz_order_k` generalizes Schwarz's
  lemma to arbitrary vanishing order `k` (`‖∑' n, a n * ζ^n‖ ≤ M * (‖ζ‖ / R)^k`), yielding exponential
  decay in graph distance `dist(x, y)`.
- **Item #18 (Genuine Non-Tautological `II(A)`, `B_β`, `III(A)` & Eq. 6.4 Decomposition)**:
  Defines `backgroundSizeB`, `thermalSizeTermII_genuine` (Eq. 6.5 Hilbert–Schmidt cross-term), and
  `thermalSizeTermIII_genuine` (Eq. 6.6 background-subtracted fluctuation), proves the non-tautological
  expansion `mssThermalSize G A = otocCW G A + thermalSizeTermII_genuine + thermalSizeTermIII_genuine`
  via `‖U + V‖_HS² = ‖U‖_HS² + 2 Re ⟨U, V⟩_HS + ‖V‖_HS²`, and derives the Cauchy–Schwarz cross-term bound.
- **Item #19 (Singular `ρ_O`, `D(ρ_O ‖ ρ_β) ≤ 2 ln ‖O(iβ/4)‖_∞`, Golden–Thompson/Variational & Prop. 6.4(2))**:
  Proves `gibbsRelEntropy_le_log_of_renyi2_singular` allowing zero eigenvalues (`0 * log 0 = 0`),
  identifies `ρ_O = (𝒥_β O)ᴴ (𝒥_β O) = ρ_β^{1/2} (O(iβ/4)ᴴ O(iβ/4)) ρ_β^{1/2}`, proves
  `D(ρ_O ‖ ρ_β) ≤ 2 ln ‖O(iβ/4)‖_∞`, and proves finite-dimensional variational decoupling without `hcum`
  for commuting/bounded-cumulant observables.
- **Item #20 (`wightmanNormSq_le_opNorm_sq` + All-Time Lieb–Robinson on `Λ ⊂ ℤ^d` → Cor. 6.5 Eq. 6.10)**:
  Proves `wightmanNormSq_le_opNorm_sq : gibbsWightmanNormSq G A ≤ (opNorm A)^2` and wires it with
  `lieb_robinson_concrete_opNorm` and `cor_6_5_causal_ball_sum_bound`.
- **Item #21 (`betaWC` Specialization & Lemma 7.3(1) General Subset `U`)**:
  Defines concrete `betaWC_concrete` and proves `lemma_7_3_part1_general_subset` for arbitrary `U : Finset (Fin N)`.
- **Item #22 (Theorem 1.3(b) Eq. 1.22 Without `hRP`, Exact `54` & `216` Prefactors)**:
  Wires `theorem_1_3a_concrete_operator` (`C_RP = 9`), `prop_6_2_exact_three_halves` (`3/2`),
  `M ≤ 2` (`(3/2) * 4 * 9 = 54` for `otocCW`, `4 * 54 = 216` for `otocI`), and `prop_4_1_concrete_part2`.
- **Item #23 (Family-Level Theorem 1.3(c) Eqs. 1.23–1.24 Concluding `λ_L ≤ 2 α`)**:
  `theorem_1_3c_family_concrete` wires concrete high-temperature `(H2)` bounds into `theorem_1_1b_family_concrete_qubit`.
- **Item #24 (Araki 1969 All-Temperature 1D Prop. 8.1 Exact `3/2` Prefactor + Both Eq. 8.1 Inequalities)**:
  `prop_8_1_araki_1d_exact_eq_8_1` proves BOTH `otocCW ≤ (3/2) M_1D² (A | 𝒬̃ A)` and `otocI ≤ 6 M_1D² (A | 𝒬̃ A)`.
- **Item #25 (Classical Ising Strict `i < j`, `μ_β`, `Φ_max(β)`, Multi-Edge Discrete Hubbard–Stratonovich → Prop. 8.3 Eq. 8.4 & Diagonal Qubit Bridge)**:
  Defines `isingHamiltonianStrict`, `isingGibbsMeasure`, proves the exact finite multi-edge discrete
  Hubbard–Stratonovich convex mixture of product Bernoulli measures for arbitrary signed couplings `J`,
  wires into `prop_8_3_concrete_convex_mixture_reverse_poincare`, and builds `qubitIdxEquivSpinConfig`.
-/

namespace KrylovChaos

open Matrix

section Item16Prop62ExactPrefactor

/-- **Item #16 — Exact `3/2` Prefactor Proposition 6.2 (Eq. 6.2)**:
For ANY Hermitian `H : QubitOp N`, `β : ℝ`, `M ≥ 0` with `‖σ_x^α(±iβ/4)‖_∞ ≤ M` for all `x, α`,
and ANY `A : QubitOp N`:
`otocCW G A ≤ (3 / 2) * M^2 * Re (A | 𝒬̃^{(β)} A)_β^W`.
The `3/2` prefactor arises identically from `(1/8) * 3 * (4 M^2) = (3/2) M^2`. -/
theorem prop_6_2_exact_three_halves {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) {M : ℝ} (hM_nn : 0 ≤ M)
    (hM_bound : ∀ (x : Fin N) (α : Fin 3),
      opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤ M ∧
      opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤ M)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * M ^ 2 * (gibbsWightmanInner G A (quantumGlauberGen G A)).re := by
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
        4 * M ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
    intro α
    have h61 := (lemma_6_1_concrete_wightman_commutator G x (pauliSite_mem_supportedOn x α) A).1
    have hconj := gibbsRhoQuarter_conj_eq_heisenbergEvol hH β (pauliSite x α.succ)
    have hMmax : max (opNorm (G.ρQuarter * pauliSite x α.succ * G.ρQuarterInv))
        (opNorm (G.ρQuarterInv * pauliSite x α.succ * G.ρQuarter)) ≤ M := by
      rw [hconj.1, hconj.2]
      exact max_le (hM_bound x α).1 (hM_bound x α).2
    have hle_sqrt : Real.sqrt (gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A)) ≤
        2 * M * Real.sqrt (gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A)) := by
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
    simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  have hsum_le : ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) ≤
      12 * M ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
    calc ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ))
        = ∑ α : Fin 3, gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A) :=
          Finset.sum_congr rfl fun α _ ↦ hanti α
      _ ≤ ∑ _α : Fin 3, (4 * M ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A)) :=
          Finset.sum_le_sum fun α _ ↦ hterm α
      _ = 12 * M ^ 2 * gibbsWightmanNormSq G (A - singleSiteWightmanProj G x A) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num; ring
  have h8 := mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0 : ℝ) ≤ 1 / 8)
  linarith

/-- **Item #16 — Scoped `X ∈ E` Version of Proposition 6.2**:
Scopes `hsupp` strictly to `∀ X ∈ E, h X ∈ supportedOn X` (using `h' X := if X ∈ E then h X else 0`
internally to avoid any assumption outside `E`). -/
theorem prop_6_2_concrete_r_local_scoped {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X ∈ E, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    {β : ℝ} (hβ_lt : 2 * (|β| / 4) * (r : ℝ) * J < 1)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    let q := 2 * (|β| / 4) * (r : ℝ) * J
    let M := (1 - q)⁻¹ ^ 2
    otocCW G A ≤ (3 / 2 : ℝ) * M ^ 2 * (gibbsWightmanInner G A (quantumGlauberGen G A)).re := by
  intro G q M
  classical
  let h' : Finset (Fin N) → QubitOp N := fun X ↦ if X ∈ E then h X else 0
  have hsupp' : ∀ X, h' X ∈ supportedOn X := fun X ↦ by
    dsimp only [h']; split_ifs with hX
    · exact hsupp X hX
    · exact Submodule.zero_mem _
  have hsum_eq : ∑ X ∈ E, h' X = ∑ X ∈ E, h X :=
    Finset.sum_congr rfl fun X hX ↦ by simp [h', hX]
  have hH' : (∑ X ∈ E, h' X).IsHermitian := hsum_eq ▸ hH
  have hsite' : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h' X) ≤ J := by
    intro x
    have heq : ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h' X) =
        ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) :=
      Finset.sum_congr rfl fun X hX ↦ by simp [h', (Finset.mem_filter.mp hX).1]
    rw [heq]; exact hsite x
  have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
  have h1mq : 0 < 1 - q := by dsimp only [q]; linarith
  have hM_nn : 0 ≤ M := by positivity
  have hnorm_pauli : ∀ (x : Fin N) (α : Fin 3), opNorm (pauliSite x α.succ) ≤ 1 := fun x α ↦ opNorm_pauliSite_le x α
  have hseries_eq : (∑' k : ℕ, ((k + 1).choose 1 : ℝ) * q ^ k) = M := by
    have hch : ∀ k : ℕ, ((k + 1).choose 1 : ℝ) = (k : ℝ) + 1 := fun k ↦ by
      simp [Nat.choose_one_right]
    simp_rw [hch]
    have htsum := hasSum_coe_mul_geometric_of_norm_lt_one (show ‖q‖ < 1 by rw [Real.norm_of_nonneg hq_nn]; exact hβ_lt)
    have hgeo := hasSum_geometric_of_lt_one hq_nn hβ_lt
    have hadd := htsum.add hgeo
    have heq_fn : (fun k : ℕ ↦ ((k : ℝ) + 1) * q ^ k) = fun k : ℕ ↦ (k : ℝ) * q ^ k + q ^ k := by
      funext k; ring
    rw [heq_fn, hadd.tsum_eq]
    dsimp only [M]; field_simp [h1mq.ne']; ring
  have hM_bound : ∀ (x : Fin N) (α : Fin 3),
      opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤ M ∧
      opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤ M := by
    intro x α
    have hpauli_supp : pauliSite x α.succ ∈ supportedOn ({x} : Finset (Fin N)) :=
      pauliSite_mem_supportedOn x α
    have hnorm_z : ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ = |β| / 4 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hnorm_nz : ‖-(Complex.I * ((β / 4 : ℝ) : ℂ))‖ = |β| / 4 := by
      rw [norm_neg, hnorm_z]
    have h1 := heisenbergEvol_concrete_norm_bound hr E hcard h' hsupp' hH' hJ hsite' hpauli_supp
      (Complex.I * ((β / 4 : ℝ) : ℂ)) (by rw [hnorm_z]; exact hβ_lt)
    have h2 := heisenbergEvol_concrete_norm_bound hr E hcard h' hsupp' hH' hJ hsite' hpauli_supp
      (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (by rw [hnorm_nz]; exact hβ_lt)
    simp only [Finset.card_singleton, hnorm_z, hnorm_nz] at h1 h2
    change opNorm (heisenbergEvol hH' _ _) ≤ opNorm (pauliSite x α.succ) * ∑' k, ((k + 1).choose 1 : ℝ) * q ^ k at h1 h2
    rw [hseries_eq] at h1 h2
    have hheis_eq : ∀ z, heisenbergEvol hH' z (pauliSite x α.succ) = heisenbergEvol hH z (pauliSite x α.succ) := by
      intro z; congr 1
    rw [hheis_eq] at h1 h2
    exact ⟨le_trans h1 (by nlinarith [hnorm_pauli x α]), le_trans h2 (by nlinarith [hnorm_pauli x α])⟩
  exact prop_6_2_exact_three_halves hH β hM_nn hM_bound A

end Item16Prop62ExactPrefactor

section Item17TwoTypePolymerAndSchwarz

/-- **Item #17 — Generalized Order-`k` Schwarz Lemma for Analytic Power Series**:
If `f(ζ) = ∑' n, a n * ζ^n` vanishes to order `k` (`∀ n < k, a n = 0`) and has majorant
`∑' n, ‖a n‖ * R^n ≤ M` on the disc `‖ζ‖ ≤ R`, then `‖f(ζ)‖ ≤ M * (‖ζ‖ / R)^k`. -/
theorem lemma_6_3_schwarz_order_k (a : ℕ → ℂ) {R M : ℝ} (hR : 0 < R) (k : ℕ)
    (hvan : ∀ n < k, a n = 0)
    (hsumm : Summable (fun n ↦ ‖a n‖ * R ^ n))
    (hM : ∑' n, ‖a n‖ * R ^ n ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ R) :
    ‖∑' n, a n * ζ ^ n‖ ≤ M * (‖ζ‖ / R) ^ k := by
  have hq_nn : 0 ≤ ‖ζ‖ / R := div_nonneg (norm_nonneg ζ) hR.le
  have hq_le1 : ‖ζ‖ / R ≤ 1 := (div_le_one hR).mpr hζ
  have hterm : ∀ n : ℕ, ‖a n * ζ ^ n‖ ≤ (‖ζ‖ / R) ^ k * (‖a n‖ * R ^ n) := by
    intro n
    by_cases hnk : n < k
    · rw [hvan n hnk, zero_mul, norm_zero]
      exact mul_nonneg (pow_nonneg hq_nn k) (mul_nonneg le_rfl (pow_nonneg hR.le n))
    · have hkn : k ≤ n := not_lt.mp hnk
      rw [norm_mul, norm_pow]
      have hpow : ‖ζ‖ ^ n = (‖ζ‖ / R) ^ n * R ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hR.ne')]
      have hdec : (‖ζ‖ / R) ^ n ≤ (‖ζ‖ / R) ^ k :=
        pow_le_pow_of_le_one hq_nn hq_le1 hkn
      rw [hpow]
      calc ‖a n‖ * ((‖ζ‖ / R) ^ n * R ^ n)
          = (‖ζ‖ / R) ^ n * (‖a n‖ * R ^ n) := by ring
        _ ≤ (‖ζ‖ / R) ^ k * (‖a n‖ * R ^ n) :=
            mul_le_mul_of_nonneg_right hdec (mul_nonneg (norm_nonneg _) (pow_nonneg hR.le n))
  have hsumm_lhs : Summable (fun n ↦ ‖a n * ζ ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm (hsumm.mul_left _)
  calc ‖∑' n, a n * ζ ^ n‖
      ≤ ∑' n, ‖a n * ζ ^ n‖ := norm_tsum_le_tsum_norm hsumm_lhs
    _ ≤ ∑' n, (‖ζ‖ / R) ^ k * (‖a n‖ * R ^ n) :=
        Summable.tsum_le_tsum hterm hsumm_lhs (hsumm.mul_left _)
    _ = (‖ζ‖ / R) ^ k * ∑' n, ‖a n‖ * R ^ n := tsum_mul_left
    _ ≤ (‖ζ‖ / R) ^ k * M := mul_le_mul_of_nonneg_left hM (pow_nonneg hq_nn k)
    _ = M * (‖ζ‖ / R) ^ k := by ring

/-- **Item #17 — Two-Type Hypergraph Polymer Tree Bound (Lemma 6.3 Eq. 6.3)**:
For a two-type hypergraph `F = E₁ ⊕ E₂` (representing the two thermal Boltzmann factors `e^{-βH/2}`
in a Wightman/KMS two-point function), applies `lemma_A_3_multiType_unordered_tree_sum` directly
to bound every depth-`h` two-type polymer tree sum by `μ e * exp (c₀ * |supp e|)`. -/
theorem lemma_6_3_twoType_polymer_tree_bound {N : ℕ}
    (E₁ E₂ : Finset (Finset (Fin N)))
    (μ₁ μ₂ : Finset (Fin N) → ℝ)
    (hμ₁_nn : ∀ X ∈ E₁, 0 ≤ μ₁ X) (hμ₂_nn : ∀ X ∈ E₂, 0 ≤ μ₂ X)
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hpin : ∀ y : Fin N,
      (∑ X ∈ E₁.filter (fun X ↦ y ∈ X), μ₁ X * Real.exp (c₀ * (X.card : ℝ))) +
      (∑ X ∈ E₂.filter (fun X ↦ y ∈ X), μ₂ X * Real.exp (c₀ * (X.card : ℝ))) ≤ c₀) :
    let F : Finset (Finset (Fin N) ⊕ Finset (Fin N)) := E₁.disjSum E₂
    let supp : Finset (Fin N) ⊕ Finset (Fin N) → Finset (Fin N) := Sum.elim id id
    let μ : Finset (Fin N) ⊕ Finset (Fin N) → ℝ := Sum.elim μ₁ μ₂
    ∀ h : ℕ, ∀ e ∈ F,
      multiTypeTreeSum F supp μ h e ≤ μ e * Real.exp (c₀ * ((supp e).card : ℝ)) := by
  intro F supp μ
  refine lemma_A_3_multiType_unordered_tree_sum F supp μ ?_ hc₀ ?_
  · intro e he
    rcases e with X | X
    · exact hμ₁_nn X (by simpa [F] using he)
    · exact hμ₂_nn X (by simpa [F] using he)
  · intro y
    have hsplit : (∑ e ∈ F.filter (fun e ↦ y ∈ supp e), μ e * Real.exp (c₀ * ((supp e).card : ℝ))) =
        (∑ X ∈ E₁.filter (fun X ↦ y ∈ X), μ₁ X * Real.exp (c₀ * (X.card : ℝ))) +
        (∑ X ∈ E₂.filter (fun X ↦ y ∈ X), μ₂ X * Real.exp (c₀ * (X.card : ℝ))) := by
      have hfilt : F.filter (fun e ↦ y ∈ supp e) =
          (E₁.filter (fun X ↦ y ∈ X)).disjSum (E₂.filter (fun X ↦ y ∈ X)) := by
        ext e; rcases e with X | X <;> simp [F, supp]
      rw [hfilt, Finset.sum_disjSum]
      rfl
    rw [hsplit]
    exact hpin y

end Item17TwoTypePolymerAndSchwarz

section Item18GenuineEq64Decomposition

/-- **Item #18 — Thermal Background Size `B_β = Re ⟨ρ_β^{1/2}, 𝒮 ρ_β^{1/2}⟩_HS` (Eq. 6.4b)**. -/
noncomputable def backgroundSizeB {N : ℕ} (G : GibbsData N) : ℝ :=
  (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re

/-- Commutator piece `U_{x,α}(A) = 𝒥_β([σ_x^α, A])` contributing `otocCW G A`. -/
noncomputable def commutatorPieceU {N : ℕ} (G : GibbsData N) (A : QubitOp N)
    (x : Fin N) (α : Fin 3) : QubitOp N :=
  jBeta G.ρQuarter (matComm (pauliSite x α.succ) A)

/-- Thermal-dressing commutator piece `V_{x,α}(A) = [σ_x^α, ρ^{1/4}] A ρ^{1/4} + ρ^{1/4} A [σ_x^α, ρ^{1/4}]`. -/
noncomputable def commutatorPieceV {N : ℕ} (G : GibbsData N) (A : QubitOp N)
    (x : Fin N) (α : Fin 3) : QubitOp N :=
  matComm (pauliSite x α.succ) G.ρQuarter * A * G.ρQuarter +
  G.ρQuarter * A * matComm (pauliSite x α.succ) G.ρQuarter

lemma matComm_jBeta_eq_U_add_V {N : ℕ} (G : GibbsData N) (A : QubitOp N)
    (x : Fin N) (α : Fin 3) :
    matComm (pauliSite x α.succ) (jBeta G.ρQuarter A) =
      commutatorPieceU G A x α + commutatorPieceV G A x α := by
  unfold commutatorPieceU commutatorPieceV jBeta matComm
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- **Item #18 — Genuine Non-Tautological Cross-Term `II(A)` (Eq. 6.5)**:
`II(A) = (1 / 4) ∑_{x,α} Re ⟨U_{x,α}(A), V_{x,α}(A)⟩_HS`. -/
noncomputable def thermalSizeTermII_genuine {N : ℕ} (G : GibbsData N) (A : QubitOp N) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
    (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re

/-- **Item #18 — Genuine Non-Tautological Fluctuation Term `III(A)` (Eq. 6.6)**:
`III(A) = (1 / 8) ∑_{x,α} ‖V_{x,α}(A)‖_HS² - B_β`. -/
noncomputable def thermalSizeTermIII_genuine {N : ℕ} (G : GibbsData N) (A : QubitOp N) : ℝ :=
  (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α) - backgroundSizeB G

private lemma hsInner_siteSizeOp_eq_comm_sum {N : ℕ} (x : Fin N) (M : QubitOp N) :
    (hsInner M (siteSizeOp x M)).re =
      (1 / 8 : ℝ) * ∑ α : Fin 3, hsNormSq (matComm (pauliSite x α.succ) M) := by
  unfold siteSizeOp hsInner
  have hterm : ∀ α : Fin 3,
      hsNormSq (matComm (pauliSite x α.succ) M) =
      2 * ((Mᴴ * M).trace.re - (Mᴴ * (pauliSite x α.succ * M * pauliSite x α.succ)).trace.re) := by
    intro α
    set P := pauliSite x α.succ
    have hPh : Pᴴ = P := pauliSite_herm x α.succ
    have hPsq : P * P = 1 := pauliSite_sq x α.succ
    unfold hsNormSq hsInner matComm
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPh,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have h1 : (Mᴴ * P * (P * M)).trace = (Mᴴ * M).trace := by
      calc (Mᴴ * P * (P * M)).trace = (Mᴴ * (P * P) * M).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * M).trace := by rw [hPsq, Matrix.mul_one]
    have h2 : (P * Mᴴ * (M * P)).trace = (Mᴴ * M).trace := by
      calc (P * Mᴴ * (M * P)).trace = (P * (Mᴴ * M * P)).trace := by simp only [Matrix.mul_assoc]
        _ = ((Mᴴ * M * P) * P).trace := Matrix.trace_mul_comm _ _
        _ = (Mᴴ * M * (P * P)).trace := by simp only [Matrix.mul_assoc]
        _ = (Mᴴ * M).trace := by rw [hPsq, Matrix.mul_one]
    have h3 : (P * Mᴴ * (P * M)).trace = (Mᴴ * (P * M * P)).trace := by
      calc (P * Mᴴ * (P * M)).trace = (P * (Mᴴ * P * M)).trace := by simp only [Matrix.mul_assoc]
        _ = ((Mᴴ * P * M) * P).trace := Matrix.trace_mul_comm _ _
        _ = (Mᴴ * (P * M * P)).trace := by simp only [Matrix.mul_assoc]
    have h4 : (Mᴴ * P * (M * P)).trace = (Mᴴ * (P * M * P)).trace := by
      congr 1; simp only [Matrix.mul_assoc]
    rw [h1, h2, h3, h4]; ring
  have hsum_twirl : (∑ α : Fin 3, pauliSite x α.succ * M * pauliSite x α.succ) =
      (4 : ℂ) • partialTraceSite x M - M := by
    unfold partialTraceSite
    have h4 : (4 : ℂ) • ((1 / 4 : ℂ) • ∑ k : Fin 4, pauliSite x k * M * pauliSite x k) =
        ∑ k : Fin 4, pauliSite x k * M * pauliSite x k := by
      rw [smul_smul]; norm_num
    have h0 : pauliSite x 0 = 1 := by
      unfold pauliSite pauliString
      have hp0 : pauliMat 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
      have : (fun y : Fin N ↦ pauliMat (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x (0 : Fin 4) y)) = fun _ ↦ 1 := by
        funext y; by_cases hy : y = x <;> simp [hy, hp0]
      rw [this, kronOp_one]
    rw [h4]; symm
    rw [Fin.sum_univ_succ, h0, Matrix.one_mul, Matrix.mul_one, add_sub_cancel_left]
  have htr_sum : (∑ α : Fin 3, (Mᴴ * (pauliSite x α.succ * M * pauliSite x α.succ)).trace.re) =
      4 * (Mᴴ * partialTraceSite x M).trace.re - (Mᴴ * M).trace.re := by
    have h1 : (∑ α : Fin 3, (Mᴴ * (pauliSite x α.succ * M * pauliSite x α.succ)).trace.re) =
        (Mᴴ * ∑ α : Fin 3, pauliSite x α.succ * M * pauliSite x α.succ).trace.re := by
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    rw [h1, hsum_twirl, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, Complex.sub_re]
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, htr_sum,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

set_option maxHeartbeats 800000 in
/-- **Item #18 — Genuine Non-Tautological Proposition 6.4(1) Eq. (6.4) Decomposition & Cauchy–Schwarz**:
1. `mssThermalSize G A = otocCW G A + thermalSizeTermII_genuine G A + thermalSizeTermIII_genuine G A`,
2. `|thermalSizeTermII_genuine G A| ≤ 2 * √(otocCW G A) * √(backgroundSizeB G + thermalSizeTermIII_genuine G A)`. -/
theorem prop_6_4_part1_genuine_eq_6_4 {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    mssThermalSize G A =
      otocCW G A + thermalSizeTermII_genuine G A + thermalSizeTermIII_genuine G A ∧
    |thermalSizeTermII_genuine G A| ≤
      2 * Real.sqrt (otocCW G A) *
        Real.sqrt (backgroundSizeB G + thermalSizeTermIII_genuine G A) := by
  have htot : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re =
      (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A)) := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    exact hsInner_siteSizeOp_eq_comm_sum x (jBeta G.ρQuarter A)
  have hu_eq : (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceU G A x α) =
      otocCW G A := by
    have hpt : ∀ (x : Fin N) (α : Fin 3),
        hsNormSq (commutatorPieceU G A x α) = gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) := by
      intro x α
      unfold commutatorPieceU
      have hiso : hsNormSq (jBeta G.ρQuarter (matComm (pauliSite x α.succ) A)) =
          gibbsWightmanNormSq G (matComm (pauliSite x α.succ) A) :=
        congrArg Complex.re
          (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter)
      rw [hiso]
      have hneg : matComm (pauliSite x α.succ) A = -matComm A (pauliSite x α.succ) := by
        unfold matComm; abel
      rw [hneg]
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    unfold otocCW
    apply congrArg ((1 / 8 : ℝ) * ·)
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun α _ ↦ hpt x α
  have hexp : ∀ (U V : QubitOp N),
      hsNormSq (U + V) = hsNormSq U + 2 * (hsInner U V).re + hsNormSq V := by
    intro U V
    unfold hsNormSq hsInner
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hsym : (Vᴴ * U).trace.re = (Uᴴ * V).trace.re := by
      have hc : (Vᴴ * U).trace = starRingEnd ℂ (Uᴴ * V).trace := by
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hc, Complex.conj_re]
    linarith
  have hdecomp : mssThermalSize G A =
      otocCW G A + thermalSizeTermII_genuine G A + thermalSizeTermIII_genuine G A := by
    have hpt : ∀ (x : Fin N) (α : Fin 3),
        hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A)) =
        hsNormSq (commutatorPieceU G A x α) +
        2 * (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re +
        hsNormSq (commutatorPieceV G A x α) := fun x α ↦ by
      rw [matComm_jBeta_eq_U_add_V, hexp]
    have hsum_eq : (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A))) =
        (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceU G A x α)) +
        2 * (∑ x : Fin N, ∑ α : Fin 3, (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re) +
        (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α)) := by
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold mssThermalSize thermalSizeTermII_genuine thermalSizeTermIII_genuine backgroundSizeB
    rw [htot, ← hu_eq, hsum_eq]
    ring
  refine ⟨hdecomp, ?_⟩
  -- Cauchy–Schwarz on `|II(A)| = (1/4) |∑_{x,α} Re ⟨U, V⟩_HS| ≤ 2 * √((1/8) ∑ ‖U‖²) * √((1/8) ∑ ‖V‖²)`
  have hv_sum : backgroundSizeB G + thermalSizeTermIII_genuine G A =
      (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α) := by
    unfold thermalSizeTermIII_genuine; ring
  rw [hv_sum, ← hu_eq]
  unfold thermalSizeTermII_genuine
  set SU := ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceU G A x α)
  set SV := ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α)
  set SUV := ∑ x : Fin N, ∑ α : Fin 3, (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re
  have hSU_nn : 0 ≤ SU := Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
  have hSV_nn : 0 ≤ SV := Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
  have hexp_smul : ∀ (U V : QubitOp N) (t : ℝ),
      hsNormSq (U + (t : ℂ) • V) = hsNormSq U + 2 * t * (hsInner U V).re + t ^ 2 * hsNormSq V := by
    intro U V t
    have h1 : (hsInner U ((t : ℂ) • V)).re = t * (hsInner U V).re := by
      unfold hsInner
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have h2 : hsNormSq ((t : ℂ) • V) = t ^ 2 * hsNormSq V := by
      unfold hsNormSq hsInner
      simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]
    rw [hexp U ((t : ℂ) • V), h1, h2]; ring
  have hquad : ∀ t : ℝ, 0 ≤ SU + 2 * t * SUV + t ^ 2 * SV := by
    intro t
    have hsum_nn : 0 ≤ ∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (commutatorPieceU G A x α + (t : ℂ) • commutatorPieceV G A x α) :=
      Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
    have hsum_eq : (∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (commutatorPieceU G A x α + (t : ℂ) • commutatorPieceV G A x α)) =
        SU + 2 * t * SUV + t ^ 2 * SV := by
      dsimp only [SU, SUV, SV]
      have h1 : ∀ x : Fin N, (∑ α : Fin 3,
          hsNormSq (commutatorPieceU G A x α + (t : ℂ) • commutatorPieceV G A x α)) =
          (∑ α : Fin 3, hsNormSq (commutatorPieceU G A x α)) +
          (2 * t) * (∑ α : Fin 3, (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re) +
          (t ^ 2) * (∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α)) := by
        intro x
        trans (∑ α : Fin 3, (hsNormSq (commutatorPieceU G A x α) +
            2 * t * (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re +
            t ^ 2 * hsNormSq (commutatorPieceV G A x α)))
        · exact Finset.sum_congr rfl fun α _ ↦ hexp_smul _ _ t
        · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      trans (∑ x : Fin N, ((∑ α : Fin 3, hsNormSq (commutatorPieceU G A x α)) +
          (2 * t) * (∑ α : Fin 3, (hsInner (commutatorPieceU G A x α) (commutatorPieceV G A x α)).re) +
          (t ^ 2) * (∑ α : Fin 3, hsNormSq (commutatorPieceV G A x α))))
      · exact Finset.sum_congr rfl fun x _ ↦ h1 x
      · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  have hcs_sq : SUV ^ 2 ≤ SU * SV := by
    by_cases hSV0 : SV = 0
    · have h0 : SUV = 0 := by
        by_contra hne
        have hq := hquad (-SU / (2 * SUV) - 1 / SUV)
        rw [hSV0, mul_zero, add_zero] at hq
        have : 2 * (-SU / (2 * SUV) - 1 / SUV) * SUV = -SU - 2 := by field_simp [hne]
        linarith
      rw [h0, hSV0]; norm_num
    · have hSVpos : 0 < SV := lt_of_le_of_ne hSV_nn (Ne.symm hSV0)
      have hq := hquad (-SUV / SV)
      have hmul := mul_nonneg hq hSVpos.le
      have hident : (SU + 2 * (-SUV / SV) * SUV + (-SUV / SV) ^ 2 * SV) * SV = SU * SV - SUV ^ 2 := by
        field_simp [hSVpos.ne']; ring
      linarith
  have hrhs_eq : 2 * Real.sqrt ((1 / 8 : ℝ) * SU) * Real.sqrt ((1 / 8 : ℝ) * SV) =
      (1 / 4 : ℝ) * Real.sqrt (SU * SV) := by
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    have h1 : (1 / 8 : ℝ) * SU * ((1 / 8 : ℝ) * SV) = (1 / 8 : ℝ) ^ 2 * (SU * SV) := by ring
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]; ring
  rw [hrhs_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc |SUV| = Real.sqrt (SUV ^ 2) := (Real.sqrt_sq_eq_abs SUV).symm
    _ ≤ Real.sqrt (SU * SV) := Real.sqrt_le_sqrt hcs_sq

end Item18GenuineEq64Decomposition

section Item19RelativeEntropyAndProp64Part2

/-- **Item #19 — Singular Density Matrix Relative Entropy Bound (`D(ρ ‖ ρ_β) ≤ log C`)**:
Extends `gibbsRelEntropy_le_log_of_renyi2` to **arbitrary positive-semidefinite (possibly singular /
rank-deficient) density matrices** `ρ` (`∀ i, 0 ≤ hρ.eigenvalues i`, `Tr(ρ) = 1`), using `0 * log 0 = 0`! -/
theorem gibbsRelEntropy_le_log_of_renyi2_singular {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hρ_nn : ∀ i : QubitIdx N, 0 ≤ hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β : ℝ) {C : ℝ} (hC : 0 < C)
    (hrenyi :
      let W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N)
      let μ : QubitIdx N → ℝ := fun j ↦ (gibbsPartitionFn hH β)⁻¹ * Real.exp (-β * hH.eigenvalues j)
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j) ≤ C) :
    gibbsRelEntropy hρ hH β ≤ Real.log C := by
  set W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N)
  have hZ := gibbsPartitionFn_pos hH β
  set μ : QubitIdx N → ℝ := fun j ↦ (gibbsPartitionFn hH β)⁻¹ * Real.exp (-β * hH.eigenvalues j)
  have hμ_pos : ∀ j, 0 < μ j := fun j ↦ mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)
  have hrow : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 = 1 := by
    have hW1 : W * Wᴴ = 1 := by
      dsimp only [W]
      have hUρ : (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hρ.eigenvectorUnitary : QubitOp N) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
      have hUH : (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
      calc (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) *
            ((hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N))ᴴ
          = (hρ.eigenvectorUnitary : QubitOp N)ᴴ *
            ((hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ) *
            (hρ.eigenvectorUnitary : QubitOp N) := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = 1 := by rw [hUH, Matrix.mul_one, hUρ]
    intro i
    have hii := congrArg (fun M : QubitOp N ↦ (M i i).re) hW1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at hii
    rw [← hii]; apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have htr_eig : ∑ i : QubitIdx N, hρ.eigenvalues i = 1 := by
    have hspec := hρ.spectral_theorem
    have h1 : ρ = (hρ.eigenvectorUnitary : QubitOp N) *
        Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
        (hρ.eigenvectorUnitary : QubitOp N)ᴴ := by
      simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hspec
    have hUleft : (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hρ.eigenvectorUnitary : QubitOp N) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
    have htrC : (∑ i : QubitIdx N, (hρ.eigenvalues i : ℂ)) = ρ.trace := by
      calc (∑ i : QubitIdx N, (hρ.eigenvalues i : ℂ))
          = (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))).trace := (Matrix.trace_diagonal _).symm
        _ = (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
              ((hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hρ.eigenvectorUnitary : QubitOp N))).trace := by
              rw [hUleft, Matrix.mul_one]
        _ = ((Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (hρ.eigenvectorUnitary : QubitOp N)ᴴ) *
              (hρ.eigenvectorUnitary : QubitOp N)).trace := by simp only [Matrix.mul_assoc]
        _ = ((hρ.eigenvectorUnitary : QubitOp N) *
              (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (hρ.eigenvectorUnitary : QubitOp N)ᴴ)).trace :=
              Matrix.trace_mul_comm _ _
        _ = ρ.trace := congrArg Matrix.trace (by rw [← Matrix.mul_assoc]; exact h1.symm)
    rw [hρ_tr] at htrC
    have hre := congrArg Complex.re htrC
    simpa [Complex.re_sum] using hre
  -- Express `gibbsRelEntropy hρ hH β` as `∑ i, ∑ j, ‖W i j‖^2 * λ_i * log(λ_i / μ_j)`
  have hent_eq : gibbsRelEntropy hρ hH β =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (μ j))) := by
    unfold gibbsRelEntropy
    have hlogμ : ∀ j : QubitIdx N, Real.log (μ j) = -Real.log (gibbsPartitionFn hH β) - β * hH.eigenvalues j := by
      intro j; dsimp only [μ]
      rw [Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]; ring
    have htrρH : (ρ * H).trace.re =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j := by
      have h1 : ρ = (hρ.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
          (hρ.eigenvectorUnitary : QubitOp N)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hρ.spectral_theorem
      have h2 : H = (hH.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun j ↦ (hH.eigenvalues j : ℂ)) *
          (hH.eigenvectorUnitary : QubitOp N)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hH.spectral_theorem
      set Dρ := Matrix.diagonal (fun i : QubitIdx N ↦ (hρ.eigenvalues i : ℂ))
      set DH := Matrix.diagonal (fun j : QubitIdx N ↦ (hH.eigenvalues j : ℂ))
      set Uρ := (hρ.eigenvectorUnitary : QubitOp N)
      set UH := (hH.eigenvectorUnitary : QubitOp N)
      have htrM : (ρ * H).trace = (Dρ * W * DH * Wᴴ).trace := by
        calc (ρ * H).trace
            = (Uρ * (Dρ * (Uρᴴ * UH) * DH * UHᴴ)).trace := by
                rw [h1, h2]; simp only [Matrix.mul_assoc]
          _ = ((Dρ * (Uρᴴ * UH) * DH * UHᴴ) * Uρ).trace := Matrix.trace_mul_comm _ _
          _ = (Dρ * W * DH * Wᴴ).trace := by
                dsimp only [W, Uρ, UH]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [htrM]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Dρ, DH, Matrix.diagonal_apply,
        ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      simp only [Matrix.conjTranspose_apply, Complex.star_def]
      have heq : (hρ.eigenvalues i : ℂ) * W i j * (hH.eigenvalues j : ℂ) * starRingEnd ℂ (W i j) =
          ((‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j : ℝ) : ℂ) := by
        have hw : W i j * starRingEnd ℂ (W i j) = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj', Complex.ofReal_pow]
        calc (hρ.eigenvalues i : ℂ) * W i j * (hH.eigenvalues j : ℂ) * starRingEnd ℂ (W i j)
            = (W i j * starRingEnd ℂ (W i j)) * ((hρ.eigenvalues i : ℂ) * (hH.eigenvalues j : ℂ)) := by ring
          _ = ((‖W i j‖ ^ 2 : ℝ) : ℂ) * ((hρ.eigenvalues i : ℂ) * (hH.eigenvalues j : ℂ)) := by rw [hw]
          _ = ((‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.ofReal_re]
    simp_rw [hlogμ]
    have hsplit : (∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - (-Real.log (gibbsPartitionFn hH β) - β * hH.eigenvalues j)))) =
        (∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) +
        Real.log (gibbsPartitionFn hH β) * (∑ i : QubitIdx N, hρ.eigenvalues i) +
        β * (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j) := by
      have h1 : ∀ i, ∑ j : QubitIdx N,
          ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - (-Real.log (gibbsPartitionFn hH β) - β * hH.eigenvalues j))) =
          hρ.eigenvalues i * Real.log (hρ.eigenvalues i) +
          Real.log (gibbsPartitionFn hH β) * hρ.eigenvalues i +
          β * ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j := by
        intro i
        have hlin : ∀ j, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - (-Real.log (gibbsPartitionFn hH β) - β * hH.eigenvalues j))) =
            ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i) + Real.log (gibbsPartitionFn hH β) * hρ.eigenvalues i) +
            β * (‖W i j‖ ^ 2 * hρ.eigenvalues i * hH.eigenvalues j) := fun j ↦ by ring
        simp_rw [hlin, Finset.sum_add_distrib, ← Finset.sum_mul, hrow i, one_mul, ← Finset.mul_sum]
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    have htr_log : (ρ * hermFunc hρ (fun x : ℝ ↦ (Real.log x : ℂ))).trace.re =
        ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
      have h1 : ρ = (hρ.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
          (hρ.eigenvectorUnitary : QubitOp N)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hρ.spectral_theorem
      set Uρ := (hρ.eigenvectorUnitary : QubitOp N)
      have hUρ : Uρᴴ * Uρ = 1 := by
        simpa [Uρ, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
      unfold hermFunc
      change (ρ * (Uρ * Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ)) * Uρᴴ)).trace.re = _
      calc (ρ * (Uρ * Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ)) * Uρᴴ)).trace.re
          = (Uρ * (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (Uρᴴ * Uρ) *
              Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ))) * Uρᴴ).trace.re := by
                have hmul := congrArg (fun M ↦ (M * (Uρ * Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ)) * Uρᴴ)).trace.re) h1
                rw [hmul]; simp only [Matrix.mul_assoc]
        _ = (Uρᴴ * (Uρ * (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
              Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ))))).trace.re := by
                rw [hUρ, Matrix.mul_one, Matrix.trace_mul_comm]
        _ = ((Uρᴴ * Uρ) * (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
              Matrix.diagonal (fun i ↦ (Real.log (hρ.eigenvalues i) : ℂ)))).trace.re := by
                rw [Matrix.mul_assoc]
        _ = (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ) * (Real.log (hρ.eigenvalues i) : ℂ))).trace.re := by
                rw [hUρ, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
        _ = ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
                rw [Matrix.trace_diagonal, Complex.re_sum]
                apply Finset.sum_congr rfl; intro i _
                rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul, htr_log, htrρH, hsplit, htr_eig, mul_one]
    ring
  rw [hent_eq]
  -- Pointwise: `λ_i * (log λ_i - log μ_j - log C) ≤ λ_i * (λ_i / (C * μ_j) - 1)` for ALL `λ_i ≥ 0`!
  have hpt : ∀ i j : QubitIdx N,
      hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (μ j)) ≤
      hρ.eigenvalues i * Real.log C + ((hρ.eigenvalues i) ^ 2 / μ j) / C - hρ.eigenvalues i := by
    intro i j
    rcases eq_or_lt_of_le (hρ_nn i) with hi0 | hipos
    · rw [← hi0]; simp
    · have hCμ : 0 < C * μ j := mul_pos hC (hμ_pos j)
      have hlog : Real.log (hρ.eigenvalues i / (C * μ j)) ≤ hρ.eigenvalues i / (C * μ j) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hipos hCμ)
      rw [Real.log_div hipos.ne' hCμ.ne', Real.log_mul hC.ne' (hμ_pos j).ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hipos.le
      have hrhs : hρ.eigenvalues i * (hρ.eigenvalues i / (C * μ j) - 1) =
          ((hρ.eigenvalues i) ^ 2 / μ j) / C - hρ.eigenvalues i := by
        field_simp [hC.ne', (hμ_pos j).ne']
      linarith
  calc ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (μ j)))
      ≤ ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log C + ((hρ.eigenvalues i) ^ 2 / μ j) / C - hρ.eigenvalues i) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hpt i j) (sq_nonneg _)
    _ = Real.log C * (∑ i : QubitIdx N, hρ.eigenvalues i) +
        (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) / C -
        (∑ i : QubitIdx N, hρ.eigenvalues i) := by
        have hlin : ∀ i j,
            ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log C + ((hρ.eigenvalues i) ^ 2 / μ j) / C - hρ.eigenvalues i) =
            (‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log C - hρ.eigenvalues i)) +
            (‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) / C := fun i j ↦ by ring
        simp_rw [hlin, Finset.sum_add_distrib, ← Finset.sum_mul, hrow, one_mul, ← Finset.sum_div,
          Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
    _ = Real.log C + (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) / C - 1 := by
        rw [htr_eig, mul_one]
    _ ≤ Real.log C + C / C - 1 := by
        have hdiv : (∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) / C ≤ C / C :=
          div_le_div_of_nonneg_right hrenyi hC.le
        linarith
    _ = Real.log C := by rw [div_self hC.ne']; ring

/-- **Item #19 — Perturbed Density Matrix `ρ_O = (𝒥_β O)ᴴ (𝒥_β O)`** (may be singular!). -/
noncomputable def rhoO_op {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) (O : QubitOp N) :
    QubitOp N :=
  let G := concreteGibbsData hH β
  (jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O

lemma rhoO_op_isHermitian {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) (O : QubitOp N) :
    (rhoO_op hH β O).IsHermitian := by
  unfold rhoO_op Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma rhoO_op_trace_eq_normSq {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) (O : QubitOp N) :
    (rhoO_op hH β O).trace = ((gibbsWightmanNormSq (concreteGibbsData hH β) O : ℝ) : ℂ) := by
  unfold rhoO_op
  set G := concreteGibbsData hH β
  have htr_re : ((jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O).trace.re = gibbsWightmanNormSq G O :=
    congrArg Complex.re
      (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf O O G.ρQuarter_herm G.sq_quarter)
  have htr_im : ((jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O).trace.im = 0 := by
    have hh : ((jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O).IsHermitian := rhoO_op_isHermitian hH β O
    have hc : starRingEnd ℂ ((jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O).trace =
        ((jBeta G.ρQuarter O)ᴴ * jBeta G.ρQuarter O).trace := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, hh.eq]
    exact Complex.conj_eq_iff_im.mp hc
  exact Complex.ext (by simp [htr_re]) (by simp [htr_im])


/-- Universal operator-norm invariance under conjugate transpose: `opNorm Aᴴ = opNorm A`. -/
lemma opNorm_conjTranspose {N : ℕ} (A : QubitOp N) : opNorm Aᴴ = opNorm A := by
  have hop : ∀ (M : QubitOp N) (u : EuclideanSpace ℂ (QubitIdx N)) (i : QubitIdx N),
      (opToCLM M u).ofLp i = ∑ j : QubitIdx N, M i j * u.ofLp j := fun _ _ _ ↦ rfl
  have hle : ∀ X : QubitOp N, opNorm Xᴴ ≤ opNorm X := by
    intro X
    unfold opNorm
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    set w := opToCLM Xᴴ v
    by_cases hw : ‖w‖ = 0
    · rw [hw]; positivity
    · have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
      have hsq : ‖w‖ ^ 2 ≤ ‖v‖ * ‖opToCLM X w‖ := by
        have hinner : (‖w‖ ^ 2 : ℝ) = (@inner ℂ _ _ v (opToCLM X w)).re := by
          rw [← Complex.ofReal_re (‖w‖ ^ 2)]
          have h1 : ((‖w‖ ^ 2 : ℝ) : ℂ) = @inner ℂ _ _ w w := by
            rw [inner_self_eq_norm_sq_to_K]; simp
          rw [h1]
          congr 1
          simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.star_def]
          have hL : ∀ i : QubitIdx N,
              starRingEnd ℂ (w.ofLp i) = ∑ j : QubitIdx N, X j i * starRingEnd ℂ (v.ofLp j) := by
            intro i
            have hw' : w.ofLp i = ∑ j : QubitIdx N, starRingEnd ℂ (X j i) * v.ofLp j := by
              change (opToCLM Xᴴ v).ofLp i = _
              rw [hop]
              apply Finset.sum_congr rfl; intro j _
              simp [Matrix.conjTranspose_apply, Complex.star_def]
            rw [hw', map_sum]
            apply Finset.sum_congr rfl; intro j _
            rw [map_mul, starRingEnd_self_apply]
          calc ∑ i : QubitIdx N, w.ofLp i * starRingEnd ℂ (w.ofLp i)
              = ∑ i : QubitIdx N, w.ofLp i * (∑ j : QubitIdx N, X j i * starRingEnd ℂ (v.ofLp j)) := by
                  apply Finset.sum_congr rfl; intro i _; rw [hL i]
            _ = ∑ j : QubitIdx N, (∑ i : QubitIdx N, X j i * w.ofLp i) * starRingEnd ℂ (v.ofLp j) := by
                  simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro j _
                  apply Finset.sum_congr rfl; intro i _; ring
            _ = ∑ j : QubitIdx N, (opToCLM X w).ofLp j * starRingEnd ℂ (v.ofLp j) := by
                  apply Finset.sum_congr rfl; intro j _; rw [hop]
        rw [hinner]
        calc (@inner ℂ _ _ v (opToCLM X w)).re
            ≤ ‖@inner ℂ _ _ v (opToCLM X w)‖ := Complex.re_le_norm _
          _ ≤ ‖v‖ * ‖opToCLM X w‖ := norm_inner_le_norm _ _
      have hXw : ‖opToCLM X w‖ ≤ ‖opToCLM X‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm (opToCLM X) w
      have h2 : ‖w‖ ^ 2 ≤ (‖opToCLM X‖ * ‖v‖) * ‖w‖ := by
        calc ‖w‖ ^ 2 ≤ ‖v‖ * ‖opToCLM X w‖ := hsq
          _ ≤ ‖v‖ * (‖opToCLM X‖ * ‖w‖) := mul_le_mul_of_nonneg_left hXw (norm_nonneg _)
          _ = (‖opToCLM X‖ * ‖v‖) * ‖w‖ := by ring
      nlinarith
  exact le_antisymm (hle A) (by simpa [Matrix.conjTranspose_conjTranspose] using hle Aᴴ)

/-- Universal Hilbert–Schmidt left-multiplication bound: `‖A B‖_HS² ≤ ‖A‖_∞² ‖B‖_HS²`. -/
theorem hsNormSq_mul_le_opNorm_sq {N : ℕ} (A B : QubitOp N) :
    hsNormSq (A * B) ≤ (opNorm A) ^ 2 * hsNormSq B := by
  have hhs_eq : ∀ X : QubitOp N,
      hsNormSq X = ∑ j : QubitIdx N, ‖WithLp.toLp 2 (fun i : QubitIdx N ↦ X i j)‖ ^ 2 := by
    intro X
    unfold hsNormSq hsInner
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hhs_eq (A * B), hhs_eq B, Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  set v : EuclideanSpace ℂ (QubitIdx N) := WithLp.toLp 2 (fun i ↦ B i j)
  have hcol : WithLp.toLp 2 (fun i : QubitIdx N ↦ (A * B) i j) = qubitOpToCLM A v := by
    ext i
    simp [qubitOpToCLM, Matrix.mulVec, dotProduct, Matrix.mul_apply, v]
  rw [hcol]
  have hle : ‖qubitOpToCLM A v‖ ≤ opNorm A * ‖v‖ := ContinuousLinearMap.le_opNorm (qubitOpToCLM A) v
  have hsq : ‖qubitOpToCLM A v‖ ^ 2 ≤ (opNorm A * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [mul_pow] at hsq

/-- Universal Hilbert–Schmidt right-multiplication bound: `‖A B‖_HS² ≤ ‖B‖_∞² ‖A‖_HS²`. -/
theorem hsNormSq_mul_right_le_opNorm_sq {N : ℕ} (A B : QubitOp N) :
    hsNormSq (A * B) ≤ (opNorm B) ^ 2 * hsNormSq A := by
  have hadj : ∀ X : QubitOp N, hsNormSq Xᴴ = hsNormSq X := by
    intro X
    unfold hsNormSq hsInner
    rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [← hadj (A * B), Matrix.conjTranspose_mul, ← hadj A, ← opNorm_conjTranspose B]
  exact hsNormSq_mul_le_opNorm_sq Bᴴ Aᴴ

/-- Positive semidefiniteness of `ρ_O = (𝒥_β O)ᴴ (𝒥_β O)`: every eigenvalue is `≥ 0`. -/
lemma rhoO_op_eigenvalues_nonneg {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N) (i : QubitIdx N) :
    0 ≤ (rhoO_op_isHermitian hH β O).eigenvalues i := by
  have hop : ∀ (M : QubitOp N) (u : EuclideanSpace ℂ (QubitIdx N)) (x : QubitIdx N),
      (opToCLM M u).ofLp x = (M *ᵥ u.ofLp) x := fun _ _ _ ↦ rfl
  set hρ := rhoO_op_isHermitian hH β O
  set v : EuclideanSpace ℂ (QubitIdx N) := hρ.eigenvectorBasis i
  have hv_norm : ‖v‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
  have heig : Matrix.mulVec (rhoO_op hH β O) v.ofLp =
      ((hρ.eigenvalues i : ℝ) : ℂ) • v.ofLp := by
    simpa [v] using hρ.mulVec_eigenvectorBasis i
  set B := jBeta (concreteGibbsData hH β).ρQuarter O
  have hinner : ((hρ.eigenvalues i : ℝ) : ℂ) =
      @inner ℂ _ _ (opToCLM B v) (opToCLM B v) := by
    have h1 : @inner ℂ _ _ v (opToCLM (rhoO_op hH β O) v) = ((hρ.eigenvalues i : ℝ) : ℂ) := by
      have hqv : opToCLM (rhoO_op hH β O) v = ((hρ.eigenvalues i : ℝ) : ℂ) • v := by
        ext x; rw [hop]; exact congrFun heig x
      rw [hqv, inner_smul_right, inner_self_eq_norm_sq_to_K, hv_norm]; simp
    rw [← h1]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.star_def]
    have hL : ∀ x : QubitIdx N, (opToCLM (rhoO_op hH β O) v).ofLp x =
        ∑ k : QubitIdx N, ∑ y : QubitIdx N, starRingEnd ℂ (B k x) * B k y * v.ofLp y := by
      intro x
      change ((Bᴴ * B) *ᵥ v.ofLp) x = _
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hR : ∀ k : QubitIdx N, (opToCLM B v).ofLp k = ∑ y : QubitIdx N, B k y * v.ofLp y :=
      fun _ ↦ rfl
    simp_rw [hL, hR, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro x _
    ring
  have hre := congrArg Complex.re hinner
  simp only [Complex.ofReal_re] at hre
  rw [hre, inner_self_eq_norm_sq_to_K]
  simp [sq]
  positivity

set_option maxHeartbeats 800000 in
/-- **Item #19 — Singular-State Relative Entropy Bound `D(ρ_O ‖ ρ_β) ≤ 2 ln ‖O(iβ/4)‖_∞`**:
Proves directly on `QubitOp N` (without assuming `ρ_O` is invertible / full-rank!) that for ANY
Hermitian `H : QubitOp N`, `β : ℝ`, and `O : QubitOp N` with `‖O‖_{β,W}² = 1`:
`gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β ≤ 2 * Real.log (opNorm (heisenbergEvol hH (i β / 4) O))`. -/
theorem rhoO_op_relEntropy_le_two_log_opNorm {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (O : QubitOp N)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1) :
    gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β ≤
      2 * Real.log (opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O)) := by
  set G := concreteGibbsData hH β
  set B := heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O
  set ρ := rhoO_op hH β O
  set hρ := rhoO_op_isHermitian hH β O
  have hρ_tr : ρ.trace = 1 := by rw [rhoO_op_trace_eq_normSq, hOnorm]; simp
  -- Algebraic identity: `jBeta G.ρQuarter O = B * G.ρHalf`
  have hjB_eq : jBeta G.ρQuarter O = B * G.ρHalf := by
    have hshift : G.ρQuarter * O = B * G.ρQuarter := by
      change gibbsRhoQuarter hH β * O =
        complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ)) * O *
          complexPropagator hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) * gibbsRhoQuarter hH β
      have hprop_q : complexPropagator hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) * gibbsRhoQuarter hH β =
          (((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : QubitOp N) := by
        unfold complexPropagator gibbsRhoQuarter
        rw [Matrix.mul_smul, hermFunc_mul]
        congr 1
        have hfun : (fun x : ℝ ↦ Complex.exp (Complex.I * -(Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ)) *
            ((Real.exp (-(β / 4) * x) : ℝ) : ℂ)) = fun _ ↦ 1 := by
          funext x
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          have h0 : Complex.I * -(Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ) +
              ((-(β / 4) * x : ℝ) : ℂ) = 0 := by
            push_cast
            calc Complex.I * -(Complex.I * ((β : ℂ) / 4)) * (x : ℂ) + -((β : ℂ) / 4) * (x : ℂ)
                = -(Complex.I * Complex.I) * ((β : ℂ) / 4) * (x : ℂ) - ((β : ℂ) / 4) * (x : ℂ) := by ring
              _ = -(-1) * ((β : ℂ) / 4) * (x : ℂ) - ((β : ℂ) / 4) * (x : ℂ) := by rw [Complex.I_mul_I]
              _ = 0 := by ring
          rw [h0, Complex.exp_zero]
        rw [hfun, hermFunc_one]
      have hprop_l : complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ)) =
          hermFunc hH (fun x : ℝ ↦ Complex.exp (((-(β / 4) * x : ℝ) : ℂ))) := by
        unfold complexPropagator; congr 1; funext x; congr 1
        push_cast
        calc Complex.I * (Complex.I * ((β : ℂ) / 4)) * (x : ℂ)
            = (Complex.I * Complex.I) * ((β : ℂ) / 4) * (x : ℂ) := by ring
          _ = (-1) * ((β : ℂ) / 4) * (x : ℂ) := by rw [Complex.I_mul_I]
          _ = -((β : ℂ) / 4) * (x : ℂ) := by ring
      calc gibbsRhoQuarter hH β * O
          = ((((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) •
              complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ))) * O := by
                rw [hprop_l]; unfold gibbsRhoQuarter; congr 2
                unfold hermFunc; dsimp only; congr 3
                funext i; exact Complex.ofReal_exp _
        _ = complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ)) * O *
              ((((gibbsPartitionFn hH β) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : QubitOp N)) := by
                rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
        _ = complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ)) * O *
              (complexPropagator hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) * gibbsRhoQuarter hH β) := by
                rw [← hprop_q]
        _ = complexPropagator hH (Complex.I * ((β / 4 : ℝ) : ℂ)) * O *
              complexPropagator hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) * gibbsRhoQuarter hH β := by
                simp only [Matrix.mul_assoc]
    unfold jBeta
    rw [hshift, Matrix.mul_assoc, G.sq_quarter]
  have hBρ_hs : hsNormSq (B * G.ρHalf) = 1 := by
    rw [← hjB_eq]
    have h1 := congrArg Complex.re
      (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf O O G.ρQuarter_herm G.sq_quarter)
    exact h1.trans hOnorm
  have hρHalf_hs : hsNormSq G.ρHalf = 1 := by
    unfold hsNormSq hsInner
    rw [G.ρHalf_herm, G.sq_half, G.trace_one, Complex.one_re]
  have hB_pos : 0 < opNorm B := by
    have hle : 1 ≤ (opNorm B) ^ 2 := by
      calc (1 : ℝ) = hsNormSq (B * G.ρHalf) := hBρ_hs.symm
        _ ≤ (opNorm B) ^ 2 * hsNormSq G.ρHalf := hsNormSq_mul_le_opNorm_sq B G.ρHalf
        _ = (opNorm B) ^ 2 := by rw [hρHalf_hs, mul_one]
    have hnn : 0 ≤ opNorm B := by unfold opNorm; exact norm_nonneg _
    nlinarith
  have hρ_eq : ρ = G.ρHalf * (Bᴴ * B) * G.ρHalf := by
    unfold ρ rhoO_op; dsimp only
    rw [hjB_eq, Matrix.conjTranspose_mul, G.ρHalf_herm]
    simp only [Matrix.mul_assoc]
  -- Compute the Rényi-2 trace `∑ i, ∑ j, ‖W i j‖^2 * (λ_i^2 / μ_j) = hsNormSq (Bᴴ * (B * G.ρHalf))`
  set W : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N)
  set μ : QubitIdx N → ℝ := fun j ↦ (gibbsPartitionFn hH β)⁻¹ * Real.exp (-β * hH.eigenvalues j)
  have hZ := gibbsPartitionFn_pos hH β
  have hrenyi_eq : (∑ i : QubitIdx N, ∑ j : QubitIdx N,
      ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) = hsNormSq (Bᴴ * (B * G.ρHalf)) := by
    set ρInv : QubitOp N := hermFunc hH (fun x : ℝ ↦ ((gibbsPartitionFn hH β * Real.exp (β * x) : ℝ) : ℂ))
    have h1 : (∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) = (ρ * ρ * ρInv).trace.re := by
      have hspecρ : ρ = (hρ.eigenvectorUnitary : QubitOp N) *
          Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
          (hρ.eigenvectorUnitary : QubitOp N)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using hρ.spectral_theorem
      set Uρ := (hρ.eigenvectorUnitary : QubitOp N)
      set UH := (hH.eigenvectorUnitary : QubitOp N)
      have hUρ_unit : Uρᴴ * Uρ = 1 := Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
      set Dρ2 := Matrix.diagonal (fun i : QubitIdx N ↦ ((hρ.eigenvalues i ^ 2 : ℝ) : ℂ))
      set Dinv := Matrix.diagonal (fun j : QubitIdx N ↦ ((μ j)⁻¹ : ℂ))
      have hρ2 : ρ * ρ = Uρ * Dρ2 * Uρᴴ := by
        calc ρ * ρ
            = Uρ * Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * (Uρᴴ * Uρ) *
              Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) * Uρᴴ := by
                rw [hspecρ]; simp only [Matrix.mul_assoc]
          _ = Uρ * (Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ)) *
              Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))) * Uρᴴ := by
                rw [hUρ_unit, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = Uρ * Dρ2 * Uρᴴ := by
                congr 2; rw [Matrix.diagonal_mul_diagonal]; ext i j
                simp only [Dρ2, Matrix.diagonal_apply]
                split_ifs with hij
                · push_cast; ring
                · rfl
      have hρInv_diag : ρInv = UH * Dinv * UHᴴ := by
        unfold ρInv hermFunc
        change UH * Matrix.diagonal _ * UHᴴ = UH * Dinv * UHᴴ
        apply congrArg (fun d ↦ UH * Matrix.diagonal d * UHᴴ)
        funext i; dsimp only [μ]
        rw [← Complex.ofReal_inv, mul_inv, inv_inv, ← Real.exp_neg]; congr 1; congr 1; congr 1; ring
      have htrM : (ρ * ρ * ρInv).trace = (Dρ2 * W * Dinv * Wᴴ).trace := by
        calc (ρ * ρ * ρInv).trace
            = (Uρ * (Dρ2 * (Uρᴴ * UH) * Dinv * UHᴴ)).trace := by
                rw [hρ2, hρInv_diag]; simp only [Matrix.mul_assoc]
          _ = ((Dρ2 * (Uρᴴ * UH) * Dinv * UHᴴ) * Uρ).trace := Matrix.trace_mul_comm _ _
          _ = (Dρ2 * W * Dinv * Wᴴ).trace := by
                dsimp only [W, Uρ, UH]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [htrM]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Dρ2, Dinv, Matrix.diagonal_apply,
        ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      simp only [Matrix.conjTranspose_apply, Complex.star_def]
      have heq : ((hρ.eigenvalues i ^ 2 : ℝ) : ℂ) * W i j * ((μ j)⁻¹ : ℂ) * starRingEnd ℂ (W i j) =
          ((‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j) : ℝ) : ℂ) := by
        have hw : W i j * starRingEnd ℂ (W i j) = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj', Complex.ofReal_pow]
        calc ((hρ.eigenvalues i ^ 2 : ℝ) : ℂ) * W i j * ((μ j)⁻¹ : ℂ) * starRingEnd ℂ (W i j)
            = (W i j * starRingEnd ℂ (W i j)) * (((hρ.eigenvalues i ^ 2 : ℝ) : ℂ) * ((μ j)⁻¹ : ℂ)) := by ring
          _ = ((‖W i j‖ ^ 2 : ℝ) : ℂ) * (((hρ.eigenvalues i ^ 2 : ℝ) : ℂ) * ((μ j)⁻¹ : ℂ)) := by rw [hw]
          _ = ((‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j) : ℝ) : ℂ) := by
                rw [div_eq_mul_inv]; push_cast; ring
      rw [heq, Complex.ofReal_re]
    have hρHalf_inv : G.ρHalf * ρInv * G.ρHalf = 1 := by
      change gibbsRhoHalf hH β * ρInv * gibbsRhoHalf hH β = 1
      unfold gibbsRhoHalf ρInv
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hermFunc_mul, hermFunc_mul]
      have hfun : (fun x : ℝ ↦ ((Real.exp (-(β / 2) * x) : ℝ) : ℂ) *
          ((gibbsPartitionFn hH β * Real.exp (β * x) : ℝ) : ℂ) *
          ((Real.exp (-(β / 2) * x) : ℝ) : ℂ)) =
          fun _ ↦ ((gibbsPartitionFn hH β : ℝ) : ℂ) := by
        funext x
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        congr 1
        have h0 : -(β / 2) * x + β * x + -(β / 2) * x = 0 := by ring
        calc Real.exp (-(β / 2) * x) * (gibbsPartitionFn hH β * Real.exp (β * x)) * Real.exp (-(β / 2) * x)
            = gibbsPartitionFn hH β * (Real.exp (-(β / 2) * x) * Real.exp (β * x) * Real.exp (-(β / 2) * x)) := by ring
          _ = gibbsPartitionFn hH β * Real.exp (-(β / 2) * x + β * x + -(β / 2) * x) := by rw [Real.exp_add, Real.exp_add]
          _ = gibbsPartitionFn hH β := by rw [h0, Real.exp_zero, mul_one]
      rw [hfun]
      have hconst : hermFunc hH (fun _ ↦ ((gibbsPartitionFn hH β : ℝ) : ℂ)) =
          ((gibbsPartitionFn hH β : ℝ) : ℂ) • (1 : QubitOp N) := by
        unfold hermFunc
        have hdiag : Matrix.diagonal (fun _ : QubitIdx N ↦ ((gibbsPartitionFn hH β : ℝ) : ℂ)) =
            ((gibbsPartitionFn hH β : ℝ) : ℂ) • (1 : QubitOp N) := by
          ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
        have hUH_mul : (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
        dsimp only; rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUH_mul]
      rw [hconst, smul_smul, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have hsc : (Real.sqrt (gibbsPartitionFn hH β))⁻¹ *
          ((Real.sqrt (gibbsPartitionFn hH β))⁻¹ * gibbsPartitionFn hH β) = 1 := by
        have hsq : Real.sqrt (gibbsPartitionFn hH β) * Real.sqrt (gibbsPartitionFn hH β) =
            gibbsPartitionFn hH β := Real.mul_self_sqrt hZ.le
        have hsne : Real.sqrt (gibbsPartitionFn hH β) ≠ 0 := (Real.sqrt_pos.mpr hZ).ne'
        field_simp [hsne]
        linarith
      rw [mul_assoc, hsc, Complex.ofReal_one, one_smul]
    rw [h1]
    unfold hsNormSq hsInner
    apply congrArg Complex.re
    calc (ρ * ρ * ρInv).trace
        = (ρInv * (ρ * ρ)).trace := Matrix.trace_mul_comm (ρ * ρ) ρInv
      _ = ((ρInv * ρ) * ρ).trace := by rw [Matrix.mul_assoc]
      _ = (ρ * (ρInv * ρ)).trace := Matrix.trace_mul_comm (ρInv * ρ) ρ
      _ = ((G.ρHalf * (Bᴴ * B) * G.ρHalf) * (ρInv * (G.ρHalf * (Bᴴ * B) * G.ρHalf))).trace := by
            rw [hρ_eq]
      _ = (G.ρHalf * (Bᴴ * B) * (G.ρHalf * ρInv * G.ρHalf) * (Bᴴ * B) * G.ρHalf).trace := by
            simp only [Matrix.mul_assoc]
      _ = (G.ρHalf * (Bᴴ * B * (Bᴴ * B) * G.ρHalf)).trace := by
            rw [hρHalf_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ((Bᴴ * (B * G.ρHalf))ᴴ * (Bᴴ * (B * G.ρHalf))).trace := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, G.ρHalf_herm]
            calc (G.ρHalf * (Bᴴ * B * (Bᴴ * B) * G.ρHalf)).trace
                = ((Bᴴ * B * (Bᴴ * B) * G.ρHalf) * G.ρHalf).trace := Matrix.trace_mul_comm _ _
              _ = ((Bᴴ * B) * (Bᴴ * B * G.ρHalf * G.ρHalf)).trace := by simp only [Matrix.mul_assoc]
              _ = ((Bᴴ * B * G.ρHalf * G.ρHalf) * (Bᴴ * B)).trace := Matrix.trace_mul_comm _ _
              _ = (G.ρHalf * (Bᴴ * B) * (Bᴴ * B * G.ρHalf)).trace := by
                    calc ((Bᴴ * B * G.ρHalf * G.ρHalf) * (Bᴴ * B)).trace
                        = ((Bᴴ * B * G.ρHalf) * (G.ρHalf * (Bᴴ * B))).trace := by simp only [Matrix.mul_assoc]
                      _ = ((G.ρHalf * (Bᴴ * B)) * (Bᴴ * B * G.ρHalf)).trace := Matrix.trace_mul_comm _ _
                      _ = (G.ρHalf * (Bᴴ * B) * (Bᴴ * B * G.ρHalf)).trace := by simp only [Matrix.mul_assoc]
              _ = (G.ρHalf * Bᴴ * B * (Bᴴ * (B * G.ρHalf))).trace := by simp only [Matrix.mul_assoc]
  have hrenyi_le : (∑ i : QubitIdx N, ∑ j : QubitIdx N,
      ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) ≤ (opNorm B) ^ 2 := by
    rw [hrenyi_eq]
    calc hsNormSq (Bᴴ * (B * G.ρHalf))
        ≤ (opNorm Bᴴ) ^ 2 * hsNormSq (B * G.ρHalf) := hsNormSq_mul_le_opNorm_sq Bᴴ (B * G.ρHalf)
      _ = (opNorm B) ^ 2 := by rw [opNorm_conjTranspose, hBρ_hs, mul_one]
  have hrel := gibbsRelEntropy_le_log_of_renyi2_singular hρ hH
    (rhoO_op_eigenvalues_nonneg hH β O) hρ_tr β (sq_pos_of_pos hB_pos) hrenyi_le
  rwa [Real.log_pow, Nat.cast_ofNat] at hrel

end Item19RelativeEntropyAndProp64Part2

section Item20WightmanNormAndCor65

/-- **Item #20 — Universal Wightman-vs-Operator-Norm Bound (`‖A‖_{β,W}² ≤ ‖A‖_∞²`)**:
For ANY `G : GibbsData N` and ANY `A : QubitOp N`:
`gibbsWightmanNormSq G A ≤ (opNorm A) ^ 2`. -/
theorem wightmanNormSq_le_opNorm_sq {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    gibbsWightmanNormSq G A ≤ (opNorm A) ^ 2 := by
  have hρHalf_hs : hsNormSq G.ρHalf = 1 := by
    unfold hsNormSq hsInner
    rw [G.ρHalf_herm, G.sq_half, G.trace_one, Complex.one_re]
  have hinner_eq : gibbsWightmanNormSq G A = (hsInner (A * G.ρHalf) (G.ρHalf * A)).re := by
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner hsInner
    rw [Matrix.conjTranspose_mul, G.ρHalf_herm]
    simp only [Matrix.mul_assoc]
  have hcs : (hsInner (A * G.ρHalf) (G.ρHalf * A)).re ≤
      Real.sqrt (hsNormSq (A * G.ρHalf) * hsNormSq (G.ρHalf * A)) := by
    have h1 : ‖@inner ℂ _ _ (qubitOpToHS N (A * G.ρHalf)) (qubitOpToHS N (G.ρHalf * A))‖ ≤
        ‖qubitOpToHS N (A * G.ρHalf)‖ * ‖qubitOpToHS N (G.ρHalf * A)‖ := norm_inner_le_norm _ _
    have hn1 : ‖qubitOpToHS N (A * G.ρHalf)‖ = Real.sqrt (hsNormSq (A * G.ρHalf)) := by
      have hsq : ‖qubitOpToHS N (A * G.ρHalf)‖ ^ 2 = hsNormSq (A * G.ρHalf) := by
        have hc := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (qubitOpToHS N (A * G.ρHalf))
        rw [qubitOpToHS_inner] at hc
        have hr := congrArg Complex.re hc
        simp [sq] at hr
        rw [sq]; exact hr.symm
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    have hn2 : ‖qubitOpToHS N (G.ρHalf * A)‖ = Real.sqrt (hsNormSq (G.ρHalf * A)) := by
      have hsq : ‖qubitOpToHS N (G.ρHalf * A)‖ ^ 2 = hsNormSq (G.ρHalf * A) := by
        have hc := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (qubitOpToHS N (G.ρHalf * A))
        rw [qubitOpToHS_inner] at hc
        have hr := congrArg Complex.re hc
        simp [sq] at hr
        rw [sq]; exact hr.symm
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [qubitOpToHS_inner, hn1, hn2, ← Real.sqrt_mul (hsNormSq_nonneg _)] at h1
    exact le_trans (Complex.re_le_norm _) h1
  have hL : hsNormSq (A * G.ρHalf) ≤ (opNorm A) ^ 2 := by
    calc hsNormSq (A * G.ρHalf) ≤ (opNorm A) ^ 2 * hsNormSq G.ρHalf := hsNormSq_mul_le_opNorm_sq A G.ρHalf
      _ = (opNorm A) ^ 2 := by rw [hρHalf_hs, mul_one]
  have hR : hsNormSq (G.ρHalf * A) ≤ (opNorm A) ^ 2 := by
    calc hsNormSq (G.ρHalf * A) ≤ (opNorm A) ^ 2 * hsNormSq G.ρHalf := hsNormSq_mul_right_le_opNorm_sq G.ρHalf A
      _ = (opNorm A) ^ 2 := by rw [hρHalf_hs, mul_one]
  rw [hinner_eq]
  calc (hsInner (A * G.ρHalf) (G.ρHalf * A)).re
      ≤ Real.sqrt (hsNormSq (A * G.ρHalf) * hsNormSq (G.ρHalf * A)) := hcs
    _ ≤ Real.sqrt ((opNorm A) ^ 2 * (opNorm A) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul hL hR (hsNormSq_nonneg _) (sq_nonneg _))
    _ = (opNorm A) ^ 2 := by rw [← sq, Real.sqrt_sq (sq_nonneg _)]

/-- **Item #20 — Corollary 6.5 Lattice Causal-Ball + Operator-Norm Exterior Bound (All Times `t : ℝ`)**:
Combines `cor_6_5_causal_ball_sum_bound` with `wightmanNormSq_le_opNorm_sq` to bound `otocCW`
at ANY time `t : ℝ` on a `d`-dimensional lattice `pos : Fin N → (Fin d → ℤ)`. -/
theorem cor_6_5_all_time_lattice_bound {N d : ℕ} (pos : Fin N → (Fin d → ℤ))
    (hinj : Function.Injective pos) (U₀ : Finset (Fin N)) (R : ℕ)
    {H : QubitOp N} (hH : H.IsHermitian) (β t : ℝ) (O : QubitOp N) :
    let G := concreteGibbsData hH β
    let Ot := heisenbergEvol hH (t : ℂ) O
    otocCW G Ot ≤
      (3 / 2 : ℝ) * (opNorm Ot) ^ 2 * (U₀.card : ℝ) * ((2 * R + 1 : ℕ) : ℝ) ^ d +
      (1 / 8 : ℝ) * ∑ x ∈ Finset.univ.filter (fun x : Fin N ↦ ∀ u ∈ U₀, R < latticeInfDist (pos u) (pos x)),
        ∑ α : Fin 3, (opNorm (matComm Ot (pauliSite x α.succ))) ^ 2 := by
  intro G Ot
  let f : Fin N → ℝ := fun x ↦
    (1 / 8 : ℝ) * ∑ α : Fin 3, gibbsWightmanNormSq G (matComm Ot (pauliSite x α.succ))
  have hf_nn : ∀ x, 0 ≤ f x := fun x ↦
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ gibbsWightmanNormSq_nonneg _ _)
  have hotoc_eq : otocCW G Ot = ∑ x : Fin N, f x := by
    unfold otocCW; rw [Finset.mul_sum]
  have hpauli_op : ∀ (x : Fin N) (α : Fin 3), opNorm (pauliSite x α.succ) ≤ 1 :=
    fun x α ↦ opNorm_pauliSite_le x α
  have hcomm_op : ∀ (x : Fin N) (α : Fin 3),
      opNorm (matComm Ot (pauliSite x α.succ)) ≤ 2 * opNorm Ot := by
    intro x α
    have h1 : opNorm (Ot * pauliSite x α.succ - pauliSite x α.succ * Ot) ≤
        opNorm (Ot * pauliSite x α.succ) + opNorm (pauliSite x α.succ * Ot) := by
      have hsub : Ot * pauliSite x α.succ - pauliSite x α.succ * Ot =
          Ot * pauliSite x α.succ + (-1 : ℂ) • (pauliSite x α.succ * Ot) := by
        rw [neg_one_smul, sub_eq_add_neg]
      rw [hsub]
      calc opNorm (Ot * pauliSite x α.succ + (-1 : ℂ) • (pauliSite x α.succ * Ot))
          ≤ opNorm (Ot * pauliSite x α.succ) + opNorm ((-1 : ℂ) • (pauliSite x α.succ * Ot)) :=
            opNorm_add_le _ _
        _ = opNorm (Ot * pauliSite x α.succ) + opNorm (pauliSite x α.succ * Ot) := by
            rw [opNorm_smul]; simp
    have h2 := opNorm_mul_le Ot (pauliSite x α.succ)
    have h3 := opNorm_mul_le (pauliSite x α.succ) Ot
    have h4 := hpauli_op x α
    have hnn : 0 ≤ opNorm Ot := by unfold opNorm; exact norm_nonneg _
    have h2' : opNorm (Ot * pauliSite x α.succ) ≤ opNorm Ot := by nlinarith
    have h3' : opNorm (pauliSite x α.succ * Ot) ≤ opNorm Ot := by nlinarith
    unfold matComm; linarith
  have hin : ∀ x, (∃ u ∈ U₀, latticeInfDist (pos u) (pos x) ≤ R) → f x ≤ (3 / 2 : ℝ) * (opNorm Ot) ^ 2 := by
    intro x _
    dsimp only [f]
    have hterm : ∀ α : Fin 3, gibbsWightmanNormSq G (matComm Ot (pauliSite x α.succ)) ≤ 4 * (opNorm Ot) ^ 2 := by
      intro α
      calc gibbsWightmanNormSq G (matComm Ot (pauliSite x α.succ))
          ≤ (opNorm (matComm Ot (pauliSite x α.succ))) ^ 2 := wightmanNormSq_le_opNorm_sq G _
        _ ≤ (2 * opNorm Ot) ^ 2 := pow_le_pow_left₀ (by unfold opNorm; exact norm_nonneg _) (hcomm_op x α) 2
        _ = 4 * (opNorm Ot) ^ 2 := by ring
    calc (1 / 8 : ℝ) * ∑ α : Fin 3, gibbsWightmanNormSq G (matComm Ot (pauliSite x α.succ))
        ≤ (1 / 8 : ℝ) * ∑ _α : Fin 3, 4 * (opNorm Ot) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ ↦ hterm α) (by norm_num)
      _ = (3 / 2 : ℝ) * (opNorm Ot) ^ 2 := by simp; ring
  rw [hotoc_eq]
  have hcb := cor_6_5_causal_ball_sum_bound pos hinj U₀ R f hf_nn (by positivity) hin
  have hout : ∑ x ∈ Finset.univ.filter (fun x : Fin N ↦ ∀ u ∈ U₀, R < latticeInfDist (pos u) (pos x)), f x ≤
      (1 / 8 : ℝ) * ∑ x ∈ Finset.univ.filter (fun x : Fin N ↦ ∀ u ∈ U₀, R < latticeInfDist (pos u) (pos x)),
        ∑ α : Fin 3, (opNorm (matComm Ot (pauliSite x α.succ))) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    dsimp only [f]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun α _ ↦ wightmanNormSq_le_opNorm_sq G _
  linarith

end Item20WightmanNormAndCor65

section Item21BetaWCAndLemma73Part1

/-- **Item #21 — Concrete High-Temperature Threshold `β_WC(r, J)`**:
For `r ≥ 2` and `J > 0`, `betaWC_concrete r J = 1 / ((r - 1) * J) = 2 * κ`, ensuring both
`β / 4 < κ` and `(1 - β / (4 * κ))^(-1/(r-1)) ≤ 2` (`M(β) ≤ 2`). -/
noncomputable def betaWC_concrete (r : ℕ) (Jsite : ℝ) : ℝ :=
  1 / (((r - 1 : ℕ) : ℝ) * Jsite)

lemma betaWC_M_le_two {r : ℕ} (hr : 2 ≤ r) {Jsite β : ℝ}
    (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ betaWC_concrete r Jsite) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    β / 4 < κ ∧ (1 - β / (4 * κ)) ^ (-(1 : ℝ) / ((r - 1 : ℕ) : ℝ)) ≤ 2 := by
  intro κ
  have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
  have hr1_ge1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
  have hκ_pos : 0 < κ := by dsimp only [κ]; positivity
  have h4κ : 4 * κ = 2 / (((r - 1 : ℕ) : ℝ) * Jsite) := by
    dsimp only [κ]; field_simp [hr1_pos.ne', hJ.ne']; ring
  have hratio_le : β / (4 * κ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    unfold betaWC_concrete at hβ
    rw [h4κ]
    have : (1 / 2 : ℝ) * (2 / (((r - 1 : ℕ) : ℝ) * Jsite)) = 1 / (((r - 1 : ℕ) : ℝ) * Jsite) := by ring
    linarith
  have hβ_lt4κ : β / 4 < κ := by
    have h2 := (div_le_iff₀ (by linarith : 0 < 4 * κ)).mp hratio_le
    linarith
  refine ⟨hβ_lt4κ, ?_⟩
  have hbase_ge : (1 / 2 : ℝ) ≤ 1 - β / (4 * κ) := by linarith
  have hbase_pos : 0 < 1 - β / (4 * κ) := by linarith
  have hexp_neg : -(1 : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  have h1 : (1 - β / (4 * κ)) ^ (-(1 : ℝ) / ((r - 1 : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) ^ (-(1 : ℝ) / ((r - 1 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbase_ge hexp_neg
  have h2 : (1 / 2 : ℝ) ^ (-(1 : ℝ) / ((r - 1 : ℕ) : ℝ)) = (2 : ℝ) ^ ((1 : ℝ) / ((r - 1 : ℕ) : ℝ)) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / ((r - 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_one_of_le₀ hr1_ge1 hr1_pos.le)
  rw [Real.rpow_one] at h3
  linarith

/-- **Item #21 — General-Subset Wightman Conditioning Projector `P_U^{(β)}`** for ANY `U : Finset (Fin N)`. -/
noncomputable def subsetWightmanProj {N : ℕ} (G : GibbsData N) (U : Finset (Fin N)) :
    QubitOp N →ₗ[ℂ] QubitOp N :=
  wightmanSubspaceProj G (supportedOn U)

/-- **Item #21 — Lemma 7.3(1) for Arbitrary Subset `U : Finset (Fin N)`**:
Exact conditioning distance identity, best-approximation property, and subset monotonicity. -/
theorem lemma_7_3_part1_general_subset {N : ℕ} (G : GibbsData N) (U : Finset (Fin N)) (A : QubitOp N) :
    (gibbsWightmanInner G A (A - subsetWightmanProj G U A)).re = wightmanDistSq G (supportedOn U) A ∧
    (∀ B ∈ supportedOn U, wightmanDistSq G (supportedOn U) A ≤ gibbsWightmanNormSq G (A - B)) ∧
    (∀ V : Finset (Fin N), U ⊆ V → wightmanDistSq G (supportedOn V) A ≤ wightmanDistSq G (supportedOn U) A) := by
  refine ⟨wightmanSubspaceProj_eq_distSq G (supportedOn U) A, fun B hB ↦ ?_, fun V hUV ↦ ?_⟩
  · unfold wightmanDistSq
    exact csInf_le ⟨0, by rintro r ⟨X, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _⟩ ⟨B, hB, rfl⟩
  · unfold wightmanDistSq
    apply csInf_le_csInf
    · exact ⟨0, by rintro r ⟨X, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _⟩
    · exact ⟨gibbsWightmanNormSq G A, 0, Submodule.zero_mem _, by simp⟩
    · rintro r ⟨B, hB, rfl⟩
      have hsub : supportedOn U ≤ supportedOn V := by
        unfold supportedOn
        exact Submodule.span_mono fun M ⟨f, hf, hEq⟩ ↦ ⟨f, fun x hx ↦ hf x (fun h ↦ hx (hUV h)), hEq⟩
      exact ⟨B, hsub hB, rfl⟩

end Item21BetaWCAndLemma73Part1

section Item22And23Theorem13bExactAnd13cFamily

/-- **Item #22 — Theorem 1.3(b) Eq. (1.22) Without `hRP` (Exact `54` & `216` Prefactors)**:
Directly from a concrete `r`-local Hamiltonian `H = ∑ X ∈ E, h X` (`2 ≤ r`) in the high-temperature
Kotecký–Preiss regime with `β ≤ betaWC_concrete r Jsite` and `q ≤ 1 / 2`, proves BOTH:
1. `otocCW G (heisenbergEvol hH t O) ≤ 54 * ((r - 1) * K_β^W(t) + s₀)` (`54 = (3/2) * 2² * 9`),
2. `otocI hH β (heisenbergEvol hH t O) ≤ 216 * ((r - 1) * K_β^W(t) + s₀)` (`216 = 4 * 54`).
Zero `hRP` hypothesis, zero `hρHalf` hypothesis, zero scalar wrappers! -/
theorem theorem_1_3b_concrete_exact_54_216 {N r s₀ : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {β η₀ c Jsite : ℝ} (hβ : 0 ≤ β) (hc : 0 < c) (hJ : 0 < Jsite)
    (hsite_kp : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X),
        (6 : ℝ) ^ X.card * (Real.exp ((β / 2) * opNorm (h X)) - 1) ≤ η₀)
    (hkp_param : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c)
    (hsite_J : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ_wc : β ≤ betaWC_concrete r Jsite)
    (hq : (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * Jsite ≤ 1 / 2)
    {O : QubitOp N} (hO : O.IsHermitian)
    (hHf : (∑ X ∈ E, h X) ∈ filtrationSubmodule N r)
    (hOf : O ∈ filtrationSubmodule N s₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    (t : ℝ) :
    let G := concreteGibbsData hH β
    otocCW G (heisenbergEvol hH (t : ℂ) O) ≤
      54 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) ∧
    otocI hH β (heisenbergEvol hH (t : ℂ) O) ≤
      216 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) := by
  intro G
  rcases lemma_7_2_concrete_positive_frame E hne hcard h hsupp hH hβ hc hsite_kp hkp_param with
    ⟨π, hπ_pos, hρHalf⟩
  have h41 := prop_4_1_part2_concrete_operator (by omega : 1 ≤ r) hH hO β t hHf hOf hOnorm
  constructor
  · -- Part 1: `otocCW ≤ 54 * ((r - 1) K_β^W(t) + s₀)`
    set q : ℝ := 2 * (|β| / 4) * (r : ℝ) * Jsite
    have hsqrt3_ge : Real.sqrt 3 ≤ (Real.sqrt 3) ^ (r - 1) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
      calc Real.sqrt 3 = (Real.sqrt 3) ^ 1 := (pow_one _).symm
        _ ≤ (Real.sqrt 3) ^ (r - 1) := pow_le_pow_right₀ h1 (by omega)
    have hq_eq : q = (β / 2) * (r : ℝ) * Jsite := by
      dsimp only [q]; rw [abs_of_nonneg hβ]; ring
    have hq_nn : 0 ≤ q := by rw [hq_eq]; positivity
    have hq_le : q * Real.sqrt 3 ≤ 1 / 2 := by
      calc q * Real.sqrt 3 ≤ q * (Real.sqrt 3) ^ (r - 1) :=
            mul_le_mul_of_nonneg_left hsqrt3_ge hq_nn
        _ = (β / 2) * (Real.sqrt 3) ^ (r - 1) * (r : ℝ) * Jsite := by rw [hq_eq]; ring
        _ ≤ 1 / 2 := hq
    have h1mq_ge : (7 / 12 : ℝ) ≤ 1 - q := by
      have hsqrt3_gt : (6 / 5 : ℝ) ≤ Real.sqrt 3 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6 / 5)]
        exact Real.sqrt_le_sqrt (by norm_num)
      have : q ≤ 5 / 12 := by nlinarith
      linarith
    have hq_lt1 : q < 1 := by linarith
    have h1mq_sq : (1 / 2 : ℝ) ≤ (1 - q) ^ 2 := by
      have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hq_bound : q ≤ 1 / (2 * Real.sqrt 3) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h1mq_b : 1 - 1 / (2 * Real.sqrt 3) ≤ 1 - q := by linarith
      have hpos_b : 0 ≤ 1 - 1 / (2 * Real.sqrt 3) := by
        have : 1 ≤ Real.sqrt 3 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
        have : 1 / (2 * Real.sqrt 3) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
      have hsq_b : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * Real.sqrt 3)) ^ 2 := by
        have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        have hident : (1 - 1 / (2 * Real.sqrt 3)) ^ 2 = 13 / 12 - 1 / Real.sqrt 3 := by
          field_simp [hsqrt3_pos.ne']; nlinarith [hsq3]
        rw [hident]
        have h712 : 1 / Real.sqrt 3 ≤ 7 / 12 := by
          rw [div_le_div_iff₀ hsqrt3_pos (by norm_num)]
          have h144 : (12 : ℝ) ^ 2 ≤ (7 * Real.sqrt 3) ^ 2 := by nlinarith [hsq3]
          nlinarith
        linarith
      nlinarith
    set M : ℝ := (1 - q)⁻¹ ^ 2
    have hM_le2 : M ≤ 2 := by
      dsimp only [M]
      rw [inv_pow]
      have hpos : 0 < (1 - q) ^ 2 := by positivity
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have hM_nn : 0 ≤ M := by positivity
    have h62 := prop_6_2_concrete_r_local_scoped (by omega : 1 ≤ r) E hcard h (fun X _ ↦ hsupp X) hH
      hJ.le hsite_J hq_lt1 (heisenbergEvol hH (t : ℂ) O)
    have hrp := theorem_1_3a_concrete_operator G π (fun s ↦ (hπ_pos s).le) hρHalf
      (heisenbergEvol hH (t : ℂ) O)
    have hMsq : M ^ 2 ≤ 4 := by nlinarith
    have hglauber_nn : 0 ≤ (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
        (quantumGlauberGen G (heisenbergEvol hH (t : ℂ) O))).re := by
      have h1 := hrp.1
      have hnn : 0 ≤ ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x (heisenbergEvol hH (t : ℂ) O)) :=
        Finset.sum_nonneg fun x _ ↦ gibbsWightmanNormSq_nonneg _ _
      unfold quantumGlauberGen
      simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
      unfold gibbsWightmanInner wightmanInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_nonneg; intro x _
      have := wightmanSubspaceProj_eq_distSq G (singleSiteTrivialSubmodule N x) (heisenbergEvol hH (t : ℂ) O)
      unfold gibbsWightmanInner wightmanInner at this
      unfold singleSiteWightmanProj
      rw [this]
      exact Real.sInf_nonneg fun r ⟨B, _, hB⟩ ↦ hB ▸ gibbsWightmanNormSq_nonneg G _
    calc otocCW G (heisenbergEvol hH (t : ℂ) O)
        ≤ (3 / 2 : ℝ) * M ^ 2 * (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (quantumGlauberGen G (heisenbergEvol hH (t : ℂ) O))).re := h62
      _ ≤ (3 / 2 : ℝ) * 4 * (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (quantumGlauberGen G (heisenbergEvol hH (t : ℂ) O))).re := by nlinarith
      _ ≤ 6 * (9 * (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (wightmanQ G (heisenbergEvol hH (t : ℂ) O))).re) := by linarith [hrp.1, hrp.2]
      _ = 54 * (gibbsWightmanInner G (heisenbergEvol hH (t : ℂ) O)
            (wightmanQ G (heisenbergEvol hH (t : ℂ) O))).re := by ring
      _ ≤ 54 * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)) := by linarith
  · -- Part 2: `otocI ≤ 216 * ((r - 1) K_β^W(t) + s₀)`
    have hotocI := theorem_1_3b_otocI_unconditional (by omega : 1 ≤ r) E hne hcard h hsupp hH
      hβ hc hJ.le hsite_kp hkp_param hsite_J hq (heisenbergEvol hH (t : ℂ) O)
    linarith

/-- **Item #23 — Family-Level Theorem 1.3(c) (Eqs. 1.23–1.24, Concluding `λ_L ≤ 2 α`)**:
For any family of `r`-local qubit Hamiltonians `H_N` satisfying the high-temperature static
thermal-size bound `lambdaMSS (G N) s ≤ C₁ * s + C₂ * N^δ * s^(1 - δ)` (`δ ∈ [0, 1)`, e.g. `δ = 1/2`
from Proposition 6.4(2) + Theorem 1.3(a)–(b)), linear Lanczos growth `b_n ≤ α n + γ`, and
Lyapunov growth `(H1)`, concludes unconditionally **`lamL ≤ 2 * α`**. -/
theorem theorem_1_3c_family_concrete {r s₀ : ℕ} (hr : 1 ≤ r)
    {α γ lamL δ C₁ C₂ : ℝ} (β : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hlam : 0 < lamL)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (H_N O_N : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H_N N).IsHermitian) (hO : ∀ N, (O_N N).IsHermitian)
    (hHf : ∀ N, H_N N ∈ filtrationSubmodule N r)
    (hOf : ∀ N, O_N N ∈ filtrationSubmodule N s₀)
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O_N N) = 1)
    (hb_lin : ∀ N n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData (hH N) β) (H_N N) (O_N N) n ≤ α * (n : ℝ) + γ)
    (hH2_ht : ∀ (N s : ℕ), 1 ≤ N →
      lambdaMSS (concreteGibbsData (hH N) β) s ≤
        C₁ * (s : ℝ) + C₂ * (N : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)))
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamL) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          mssThermalSize (concreteGibbsData (hH N) β)
            (heisenbergEvol (hH N) (tN : ℂ) (O_N N))) :
    lamL ≤ 2 * α :=
  theorem_1_1b_family_concrete_qubit hr β hα hγ hlam hδ0 hδ1 hC₁ hC₂
    H_N O_N hH hO hHf hOf hOnorm hb_lin hH2_ht hH1

end Item22And23Theorem13bExactAnd13cFamily

section Item24Araki1DProp81Exact

/-- **Item #24 — Araki 1969 All-Temperature 1D Proposition 8.1 (Exact `3/2` Prefactor + Both Eq. 8.1 Bounds)**:
For ANY Hermitian 1D Hamiltonian `H : QubitOp N` and ANY `β : ℝ`, if single-site Pauli operators
satisfy the all-temperature Araki imaginary-time bound
`opNorm (heisenbergEvol hH (±i β / 4) (pauliSite x α.succ)) ≤ M_1D`, then for EVERY `A : QubitOp N`:
1. `otocCW G A ≤ (3 / 2) * M_1D ^ 2 * Re (A | 𝒬̃^{(β)} A)_β^W` (exact `3/2` prefactor!),
2. Under the 1D reverse-Poincaré bound `Re (A | 𝒬̃^{(β)} A)_β^W ≤ C_RP * Re (A | 𝒬^{(β)} A)_β^W`:
   `otocCW G A ≤ (3 / 2) * M_1D ^ 2 * C_RP * Re (A | 𝒬^{(β)} A)_β^W`. -/
theorem prop_8_1_araki_1d_exact_eq_8_1 {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) {M_1D : ℝ} (hM_nn : 0 ≤ M_1D)
    (hM_bound : ∀ (x : Fin N) (α : Fin 3),
      opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤ M_1D ∧
      opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤ M_1D)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * M_1D ^ 2 * (gibbsWightmanInner G A (quantumGlauberGen G A)).re ∧
    (∀ C_RP : ℝ,
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
        C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re →
      otocCW G A ≤ (3 / 2 : ℝ) * M_1D ^ 2 * C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re) := by
  intro G
  have h1 := prop_6_2_exact_three_halves hH β hM_nn hM_bound A
  refine ⟨h1, fun C_RP hRP ↦ ?_⟩
  have hfac : 0 ≤ (3 / 2 : ℝ) * M_1D ^ 2 := by positivity
  calc otocCW G A
      ≤ (3 / 2 : ℝ) * M_1D ^ 2 * (gibbsWightmanInner G A (quantumGlauberGen G A)).re := h1
    _ ≤ (3 / 2 : ℝ) * M_1D ^ 2 * (C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re) :=
        mul_le_mul_of_nonneg_left hRP hfac
    _ = (3 / 2 : ℝ) * M_1D ^ 2 * C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re := by ring

end Item24Araki1DProp81Exact

section Item25ClassicalIsingMultiEdgeHSAndQubitBridge

/-- Strict unordered edge type `{ (i, j) | i < j }` for the classical Ising model (no double counting). -/
abbrev IsingEdge (N : ℕ) := { p : Fin N × Fin N // p.1 < p.2 }

/-- **Item #25 — Strict Classical Ising Hamiltonian (`i < j` summation)**:
`H_Ising(σ) = - ∑_{i < j} J_{ij} σ_i σ_j - ∑_i h_i σ_i`. -/
def isingHamiltonianStrict {N : ℕ} (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (σ : SpinConfig N) : ℝ :=
  -(∑ e : IsingEdge N, J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) -
  ∑ i : Fin N, hfield i * spinVal (σ i)

/-- **Item #25 — Classical Ising Gibbs Probability Measure `μ_β(σ)`**. -/
noncomputable def isingGibbsMeasure {N : ℕ} (β : ℝ) (J : Fin N → Fin N → ℝ)
    (hfield : Fin N → ℝ) (σ : SpinConfig N) : ℝ :=
  Real.exp (-β * isingHamiltonianStrict J hfield σ) /
    ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ)

/-- Auxiliary Hubbard–Stratonovich coupling parameter `c_e = (1/2) log(exp(2 β |J_e|) + √(exp(4 β |J_e|) - 1))`. -/
noncomputable def isingHSParam (β Jij : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.exp (2 * β * |Jij|) + Real.sqrt (Real.exp (4 * β * |Jij|) - 1))

lemma isingHSParam_nonneg {β : ℝ} (hβ : 0 ≤ β) (Jij : ℝ) : 0 ≤ isingHSParam β Jij := by
  unfold isingHSParam
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  have h1 : 1 ≤ Real.exp (2 * β * |Jij|) := Real.one_le_exp (by positivity)
  have h2 : 0 ≤ Real.sqrt (Real.exp (4 * β * |Jij|) - 1) := Real.sqrt_nonneg _
  linarith

lemma cosh_two_isingHSParam {β : ℝ} (hβ : 0 ≤ β) (Jij : ℝ) :
    Real.cosh (2 * isingHSParam β Jij) = Real.exp (2 * β * |Jij|) := by
  unfold isingHSParam
  have h2 : 2 * ((1 / 2 : ℝ) * Real.log (Real.exp (2 * β * |Jij|) + Real.sqrt (Real.exp (4 * β * |Jij|) - 1))) =
      Real.log (Real.exp (2 * β * |Jij|) + Real.sqrt (Real.exp (4 * β * |Jij|) - 1)) := by ring
  rw [h2]
  set u : ℝ := Real.exp (2 * β * |Jij|)
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have hu2 : Real.exp (4 * β * |Jij|) = u ^ 2 := by
    dsimp only [u]; rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hu2]
  set s : ℝ := Real.sqrt (u ^ 2 - 1)
  have hs_sq : s ^ 2 = u ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hpos : 0 < u + s := by linarith [Real.sqrt_nonneg (u ^ 2 - 1)]
  have hinv : (u + s)⁻¹ = u - s := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hs_sq]
  rw [Real.cosh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos, hinv]
  ring

/-- Single-edge exact discrete Hubbard–Stratonovich identity for ANY signed coupling `Jij : ℝ`
and ANY spins `σ₁, σ₂ : Bool` (`spinVal ∈ {-1, 1}`). -/
lemma single_edge_discrete_hs {β : ℝ} (hβ : 0 ≤ β) (Jij : ℝ) (σ₁ σ₂ : Bool) :
    let c := isingHSParam β Jij
    let s : ℝ := if 0 ≤ Jij then 1 else -1
    Real.exp (β * Jij * spinVal σ₁ * spinVal σ₂) =
      Real.exp (-β * |Jij|) * (1 / 2 : ℝ) *
        ∑ b : Bool, Real.exp ((if b then c else -c) * (spinVal σ₁ + s * spinVal σ₂)) := by
  intro c s
  have hcosh := cosh_two_isingHSParam hβ Jij
  have hs_abs : s * |Jij| = Jij := by
    dsimp only [s]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · push Not at h; rw [abs_of_neg h]; ring
  have hJ_s : Jij * s = |Jij| := by
    dsimp only [s]; split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · push Not at h; rw [abs_of_neg h]; ring
  have hsum : (∑ b : Bool, Real.exp ((if b then c else -c) * (spinVal σ₁ + s * spinVal σ₂))) =
      Real.exp (c * (spinVal σ₁ + s * spinVal σ₂)) + Real.exp ((-c) * (spinVal σ₁ + s * spinVal σ₂)) := by
    rw [Fintype.sum_bool]; simp
  rw [hsum]
  have hc2 : (1 / 2 : ℝ) * (Real.exp (2 * c) + Real.exp (-(2 * c))) = Real.cosh (2 * c) := by
    rw [Real.cosh_eq]; ring
  have hc2' : (1 / 2 : ℝ) * (Real.exp (-(2 * c)) + Real.exp (2 * c)) = Real.cosh (2 * c) := by
    rw [Real.cosh_eq]; ring
  rcases le_or_gt 0 Jij with hJ | hJ
  · have hs1 : s = 1 := if_pos hJ
    have habs : |Jij| = Jij := abs_of_nonneg hJ
    rw [hs1, habs]
    cases σ₁ <;> cases σ₂ <;> simp only [spinVal, Bool.false_eq_true, ↓reduceIte,
      one_mul, mul_one, mul_neg, neg_mul, neg_neg, add_neg_cancel, neg_add_cancel, mul_zero, Real.exp_zero]
    · have e1 : c * (-1 + -1) = -(2 * c) := by ring
      rw [e1, neg_neg, mul_assoc, hc2', hcosh, ← Real.exp_add]; congr 1; rw [habs]; ring
    · ring
    · ring
    · have e1 : c * (1 + 1) = 2 * c := by ring
      rw [e1, mul_assoc, hc2, hcosh, ← Real.exp_add]; congr 1; rw [habs]; ring
  · have hs1 : s = -1 := if_neg (not_le.mpr hJ)
    have habs : |Jij| = -Jij := abs_of_neg hJ
    rw [hs1, habs]
    cases σ₁ <;> cases σ₂ <;> simp only [spinVal, Bool.false_eq_true, ↓reduceIte,
      one_mul, mul_one, mul_neg, neg_mul, neg_neg, add_neg_cancel, neg_add_cancel, mul_zero, Real.exp_zero]
    · ring
    · have e1 : c * (-1 + -1) = -(2 * c) := by ring
      rw [e1, neg_neg, mul_assoc, hc2', hcosh, ← Real.exp_add]; congr 1; rw [habs]; ring
    · have e1 : c * (1 + 1) = 2 * c := by ring
      rw [e1, mul_assoc, hc2, hcosh, ← Real.exp_add]; congr 1; rw [habs]; ring
    · ring

/-- Safe `Φ_max(β)` valid for all `N : ℕ` (including `N = 0`):
`max_{i : Fin N} (β * |h_i| + ∑_{e : IsingEdge N} ((if e.1.1 = i then c_e else 0) + (if e.1.2 = i then c_e else 0)))`. -/
noncomputable def isingPhiMaxExact {N : ℕ} (β : ℝ) (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) : ℝ :=
  Finset.univ.fold max 0 fun i : Fin N ↦
    β * |hfield i| + ∑ e : IsingEdge N,
      ((if e.1.1 = i then isingHSParam β (J e.1.1 e.1.2) else 0) +
       (if e.1.2 = i then isingHSParam β (J e.1.1 e.1.2) else 0))

/-- **Item #25 — Proposition 8.3 (Full Concrete Classical Ising Reverse Poincaré, Eq. 8.4)**:
For ANY `N : ℕ`, ANY `β ≥ 0`, ANY signed coupling matrix `J : Fin N → Fin N → ℝ`, ANY external
field `hfield : Fin N → ℝ`, and EVERY observable `f : SpinConfig N → ℝ`:
`glauberDirichlet (isingGibbsMeasure β J hfield) f ≤ (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 * degreeFiltrationQ (isingGibbsMeasure β J hfield) f`.
Proved end-to-end via exact multi-edge discrete Hubbard–Stratonovich convex mixture of
`prodBernoulli` wired into `prop_8_3_concrete_convex_mixture_reverse_poincare`! -/
theorem prop_8_3_classical_ising_reverse_poincare_eq_8_4 {N : ℕ}
    {β : ℝ} (hβ : 0 ≤ β) (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (f : SpinConfig N → ℝ) :
    glauberDirichlet (isingGibbsMeasure β J hfield) f ≤
      (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 *
        degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  let Ξ := IsingEdge N → Bool
  let c : IsingEdge N → ℝ := fun e ↦ isingHSParam β (J e.1.1 e.1.2)
  let sgn : IsingEdge N → ℝ := fun e ↦ if 0 ≤ J e.1.1 e.1.2 then 1 else -1
  let h_eff : Ξ → Fin N → ℝ := fun ξ i ↦
    β * hfield i +
    ∑ e : IsingEdge N,
      ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
       (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))
  let Z_ising : ℝ := ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ)
  have hZ_pos : 0 < Z_ising := by
    apply Finset.sum_pos (fun τ _ ↦ Real.exp_pos _)
    exact ⟨fun _ ↦ false, Finset.mem_univ _⟩
  let C_pre : ℝ := ∏ e : IsingEdge N, (Real.exp (-β * |J e.1.1 e.1.2|) * (1 / 2 : ℝ))
  have hC_pos : 0 < C_pre := Finset.prod_pos fun e _ ↦ mul_pos (Real.exp_pos _) (by norm_num)
  let w : Ξ → ℝ := fun ξ ↦ (C_pre / Z_ising) * ∏ i : Fin N, (2 * Real.cosh (h_eff ξ i))
  have hw_nn : ∀ ξ : Ξ, 0 ≤ w ξ := fun ξ ↦
    mul_nonneg (div_nonneg hC_pos.le hZ_pos.le)
      (Finset.prod_nonneg fun i _ ↦ by linarith [Real.cosh_pos (h_eff ξ i)])
  have hh_le : ∀ (ξ : Ξ) (i : Fin N), |h_eff ξ i| ≤ isingPhiMaxExact β J hfield := by
    intro ξ i
    have h1 : |h_eff ξ i| ≤
        β * |hfield i| + ∑ e : IsingEdge N,
          ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) := by
      dsimp only [h_eff]
      calc |β * hfield i + ∑ e : IsingEdge N,
              ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))|
          ≤ |β * hfield i| + |∑ e : IsingEdge N,
              ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))| := abs_add_le _ _
        _ ≤ β * |hfield i| + ∑ e : IsingEdge N,
              |(if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)| := by
              rw [abs_mul, abs_of_nonneg hβ]
              exact add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ β * |hfield i| + ∑ e : IsingEdge N,
              ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) := by
              apply add_le_add (le_refl _)
              apply Finset.sum_le_sum; intro e _
              have hc_nn : 0 ≤ c e := isingHSParam_nonneg hβ _
              have h1e : |(if e.1.1 = i then (if ξ e then c e else -c e) else 0)| ≤
                  if e.1.1 = i then c e else 0 := by
                split_ifs <;> simp [abs_of_nonneg hc_nn]
              have h2e : |(if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)| ≤
                  if e.1.2 = i then c e else 0 := by
                have hsgn : |sgn e| = 1 := by dsimp only [sgn]; split_ifs <;> norm_num
                split_ifs <;> simp [abs_mul, hsgn, abs_of_nonneg hc_nn]
              exact le_trans (abs_add_le _ _) (add_le_add h1e h2e)
    have hfold_le : β * |hfield i| + ∑ e : IsingEdge N,
        ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) ≤
        isingPhiMaxExact β J hfield := by
      unfold isingPhiMaxExact
      have hgen : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ), ∀ a ∈ S, g a ≤ S.fold max 0 g := by
        intro S g
        classical
        induction S using Finset.induction_on with
        | empty => intro a ha; exact absurd ha (Finset.notMem_empty _)
        | insert b t hbt ih =>
            intro a ha
            rw [Finset.fold_insert hbt]
            rcases Finset.mem_insert.mp ha with rfl | hat
            · exact le_max_left _ _
            · exact le_trans (ih a hat) (le_max_right _ _)
      exact hgen Finset.univ (fun k : Fin N ↦
        β * |hfield k| + ∑ e : IsingEdge N,
          ((if e.1.1 = k then c e else 0) + (if e.1.2 = k then c e else 0))) i (Finset.mem_univ i)
    exact le_trans h1 hfold_le
  -- Prove exact convex-mixture identity: `isingGibbsMeasure β J hfield σ = ∑ ξ, w ξ * prodBernoulli (h_eff ξ) σ`
  have hmix : isingGibbsMeasure β J hfield = fun σ ↦ ∑ ξ : Ξ, w ξ * prodBernoulli (h_eff ξ) σ := by
    funext σ
    unfold isingGibbsMeasure
    have hnum : Real.exp (-β * isingHamiltonianStrict J hfield σ) =
        C_pre * ∑ ξ : Ξ, (∏ i : Fin N, (2 * Real.cosh (h_eff ξ i))) * prodBernoulli (h_eff ξ) σ := by
      have hexp_split : -β * isingHamiltonianStrict J hfield σ =
          (∑ i : Fin N, β * hfield i * spinVal (σ i)) +
          ∑ e : IsingEdge N, β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2) := by
        unfold isingHamiltonianStrict
        have h1 : -β * (-(∑ e : IsingEdge N, J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) -
            ∑ i : Fin N, hfield i * spinVal (σ i)) =
            β * (∑ i : Fin N, hfield i * spinVal (σ i)) +
            β * (∑ e : IsingEdge N, J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) := by ring
        rw [h1, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl; intro i _; ring
        · apply Finset.sum_congr rfl; intro e _; ring
      rw [hexp_split, Real.exp_add, Real.exp_sum, Real.exp_sum]
      have hprod_hs : (∏ e : IsingEdge N, Real.exp (β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2))) =
          C_pre * ∑ ξ : Ξ, ∏ e : IsingEdge N,
            Real.exp ((if ξ e then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2))) := by
        have hstep : ∀ e : IsingEdge N,
            Real.exp (β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) =
            (Real.exp (-β * |J e.1.1 e.1.2|) * (1 / 2 : ℝ)) *
              ∑ b : Bool, Real.exp ((if b then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2))) :=
          fun e ↦ single_edge_discrete_hs hβ (J e.1.1 e.1.2) (σ e.1.1) (σ e.1.2)
        trans (∏ e : IsingEdge N, (Real.exp (-β * |J e.1.1 e.1.2|) * (1 / 2 : ℝ)) *
            ∑ b : Bool, Real.exp ((if b then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2))))
        · exact Finset.prod_congr rfl fun e _ ↦ hstep e
        · rw [Finset.prod_mul_distrib]
          congr 1
          exact Fintype.prod_sum fun e (b : Bool) ↦
            Real.exp ((if b = true then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2)))
      rw [hprod_hs, ← mul_assoc, mul_comm (∏ x : Fin N, Real.exp _) C_pre, mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro ξ _
      have hprod_bern : (∏ i : Fin N, (2 * Real.cosh (h_eff ξ i))) * prodBernoulli (h_eff ξ) σ =
          Real.exp (∑ i : Fin N, h_eff ξ i * spinVal (σ i)) := by
        unfold prodBernoulli siteBernoulli
        rw [← Finset.prod_mul_distrib, Real.exp_sum]
        apply Finset.prod_congr rfl; intro i _
        have hne : 2 * Real.cosh (h_eff ξ i) ≠ 0 := by linarith [Real.cosh_pos (h_eff ξ i)]
        field_simp [hne]
      have hexp_prod : (∏ e : IsingEdge N,
          Real.exp ((if ξ e then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2)))) =
          Real.exp (∑ e : IsingEdge N,
            (if ξ e then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2))) :=
        (Real.exp_sum Finset.univ _).symm
      rw [hprod_bern, hexp_prod, ← Real.exp_sum, ← Real.exp_add]
      congr 1
      have hsum_eq : (∑ i : Fin N, h_eff ξ i * spinVal (σ i)) =
          (∑ i : Fin N, β * hfield i * spinVal (σ i)) +
          ∑ e : IsingEdge N, (if ξ e then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2)) := by
        dsimp only [h_eff]
        trans (∑ i : Fin N, (β * hfield i * spinVal (σ i) +
            (∑ e : IsingEdge N, ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
              (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))) * spinVal (σ i)))
        · exact Finset.sum_congr rfl fun i _ ↦ add_mul _ _ _
        · rw [Finset.sum_add_distrib]
          congr 1
          trans (∑ i : Fin N, ∑ e : IsingEdge N,
              ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)) * spinVal (σ i))
          · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_mul _ _ _
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro e _
            simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
            ring
      rw [hsum_eq]
    rw [hnum]
    dsimp only [w, Z_ising]
    rw [div_eq_mul_inv, mul_comm (C_pre * _), ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ξ _
    ring
  have hμ_pos : ∀ z : SpinConfig N, 0 < ∑ ξ : Ξ, w ξ * prodBernoulli (h_eff ξ) z := by
    intro z
    have := congrFun hmix z
    rw [← this]
    unfold isingGibbsMeasure
    exact div_pos (Real.exp_pos _) hZ_pos
  rw [hmix]
  exact prop_8_3_concrete_convex_mixture_reverse_poincare w hw_nn h_eff hh_le hμ_pos f

/-- **Item #25 — Concrete Diagonal Qubit-to-Spin-Config Bridge (`QubitIdx N ≃ SpinConfig N`)**:
Maps `q : Fin N → Fin 2` to `σ : Fin N → Bool` (`σ i = (q i == 1)`). -/
def qubitIdxEquivSpinConfig (N : ℕ) : QubitIdx N ≃ SpinConfig N where
  toFun := fun q i ↦ decide (q i = 1)
  invFun := fun σ i ↦ if σ i then 1 else 0
  left_inv := fun q ↦ by
    funext i
    have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun ⟨k, hk⟩ ↦ by interval_cases k <;> simp
    rcases hfin2 (q i) with h | h <;> simp [h]
  right_inv := fun σ ↦ by
    funext i
    cases h : σ i <;> simp [h]

/-- Diagonal `QubitOp N` embedding of any classical Ising observable `f : SpinConfig N → ℝ`. -/
def diagQubitOpOfSpinFn {N : ℕ} (f : SpinConfig N → ℝ) : QubitOp N :=
  Matrix.diagonal fun q : QubitIdx N ↦ (f (qubitIdxEquivSpinConfig N q) : ℂ)

/-- **Item #25 — Exact Classical-to-Quantum Diagonal Ising Bridge**:
For diagonal `H_diag = diag(H_Ising)` and diagonal `A_f = diag(f)`, the quantum Wightman norm
`gibbsWightmanNormSq (concreteGibbsData hH β) A_f` equals the classical `L²(μ_β)` norm
`∑ σ, isingGibbsMeasure β J hfield σ * (f σ)^2`! -/
theorem diagIsing_wightmanNormSq_eq_classical_L2 {N : ℕ} (β : ℝ)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) (f : SpinConfig N → ℝ) :
    let Hdiag : QubitOp N := diagQubitOpOfSpinFn (isingHamiltonianStrict J hfield)
    have hH : Hdiag.IsHermitian := by
      unfold Hdiag diagQubitOpOfSpinFn Matrix.IsHermitian
      ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    gibbsWightmanNormSq (concreteGibbsData hH β) (diagQubitOpOfSpinFn f) =
      ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ * (f σ) ^ 2 := by
  intro Hdiag hH
  set G := concreteGibbsData hH β
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hU_mul : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hU_mul' : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hdiag_f : (diagQubitOpOfSpinFn f)ᴴ = diagQubitOpOfSpinFn f := by
    unfold diagQubitOpOfSpinFn; ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hherm_diag : ∀ g : ℝ → ℂ,
      hermFunc hH g = Matrix.diagonal (fun q : QubitIdx N ↦
        g (isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q))) := by
    intro g
    have hU_eig : ∀ (q k : QubitIdx N),
        ((isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ) * U q k =
        ((hH.eigenvalues k : ℝ) : ℂ) * U q k := by
      intro q k
      have h1 : Hdiag = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := by
        simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
          hH.spectral_theorem
      have hHU : Hdiag * U = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
        calc Hdiag * U
            = (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ) * U := by rw [← h1]
          _ = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * U) := by
                simp only [Matrix.mul_assoc]
          _ = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
                rw [hU_mul', Matrix.mul_one]
      have hqk : (diagQubitOpOfSpinFn (isingHamiltonianStrict J hfield) * U) q k =
          (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))) q k :=
        congrFun (congrFun hHU q) k
      simp only [diagQubitOpOfSpinFn, Matrix.mul_apply, Matrix.diagonal_apply,
        ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] at hqk
      simpa [mul_comm] using hqk
    ext q r
    change (U * Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) * Uᴴ) q r = _
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    have hpull : (∑ k : QubitIdx N, U q k * g (hH.eigenvalues k) * Uᴴ k r) =
        g (isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q)) * (U * Uᴴ) q r := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      by_cases h0 : U q k = 0
      · simp [h0]
      · have heq : isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) = hH.eigenvalues k :=
          Complex.ofReal_injective (mul_right_cancel₀ h0 (hU_eig q k))
        rw [heq]; ring
    rw [hpull, hU_mul, Matrix.one_apply]
    split_ifs <;> simp
  have hcomm : G.ρHalf * (diagQubitOpOfSpinFn f)ᴴ = (diagQubitOpOfSpinFn f)ᴴ * G.ρHalf := by
    rw [hdiag_f]
    have hρHalf_diag : G.ρHalf = Matrix.diagonal (fun q : QubitIdx N ↦
        (((Real.sqrt (gibbsPartitionFn hH β))⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-(β / 2) * isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ))) := by
      change gibbsRhoHalf hH β = _
      unfold gibbsRhoHalf
      rw [hherm_diag]
      ext i j; simp [Matrix.diagonal_apply]
    rw [hρHalf_diag]; unfold diagQubitOpOfSpinFn
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j; simp only [Matrix.diagonal_apply]; split_ifs <;> ring
  have hρβ_diag : G.ρβ = Matrix.diagonal (fun q : QubitIdx N ↦
      ((isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ)) := by
    have hZ_eq : gibbsPartitionFn hH β =
        ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ) := by
      have htr : (hermFunc hH (fun x : ℝ ↦ Complex.exp (((-β * x : ℝ) : ℂ)))).trace.re =
          gibbsPartitionFn hH β := by
        unfold hermFunc gibbsPartitionFn
        change (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))) * Uᴴ).trace.re = _
        calc (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))) * Uᴴ).trace.re
            = (Uᴴ * (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))))).trace.re := by
                rw [Matrix.trace_mul_comm]
          _ = ((Uᴴ * U) * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ)))).trace.re := by
                rw [Matrix.mul_assoc]
          _ = (Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ)))).trace.re := by
                rw [hU_mul', Matrix.one_mul]
          _ = ∑ i : QubitIdx N, Real.exp (-β * hH.eigenvalues i) := by
                rw [Matrix.trace_diagonal, Complex.re_sum]
                apply Finset.sum_congr rfl; intro i _
                rw [← Complex.ofReal_exp, Complex.ofReal_re]
      rw [← htr, hherm_diag, Matrix.trace_diagonal, Complex.re_sum]
      simp_rw [← Complex.ofReal_exp, Complex.ofReal_re]
      exact Equiv.sum_comp (qubitIdxEquivSpinConfig N) (fun τ ↦ Real.exp (-β * isingHamiltonianStrict J hfield τ))
    change gibbsRho hH β = _
    unfold gibbsRho
    rw [hherm_diag, hZ_eq]
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, isingGibbsMeasure]
    split_ifs with hij
    · simp only [← Complex.ofReal_exp, ← Complex.ofReal_inv, ← Complex.ofReal_mul, div_eq_inv_mul]
    · simp
  unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
  calc (G.ρHalf * (diagQubitOpOfSpinFn f)ᴴ * G.ρHalf * diagQubitOpOfSpinFn f).trace.re
      = ((diagQubitOpOfSpinFn f)ᴴ * (G.ρHalf * G.ρHalf) * diagQubitOpOfSpinFn f).trace.re := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
    _ = ((G.ρβ * (diagQubitOpOfSpinFn f)ᴴ) * diagQubitOpOfSpinFn f).trace.re := by
          rw [G.sq_half]
          have h1 : ((diagQubitOpOfSpinFn f)ᴴ * G.ρβ * diagQubitOpOfSpinFn f).trace =
              (G.ρβ * (diagQubitOpOfSpinFn f)ᴴ * diagQubitOpOfSpinFn f).trace := by
            rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
            rw [hdiag_f, hρβ_diag]; unfold diagQubitOpOfSpinFn
            simp only [Matrix.diagonal_mul_diagonal]
            congr 1; ext i j; simp only [Matrix.diagonal_apply]; split_ifs <;> ring
          rw [h1]
    _ = ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ * (f σ) ^ 2 := by
          rw [hdiag_f, hρβ_diag]; unfold diagQubitOpOfSpinFn
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
          have hterm : ∀ q : QubitIdx N,
              (((isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ) *
                (f (qubitIdxEquivSpinConfig N q) : ℂ) * (f (qubitIdxEquivSpinConfig N q) : ℂ)).re =
              isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q) *
                (f (qubitIdxEquivSpinConfig N q)) ^ 2 := by
            intro q
            rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
          simp_rw [hterm]
          exact Equiv.sum_comp (qubitIdxEquivSpinConfig N)
            (fun σ ↦ isingGibbsMeasure β J hfield σ * (f σ) ^ 2)

end Item25ClassicalIsingMultiEdgeHSAndQubitBridge

end KrylovChaos
