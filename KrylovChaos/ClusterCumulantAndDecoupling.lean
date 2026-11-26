/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.CausalExpansion
import KrylovChaos.OperatorGlauberAndLanczosFiltration

/-!
# Concrete Trace Cumulant Expansion (Lemma 6.3), Entropic Background Decoupling (Prop. 6.4(2)),
# and Lattice Lieb–Robinson Propagation (Corollary 6.5)

Closes Open Sub-Gap 3 strictly on top of Mathlib `v4.35.0` with zero custom axioms,
zero `sorry`s, and zero hypothesis-laundering:
1. **Concrete Power-Series Schwarz Lemma** (`power_series_schwarz_bound`) and
   **Normalized Trace Polymer Expansion** (`normalizedTrace`, `normalizedTrace_mul_of_disjoint`,
   `norm_normalizedTrace_le`, `lemma_6_3_trace_polymer_kp` via `kotecky_preiss_convergence`
   and `lemma_A_3_concrete_unordered_tree_sum`).
2. **Concrete Entropic Background Decoupling (Prop. 6.4(2))**:
   - `gibbsRelEntropy_unitary_invariant` & `gibbsRelEntropy_heisenberg_invariant`:
     exact unitary invariance `D(U ρ Uᴴ ‖ ρ_β) = D(ρ ‖ ρ_β)` when `[U, H] = 0`, in particular
     for `U = exp(i t H)`.
   - `gibbsRelEntropy_le_log_of_renyi2`: elementary proof `D(ρ ‖ ρ_β) ≤ log C` whenever
     `Tr(ρ^2 ρ_β^{-1}) ≤ C` (Petz–Rényi `D_1 ≤ D_2 ≤ D_∞` without operator monotonicity).
   - `prop_6_4_2_concrete_entropic_decoupling`: combines `gibbs_variational_bound`,
     `gibbsRelEntropy_heisenberg_invariant`, and quadratic cumulant optimization on `QubitOp N`.
3. **Concrete Lattice Lieb–Robinson Bound (Corollary 6.5)**:
   - `causalUnion_dist_le` and `matComm_iterComm_eq_zero_of_dist`: exact light-cone support
     growth under `iterComm` for finite-range interactions on any finite metric `(Fin N, dist)`.
   - `lieb_robinson_concrete_opNorm`: concrete operator-norm Lieb–Robinson tail bound on
     `opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B)` directly from `hasSum_heisenbergEvol_adPow`,
     `adPowMat_eq_sum_causal`, and `fwdCausalSum_le`.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section SchwarzAndTracePolymer

/-- **Concrete Schwarz Lemma for Convergent Power Series**:
If `f(ζ) = ∑' n, a n * ζ ^ n` has `a 0 = 0`, `a 1 = 0`, and `∑' n, ‖a n‖ * R ^ n ≤ M` (`0 < R`),
then for every `ζ : ℂ` with `‖ζ‖ ≤ R`, `‖∑' n, a n * ζ ^ n‖ ≤ M * (‖ζ‖ / R) ^ 2`. -/
theorem power_series_schwarz_bound (a : ℕ → ℂ) {R M : ℝ} (hR : 0 < R)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hsumm : Summable (fun n ↦ ‖a n‖ * R ^ n))
    (hM : ∑' n, ‖a n‖ * R ^ n ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ R) :
    ‖∑' n, a n * ζ ^ n‖ ≤ M * (‖ζ‖ / R) ^ 2 := by
  have hq_nn : 0 ≤ ‖ζ‖ / R := div_nonneg (norm_nonneg ζ) hR.le
  have hq_le1 : ‖ζ‖ / R ≤ 1 := (div_le_one hR).mpr hζ
  have hterm : ∀ n : ℕ, ‖a n * ζ ^ n‖ ≤ (‖ζ‖ / R) ^ 2 * (‖a n‖ * R ^ n) := by
    intro n
    match n with
    | 0 => simp [ha0]
    | 1 => simp [ha1]
    | m + 2 =>
      rw [norm_mul, norm_pow]
      have hpow : ‖ζ‖ ^ (m + 2) = (‖ζ‖ / R) ^ (m + 2) * R ^ (m + 2) := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')]
      rw [hpow]
      have hq_pow : (‖ζ‖ / R) ^ (m + 2) ≤ (‖ζ‖ / R) ^ 2 := by
        rw [pow_add]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hq_nn hq_le1)
      have hfac : 0 ≤ ‖a (m + 2)‖ * R ^ (m + 2) :=
        mul_nonneg (norm_nonneg _) (pow_nonneg hR.le _)
      calc ‖a (m + 2)‖ * ((‖ζ‖ / R) ^ (m + 2) * R ^ (m + 2))
          = (‖ζ‖ / R) ^ (m + 2) * (‖a (m + 2)‖ * R ^ (m + 2)) := by ring
        _ ≤ (‖ζ‖ / R) ^ 2 * (‖a (m + 2)‖ * R ^ (m + 2)) :=
            mul_le_mul_of_nonneg_right hq_pow hfac
  have hsumm_norm : Summable (fun n ↦ ‖a n * ζ ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm (hsumm.mul_left _)
  calc ‖∑' n, a n * ζ ^ n‖
      ≤ ∑' n, ‖a n * ζ ^ n‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n, (‖ζ‖ / R) ^ 2 * (‖a n‖ * R ^ n) :=
        hsumm_norm.tsum_le_tsum hterm (hsumm.mul_left _)
    _ = (‖ζ‖ / R) ^ 2 * ∑' n, ‖a n‖ * R ^ n := tsum_mul_left
    _ ≤ (‖ζ‖ / R) ^ 2 * M := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
    _ = M * (‖ζ‖ / R) ^ 2 := by ring

/-- Normalized trace `τ(A) := 2^{-N} Tr(A)` on `QubitOp N`. -/
noncomputable def normalizedTrace {N : ℕ} (A : QubitOp N) : ℂ :=
  (((2 : ℝ) ^ N : ℂ)⁻¹) * A.trace

lemma normalizedTrace_one {N : ℕ} : normalizedTrace (1 : QubitOp N) = 1 := by
  unfold normalizedTrace
  have htr : (1 : QubitOp N).trace = ((2 : ℝ) ^ N : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.one_apply_eq, Finset.sum_const,
      Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul,
      mul_one]
    push_cast; rfl
  rw [htr]
  have hne : ((2 : ℝ) ^ N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact inv_mul_cancel₀ hne

lemma normalizedTrace_add {N : ℕ} (A B : QubitOp N) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  unfold normalizedTrace; rw [Matrix.trace_add, mul_add]

lemma normalizedTrace_smul {N : ℕ} (c : ℂ) (A : QubitOp N) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  unfold normalizedTrace; rw [Matrix.trace_smul, smul_eq_mul]; ring

lemma normalizedTrace_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QubitOp N) :
    normalizedTrace (∑ i ∈ s, f i) = ∑ i ∈ s, normalizedTrace (f i) := by
  unfold normalizedTrace; rw [Matrix.trace_sum, Finset.mul_sum]

lemma norm_normalizedTrace_le {N : ℕ} (A : QubitOp N) :
    ‖normalizedTrace A‖ ≤ opNorm A := by
  unfold normalizedTrace
  rw [norm_mul, norm_inv]
  have h2 : ‖((2 : ℝ) ^ N : ℂ)‖ = (2 : ℝ) ^ N := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h2]
  have htr : ‖A.trace‖ ≤ (2 : ℝ) ^ N * opNorm A := by
    calc ‖A.trace‖ = ‖∑ i : QubitIdx N, A i i‖ := rfl
      _ ≤ ∑ i : QubitIdx N, ‖A i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : QubitIdx N, opNorm A :=
          Finset.sum_le_sum fun i _ ↦ norm_entry_le_opNorm A i i
      _ = (Fintype.card (QubitIdx N) : ℝ) * opNorm A := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (2 : ℝ) ^ N * opNorm A := by
          simp [QubitIdx, Fintype.card_pi, Fintype.card_fin]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  calc ((2 : ℝ) ^ N)⁻¹ * ‖A.trace‖
      ≤ ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ N * opNorm A) :=
        mul_le_mul_of_nonneg_left htr (inv_nonneg.mpr hpos.le)
    _ = opNorm A := by field_simp [hpos.ne']

lemma normalizedTrace_mul_of_disjoint {N : ℕ} {U V : Finset (Fin N)}
    (hdisj : Disjoint U V) {A B : QubitOp N}
    (hA : A ∈ supportedOn U) (hB : B ∈ supportedOn V) :
    normalizedTrace (A * B) = normalizedTrace A * normalizedTrace B := by
  have hpauli_tr : ∀ a : Fin N → Fin 4,
      normalizedTrace (pauliString a) = ∏ x : Fin N, ((1 / 2 : ℂ) * (pauliMat (a x)).trace) := by
    intro a
    unfold normalizedTrace pauliString
    rw [kronOp_trace, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [one_div, inv_pow]
    push_cast; rfl
  have hpauli0 : (1 / 2 : ℂ) * (pauliMat 0).trace = 1 := by
    simp [pauliMat, Matrix.trace, Fin.sum_univ_two]
  have hmat0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext p q; fin_cases p <;> fin_cases q <;> simp [pauliMat]
  induction hA using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ⟨a, ha, rfl⟩
    induction hB using Submodule.span_induction with
    | mem Q hQ =>
      rcases hQ with ⟨b, hb, rfl⟩
      have hmul : pauliString a * pauliString b =
          kronOp (fun x ↦ pauliMat (a x) * pauliMat (b x)) := by
        unfold pauliString; rw [kronOp_mul]
      rw [hmul, hpauli_tr, hpauli_tr]
      unfold normalizedTrace
      rw [kronOp_trace, ← Finset.prod_mul_distrib]
      have hinv : (((2 : ℝ) ^ N : ℂ)⁻¹) = ∏ _x : Fin N, (1 / 2 : ℂ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div, inv_pow]
        push_cast; rfl
      rw [hinv, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro x _
      by_cases hxU : x ∈ U
      · have hxV : x ∉ V := Finset.disjoint_left.mp hdisj hxU
        rw [hb x hxV, hpauli0, mul_one, hmat0, Matrix.mul_one]
      · rw [ha x hxU, hpauli0, one_mul, hmat0, Matrix.one_mul]
    | zero => simp [normalizedTrace]
    | add X Y _ _ ihX ihY =>
      rw [mul_add, normalizedTrace_add, normalizedTrace_add, ihX, ihY, mul_add]
    | smul c X _ ihX =>
      rw [Matrix.mul_smul, normalizedTrace_smul, normalizedTrace_smul, ihX]; ring
  | zero => simp [normalizedTrace]
  | add X Y _ _ ihX ihY =>
    rw [add_mul, normalizedTrace_add, normalizedTrace_add, ihX, ihY, add_mul]
  | smul c X _ ihX =>
    rw [Matrix.smul_mul, normalizedTrace_smul, normalizedTrace_smul, ihX]; ring

/-- Concrete trace polymer weight `w_τ(γ) := τ(Q_γ)` for a connected polymer `γ ⊆ E`. -/
noncomputable def tracePolyWeight {N : ℕ} (h : Finset (Fin N) → QubitOp N) (β' : ℝ)
    (γ : Finset (Finset (Fin N))) : ℂ :=
  normalizedTrace (polyOp h β' γ)

lemma norm_tracePolyWeight_le {N : ℕ} (h : Finset (Fin N) → QubitOp N)
    {β' : ℝ} (hβ' : 0 ≤ β') (γ : Finset (Finset (Fin N))) :
    ‖tracePolyWeight h β' γ‖ ≤ ∏ X ∈ γ, (Real.exp (β' * opNorm (h X)) - 1) :=
  by unfold tracePolyWeight; simpa [abs_of_nonneg hβ'] using le_trans (norm_normalizedTrace_le _) (opNorm_polyOp_le h β' γ)

/-- **Concrete Lemma 6.3 Trace Polymer Kotecký–Preiss Verification**:
For any `r`-local interaction `h` on `QubitOp N` in the high-temperature regime
`∑_{X ∋ x} (exp(β' ‖h_X‖_op) - 1) ≤ η₀` with `η₀ * exp(2 c r) ≤ c`, the trace polymer
system `(connectedPolymers E, polyIncompat, tracePolyWeight h β')` satisfies the exact
Kotecký–Preiss convergence criterion and yields `polymerZ ≠ 0` directly via
`sum_connectedPolymers_le_unorderedTreeSum`, `lemma_A_3_concrete_unordered_tree_sum`, and
`kotecky_preiss_convergence`. -/
theorem lemma_6_3_trace_polymer_kp {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N)
    {β' η₀ c : ℝ} (hβ' : 0 ≤ β') (hc : 0 < c)
    (hsite : ∀ x : Fin N,
      ∑ X ∈ E.filter (fun X ↦ x ∈ X), (Real.exp (β' * opNorm (h X)) - 1) ≤ η₀)
    (hkp : η₀ * Real.exp (2 * c * (r : ℝ)) ≤ c) :
    let Γ := connectedPolymers E
    let w := tracePolyWeight h β'
    let a : Finset (Finset (Fin N)) → ℝ := fun γ ↦ c * (polySupp γ).card
    (∀ γ₁ ∈ Γ, ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ polyIncompat γ₁ γ₂),
        ‖w γ₂‖ * Real.exp (a γ₂) ≤ a γ₁) ∧
    polymerZ polyIncompat w Γ ≠ 0 := by
  classical
  intro Γ w a
  let η : Finset (Fin N) → ℝ :=
    fun X ↦ (Real.exp (β' * opNorm (h X)) - 1) * Real.exp (c * (X.card : ℝ))
  have hη_nn : ∀ X ∈ E, 0 ≤ η X := fun X _ ↦ by
    apply mul_nonneg
    · linarith [Real.one_le_exp (mul_nonneg hβ' (opNorm_nonneg (h X)))]
    · exact (Real.exp_pos _).le
  have hkp_cond : ∀ γ₁ ∈ Γ, ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ polyIncompat γ₁ γ₂),
      ‖w γ₂‖ * Real.exp (a γ₂) ≤ a γ₁ := by
    intro γ₁ hγ₁
    have hpoly_le : ∀ γ₂ ∈ Γ,
        ‖w γ₂‖ * Real.exp (a γ₂) ≤ ∏ X ∈ γ₂, η X := by
      intro γ₂ hγ₂
      have hsub : γ₂ ⊆ E := (mem_connectedPolymers.mp hγ₂).1
      have hcard_bi : (polySupp γ₂).card ≤ ∑ X ∈ γ₂, X.card := Finset.card_biUnion_le
      have hexp_le : Real.exp (a γ₂) ≤ ∏ X ∈ γ₂, Real.exp (c * (X.card : ℝ)) := by
        rw [← Real.exp_sum]
        apply Real.exp_le_exp.mpr
        have hcast : ((polySupp γ₂).card : ℝ) ≤ ∑ X ∈ γ₂, (X.card : ℝ) := by
          exact_mod_cast hcard_bi
        calc c * ((polySupp γ₂).card : ℝ)
            ≤ c * ∑ X ∈ γ₂, (X.card : ℝ) := mul_le_mul_of_nonneg_left hcast hc.le
          _ = ∑ X ∈ γ₂, c * (X.card : ℝ) := Finset.mul_sum _ _ _
      calc ‖w γ₂‖ * Real.exp (a γ₂)
          ≤ (∏ X ∈ γ₂, (Real.exp (β' * opNorm (h X)) - 1)) *
              (∏ X ∈ γ₂, Real.exp (c * (X.card : ℝ))) :=
            mul_le_mul (norm_tracePolyWeight_le h hβ' γ₂) hexp_le
              (Real.exp_pos _).le
              (Finset.prod_nonneg fun X _ ↦ by
                linarith [Real.one_le_exp (mul_nonneg hβ' (opNorm_nonneg (h X)))])
        _ = ∏ X ∈ γ₂, η X := by rw [← Finset.prod_mul_distrib]
    have hbi : Γ.filter (fun γ₂ ↦ polyIncompat γ₁ γ₂) ⊆
        (polySupp γ₁).biUnion (fun x ↦ Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂)) := by
      intro γ₂ hγ₂
      rw [Finset.mem_filter] at hγ₂
      rcases Finset.not_disjoint_iff.mp hγ₂.2 with ⟨x, hx1, hx2⟩
      exact Finset.mem_biUnion.mpr ⟨x, hx1, Finset.mem_filter.mpr ⟨hγ₂.1, hx2⟩⟩
    have hsite_sum : ∀ x ∈ polySupp γ₁,
        ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂), ∏ X ∈ γ₂, η X ≤ c := by
      intro x _
      have hη₀_nn : 0 ≤ η₀ := by
        refine le_trans (Finset.sum_nonneg fun X _ ↦ ?_) (hsite x)
        linarith [Real.one_le_exp (mul_nonneg hβ' (opNorm_nonneg (h X)))]
      have hpin : Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂) ⊆
          (E.filter (fun X ↦ x ∈ X)).biUnion
            (fun X₀ ↦ Γ.filter (fun γ₂ ↦ X₀ ∈ γ₂ ∧ γ₂.card ≤ E.card + 1)) := by
        intro γ₂ hγ₂
        rcases Finset.mem_filter.mp hγ₂ with ⟨hγ₂Γ, hxγ₂⟩
        have hsub : γ₂ ⊆ E := (mem_connectedPolymers.mp hγ₂Γ).1
        rcases Finset.mem_biUnion.mp hxγ₂ with ⟨X₀, hX₀γ₂, hxX₀⟩
        exact Finset.mem_biUnion.mpr ⟨X₀, Finset.mem_filter.mpr ⟨hsub hX₀γ₂, hxX₀⟩,
          Finset.mem_filter.mpr ⟨hγ₂Γ, hX₀γ₂, le_trans (Finset.card_le_card hsub) (Nat.le_succ _)⟩⟩
      have hη_site : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), η X ≤
          η₀ * Real.exp (c * (r : ℝ)) := by
        intro y
        calc ∑ X ∈ E.filter (fun X ↦ y ∈ X), η X
            ≤ ∑ X ∈ E.filter (fun X ↦ y ∈ X),
                (Real.exp (β' * opNorm (h X)) - 1) * Real.exp (c * (r : ℝ)) := by
              apply Finset.sum_le_sum; intro X hX
              have hXE := (Finset.mem_filter.mp hX).1
              apply mul_le_mul_of_nonneg_left
              · apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard X hXE) hc.le
              · linarith [Real.one_le_exp (mul_nonneg hβ' (opNorm_nonneg (h X)))]
          _ = (∑ X ∈ E.filter (fun X ↦ y ∈ X), (Real.exp (β' * opNorm (h X)) - 1)) *
                Real.exp (c * (r : ℝ)) := by rw [← Finset.sum_mul]
          _ ≤ η₀ * Real.exp (c * (r : ℝ)) :=
              mul_le_mul_of_nonneg_right (hsite y) (Real.exp_pos _).le
      have hA3_param : (η₀ * Real.exp (c * (r : ℝ))) * Real.exp (c * (r : ℝ)) ≤ c := by
        calc (η₀ * Real.exp (c * (r : ℝ))) * Real.exp (c * (r : ℝ))
            = η₀ * (Real.exp (c * (r : ℝ)) * Real.exp (c * (r : ℝ))) := by ring
          _ = η₀ * Real.exp (2 * c * (r : ℝ)) := by rw [← Real.exp_add]; ring_nf
          _ ≤ c := hkp
      have htree : ∀ X₀ ∈ E, unorderedTreeSum E η E.card X₀ ≤ η X₀ * Real.exp (c * (r : ℝ)) := by
        intro X₀ hX₀
        have htree0 := lemma_A_3_concrete_unordered_tree_sum E hcard η hη_nn hc.le
          hη_site hA3_param E.card X₀ hX₀
        exact le_trans htree0 (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard X₀ hX₀) hc.le))
          (hη_nn X₀ hX₀))
      calc ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂), ∏ X ∈ γ₂, η X
          ≤ ∑ γ₂ ∈ (E.filter (fun X ↦ x ∈ X)).biUnion
              (fun X₀ ↦ Γ.filter (fun γ₂ ↦ X₀ ∈ γ₂ ∧ γ₂.card ≤ E.card + 1)),
              ∏ X ∈ γ₂, η X :=
            Finset.sum_le_sum_of_subset_of_nonneg hpin fun γ₂ hγ₂ _ ↦ by
              rcases Finset.mem_biUnion.mp hγ₂ with ⟨_, _, hγ₂'⟩
              exact Finset.prod_nonneg fun X hX ↦
                hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ₂').1).1 hX)
        _ ≤ ∑ X₀ ∈ E.filter (fun X ↦ x ∈ X),
              ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ X₀ ∈ γ₂ ∧ γ₂.card ≤ E.card + 1), ∏ X ∈ γ₂, η X :=
            real_sum_biUnion_le _ _ _ fun γ₂ hγ₂ ↦ by
              rcases Finset.mem_biUnion.mp hγ₂ with ⟨_, _, hγ₂'⟩
              exact Finset.prod_nonneg fun X hX ↦
                hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ₂').1).1 hX)
        _ ≤ ∑ X₀ ∈ E.filter (fun X ↦ x ∈ X), unorderedTreeSum E η E.card X₀ :=
            Finset.sum_le_sum fun X₀ hX₀ ↦
              sum_connectedPolymers_le_unorderedTreeSum E hne η hη_nn E.card X₀
                (Finset.mem_filter.mp hX₀).1
        _ ≤ ∑ X₀ ∈ E.filter (fun X ↦ x ∈ X), η X₀ * Real.exp (c * (r : ℝ)) :=
            Finset.sum_le_sum fun X₀ hX₀ ↦ htree X₀ (Finset.mem_filter.mp hX₀).1
        _ = (∑ X₀ ∈ E.filter (fun X ↦ x ∈ X), η X₀) * Real.exp (c * (r : ℝ)) := by
            rw [← Finset.sum_mul]
        _ ≤ (η₀ * Real.exp (c * (r : ℝ))) * Real.exp (c * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right (hη_site x) (Real.exp_pos _).le
        _ ≤ c := hA3_param
    calc ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ polyIncompat γ₁ γ₂), ‖w γ₂‖ * Real.exp (a γ₂)
        ≤ ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ polyIncompat γ₁ γ₂), ∏ X ∈ γ₂, η X :=
          Finset.sum_le_sum fun γ₂ hγ₂ ↦ hpoly_le γ₂ (Finset.mem_filter.mp hγ₂).1
      _ ≤ ∑ γ₂ ∈ (polySupp γ₁).biUnion (fun x ↦ Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂)),
            ∏ X ∈ γ₂, η X :=
          Finset.sum_le_sum_of_subset_of_nonneg hbi fun γ₂ hγ₂ _ ↦ by
            rcases Finset.mem_biUnion.mp hγ₂ with ⟨_, _, hγ₂'⟩
            exact Finset.prod_nonneg fun X hX ↦
              hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ₂').1).1 hX)
      _ ≤ ∑ x ∈ polySupp γ₁, ∑ γ₂ ∈ Γ.filter (fun γ₂ ↦ x ∈ polySupp γ₂), ∏ X ∈ γ₂, η X :=
          real_sum_biUnion_le _ _ _ fun γ₂ hγ₂ ↦ by
            rcases Finset.mem_biUnion.mp hγ₂ with ⟨_, _, hγ₂'⟩
            exact Finset.prod_nonneg fun X hX ↦
              hη_nn X ((mem_connectedPolymers.mp (Finset.mem_filter.mp hγ₂').1).1 hX)
      _ ≤ ∑ _x ∈ polySupp γ₁, c := Finset.sum_le_sum hsite_sum
      _ = a γ₁ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  let incompatRefl : Polymer N → Polymer N → Prop := fun γ₁ γ₂ ↦ γ₁ = γ₂ ∨ polyIncompat γ₁ γ₂
  have hrefl : ∀ γ, incompatRefl γ γ := fun _ ↦ Or.inl rfl
  have hsym : ∀ γ₁ γ₂, incompatRefl γ₁ γ₂ → incompatRefl γ₂ γ₁ := by
    rintro γ₁ γ₂ (rfl | hinc)
    · exact Or.inl rfl
    · exact Or.inr (polyIncompat_symm _ _ hinc)
  have hinc_eq : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, incompatRefl γ γ' ↔ polyIncompat γ γ' := by
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
  have hkp' : ∀ γ ∈ Γ,
      ∑ γ' ∈ Γ.filter (fun γ' ↦ incompatRefl γ γ'), kpActivity w a γ' ≤ a γ := by
    intro γ hγ
    have hfeq : Γ.filter (fun γ' ↦ incompatRefl γ γ') = Γ.filter (fun γ' ↦ polyIncompat γ γ') := by
      ext γ'; simp only [Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (hinc_eq γ hγ γ' h1).mp h2⟩,
             fun ⟨h1, h2⟩ ↦ ⟨h1, (hinc_eq γ hγ γ' h1).mpr h2⟩⟩
    rw [hfeq]; exact hkp_cond γ hγ
  have hZ_ne := (kotecky_preiss_convergence incompatRefl hrefl hsym w a Γ hkp' Γ Finset.Subset.rfl).1
  have hZ_eq : polymerZ incompatRefl w Γ = polymerZ polyIncompat w Γ := by
    unfold polymerZ
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext I; simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hsub, hci⟩; refine ⟨hsub, fun u hu v hv huv ↦ ?_⟩
      rw [← hinc_eq u (hsub hu) v (hsub hv)]; exact hci u hu v hv huv
    · rintro ⟨hsub, hci⟩; refine ⟨hsub, fun u hu v hv huv ↦ ?_⟩
      rw [hinc_eq u (hsub hu) v (hsub hv)]; exact hci u hu v hv huv
  rw [hZ_eq] at hZ_ne
  exact ⟨hkp_cond, hZ_ne⟩

end SchwarzAndTracePolymer

section ConcreteEntropicDecoupling

private lemma eigU_mul_star_dec {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

private lemma eigU_star_mul_dec {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

private lemma unitary_conj_isHermitian {N : ℕ} {ρ U : QubitOp N}
    (hρ : ρ.IsHermitian) : (U * ρ * Uᴴ).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hρ.eq, Matrix.mul_assoc]

private lemma unitary_conj_hermFunc {N : ℕ} {ρ U : QubitOp N}
    (hρ : ρ.IsHermitian) (hU : Uᴴ * U = 1) (f : ℝ → ℂ)
    (hρU : (U * ρ * Uᴴ).IsHermitian) :
    ((U * ρ * Uᴴ) * hermFunc hρU f).trace = (ρ * hermFunc hρ f).trace := by
  -- Both `U * ρ * Uᴴ` and `ρ` have the same spectrum; we compare via trace of polynomial/diagonal.
  -- In fact, let `V := U * hρ.eigenvectorUnitary`, then `V` is unitary and diagonalizes `U * ρ * Uᴴ`
  -- with the SAME eigenvalues as `ρ`, so `hermFunc hρU f = U * hermFunc hρ f * Uᴴ`!
  -- Wait: for general `f`, `hρU.eigenvectorUnitary` may differ from `V` within degenerate eigenspaces.
  -- We prove `hermFunc hρU f = U * hermFunc hρ f * Uᴴ` directly on every eigenvector of `ρ`!
  have hU' : U * Uᴴ = 1 := Matrix.mul_eq_one_comm.mp hU
  set P : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
  set Q : QubitOp N := (hρU.eigenvectorUnitary : QubitOp N)
  have hPP : P * Pᴴ = 1 := eigU_mul_star_dec hρ
  have hPHP : Pᴴ * P = 1 := eigU_star_mul_dec hρ
  have hQQ : Q * Qᴴ = 1 := eigU_mul_star_dec hρU
  have hQHQ : Qᴴ * Q = 1 := eigU_star_mul_dec hρU
  let W : QubitOp N := Qᴴ * U * P
  have hW_unit : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Pᴴ * Uᴴ * Q * (Qᴴ * U * P)
        = Pᴴ * Uᴴ * (Q * Qᴴ) * U * P := by simp only [Matrix.mul_assoc]
      _ = Pᴴ * (Uᴴ * U) * P := by rw [hQQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * P := by rw [hU, Matrix.mul_one]
      _ = 1 := hPHP
  have hW_unit' : W * Wᴴ = 1 := Matrix.mul_eq_one_comm.mp hW_unit
  -- `W` intertwines `diag(λ_ρ)` and `diag(λ_{ρU})`: `diag(λ_{ρU}) * W = W * diag(λ_ρ)`.
  have hinter : ∀ a b : QubitIdx N,
      (hρU.eigenvalues a : ℂ) * W a b = W a b * (hρ.eigenvalues b : ℂ) := by
    intro a b
    have hD1 : Qᴴ * (U * ρ * Uᴴ) * Q = Matrix.diagonal (fun i ↦ (hρU.eigenvalues i : ℂ)) := by
      have h1 := hermFunc_id hρU
      unfold hermFunc at h1
      calc Qᴴ * (U * ρ * Uᴴ) * Q
          = Qᴴ * (Q * Matrix.diagonal (fun i ↦ (hρU.eigenvalues i : ℂ)) * Qᴴ) * Q := by rw [h1]
        _ = (Qᴴ * Q) * Matrix.diagonal (fun i ↦ (hρU.eigenvalues i : ℂ)) * (Qᴴ * Q) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun i ↦ (hρU.eigenvalues i : ℂ)) := by
            rw [hQHQ, Matrix.one_mul, Matrix.mul_one]
    have hD2 : Pᴴ * ρ * P = Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) := by
      have h1 := hermFunc_id hρ
      unfold hermFunc at h1
      calc Pᴴ * ρ * P
          = Pᴴ * (P * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) * Pᴴ) * P := by rw [h1]
        _ = (Pᴴ * P) * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) * (Pᴴ * P) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) := by
            rw [hPHP, Matrix.one_mul, Matrix.mul_one]
    have hmat : Matrix.diagonal (fun i ↦ (hρU.eigenvalues i : ℂ)) * W =
        W * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) := by
      rw [← hD1, ← hD2]
      dsimp only [W]
      calc Qᴴ * (U * ρ * Uᴴ) * Q * (Qᴴ * U * P)
          = Qᴴ * U * ρ * Uᴴ * (Q * Qᴴ) * U * P := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * U * ρ * (Uᴴ * U) * P := by rw [hQQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Qᴴ * U * ρ * P := by rw [hU, Matrix.mul_one]
        _ = Qᴴ * U * (P * Pᴴ) * ρ * P := by rw [hPP, Matrix.mul_one]
        _ = Qᴴ * U * P * (Pᴴ * ρ * P) := by simp only [Matrix.mul_assoc]
    have hent := congrFun (congrFun hmat a) b
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using hent
  have hW_eq : ∀ a b : QubitIdx N, W a b ≠ 0 → hρU.eigenvalues a = hρ.eigenvalues b := by
    intro a b hne
    have h := hinter a b
    have hsub : ((hρU.eigenvalues a - hρ.eigenvalues b : ℝ) : ℂ) * W a b = 0 := by
      push_cast; linear_combination h
    rcases mul_eq_zero.mp hsub with h0 | h0
    · linarith [Complex.ofReal_eq_zero.mp h0]
    · exact absurd h0 hne
  have hfunc_inter : Matrix.diagonal (fun a ↦ f (hρU.eigenvalues a)) * W =
      W * Matrix.diagonal (fun b ↦ f (hρ.eigenvalues b)) := by
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : W a b = 0
    · simp [h0]
    · rw [hW_eq a b h0]; ring
  have hconj_func : hermFunc hρU f = U * hermFunc hρ f * Uᴴ := by
    unfold hermFunc
    calc Q * Matrix.diagonal (fun a ↦ f (hρU.eigenvalues a)) * Qᴴ
        = Q * Matrix.diagonal (fun a ↦ f (hρU.eigenvalues a)) * (W * Wᴴ) * Qᴴ := by
          rw [hW_unit', Matrix.mul_one]
      _ = Q * (Matrix.diagonal (fun a ↦ f (hρU.eigenvalues a)) * W) * Wᴴ * Qᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (W * Matrix.diagonal (fun b ↦ f (hρ.eigenvalues b))) * Wᴴ * Qᴴ := by
          rw [hfunc_inter]
      _ = (Q * W) * Matrix.diagonal (fun b ↦ f (hρ.eigenvalues b)) * (Q * W)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (U * P) * Matrix.diagonal (fun b ↦ f (hρ.eigenvalues b)) * (U * P)ᴴ := by
          have hQW : Q * W = U * P := by
            dsimp only [W]
            calc Q * (Qᴴ * U * P) = (Q * Qᴴ) * (U * P) := by simp only [Matrix.mul_assoc]
              _ = U * P := by rw [hQQ, Matrix.one_mul]
          rw [hQW]
      _ = U * (P * Matrix.diagonal (fun b ↦ f (hρ.eigenvalues b)) * Pᴴ) * Uᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hconj_func]
  calc (U * ρ * Uᴴ * (U * hermFunc hρ f * Uᴴ)).trace
      = (U * (ρ * (Uᴴ * U) * hermFunc hρ f) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (U * (ρ * hermFunc hρ f) * Uᴴ).trace := by rw [hU, Matrix.mul_one]
    _ = (Uᴴ * (U * (ρ * hermFunc hρ f))).trace := Matrix.trace_mul_comm _ _
    _ = ((Uᴴ * U) * (ρ * hermFunc hρ f)).trace := by simp only [Matrix.mul_assoc]
    _ = (ρ * hermFunc hρ f).trace := by rw [hU, Matrix.one_mul]

/-- **Exact Unitary Invariance of Gibbs Quantum Relative Entropy (Prop. 6.4(2))**:
For any unitary `U` commuting with `H` (`U * H = H * U`),
`D(U ρ Uᴴ ‖ ρ_β) = D(ρ ‖ ρ_β)`. -/
theorem gibbsRelEntropy_unitary_invariant {N : ℕ} {ρ H U : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hU : Uᴴ * U = 1) (hcomm : U * H = H * U) (β : ℝ) :
    gibbsRelEntropy (unitary_conj_isHermitian (U := U) hρ) hH β =
      gibbsRelEntropy hρ hH β := by
  have hU' : U * Uᴴ = 1 := Matrix.mul_eq_one_comm.mp hU
  have hlog := unitary_conj_hermFunc hρ hU (fun x ↦ (Real.log x : ℂ))
    (unitary_conj_isHermitian (U := U) hρ)
  have hH_tr : ((U * ρ * Uᴴ) * (((β : ℝ) : ℂ) • H)).trace =
      (ρ * (((β : ℝ) : ℂ) • H)).trace := by
    calc ((U * ρ * Uᴴ) * (((β : ℝ) : ℂ) • H)).trace
        = (((β : ℝ) : ℂ) • (U * ρ * Uᴴ * H)).trace := by simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = (((β : ℝ) : ℂ) • (U * ρ * (H * Uᴴ))).trace := by
          have hUH : Uᴴ * H = H * Uᴴ := by
            calc Uᴴ * H = Uᴴ * (H * (U * Uᴴ)) := by rw [hU', Matrix.mul_one]
              _ = Uᴴ * ((H * U) * Uᴴ) := by simp only [Matrix.mul_assoc]
              _ = Uᴴ * ((U * H) * Uᴴ) := by rw [hcomm]
              _ = (Uᴴ * U) * (H * Uᴴ) := by simp only [Matrix.mul_assoc]
              _ = H * Uᴴ := by rw [hU, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hUH]
      _ = (((β : ℝ) : ℂ) • (Uᴴ * (U * ρ * H))).trace := by
          rw [Matrix.trace_smul, Matrix.trace_smul]
          congr 1
          calc (U * ρ * (H * Uᴴ)).trace = ((U * ρ * H) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
            _ = (Uᴴ * (U * ρ * H)).trace := Matrix.trace_mul_comm _ _
      _ = (((β : ℝ) : ℂ) • (ρ * H)).trace := by
          congr 2
          calc Uᴴ * (U * ρ * H) = (Uᴴ * U) * (ρ * H) := by simp only [Matrix.mul_assoc]
            _ = ρ * H := by rw [hU, Matrix.one_mul]
      _ = (ρ * (((β : ℝ) : ℂ) • H)).trace := by simp [Matrix.mul_smul]
  unfold gibbsRelEntropy
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, hlog, hH_tr]

/-- **Heisenberg Time-Evolution Invariance of `gibbsRelEntropy` (Prop. 6.4(2))**:
For `U(t) = exp(i t H)`, `D(U(t) ρ U(t)ᴴ ‖ ρ_β) = D(ρ ‖ ρ_β)` for all `t : ℝ`. -/
theorem gibbsRelEntropy_heisenberg_invariant {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian) (β t : ℝ) :
    let U := complexPropagator hH (t : ℂ)
    gibbsRelEntropy (unitary_conj_isHermitian (U := U) hρ) hH β =
      gibbsRelEntropy hρ hH β := by
  intro U
  have hU_unit : Uᴴ * U = 1 := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose, hermFunc_mul]
    have hfun : (fun x : ℝ ↦ star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) = fun _ ↦ 1 := by
      funext x
      rw [Complex.star_def, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      rw [← Complex.exp_add]
      have h0 : -Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero]
    rw [hfun, hermFunc_one]
  have hcomm : U * H = H * U := by
    dsimp only [U, complexPropagator]
    conv_lhs => arg 2; rw [← hermFunc_id hH]
    conv_rhs => arg 1; rw [← hermFunc_id hH]
    exact hermFunc_comm hH _ _
  exact gibbsRelEntropy_unitary_invariant hρ hH hU_unit hcomm β

/-- **Elementary Petz–Rényi Max-Relative Entropy Bound (`D(ρ ‖ ρ_β) ≤ log C`)**:
Without assuming operator monotonicity of `log`, proves directly from `Real.log_le_sub_one_of_pos`
that if `ρ` is positive-definite with `Tr(ρ) = 1` and `Re Tr(ρ^2 * ρ_β^{-1}) ≤ C` (`C > 0`),
then `gibbsRelEntropy hρ hH β ≤ Real.log C`. -/
theorem gibbsRelEntropy_le_log_of_renyi2 {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hρ_pos : ∀ i : QubitIdx N, 0 < hρ.eigenvalues i)
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
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hH.eigenvectorUnitary : QubitOp N) *
            ((hH.eigenvectorUnitary : QubitOp N)ᴴ * (hρ.eigenvectorUnitary : QubitOp N))
          = (hρ.eigenvectorUnitary : QubitOp N)ᴴ *
              ((hH.eigenvectorUnitary : QubitOp N) * (hH.eigenvectorUnitary : QubitOp N)ᴴ) *
              (hρ.eigenvectorUnitary : QubitOp N) := by simp only [Matrix.mul_assoc]
        _ = (hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hρ.eigenvectorUnitary : QubitOp N) := by
            rw [eigU_mul_star_dec hH, Matrix.mul_one]
        _ = 1 := eigU_star_mul_dec hρ
    intro i
    have h1 := congrFun (congrFun hW1 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hsum_ρ : ∑ i : QubitIdx N, hρ.eigenvalues i = 1 := by
    have h1 := hermFunc_trace hρ (fun x ↦ (x : ℂ))
    rw [hermFunc_id hρ, hρ_tr] at h1
    simpa [Complex.re_sum] using (congrArg Complex.re h1.symm)
  have hlogμ : ∀ j, Real.log (μ j) = -β * hH.eigenvalues j - Real.log (gibbsPartitionFn hH β) := by
    intro j
    simp only [μ, Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    ring
  have htr1 : (ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))).trace.re =
      ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
    have h1 : ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) =
        hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := by
      conv_lhs => arg 1; rw [← hermFunc_id hρ]
      exact hermFunc_mul hρ _ _
    rw [h1, hermFunc_trace, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have htrH : (ρ * (((β : ℝ) : ℂ) • H)).trace.re =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j)) := by
    set U : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
    set V : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
    set Dρ : QubitOp N := Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))
    set F : QubitOp N := Matrix.diagonal (fun j ↦ ((β * hH.eigenvalues j : ℝ) : ℂ))
    have hH_eq : ((β : ℝ) : ℂ) • H = V * F * Vᴴ := by
      have hid := hermFunc_id hH
      unfold hermFunc at hid
      rw [← hid, ← smul_mul_assoc, ← mul_smul_comm]
      congr 1; congr 1; ext a b
      by_cases hab : a = b
      · subst hab; simp [F, Matrix.diagonal_apply]
      · simp [F, Matrix.diagonal_apply, hab]
    have hcyc : (ρ * (((β : ℝ) : ℂ) • H)).trace = (Dρ * W * F * Wᴴ).trace := by
      rw [← hermFunc_id hρ, hH_eq]
      unfold hermFunc
      have h1 : U * Dρ * Uᴴ * (V * F * Vᴴ) = U * (Dρ * W * F * Vᴴ) := by
        simp only [W, U, V, Matrix.mul_assoc]
      rw [h1, Matrix.trace_mul_comm]
      have h2 : Dρ * W * F * Vᴴ * U = Dρ * W * F * Wᴴ := by
        simp only [W, U, V, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [h2]
    rw [hcyc]
    simp only [Dρ, F, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hnorm : W i j * star (W i j) = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    have hrew : (hρ.eigenvalues i : ℂ) * W i j * ((β * hH.eigenvalues j : ℝ) : ℂ) * star (W i j) =
        (((‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j)) : ℝ) : ℂ)) := by
      push_cast; linear_combination (hρ.eigenvalues i : ℂ) * (β * hH.eigenvalues j : ℂ) * hnorm
    rw [hrew, Complex.ofReal_re]
  have hD_diff : gibbsRelEntropy hρ hH β - Real.log C =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * hρ.eigenvalues i * Real.log (hρ.eigenvalues i / (C * μ j)) := by
    unfold gibbsRelEntropy
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, htr1, htrH]
    have h1 : ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) := by
      apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, hrow i, one_mul]
    have h4 : Real.log (gibbsPartitionFn hH β) =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β)) := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β)) =
          hρ.eigenvalues i * Real.log (gibbsPartitionFn hH β) := fun i ↦ by
        rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this, ← Finset.sum_mul, hsum_ρ, one_mul]
    have h5 : Real.log C =
        ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log C) := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log C) =
          hρ.eigenvalues i * Real.log C := fun i ↦ by
        rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this, ← Finset.sum_mul, hsum_ρ, one_mul]
    rw [h1, h4, h5]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Real.log_div (hρ_pos i).ne' (mul_pos hC (hμ_pos j)).ne',
      Real.log_mul hC.ne' (hμ_pos j).ne', hlogμ j]
    ring
  have hle0 : gibbsRelEntropy hρ hH β - Real.log C ≤ 0 := by
    rw [hD_diff]
    calc ∑ i : QubitIdx N, ∑ j : QubitIdx N,
            ‖W i j‖ ^ 2 * hρ.eigenvalues i * Real.log (hρ.eigenvalues i / (C * μ j))
        ≤ ∑ i : QubitIdx N, ∑ j : QubitIdx N,
            ‖W i j‖ ^ 2 * hρ.eigenvalues i * (hρ.eigenvalues i / (C * μ j) - 1) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left
            (Real.log_le_sub_one_of_pos (div_pos (hρ_pos i) (mul_pos hC (hμ_pos j))))
            (mul_nonneg (sq_nonneg _) (hρ_pos i).le)
      _ = (1 / C) * (∑ i : QubitIdx N, ∑ j : QubitIdx N,
            ‖W i j‖ ^ 2 * ((hρ.eigenvalues i) ^ 2 / μ j)) - 1 := by
          have h1 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = 1 := by
            have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = hρ.eigenvalues i := fun i ↦ by
              rw [← Finset.sum_mul, hrow i, one_mul]
            simp_rw [this]; exact hsum_ρ
          conv_rhs => arg 2; rw [← h1]
          simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          field_simp [hC.ne', (hμ_pos j).ne']
      _ ≤ (1 / C) * C - 1 := by
          linarith [mul_le_mul_of_nonneg_left hrenyi (by positivity : (0 : ℝ) ≤ 1 / C)]
      _ = 0 := by field_simp [hC.ne']; ring
  linarith

/-- **Concrete Proposition 6.4(2) Entropic Background Decoupling on `QubitOp N`**:
Combines `gibbs_variational_bound` + `gibbsRelEntropy_heisenberg_invariant` + quadratic
cumulant scaling on `QubitOp N`: for any time-evolved state `ρ_t = U(t) ρ U(t)ᴴ` and
centered Hermitian observable `X̃ = X - ⟨X⟩_β I` satisfying the trace cumulant bound
`log(Z(-β H + lam X̃) / Z(-β H)) ≤ K₀ N lam^2` at `lam > 0`,
`Re Tr(ρ_t X̃) ≤ D(ρ ‖ ρ_β) / lam + K₀ N lam` for any `lam > 0`. -/
theorem prop_6_4_2_concrete_entropic_decoupling {N : ℕ} {ρ H X : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian) (hX : X.IsHermitian)
    (hρ_pos : ∀ i : QubitIdx N, 0 < hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β t : ℝ)
    {lam K₀ : ℝ} (hlam : 0 < lam)
    (hcum :
      let K : QubitOp N := ((-β : ℝ) : ℂ) • H + ((lam : ℝ) : ℂ) • X
      have hK : K.IsHermitian := by
        simp only [K, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
          Complex.star_def, Complex.conj_ofReal, hH.eq, hX.eq]
      Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) ≤ K₀ * (N : ℝ) * lam ^ 2) :
    let U := complexPropagator hH (t : ℂ)
    let ρt := U * ρ * Uᴴ
    (ρt * X).trace.re ≤ gibbsRelEntropy hρ hH β / lam + K₀ * (N : ℝ) * lam := by
  intro U ρt
  have hU_unit : Uᴴ * U = 1 := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose, hermFunc_mul]
    have hfun : (fun x : ℝ ↦ star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) = fun _ ↦ 1 := by
      funext x
      rw [Complex.star_def, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      rw [← Complex.exp_add]
      have h0 : -Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero]
    rw [hfun, hermFunc_one]
  have hρt : ρt.IsHermitian := unitary_conj_isHermitian (U := U) hρ
  have hρt_tr : ρt.trace = 1 := by
    dsimp only [ρt]
    calc (U * ρ * Uᴴ).trace = (Uᴴ * (U * ρ)).trace := Matrix.trace_mul_comm _ _
      _ = ((Uᴴ * U) * ρ).trace := by simp only [Matrix.mul_assoc]
      _ = ρ.trace := by rw [hU_unit, Matrix.one_mul]
      _ = 1 := hρ_tr
  have hρt_pos : ∀ i : QubitIdx N, 0 < hρt.eigenvalues i := by
    intro i
    let Q : QubitOp N := (hρt.eigenvectorUnitary : QubitOp N)
    let P : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
    let W : QubitOp N := Qᴴ * U * P
    have hrow : ∑ j : QubitIdx N, ‖W i j‖ ^ 2 = 1 := by
      have hW1 : W * Wᴴ = 1 := by
        simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        calc Qᴴ * U * P * (Pᴴ * Uᴴ * Q)
            = Qᴴ * U * (P * Pᴴ) * Uᴴ * Q := by simp only [Matrix.mul_assoc]
          _ = Qᴴ * (U * Uᴴ) * Q := by rw [eigU_mul_star_dec hρ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = Qᴴ * Q := by rw [Matrix.mul_eq_one_comm.mp hU_unit, Matrix.mul_one]
          _ = 1 := eigU_star_mul_dec hρt
      have h1 := congrFun (congrFun hW1 i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
      have hre := congrArg Complex.re h1
      rw [Complex.re_sum, Complex.one_re] at hre
      rw [← hre]
      apply Finset.sum_congr rfl; intro j _
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    have heig : hρt.eigenvalues i = ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues j := by
      have hD : Qᴴ * ρt * Q = Matrix.diagonal (fun a ↦ (hρt.eigenvalues a : ℂ)) := by
        have h1 := hermFunc_id hρt; unfold hermFunc at h1
        calc Qᴴ * ρt * Q = Qᴴ * (Q * Matrix.diagonal (fun a ↦ (hρt.eigenvalues a : ℂ)) * Qᴴ) * Q := by rw [h1]
          _ = (Qᴴ * Q) * Matrix.diagonal (fun a ↦ (hρt.eigenvalues a : ℂ)) * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal (fun a ↦ (hρt.eigenvalues a : ℂ)) := by rw [eigU_star_mul_dec hρt, Matrix.one_mul, Matrix.mul_one]
      have hW_eq : Qᴴ * ρt * Q = W * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) * Wᴴ := by
        have h1 := hermFunc_id hρ; unfold hermFunc at h1
        dsimp only [ρt, W]
        rw [← h1]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      have hent := congrFun (congrFun (hD.symm.trans hW_eq) i) i
      simp only [Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.mul_diagonal,
        Matrix.conjTranspose_apply] at hent
      have hre := congrArg Complex.re hent
      rw [Complex.ofReal_re, Complex.re_sum] at hre
      rw [hre]
      apply Finset.sum_congr rfl; intro j _
      have hnorm : W i j * star (W i j) = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
      have hrew : W i j * (hρ.eigenvalues j : ℂ) * star (W i j) =
          (((‖W i j‖ ^ 2 * hρ.eigenvalues j : ℝ) : ℂ)) := by
        push_cast; linear_combination (hρ.eigenvalues j : ℂ) * hnorm
      rw [hrew, Complex.ofReal_re]
    rw [heig]
    have hex : ∃ j : QubitIdx N, 0 < ‖W i j‖ ^ 2 := by
      by_contra hall; push Not at hall
      have h0 : ∑ j : QubitIdx N, ‖W i j‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun j _ ↦ le_antisymm (hall j) (sq_nonneg _)
      linarith
    rcases hex with ⟨j₀, hj₀⟩
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (sq_nonneg _) (hρ_pos j).le)
      ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (hρ_pos j₀)⟩
  have hlamX : (((lam : ℝ) : ℂ) • X).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal, hX.eq]
  have hvar := gibbs_variational_bound hρt hH hlamX hρt_pos hρt_tr β
  have hinv := gibbsRelEntropy_heisenberg_invariant hρ hH β t
  have htr_smul : (ρt * (((lam : ℝ) : ℂ) • X)).trace.re = lam * (ρt * X).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [htr_smul] at hvar
  have hcomb : lam * (ρt * X).trace.re ≤ gibbsRelEntropy hρ hH β + K₀ * (N : ℝ) * lam ^ 2 := by
    have h1 : gibbsRelEntropy hρt hH β = gibbsRelEntropy hρ hH β := hinv
    linarith [hvar, hcum]
  have hdiv := div_le_div_of_nonneg_right hcomb hlam.le
  have hlhs : lam * (ρt * X).trace.re / lam = (ρt * X).trace.re := by field_simp [hlam.ne']
  have hrhs : (gibbsRelEntropy hρ hH β + K₀ * (N : ℝ) * lam ^ 2) / lam =
      gibbsRelEntropy hρ hH β / lam + K₀ * (N : ℝ) * lam := by field_simp [hlam.ne']
  linarith

end ConcreteEntropicDecoupling

section ConcreteLiebRobinson

/-- **Light-Cone Support Growth under `iterComm` (Corollary 6.5)**:
In any finite metric `(Fin N, dist)` satisfying reflexivity and triangle inequality where every
interaction `X ∈ E` has diameter `≤ R_int`, every site `y ∈ causalUnion U₀ f` for a causal
sequence `f : Fin k → Finset (Fin N)` lies within distance `k * R_int` of some `x ∈ U₀`. -/
lemma causalUnion_dist_le {N R_int : ℕ} (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N)))
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (U₀ : Finset (Fin N)) :
    ∀ {k : ℕ} (f : Fin k → Finset (Fin N)),
      (∀ j : Fin k, f j ∈ E) → isCausalSeq U₀ f →
      ∀ y ∈ causalUnion U₀ f, ∃ x ∈ U₀, dist x y ≤ k * R_int := by
  intro k
  induction k with
  | zero =>
    intro f _ _ y hy
    simp only [causalUnion] at hy
    exact ⟨y, hy, by simp [hself]⟩
  | succ k ih =>
    intro f hf hcs y hy
    simp only [causalUnion] at hy
    simp only [isCausalSeq] at hcs
    rcases hcs with ⟨hinter, hcs_tail⟩
    have hf_tail : ∀ j : Fin k, Fin.tail f j ∈ E := fun j ↦ hf j.succ
    rcases Finset.mem_union.mp hy with hy_head | hy_tail
    · rcases hinter with ⟨z, hz⟩
      rcases Finset.mem_inter.mp hz with ⟨hz_head, hz_tail⟩
      rcases ih (Fin.tail f) hf_tail hcs_tail z hz_tail with ⟨x, hxU₀, hdxz⟩
      have hdz : dist z y ≤ R_int := hdiam (f 0) (hf 0) z hz_head y hy_head
      refine ⟨x, hxU₀, ?_⟩
      calc dist x y ≤ dist x z + dist z y := htri x z y
        _ ≤ k * R_int + R_int := Nat.add_le_add hdxz hdz
        _ = (k + 1) * R_int := by ring
    · rcases ih (Fin.tail f) hf_tail hcs_tail y hy_tail with ⟨x, hxU₀, hdx⟩
      exact ⟨x, hxU₀, le_trans hdx (Nat.mul_le_mul_right R_int (Nat.le_succ k))⟩

/-- Outside the light cone (`k * R_int < dist(U₀, V)`), every length-`k` causal commutator
`iterComm h f O` commutes with every `B ∈ supportedOn V`. -/
lemma matComm_iterComm_eq_zero_of_dist {N R_int : ℕ} (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N)))
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    {U₀ V : Finset (Fin N)} {O B : QubitOp N}
    (hO : O ∈ supportedOn U₀) (hB : B ∈ supportedOn V)
    {k : ℕ} (f : Fin k → Finset (Fin N)) (hf : ∀ j : Fin k, f j ∈ E)
    (hsep : ∀ x ∈ U₀, ∀ y ∈ V, k * R_int < dist x y) :
    matComm (iterComm h f O) B = 0 := by
  by_cases hcs : isCausalSeq U₀ f
  · have hmem : iterComm h f O ∈ supportedOn (causalUnion U₀ f) :=
      iterComm_mem_supportedOn h hsupp hO f
    have hdisj : Disjoint (causalUnion U₀ f) V := by
      rw [Finset.disjoint_left]
      intro y hy_c hy_V
      rcases causalUnion_dist_le dist hself htri E hdiam U₀ f hf hcs y hy_c with ⟨x, hxU₀, hle⟩
      exact absurd hle (not_le.mpr (hsep x hxU₀ y hy_V))
    have hcomm := supportedOn_comm_of_disjoint hdisj hmem hB
    unfold matComm; rw [hcomm, sub_self]
  · rw [iterComm_eq_zero_of_not_causal h hsupp hO f hcs]
    unfold matComm; simp

/-- **Concrete Lattice Lieb–Robinson Light-Cone Bound (Corollary 6.5)**:
For any `r`-local Hermitian Hamiltonian `H = ∑ X ∈ E, h X` of interaction range `≤ R_int`
and local strength `∑_{X ∋ x} ‖h_X‖_op ≤ J`, any `O ∈ supportedOn U₀`, and any `B ∈ supportedOn V`
separated by `∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y`, the Heisenberg commutator
`matComm (heisenbergEvol hH (t : ℂ) O) B` vanishes to order `m` in the causal Dyson expansion
and satisfies the concrete operator-norm tail bound for all `t : ℝ` with `2 * |t| * r * J < 1`
(and unconditionally for all `m` via the exact factorial series). -/
theorem lieb_robinson_concrete_opNorm {N r R_int : ℕ} (hr : 1 ≤ r)
    (dist : Fin N → Fin N → ℕ)
    (hself : ∀ x : Fin N, dist x x = 0)
    (htri : ∀ x y z : Fin N, dist x z ≤ dist x y + dist y z)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ R_int)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    {U₀ V : Finset (Fin N)} {O B : QubitOp N}
    (hO : O ∈ supportedOn U₀) (hB : B ∈ supportedOn V)
    (m : ℕ) (hsep : ∀ x ∈ U₀, ∀ y ∈ V, m * R_int < dist x y)
    (t : ℝ) (ht : 2 * |t| * (r : ℝ) * J < 1) :
    let q := 2 * |t| * (r : ℝ) * J
    opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B) ≤
      2 * opNorm O * opNorm B *
        ∑' k : ℕ, if k ≤ m then (0 : ℝ)
          else (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k *
            fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ := by
  intro q
  have hhas_ev := hasSum_heisenbergEvol_adPow hH (t : ℂ) O
  -- Continuous linear map `M ↦ matComm M B`
  let Lcomm : QubitOp N →L[ℂ] QubitOp N :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M ↦ matComm M B
        map_add' := fun M₁ M₂ ↦ by unfold matComm; noncomm_ring
        map_smul' := fun c M ↦ by unfold matComm; simp [Matrix.smul_mul, Matrix.mul_smul, smul_sub] }
  have hhas_comm : HasSum (fun k : ℕ ↦
      ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B)
      (matComm (heisenbergEvol hH (t : ℂ) O) B) := by
    have h1 := hhas_ev.map Lcomm Lcomm.continuous
    refine h1.congr_fun fun k ↦ ?_
    exact (Lcomm.map_smul _ _).symm
  have hhas_clm : HasSum (fun k : ℕ ↦
      opToCLM (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B))
      (opToCLM (matComm (heisenbergEvol hH (t : ℂ) O) B)) := by
    let φ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
      LinearMap.toContinuousLinearMap
        { toFun := opToCLM
          map_add' := opToCLM_add
          map_smul' := fun c A ↦ by simp [opToCLM_smul] }
    exact hhas_comm.map φ φ.continuous
  -- Each term `k ≤ m` vanishes!
  have hzero_le : ∀ k ≤ m, matComm (adPowMat (∑ X ∈ E, h X) k O) B = 0 := by
    intro k hkm
    rw [adPowMat_eq_sum_causal E h hsupp hO k]
    unfold matComm
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro f hf
    have hfE : ∀ j : Fin k, f j ∈ E :=
      fun j ↦ Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 j
    exact matComm_iterComm_eq_zero_of_dist dist hself htri E hdiam h hsupp hO hB f hfE
      (fun x hx y hy ↦ lt_of_le_of_lt (Nat.mul_le_mul_right R_int hkm) (hsep x hx y hy))
  -- Termwise operator-norm bound
  let bound : ℕ → ℝ := fun k ↦
    if k ≤ m then (0 : ℝ)
    else 2 * opNorm O * opNorm B *
      ((|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀)
  have hterm : ∀ k : ℕ,
      opNorm (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B) ≤
        bound k := by
    intro k
    dsimp only [bound]
    by_cases hkm : k ≤ m
    · simp only [hkm, ↓reduceIte, hzero_le k hkm, smul_zero]
      unfold opNorm
      have h0 : opToCLM (0 : QubitOp N) = 0 := by apply ContinuousLinearMap.ext; intro v; apply PiLp.ext; intro i; change ((0 : QubitOp N) *ᵥ v.ofLp) i = 0; simp
      rw [h0, norm_zero]
    · simp only [hkm, ↓reduceIte]
      rw [opNorm_smul]
      have hcoeff : ‖(Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)‖ = |t| ^ k / (k.factorial : ℝ) := by
        rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_natCast]
      rw [hcoeff]
      have hcomm_le : opNorm (matComm (adPowMat (∑ X ∈ E, h X) k O) B) ≤
          2 * opNorm (adPowMat (∑ X ∈ E, h X) k O) * opNorm B := by
        unfold matComm
        calc opNorm (adPowMat (∑ X ∈ E, h X) k O * B - B * adPowMat (∑ X ∈ E, h X) k O)
            = opNorm (adPowMat (∑ X ∈ E, h X) k O * B + (-1 : ℂ) • (B * adPowMat (∑ X ∈ E, h X) k O)) := by
              congr 1; simp [sub_eq_add_neg]
          _ ≤ opNorm (adPowMat (∑ X ∈ E, h X) k O * B) +
              opNorm ((-1 : ℂ) • (B * adPowMat (∑ X ∈ E, h X) k O)) := opNorm_add_le _ _
          _ ≤ opNorm (adPowMat (∑ X ∈ E, h X) k O) * opNorm B +
              opNorm B * opNorm (adPowMat (∑ X ∈ E, h X) k O) := by
              rw [opNorm_smul, norm_neg, norm_one, one_mul]
              exact add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
          _ = 2 * opNorm (adPowMat (∑ X ∈ E, h X) k O) * opNorm B := by ring
      have had_le : opNorm (adPowMat (∑ X ∈ E, h X) k O) ≤
          (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O := by
        rw [adPowMat_eq_sum_causal E h hsupp hO k]
        calc opNorm (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀), iterComm h f O)
            ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀), opNorm (iterComm h f O) :=
              opNorm_sum_le _ _
          _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeq U₀),
                (2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (f j))) * opNorm O :=
              Finset.sum_le_sum fun f _ ↦ opNorm_iterComm_le h O f
          _ = (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O := by
              unfold fwdCausalSum
              rw [Finset.mul_sum, Finset.sum_mul]
      have hfac_nn : 0 ≤ |t| ^ k / (k.factorial : ℝ) := by positivity
      calc |t| ^ k / (k.factorial : ℝ) * opNorm (matComm (adPowMat (∑ X ∈ E, h X) k O) B)
          ≤ |t| ^ k / (k.factorial : ℝ) * (2 * opNorm (adPowMat (∑ X ∈ E, h X) k O) * opNorm B) :=
            mul_le_mul_of_nonneg_left hcomm_le hfac_nn
        _ ≤ |t| ^ k / (k.factorial : ℝ) *
              (2 * ((2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O) * opNorm B) := by
            apply mul_le_mul_of_nonneg_left _ hfac_nn
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left had_le (by norm_num)) (opNorm_nonneg B)
        _ = 2 * opNorm O * opNorm B *
              ((|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀) := by
            ring
  -- Summability of the tail bound via `fwdCausalSum_le` and `q = 2 |t| r J < 1`
  have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
  have hsumm_raw : Summable (fun k : ℕ ↦
      (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀) := by
    let p : ℕ := U₀.card
    have hdom : ∀ k : ℕ,
        (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ ≤
          ((k + p).choose p : ℝ) * q ^ k := by
      intro k
      have hfwd := fwdCausalSum_general_le hr E hcard (fun X ↦ opNorm (h X)) (fun X _ ↦ opNorm_nonneg _)
        hJ hsite k U₀
      -- `∏ j : Fin k, (p + j * r) ≤ ∏ j : Fin k, (p + j) * r = r^k * (p+k)! / p!`
      have hprod_le : (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) ≤
          (r : ℝ) ^ k * ((∏ j : Fin k, ((p + j.val + 1 : ℕ) : ℝ))) := by
        have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        have h1 : (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) ≤
            ∏ j : Fin k, ((r : ℝ) * ((p + j.val + 1 : ℕ) : ℝ)) := by
          apply real_prod_le_prod
          · intro j _; positivity
          · intro j _
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) j.val]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      have hfact_prod : (∏ j : Fin k, ((p + j.val + 1 : ℕ) : ℝ)) =
          ((k + p).choose p : ℝ) * (k.factorial : ℝ) := by
        have hnat : (∏ j : Fin k, (p + j.val + 1)) * p.factorial = (k + p).factorial := by
          clear hfwd hprod_le
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [Fin.prod_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            calc (∏ j : Fin k, (p + j.val + 1)) * (p + k + 1) * p.factorial
                = (p + k + 1) * ((∏ j : Fin k, (p + j.val + 1)) * p.factorial) := by ring
              _ = (p + k + 1) * (k + p).factorial := by rw [ihk]
              _ = (k + 1 + p).factorial := by
                  rw [show k + 1 + p = (k + p) + 1 by omega, Nat.factorial_succ]; ring
        have hch := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left p k)
        rw [Nat.add_sub_cancel] at hch
        have hnat2 : (∏ j : Fin k, (p + j.val + 1)) * p.factorial =
            (k + p).choose p * k.factorial * p.factorial := by
          rw [hnat]; linarith [hch]
        have hnat3 : ∏ j : Fin k, (p + j.val + 1) = (k + p).choose p * k.factorial :=
          Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos p) hnat2
        exact_mod_cast hnat3
      have hfwd_le : fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ ≤
          ((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k := by
        calc fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀
            ≤ (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) * J ^ k := hfwd
          _ ≤ ((r : ℝ) ^ k * (∏ j : Fin k, ((p + j.val + 1 : ℕ) : ℝ))) * J ^ k :=
              mul_le_mul_of_nonneg_right hprod_le (pow_nonneg hJ k)
          _ = ((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k := by
              rw [hfact_prod, mul_pow]; ring
      have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      calc (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀
          ≤ (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k *
              (((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k) :=
            mul_le_mul_of_nonneg_left hfwd_le (by positivity)
        _ = ((k + p).choose p : ℝ) * q ^ k := by
            dsimp only [q]; simp only [mul_pow]
            field_simp [hkf.ne']; ring
    -- `((k + p).choose p : ℝ) * q ^ k ≤ ((k + p + 1) : ℝ) ^ p * q ^ k`, summable since `0 ≤ q < 1`
    have hsumm_poly : Summable (fun k : ℕ ↦ ((k + p).choose p : ℝ) * q ^ k) := by
      -- Since `q < 1`, choose `s = (q + 1) / 2 ∈ (q, 1)` and bound `choose (k+p) p ≤ (k+p)^p ≤ C * (s/q)^k`
      -- Even simpler: `((k + p).choose p : ℝ) ≤ (2 : ℝ) ^ (k + p)` only works for `q < 1/2`.
      -- For ALL `q < 1`, use `summable_of_ratio_norm_eventually_le`!
      by_cases hq0 : q = 0
      · simp only [hq0]
        refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
        have hk0 : k ≠ 0 := by simpa using hk
        simp [zero_pow hk0]
      · have hq_pos : 0 < q := lt_of_le_of_ne hq_nn (Ne.symm hq0)
        let r_lim : ℝ := (q + 1) / 2
        have hr_lt : r_lim < 1 := by dsimp only [r_lim]; linarith
        refine summable_of_ratio_norm_eventually_le (r := r_lim) hr_lt ?_
        have hN : ∃ N₀ : ℕ, ∀ k ≥ N₀, ((k + 1 + p : ℝ) / (k + 1 : ℝ)) * q ≤ r_lim := by
          obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((p : ℝ) * q / (r_lim - q))
          refine ⟨N₀, fun k hk ↦ ?_⟩
          have hrq : 0 < r_lim - q := by dsimp only [r_lim]; linarith
          have hk1 : (0 : ℝ) < (k + 1 : ℝ) := by positivity
          have hbig : (p : ℝ) * q / (r_lim - q) < (k + 1 : ℝ) := by
            have : (N₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            linarith
          have hmul : (p : ℝ) * q < (r_lim - q) * (k + 1 : ℝ) := by linarith [(div_lt_iff₀ hrq).mp hbig]
          rw [div_mul_eq_mul_div, div_le_iff₀ hk1]
          linarith
        rcases hN with ⟨N₀, hN₀⟩
        rw [Filter.eventually_atTop]
        refine ⟨N₀, fun k hk ↦ ?_⟩
        have hch_step : ((k + 1 + p).choose p : ℝ) * (k + 1 : ℝ) =
            ((k + p).choose p : ℝ) * (k + 1 + p : ℝ) := by
          have h1 : (k + 1 + p).choose p * (k + 1) = (k + p).choose p * (k + 1 + p) := by
            have ha := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left p (k + 1))
            have hb := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left p k)
            rw [Nat.add_sub_cancel] at ha hb
            have hfac : (k + 1 + p).factorial = (k + 1 + p) * (k + p).factorial := by
              rw [show k + 1 + p = (k + p) + 1 by omega, Nat.factorial_succ]
            have hfac2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
            have heq : (k + 1 + p).choose p * (k + 1) * (p.factorial * k.factorial) =
                (k + p).choose p * (k + 1 + p) * (p.factorial * k.factorial) := by
              calc (k + 1 + p).choose p * (k + 1) * (p.factorial * k.factorial)
                  = (k + 1 + p).choose p * p.factorial * ((k + 1) * k.factorial) := by ring
                _ = (k + 1 + p).factorial := by rw [← hfac2, ha]
                _ = (k + 1 + p) * (k + p).factorial := hfac
                _ = (k + 1 + p) * ((k + p).choose p * p.factorial * k.factorial) := by rw [hb]
                _ = (k + p).choose p * (k + 1 + p) * (p.factorial * k.factorial) := by ring
            exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos p) (Nat.factorial_pos k)) heq
          exact_mod_cast h1
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        have hk1 : (0 : ℝ) < (k + 1 : ℝ) := by positivity
        have hch_div : ((k + 1 + p).choose p : ℝ) =
            ((k + p).choose p : ℝ) * ((k + 1 + p : ℝ) / (k + 1 : ℝ)) := by
          rw [mul_div_assoc', eq_div_iff hk1.ne']; exact hch_step
        rw [hch_div, pow_succ]
        have hstep := hN₀ k hk
        have hnn : 0 ≤ ((k + p).choose p : ℝ) * q ^ k := by positivity
        calc ((k + p).choose p : ℝ) * ((k + 1 + p : ℝ) / (k + 1 : ℝ)) * (q ^ k * q)
            = (((k + 1 + p : ℝ) / (k + 1 : ℝ)) * q) * (((k + p).choose p : ℝ) * q ^ k) := by ring
          _ ≤ r_lim * (((k + p).choose p : ℝ) * q ^ k) :=
              mul_le_mul_of_nonneg_right hstep hnn
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) hdom hsumm_poly
    have hfwd_nn : 0 ≤ fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ :=
      Finset.sum_nonneg fun f _ ↦ Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _
    positivity
  have hsumm_tail : Summable (fun k : ℕ ↦
      if k ≤ m then (0 : ℝ)
      else (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀) := by
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hsumm_raw
    · split_ifs
      · exact le_refl 0
      · have : 0 ≤ fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ :=
          Finset.sum_nonneg fun f _ ↦ Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _
        positivity
    · split_ifs
      · have : 0 ≤ fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ :=
          Finset.sum_nonneg fun f _ ↦ Finset.prod_nonneg fun j _ ↦ opNorm_nonneg _
        positivity
      · exact le_refl _
  have hsumm_bound : Summable bound := by
    have hrew : bound = fun k ↦ 2 * opNorm O * opNorm B *
        (if k ≤ m then (0 : ℝ)
         else (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀) := by
      funext k; dsimp only [bound]; split_ifs <;> ring
    rw [hrew]; exact hsumm_tail.mul_left _
  have hsumm_norm : Summable (fun k : ℕ ↦
      opNorm (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B)) :=
    Summable.of_nonneg_of_le (fun _ ↦ opNorm_nonneg _) hterm hsumm_bound
  have htsum_eq : opToCLM (matComm (heisenbergEvol hH (t : ℂ) O) B) =
      ∑' k : ℕ, opToCLM (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B) :=
    hhas_clm.tsum_eq.symm
  calc opNorm (matComm (heisenbergEvol hH (t : ℂ) O) B)
      = ‖∑' k : ℕ, opToCLM (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B)‖ := by
        unfold opNorm; rw [htsum_eq]
    _ ≤ ∑' k : ℕ, opNorm (((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • matComm (adPowMat (∑ X ∈ E, h X) k O) B) :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' k : ℕ, bound k := hsumm_norm.tsum_le_tsum hterm hsumm_bound
    _ = 2 * opNorm O * opNorm B *
          ∑' k : ℕ, if k ≤ m then (0 : ℝ)
            else (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k *
              fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ := by
        have hrew : (fun k ↦ bound k) = fun k ↦ 2 * opNorm O * opNorm B *
            (if k ≤ m then (0 : ℝ)
             else (|t| ^ k / (k.factorial : ℝ)) * (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀) := by
          funext k; dsimp only [bound]; split_ifs <;> ring
        rw [hrew, tsum_mul_left]

end ConcreteLiebRobinson

end KrylovChaos
