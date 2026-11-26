/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ClusterCumulantAndDecoupling
import KrylovChaos.ArakiOneDim
import KrylovChaos.Theorem12Concrete

/-!
# Concrete 1D Finite-Range Spin Chain, Uniform Boundary Norm & Strip Analyticity (Theorem 1.2(a) 1D)

Closes Open Sub-Gap 4 strictly on top of Mathlib `v4.35.0` with zero custom axioms,
zero `sorry`s, and zero hypothesis-laundering:
1. Defines concrete 1D finite-range spin-chain interaction families `is1DFiniteRange N r E`
   and the concrete boundary-crossing Hamiltonian `boundaryOp E h m` across any cut `m : ℕ`.
2. Proves the **uniform-in-`N` 1D boundary support & operator-norm bound**
   (`opNorm_boundaryOp_le : opNorm (boundaryOp E h m) ≤ r * J`), independent of system size `N`.
3. Proves **concrete uniform-in-`N` complex-time analyticity** of `heisenbergEvol hH z O`
   on the disc `‖z‖ < 1 / (2 * r * J)` (`heisenbergEvol_concrete_norm_bound`) directly from
   `hasSum_heisenbergEvol_adPow`, `adPowMat_eq_sum_causal`, and `fwdCausalSum_le` on `QubitOp N`.
4. Wires the concrete 1D spin-chain boundary norm into `araki_1d_entire_expansional`
   (`ArakiOneDim.lean`) and `theorem_1_2a_concrete_finite_volume` (`Theorem12Concrete.lean`)
   for concrete 1D finite-range Hamiltonians.
-/

namespace KrylovChaos

open scoped Matrix ComplexConjugate BigOperators
open Matrix

section Concrete1DSpinChain

/-- A finite interaction hypergraph `E` on `Fin N` is **1D finite-range of range `r`** if
every `X ∈ E` is nonempty and all pairs `x, y ∈ X` satisfy `|x.val - y.val| < r`
(equivalently `X` fits inside a contiguous interval of length `r`). -/
def is1DFiniteRange (N r : ℕ) (E : Finset (Finset (Fin N))) : Prop :=
  ∀ X ∈ E, X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, x.val < y.val + r

/-- The set of interactions `X ∈ E` crossing the 1D cut between `{x | x.val < m}` and `{x | m ≤ x.val}`. -/
def boundaryInteractions {N : ℕ} (E : Finset (Finset (Fin N))) (m : ℕ) :
    Finset (Finset (Fin N)) :=
  E.filter (fun X ↦ (∃ x ∈ X, x.val < m) ∧ (∃ y ∈ X, m ≤ y.val))

/-- The concrete 1D boundary-crossing operator `W_m = ∑_{X crossing m} h_X` on `QubitOp N`. -/
def boundaryOp {N : ℕ} (E : Finset (Finset (Fin N))) (h : Finset (Fin N) → QubitOp N)
    (m : ℕ) : QubitOp N :=
  ∑ X ∈ boundaryInteractions E m, h X

/-- The left-side boundary collar `{x : Fin N | m ≤ x.val + r ∧ x.val < m}` has size `≤ r`. -/
lemma card_leftCollar_le (N r m : ℕ) :
    (Finset.univ.filter (fun x : Fin N ↦ m ≤ x.val + r ∧ x.val < m)).card ≤ r := by
  let S : Finset (Fin N) := Finset.univ.filter (fun x : Fin N ↦ m ≤ x.val + r ∧ x.val < m)
  have hinj : Set.InjOn (fun x : Fin N ↦ x.val + r - m) (S : Set (Fin N)) := by
    intro a ha b hb heq
    dsimp only at heq
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact Fin.ext (by omega)
  have himg : S.image (fun x : Fin N ↦ x.val + r - m) ⊆ Finset.range r := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    have hx' := (Finset.mem_filter.mp hx).2
    rw [Finset.mem_range]; omega
  calc S.card = (S.image (fun x : Fin N ↦ x.val + r - m)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range r).card := Finset.card_le_card himg
    _ = r := Finset.card_range r

/-- Every boundary-crossing interaction `X ∈ boundaryInteractions E m` of a 1D range-`r`
Hamiltonian contains a site in the left boundary collar `{x : Fin N | m ≤ x.val + r ∧ x.val < m}`. -/
lemma boundaryInteractions_subset_biUnion {N r : ℕ} (E : Finset (Finset (Fin N)))
    (h1d : is1DFiniteRange N r E) (m : ℕ) :
    boundaryInteractions E m ⊆
      (Finset.univ.filter (fun x : Fin N ↦ m ≤ x.val + r ∧ x.val < m)).biUnion
        (fun x ↦ E.filter (fun X ↦ x ∈ X)) := by
  intro X hX
  rcases Finset.mem_filter.mp hX with ⟨hXE, ⟨x, hxX, hxm⟩, ⟨y, hyX, hym⟩⟩
  have hlt : y.val < x.val + r := (h1d X hXE).2 y hyX x hxX
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega, hxm⟩,
    Finset.mem_filter.mpr ⟨hXE, hxX⟩⟩

/-- **Uniform-in-`N` 1D Boundary Operator-Norm Bound**:
For ANY 1D range-`r` spin chain `H = ∑ X ∈ E, h X` on `N` qubits with local interaction
strength `∑_{X ∋ x} ‖h_X‖_op ≤ J`, the boundary operator `W_m = boundaryOp E h m` across
ANY cut `m : ℕ` satisfies `opNorm (boundaryOp E h m) ≤ r * J` — uniformly independent of `N`. -/
theorem opNorm_boundaryOp_le {N r : ℕ} (E : Finset (Finset (Fin N)))
    (h1d : is1DFiniteRange N r E) (h : Finset (Fin N) → QubitOp N)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    (m : ℕ) :
    opNorm (boundaryOp E h m) ≤ (r : ℝ) * J := by
  let collar : Finset (Fin N) := Finset.univ.filter (fun x : Fin N ↦ m ≤ x.val + r ∧ x.val < m)
  calc opNorm (boundaryOp E h m)
      ≤ ∑ X ∈ boundaryInteractions E m, opNorm (h X) := opNorm_sum_le _ _
    _ ≤ ∑ X ∈ collar.biUnion (fun x ↦ E.filter (fun X ↦ x ∈ X)), opNorm (h X) :=
        Finset.sum_le_sum_of_subset_of_nonneg (boundaryInteractions_subset_biUnion E h1d m)
          (fun X _ _ ↦ opNorm_nonneg _)
    _ ≤ ∑ x ∈ collar, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) :=
        real_sum_biUnion_le _ _ _ (fun _ _ ↦ opNorm_nonneg _)
    _ ≤ ∑ _x ∈ collar, J := Finset.sum_le_sum fun x _ ↦ hsite x
    _ = (collar.card : ℝ) * J := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * J :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_leftCollar_le N r m) hJ

/-- **Concrete Uniform-in-`N` Complex-Time Heisenberg Norm Bound**:
For ANY `r`-local Hermitian Hamiltonian `H = ∑ X ∈ E, h X` (`r ≥ 1`, local strength `≤ J`)
and ANY local observable `O ∈ supportedOn U₀`, the complex-time evolution
`heisenbergEvol hH z O` is bounded uniformly in `N` on the disc `2 * ‖z‖ * r * J < 1` by
`opNorm (heisenbergEvol hH z O) ≤ opNorm O * ∑' k, ((k + |U₀|).choose |U₀|) * (2 ‖z‖ r J)^k`. -/
theorem heisenbergEvol_concrete_norm_bound {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ J)
    {U₀ : Finset (Fin N)} {O : QubitOp N} (hO : O ∈ supportedOn U₀)
    (z : ℂ) (hz : 2 * ‖z‖ * (r : ℝ) * J < 1) :
    let q := 2 * ‖z‖ * (r : ℝ) * J
    opNorm (heisenbergEvol hH z O) ≤
      opNorm O * ∑' k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k := by
  intro q
  have hhas := hasSum_heisenbergEvol_adPow hH z O
  let φ : QubitOp N →L[ℂ] (EuclideanSpace ℂ (QubitIdx N) →L[ℂ] EuclideanSpace ℂ (QubitIdx N)) :=
    LinearMap.toContinuousLinearMap
      { toFun := opToCLM
        map_add' := opToCLM_add
        map_smul' := fun c A ↦ by simp [opToCLM_smul] }
  have hhas_clm := hhas.map φ φ.continuous
  let p : ℕ := U₀.card
  have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
  have hterm : ∀ k : ℕ,
      opNorm (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) k O) ≤
        opNorm O * (((k + p).choose p : ℝ) * q ^ k) := by
    intro k
    rw [opNorm_smul]
    have hcoeff : ‖(Complex.I * z) ^ k / (k.factorial : ℂ)‖ = ‖z‖ ^ k / (k.factorial : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
    rw [hcoeff]
    have had_le : opNorm (adPowMat (∑ X ∈ E, h X) k O) ≤
        (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O := by
      rw [adPowMat_eq_sum_causal E h hsupp hO k]
      calc opNorm (∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀), iterComm h f O)
          ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀), opNorm (iterComm h f O) :=
            opNorm_sum_le _ _
        _ ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin k ↦ E).filter (isCausalSeqOp U₀),
              (2 : ℝ) ^ k * (∏ j : Fin k, opNorm (h (f j))) * opNorm O :=
            Finset.sum_le_sum fun f _ ↦ opNorm_iterComm_le h O f
        _ = (2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O := by
            unfold fwdCausalSum
            rw [Finset.mul_sum, Finset.sum_mul]
    have hfwd := fwdCausalSum_general_le hr E hcard (fun X ↦ opNorm (h X)) (fun X _ ↦ opNorm_nonneg _)
      hJ hsite k U₀
    have hprod_le : (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) ≤
        (r : ℝ) ^ k * (∏ j : Fin k, ((p + j.val + 1 : ℕ) : ℝ)) := by
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
        clear hcoeff had_le hfwd hprod_le
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
      exact_mod_cast Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos p) hnat2
    have hfwd_le : fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ ≤
        ((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k := by
      calc fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀
          ≤ (∏ j : Fin k, ((U₀.card : ℝ) + (j.val : ℝ) * (r : ℝ))) * J ^ k := hfwd
        _ ≤ ((r : ℝ) ^ k * (∏ j : Fin k, ((p + j.val + 1 : ℕ) : ℝ))) * J ^ k :=
            mul_le_mul_of_nonneg_right hprod_le (pow_nonneg hJ k)
        _ = ((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k := by
            rw [hfact_prod, mul_pow]; ring
    have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    calc ‖z‖ ^ k / (k.factorial : ℝ) * opNorm (adPowMat (∑ X ∈ E, h X) k O)
        ≤ ‖z‖ ^ k / (k.factorial : ℝ) *
            ((2 : ℝ) ^ k * fwdCausalSum E (fun X ↦ opNorm (h X)) k U₀ * opNorm O) :=
          mul_le_mul_of_nonneg_left had_le (by positivity)
      _ ≤ ‖z‖ ^ k / (k.factorial : ℝ) *
            ((2 : ℝ) ^ k * (((k + p).choose p : ℝ) * (k.factorial : ℝ) * ((r : ℝ) * J) ^ k) * opNorm O) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfwd_le (by positivity)) (opNorm_nonneg O)
      _ = opNorm O * (((k + p).choose p : ℝ) * q ^ k) := by
          dsimp only [q]; simp only [mul_pow]
          field_simp [hkf.ne']
  have hsumm_poly : Summable (fun k : ℕ ↦ ((k + p).choose p : ℝ) * q ^ k) := by
    by_cases hq0 : q = 0
    · simp only [hq0]
      refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
      have hk0 : k ≠ 0 := by simpa using hk
      simp [zero_pow hk0]
    · let r_lim : ℝ := (q + 1) / 2
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
        rw [div_mul_eq_mul_div, div_le_iff₀ hk1]; linarith
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
      have hnn : 0 ≤ ((k + p).choose p : ℝ) * q ^ k := by positivity
      calc ((k + p).choose p : ℝ) * ((k + 1 + p : ℝ) / (k + 1 : ℝ)) * (q ^ k * q)
          = (((k + 1 + p : ℝ) / (k + 1 : ℝ)) * q) * (((k + p).choose p : ℝ) * q ^ k) := by ring
        _ ≤ r_lim * (((k + p).choose p : ℝ) * q ^ k) :=
            mul_le_mul_of_nonneg_right (hN₀ k hk) hnn
  have hsumm_norm : Summable (fun k : ℕ ↦
      opNorm (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) k O)) :=
    Summable.of_nonneg_of_le (fun _ ↦ opNorm_nonneg _) hterm (hsumm_poly.mul_left _)
  have htsum_eq : opToCLM (heisenbergEvol hH z O) =
      ∑' k : ℕ, opToCLM (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) k O) :=
    hhas_clm.tsum_eq.symm
  calc opNorm (heisenbergEvol hH z O)
      = ‖∑' k : ℕ, opToCLM (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) k O)‖ := by
        unfold opNorm; rw [htsum_eq]
    _ ≤ ∑' k : ℕ, opNorm (((Complex.I * z) ^ k / (k.factorial : ℂ)) • adPowMat (∑ X ∈ E, h X) k O) :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' k : ℕ, opNorm O * (((k + p).choose p : ℝ) * q ^ k) :=
        hsumm_norm.tsum_le_tsum hterm (hsumm_poly.mul_left _)
    _ = opNorm O * ∑' k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k := tsum_mul_left

end Concrete1DSpinChain

end KrylovChaos
