/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.InfiniteChainLimit
import KrylovChaos.Milestone1InfiniteChain
import Mathlib.Tactic

/-!
# Unconditional Infinite-Chain Theorem 1.1(a): Existence, Carleman ℓ²-Uniqueness, and Exact Eqs. (1.12)–(1.13)

Glues the finite-truncation semigroup limit `KrylovChaos/InfiniteChainLimit.lean` to the real
infinite Krylov ODE, Carleman `ℓ²`-uniqueness, exact single-exponential tail and complexity bounds
Eqs. (1.12)–(1.13), and `limsup` rate bound in `KrylovChaos/Milestone1InfiniteChain.lean`:
1. `jacobiWavefn_neg_t`: time-reversal symmetry `jacobiWavefn D b (-t) n = (-1)^n * jacobiWavefn D b t n`.
2. `infiniteKrylovWavefn_tendsto_all_time`: extends pointwise convergence to all `t : ℝ`.
3. `realFiniteKrylovWavefn` & `realInfiniteKrylovWavefn`: unitary gauge
   `φ_N(m, t) = ((-I)^m * jacobiWavefn (N + 1) b t m).re`, proved to be purely real, satisfy the
   exact finite Krylov ODE, initial condition, and uniform bound `|φ_N(m, t)| ≤ 1`.
4. `theorem_1_1a_infinite_chain_complete`: single unconditional headline theorem taking only
   `b : ℕ → ℝ` (`b 0 = 0`, `0 ≤ b n ≤ α n + γ` for `n ≥ 1`, `α > 0`, `γ ≥ 0`) and proving:
   - existence, continuity, initial condition, probability conservation `∑' m, (φ m t)² = 1`,
     and satisfaction of the infinite Krylov ODE for all `m : ℕ, t : ℝ`,
   - Carleman `ℓ²`-uniqueness among all uniformly `ℓ²`-bounded solutions,
   - exact single-exponential Eqs. (1.12)–(1.13) for all `n ≥ 0, t ≥ 0, θ₀ > 0`,
   - `Filter.limsup (fun t ↦ Real.log (∑' m, m * (φ m t)²) / t) atTop ≤ 2 * α`.
-/

namespace KrylovChaos

open Complex Filter Topology

section TimeReversalAndRealGauge

/-- Coordinate-level derivative of `jacobiWavefn hD b`. -/
private lemma jacobiWavefn_coord_hasDerivAt {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) (n : Fin D) :
    HasDerivAt (fun s : ℝ ↦ jacobiWavefn hD b s n)
      (Complex.I *
        ((if h0 : 0 < n.1 then (b n.1 : ℂ) * jacobiWavefn hD b t ⟨n.1 - 1, by omega⟩ else 0) +
         (if h1 : n.1 + 1 < D then (b (n.1 + 1) : ℂ) * jacobiWavefn hD b t ⟨n.1 + 1, h1⟩ else 0)))
      t := by
  have hode := jacobiWavefn_ode hD b t
  let L : EuclideanSpace ℂ (Fin D) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ v.ofLp n
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  have hcoord := L.hasFDerivAt.comp_hasDerivAt t hode
  convert hcoord using 1
  change Complex.I * _ = (Complex.I • jacobiCLM D b (jacobiWavefn hD b t)).ofLp n
  simp only [PiLp.smul_apply, smul_eq_mul]
  congr 1
  change _ = ∑ x : Fin D, ((jacobiMat D b n x : ℝ) : ℂ) * (jacobiWavefn hD b t).ofLp x
  have hstep : ∀ x : Fin D,
      ((jacobiMat D b n x : ℝ) : ℂ) * (jacobiWavefn hD b t).ofLp x =
      (if n.1 = x.1 + 1 then (b n.1 : ℂ) * (jacobiWavefn hD b t).ofLp x else 0) +
      (if x.1 = n.1 + 1 then (b (n.1 + 1) : ℂ) * (jacobiWavefn hD b t).ofLp x else 0) := by
    intro x
    unfold jacobiMat; simp only [Matrix.of_apply]
    by_cases h1 : x.1 = n.1 + 1
    · have h2 : ¬(n.1 = x.1 + 1) := by omega
      simp [h1, h2]
    · by_cases h2 : n.1 = x.1 + 1
      · simp [h1, h2]
      · simp [h1, h2]
  simp_rw [hstep, Finset.sum_add_distrib]
  congr 1
  · by_cases h0 : 0 < n.1
    · rw [dif_pos h0, Finset.sum_eq_single ⟨n.1 - 1, by omega⟩]
      · rw [if_pos (by dsimp; omega)]; rfl
      · intro x _ hx; rw [if_neg (fun h ↦ hx (Fin.ext (by dsimp; omega)))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg h0]; symm; apply Finset.sum_eq_zero; intro x _; rw [if_neg (by omega)]
  · by_cases h1 : n.1 + 1 < D
    · rw [dif_pos h1, Finset.sum_eq_single ⟨n.1 + 1, h1⟩]
      · rw [if_pos rfl]; rfl
      · intro x _ hx; rw [if_neg (fun h ↦ hx (Fin.ext (by dsimp; omega)))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg h1]; symm; apply Finset.sum_eq_zero; intro x _; rw [if_neg (by omega)]

/-- Time-reversal symmetry of the finite Jacobi wavefunction:
`jacobiWavefn hD b (-t) n = (-1 : ℂ) ^ n.1 * jacobiWavefn hD b t n` for all `t : ℝ`. -/
theorem jacobiWavefn_neg_t {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) (n : Fin D) :
    jacobiWavefn hD b (-t) n = (-1 : ℂ) ^ n.1 * jacobiWavefn hD b t n := by
  let S : EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ WithLp.toLp 2 (fun k : Fin D ↦ (-1 : ℂ) ^ k.1 * v k)
        map_add' := fun u v ↦ by ext k; simp [mul_add]
        map_smul' := fun c v ↦ by ext k; simp [mul_left_comm] }
  have hS_apply : ∀ v k, S v k = (-1 : ℂ) ^ k.1 * v k := fun _ _ ↦ rfl
  have hS_anti : ∀ v, S (jacobiCLM D b v) = -(jacobiCLM D b (S v)) := by
    intro v; ext k
    simp only [hS_apply, PiLp.neg_apply]
    change (-1 : ℂ) ^ k.1 * ∑ x : Fin D, ((jacobiMat D b k x : ℝ) : ℂ) * v.ofLp x =
      -(∑ x : Fin D, ((jacobiMat D b k x : ℝ) : ℂ) * ((-1 : ℂ) ^ x.1 * v.ofLp x))
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro x _
    unfold jacobiMat; simp only [Matrix.of_apply]
    by_cases h1 : x.1 = k.1 + 1
    · rw [if_pos h1, h1, pow_succ]; ring
    · by_cases h2 : k.1 = x.1 + 1
      · rw [if_neg h1, if_pos h2, h2, pow_succ]; ring
      · rw [if_neg h1, if_neg h2]; simp
  let u : ℝ → EuclideanSpace ℂ (Fin D) := fun s ↦ S (jacobiWavefn hD b (-s)) - jacobiWavefn hD b s
  have hu0 : u 0 = 0 := by
    dsimp only [u]; rw [neg_zero]
    ext k; simp only [PiLp.sub_apply, PiLp.zero_apply, hS_apply]
    have h0 : jacobiWavefn hD b 0 = EuclideanSpace.single (⟨0, hD⟩ : Fin D) 1 := by
      unfold jacobiWavefn; rw [jacobiUnitary_zero]; simp
    rw [h0]
    by_cases hk : k = ⟨0, hD⟩
    · subst hk; simp [EuclideanSpace.single, Pi.single_apply]
    · simp [EuclideanSpace.single, Pi.single_apply, hk]
  have hu_deriv : ∀ s : ℝ, HasDerivAt u ((Complex.I • jacobiCLM D b) (u s)) s := by
    intro s
    have hneg : HasDerivAt (fun r : ℝ ↦ jacobiWavefn hD b (-r))
        (-((Complex.I • jacobiCLM D b) (jacobiWavefn hD b (-s)))) s := by
      have h1 := (jacobiWavefn_ode hD b (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at h1
      exact h1
    have hS_d : HasDerivAt (fun r : ℝ ↦ S (jacobiWavefn hD b (-r)))
        (S (-((Complex.I • jacobiCLM D b) (jacobiWavefn hD b (-s))))) s :=
      (S.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hneg
    have hsub := hS_d.sub (jacobiWavefn_ode hD b s)
    convert hsub using 1
    dsimp only [u]
    rw [ContinuousLinearMap.smul_apply, map_sub, smul_sub, map_neg, ContinuousLinearMap.smul_apply,
      map_smul, hS_anti, smul_neg, neg_neg]
  have hnormSq_deriv : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ ‖u r‖ ^ 2) 0 s := by
    intro s
    have hinner := HasDerivAt.inner ℝ (hu_deriv s) (hu_deriv s)
    have hnorm_eq : (fun r ↦ ‖u r‖ ^ 2) = (fun r ↦ @inner ℝ _ _ (u r) (u r)) := by
      ext r; exact (real_inner_self_eq_norm_sq (u r)).symm
    rw [hnorm_eq]
    have hskew : @inner ℝ _ _ (u s) ((Complex.I • jacobiCLM D b) (u s)) = 0 := by
      have hre : @inner ℝ _ _ (u s) ((Complex.I • jacobiCLM D b) (u s)) =
          (inner ℂ (u s) ((Complex.I • jacobiCLM D b) (u s))).re := by
        simp only [PiLp.inner_apply, Complex.re_sum, RCLike.inner_apply]
        congr 1; ext i; simp [Complex.mul_re]
      rw [hre, ContinuousLinearMap.smul_apply, inner_smul_right,
        Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      have hreal : (inner ℂ (u s) (jacobiCLM D b (u s))).im = 0 := by
        have hsa : inner ℂ (jacobiCLM D b (u s)) (u s) = inner ℂ (u s) (jacobiCLM D b (u s)) := by
          simp only [PiLp.inner_apply, RCLike.inner_apply]
          change ∑ i : Fin D, (u s).ofLp i * star (∑ j : Fin D, ((jacobiMat D b i j : ℝ) : ℂ) * (u s).ofLp j) =
            ∑ i : Fin D, (∑ j : Fin D, ((jacobiMat D b i j : ℝ) : ℂ) * (u s).ofLp j) * star ((u s).ofLp i)
          simp_rw [map_sum, map_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          have hsym : jacobiMat D b j i = jacobiMat D b i j := by
            unfold jacobiMat; simp only [Matrix.of_apply]
            by_cases h1 : i.val = j.val + 1
            · have h2 : ¬(j.val = i.val + 1) := by omega
              rw [if_pos h1, if_neg h2, if_pos h1]
            · by_cases h2 : j.val = i.val + 1
              · rw [if_neg h1, if_pos h2, if_pos h2]
              · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
          rw [hsym]; ring
        have hconj := congrArg Complex.im (inner_conj_symm (jacobiCLM D b (u s)) (u s))
        rw [hsa, Complex.conj_im] at hconj
        linarith
      linarith
    have hskew' : @inner ℝ _ _ ((Complex.I • jacobiCLM D b) (u s)) (u s) = 0 := by
      rw [real_inner_comm]; exact hskew
    convert hinner using 1
    rw [hskew, hskew', add_zero]
  have hconst : ‖u t‖ ^ 2 = ‖u 0‖ ^ 2 :=
    is_const_of_deriv_eq_zero (fun s ↦ (hnormSq_deriv s).differentiableAt)
      (fun s ↦ (hnormSq_deriv s).deriv) t 0
  rw [hu0, norm_zero, zero_pow (by norm_num)] at hconst
  have hut : u t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hconst)
  have hcoord := congrArg (fun v : EuclideanSpace ℂ (Fin D) ↦ v n) hut
  simp only [u, PiLp.sub_apply, PiLp.zero_apply, hS_apply, sub_eq_zero] at hcoord
  calc jacobiWavefn hD b (-t) n
      = (-1 : ℂ) ^ n.1 * ((-1 : ℂ) ^ n.1 * jacobiWavefn hD b (-t) n) := by
          rw [← mul_assoc, ← mul_pow]; simp
    _ = (-1 : ℂ) ^ n.1 * jacobiWavefn hD b t n := by rw [hcoord]

/-- Pointwise convergence `jacobiWavefn hD b t m → infiniteKrylovWavefn b t m` for ALL `t : ℝ`. -/
theorem infiniteKrylovWavefn_tendsto_all_time (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    (t : ℝ) (m : ℕ) :
    Tendsto (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0)
      atTop (nhds (infiniteKrylovWavefn b t m)) := by
  rcases le_or_gt 0 t with ht | ht
  · exact infiniteKrylovWavefn_tendsto b hα hγ ht hb_nn hb_lin m
  · have hpos : 0 ≤ -t := by linarith
    have htend_pos := infiniteKrylovWavefn_tendsto b hα hγ hpos hb_nn hb_lin m
    have htend_neg : Tendsto
        (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0)
        atTop (nhds ((-1 : ℂ) ^ m * infiniteKrylovWavefn b (-t) m)) := by
      have hrew : (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0) =
          fun D : ℕ ↦ (-1 : ℂ) ^ m *
            (if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b (-t) ⟨m, hm⟩ else 0) := by
        funext D; split_ifs with hm
        · have h := jacobiWavefn_neg_t (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b (-t) ⟨m, hm⟩
          rwa [neg_neg] at h
        · simp
      rw [hrew]
      exact htend_pos.const_mul ((-1 : ℂ) ^ m)
    exact htend_neg.cauchySeq.tendsto_limUnder

/-- Time-reversal symmetry of the infinite-chain wavefunction:
`infiniteKrylovWavefn b (-t) m = (-1 : ℂ) ^ m * infiniteKrylovWavefn b t m`. -/
lemma infiniteKrylovWavefn_neg_t (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    (t : ℝ) (m : ℕ) :
    infiniteKrylovWavefn b (-t) m = (-1 : ℂ) ^ m * infiniteKrylovWavefn b t m := by
  have h1 := infiniteKrylovWavefn_tendsto_all_time b hα hγ hb_nn hb_lin (-t) m
  have h2 := (infiniteKrylovWavefn_tendsto_all_time b hα hγ hb_nn hb_lin t m).const_mul ((-1 : ℂ) ^ m)
  have hrew : (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b (-t) ⟨m, hm⟩ else 0) =
      fun D : ℕ ↦ (-1 : ℂ) ^ m *
        (if hm : m < D then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0) := by
    funext D; split_ifs with hm
    · exact jacobiWavefn_neg_t (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩
    · simp
  rw [hrew] at h1
  exact tendsto_nhds_unique h1 h2

/-- Real finite-chain Krylov wavefunction obtained via the unitary gauge
`φ_N(m, t) = ((-I)^m * jacobiWavefn (Nat.succ_pos N) b t m).re` (zero for `m > N`). -/
noncomputable def realFiniteKrylovWavefn (b : ℕ → ℝ) (N m : ℕ) (t : ℝ) : ℝ :=
  if hm : m ≤ N then
    ((-Complex.I) ^ m * jacobiWavefn (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩).re
  else 0

/-- Real infinite-chain Krylov wavefunction `φ(m, t) = ((-I)^m * infiniteKrylovWavefn b t m).re`. -/
noncomputable def realInfiniteKrylovWavefn (b : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ((-Complex.I) ^ m * infiniteKrylovWavefn b t m).re

/-- Complex gauged finite-chain coordinate `z_N(m, t) = (-I)^m * jacobiWavefn (Nat.succ_pos N) b t m`. -/
private noncomputable def gaugedFiniteWavefn (b : ℕ → ℝ) (N m : ℕ) (t : ℝ) : ℂ :=
  if hm : m ≤ N then
    (-Complex.I) ^ m * jacobiWavefn (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩
  else 0

private lemma gaugedFiniteWavefn_ode (b : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N) (t : ℝ) :
    HasDerivAt (gaugedFiniteWavefn b N m)
      ((if m = 0 then (0 : ℂ) else (b m : ℂ)) * gaugedFiniteWavefn b N (m - 1) t -
       (if m = N then (0 : ℂ) else (b (m + 1) : ℂ)) * gaugedFiniteWavefn b N (m + 1) t) t := by
  have hrew : gaugedFiniteWavefn b N m =
      fun s ↦ (-Complex.I) ^ m * jacobiWavefn (Nat.succ_pos N) b s ⟨m, Nat.lt_succ_of_le hm⟩ := by
    funext s; simp [gaugedFiniteWavefn, hm]
  rw [hrew]
  have hd := (jacobiWavefn_coord_hasDerivAt (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩).const_mul ((-Complex.I) ^ m)
  convert hd using 1
  have h1 : (if m = 0 then (0 : ℂ) else (b m : ℂ)) * gaugedFiniteWavefn b N (m - 1) t =
      (-Complex.I) ^ m * (Complex.I *
        if h0 : 0 < m then (b m : ℂ) * jacobiWavefn (Nat.succ_pos N) b t ⟨m - 1, by omega⟩ else 0) := by
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm1 : m - 1 ≤ N := by omega
      simp only [hm0, ↓reduceIte, hpos, ↓reduceDIte, gaugedFiniteWavefn, hm1]
      have hpow : (-Complex.I) ^ m * Complex.I = (-Complex.I) ^ (m - 1) := by
        cases h : m with
        | zero => omega
        | succ k =>
          simp only [Nat.succ_sub_one, pow_succ]
          calc (-Complex.I) ^ k * -Complex.I * Complex.I
              = (-Complex.I) ^ k * -(Complex.I * Complex.I) := by ring
            _ = (-Complex.I) ^ k * -(-1 : ℂ) := by rw [Complex.I_mul_I]
            _ = (-Complex.I) ^ k := by ring
      linear_combination (b m : ℂ) * jacobiWavefn (Nat.succ_pos N) b t ⟨m - 1, by omega⟩ * hpow.symm
  have h2 : -((if m = N then (0 : ℂ) else (b (m + 1) : ℂ)) * gaugedFiniteWavefn b N (m + 1) t) =
      (-Complex.I) ^ m * (Complex.I *
        if h1 : m + 1 < N.succ then (b (m + 1) : ℂ) * jacobiWavefn (Nat.succ_pos N) b t ⟨m + 1, h1⟩ else 0) := by
    by_cases hmN : m = N
    · subst hmN; simp
    · have hlt : m + 1 < N.succ := by omega
      have hle : m + 1 ≤ N := by omega
      simp only [hmN, ↓reduceIte, hlt, ↓reduceDIte, gaugedFiniteWavefn, hle]
      have hpow : -((-Complex.I) ^ (m + 1)) = (-Complex.I) ^ m * Complex.I := by
        rw [pow_succ]; ring
      linear_combination (b (m + 1) : ℂ) * jacobiWavefn (Nat.succ_pos N) b t ⟨m + 1, hlt⟩ * hpow
  simp only [Fin.val_mk]; rw [mul_add, ← h1, ← h2, sub_eq_add_neg]

private lemma gaugedFiniteWavefn_im_zero (b : ℕ → ℝ) (N m : ℕ) (t : ℝ) :
    (gaugedFiniteWavefn b N m t).im = 0 := by
  by_cases hm : m ≤ N
  · let y : ℕ → ℝ → ℝ := fun k s ↦ (gaugedFiniteWavefn b N k s).im
    have hy0 : ∀ k ≤ N, y k 0 = 0 := by
      intro k hk
      dsimp only [y, gaugedFiniteWavefn]
      rw [dif_pos hk]
      have h0 : jacobiWavefn (Nat.succ_pos N) b 0 = EuclideanSpace.single (0 : Fin (N + 1)) 1 := by
        unfold jacobiWavefn; rw [jacobiUnitary_zero]; simp
      rw [h0]
      by_cases hk0 : k = 0
      · subst hk0; simp [EuclideanSpace.single, Pi.single_apply]
      · have hne : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) ≠ 0 := fun h ↦ hk0 (congrArg Fin.val h)
        simp [EuclideanSpace.single, Pi.single_apply, hne]
    have hy_ode : ∀ k ≤ N, ∀ s : ℝ,
        HasDerivAt (y k)
          ((if k = 0 then 0 else b k) * y (k - 1) s -
           (if k = N then 0 else b (k + 1)) * y (k + 1) s) s := by
      intro k hk s
      have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (gaugedFiniteWavefn_ode b N k hk s)
      convert hd using 1
      dsimp only [y]
      change _ = ((_ : ℂ) - (_ : ℂ)).im
      rw [Complex.sub_im]
      congr 1
      · split_ifs <;> simp
      · split_ifs <;> simp
    have hE_deriv : ∀ s : ℝ, HasDerivAt (fun r ↦ ∑ k ∈ Finset.range (N + 1), (y k r) ^ 2) 0 s := by
      intro s
      have hsum : HasDerivAt (fun r ↦ ∑ k ∈ Finset.range (N + 1), (y k r) ^ 2)
          (∑ k ∈ Finset.range (N + 1),
            2 * y k s * ((if k = 0 then 0 else b k) * y (k - 1) s -
              (if k = N then 0 else b (k + 1)) * y (k + 1) s)) s := by
        apply HasDerivAt.fun_sum
        intro k hk
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        convert (hy_ode k hkN s).pow 2 using 1; ring
      convert hsum using 1
      have hsplit : ∑ k ∈ Finset.range (N + 1),
            2 * y k s * ((if k = 0 then 0 else b k) * y (k - 1) s -
              (if k = N then 0 else b (k + 1)) * y (k + 1) s) =
          (∑ k ∈ Finset.range (N + 1), if k = 0 then 0 else 2 * b k * y k s * y (k - 1) s) -
          (∑ k ∈ Finset.range (N + 1), if k = N then 0 else 2 * b (k + 1) * y k s * y (k + 1) s) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro k _
        split_ifs <;> ring
      rw [hsplit]
      have hA : (∑ k ∈ Finset.range (N + 1), if k = 0 then 0 else 2 * b k * y k s * y (k - 1) s) =
          ∑ k ∈ Finset.range N, 2 * b (k + 1) * y (k + 1) s * y k s := by
        rw [Finset.sum_range_succ']; simp
      have hB : (∑ k ∈ Finset.range (N + 1), if k = N then 0 else 2 * b (k + 1) * y k s * y (k + 1) s) =
          ∑ k ∈ Finset.range N, 2 * b (k + 1) * y (k + 1) s * y k s := by
        rw [Finset.sum_range_succ]; simp only [↓reduceIte, add_zero]
        apply Finset.sum_congr rfl; intro k hk
        have hne : k ≠ N := ne_of_lt (Finset.mem_range.mp hk)
        rw [if_neg hne]; ring
      rw [hA, hB, sub_self]
    have hconst : (∑ k ∈ Finset.range (N + 1), (y k t) ^ 2) =
        ∑ k ∈ Finset.range (N + 1), (y k 0) ^ 2 :=
      is_const_of_deriv_eq_zero (fun s ↦ (hE_deriv s).differentiableAt)
        (fun s ↦ (hE_deriv s).deriv) t 0
    have hzero : ∑ k ∈ Finset.range (N + 1), (y k 0) ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      rw [hy0 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]; simp
    rw [hzero] at hconst
    have hsq0 : (y m t) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ sq_nonneg (y k t))).mp hconst m
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    exact sq_eq_zero_iff.mp hsq0
  · simp [gaugedFiniteWavefn, hm]

/-- Exact finite-chain real Krylov ODE for `realFiniteKrylovWavefn`. -/
lemma realFiniteKrylovWavefn_ode (b : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N) (t : ℝ) :
    HasDerivAt (realFiniteKrylovWavefn b N m)
      ((if m = 0 then 0 else b m) * realFiniteKrylovWavefn b N (m - 1) t -
       (if m = N then 0 else b (m + 1)) * realFiniteKrylovWavefn b N (m + 1) t) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (gaugedFiniteWavefn_ode b N m hm t)
  convert hd using 1
  change _ = ((_ : ℂ) - (_ : ℂ)).re
  rw [Complex.sub_re]
  congr 1
  · split_ifs <;> simp [realFiniteKrylovWavefn, gaugedFiniteWavefn]
  · split_ifs <;> simp [realFiniteKrylovWavefn, gaugedFiniteWavefn]

/-- Initial condition `realFiniteKrylovWavefn b N m 0 = δ_{m0}` for `m ≤ N`. -/
lemma realFiniteKrylovWavefn_init (b : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    realFiniteKrylovWavefn b N m 0 = if m = 0 then 1 else 0 := by
  unfold realFiniteKrylovWavefn
  rw [dif_pos hm]
  have h0 : jacobiWavefn (Nat.succ_pos N) b 0 = EuclideanSpace.single (0 : Fin (N + 1)) 1 := by
    unfold jacobiWavefn; rw [jacobiUnitary_zero]; simp
  rw [h0]
  by_cases hm0 : m = 0
  · subst hm0; simp [EuclideanSpace.single, Pi.single_apply]
  · have hne : (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (N + 1)) ≠ 0 := fun h ↦ hm0 (congrArg Fin.val h)
    simp [EuclideanSpace.single, Pi.single_apply, hne, hm0]

/-- Uniform bound `|realFiniteKrylovWavefn b N m t| ≤ 1`. -/
lemma realFiniteKrylovWavefn_abs_le_one (b : ℕ → ℝ) (N m : ℕ) (t : ℝ) :
    |realFiniteKrylovWavefn b N m t| ≤ 1 := by
  unfold realFiniteKrylovWavefn
  split_ifs with hm
  · calc |((-Complex.I) ^ m * jacobiWavefn (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩).re|
        ≤ ‖(-Complex.I) ^ m * jacobiWavefn (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩‖ :=
          Complex.abs_re_le_norm _
      _ = ‖jacobiWavefn (Nat.succ_pos N) b t ⟨m, Nat.lt_succ_of_le hm⟩‖ := by
          rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
      _ ≤ ‖jacobiWavefn (Nat.succ_pos N) b t‖ := PiLp.norm_apply_le _ _
      _ = 1 := by
          unfold jacobiWavefn; rw [jacobiUnitary_norm_preserve]
          have h0eq : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := rfl
          rw [h0eq]
          have hsq : ‖EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℂ)‖ ^ 2 = 1 := by
            rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
            simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_ite_eq']
          nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℂ))]
  · simp

/-- Pointwise convergence `realFiniteKrylovWavefn b N m t → realInfiniteKrylovWavefn b m t`
for all `m : ℕ` and all `t : ℝ`. -/
theorem realInfiniteKrylovWavefn_tendsto (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    (m : ℕ) (t : ℝ) :
    Tendsto (fun N : ℕ ↦ realFiniteKrylovWavefn b N m t) atTop
      (nhds (realInfiniteKrylovWavefn b m t)) := by
  have ht := infiniteKrylovWavefn_tendsto_all_time b hα hγ hb_nn hb_lin t m
  have ht_shift : Tendsto
      (fun N : ℕ ↦ if hm : m < N + 1 then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0)
      atTop (nhds (infiniteKrylovWavefn b t m)) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp (ht_shift.const_mul ((-Complex.I) ^ m))
  refine hre.congr' ?_
  filter_upwards [eventually_ge_atTop m] with N hN
  simp only [Function.comp_apply, realFiniteKrylovWavefn, hN, ↓reduceDIte, Nat.lt_succ_of_le hN]

/-- Squared-modulus identity `(realInfiniteKrylovWavefn b m t)² = ‖infiniteKrylovWavefn b t m‖²`
for all `m : ℕ` and `t : ℝ`. -/
lemma realInfiniteKrylovWavefn_sq_eq_normSq (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    (m : ℕ) (t : ℝ) :
    (realInfiniteKrylovWavefn b m t) ^ 2 = ‖infiniteKrylovWavefn b t m‖ ^ 2 := by
  have ht := infiniteKrylovWavefn_tendsto_all_time b hα hγ hb_nn hb_lin t m
  have ht_shift := (ht.comp (tendsto_add_atTop_nat 1)).const_mul ((-Complex.I) ^ m)
  have him_zero : ((-Complex.I) ^ m * infiniteKrylovWavefn b t m).im = 0 := by
    have h1 := Complex.continuous_im.continuousAt.tendsto.comp ht_shift
    have h2 : Tendsto (fun N : ℕ ↦
        ((-Complex.I) ^ m *
          (if hm : m < N + 1 then jacobiWavefn (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) b t ⟨m, hm⟩ else 0)).im)
        atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with N hN
      have him := gaugedFiniteWavefn_im_zero b N m t
      simp only [gaugedFiniteWavefn, hN, ↓reduceDIte] at him
      simp only [Nat.lt_succ_of_le hN, ↓reduceDIte]
      exact him.symm
    exact tendsto_nhds_unique h1 h2
  have hnorm : ‖(-Complex.I) ^ m * infiniteKrylovWavefn b t m‖ = ‖infiniteKrylovWavefn b t m‖ := by
    rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  rw [← hnorm, Complex.sq_norm, Complex.normSq_apply, him_zero]
  unfold realInfiniteKrylovWavefn
  ring

end TimeReversalAndRealGauge

section HeadlineInfiniteChainTheorem

/-- **Theorem 1.1(a) (Complete Unconditional Infinite-Chain Theorem)**:
For ANY Lanczos sequence `b : ℕ → ℝ` with `b 0 = 0` and `0 ≤ b n ≤ α n + γ` for all `n ≥ 1`
(`α > 0`, `γ ≥ 0`), the canonically constructed real wavefunction `φ = realInfiniteKrylovWavefn b`
unconditionally satisfies:
1. **Existence, Initial Condition, Continuity, ODE & Probability Conservation (all `t : ℝ`)**:
   - `φ m 0 = if m = 0 then 1 else 0`,
   - `Continuous (φ m)`,
   - `HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t`,
   - `Summable (fun m ↦ (φ m t) ^ 2)` and `∑' m : ℕ, (φ m t) ^ 2 = 1`.
2. **Carleman `ℓ²`-Uniqueness**:
   For any `T ≥ 0`, `C ≥ 0`, and any solution `ψ : ℕ → ℝ → ℝ` to the infinite Krylov ODE with
   `ψ m 0 = if m = 0 then 1 else 0` and uniformly bounded `ℓ²`-norm on `[0, T]`, `ψ m t = φ m t`
   for all `t ∈ [0, T]` and `m : ℕ`.
3. **Exact Single-Exponential Tail & Complexity Bounds (Eqs. 1.12–1.13)**:
   For all `θ₀ > 0`, `t ≥ 0`, and `n : ℕ`:
   - `∑' m : ℕ, (φ (n + m) t) ^ 2 ≤ exp((1/2 + γ/α) θ₀) * exp(-4 tanh(θ₀/4) n exp(-2 α t))`,
   - `∑' m : ℕ, m * (φ m t) ^ 2 ≤ (exp((1/2 + γ/α) θ₀) / (4 e tanh(θ₀/4))) * exp(2 α t)`.
4. **Asymptotic Krylov Growth Rate Bound**:
   `Filter.limsup (fun t : ℝ ↦ Real.log (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2) / t) atTop ≤ 2 * α`. -/
theorem theorem_1_1a_infinite_chain_complete (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb0 : b 0 = 0)
    (hb_nn : ∀ n, 1 ≤ n → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → b n ≤ α * (n : ℝ) + γ) :
    let φ := realInfiniteKrylovWavefn b
    -- (1) Existence, initial condition, continuity, ODE, and probability conservation for all `t : ℝ`
    ((∀ m, φ m 0 = if m = 0 then 1 else 0) ∧
     (∀ m, Continuous (φ m)) ∧
     (∀ m t, HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t) ∧
     (∀ t : ℝ, Summable (fun m : ℕ ↦ (φ m t) ^ 2) ∧ ∑' m : ℕ, (φ m t) ^ 2 = 1)) ∧
    -- (2) Carleman `ℓ²`-uniqueness on `[0, T]` for all `T ≥ 0`
    (∀ (ψ : ℕ → ℝ → ℝ) (T C : ℝ), 0 ≤ T → 0 ≤ C →
      (∀ m s, HasDerivAt (ψ m) (b m * ψ (m - 1) s - b (m + 1) * ψ (m + 1) s) s) →
      (∀ m, ψ m 0 = if m = 0 then 1 else 0) →
      (∀ s ∈ Set.Icc 0 T, Summable (fun m ↦ (ψ m s) ^ 2) ∧ ∑' m, (ψ m s) ^ 2 ≤ C) →
      ∀ t ∈ Set.Icc 0 T, ∀ m : ℕ, ψ m t = φ m t) ∧
    -- (3) Exact Eqs. (1.12)–(1.13) for all `θ₀ > 0`, `t ≥ 0`, `n : ℕ`
    (∀ θ₀ : ℝ, 0 < θ₀ → ∀ t ≥ 0,
      (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
        Real.exp ((1 / 2 + γ / α) * θ₀) *
          Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
      (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2 ≤
        (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
          Real.exp (2 * α * t))) ∧
    -- (4) Asymptotic Krylov growth rate bound
    Filter.limsup (fun t : ℝ ↦ Real.log (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2) / t) Filter.atTop ≤ 2 * α := by
  intro φ
  have hb_nn_all : ∀ n, 0 ≤ b n := by
    intro n; cases n with
    | zero => rw [hb0]
    | succ k => exact hb_nn (k + 1) (Nat.succ_pos k)
  have hb_lin_all : ∀ n, b n ≤ α * (n : ℝ) + γ := by
    intro n; cases n with
    | zero => rw [hb0]; simp [hγ]
    | succ k => exact hb_lin (k + 1) (Nat.succ_pos k)
  have htendsto : ∀ m t, Tendsto (fun N ↦ realFiniteKrylovWavefn b N m t) atTop (nhds (φ m t)) :=
    realInfiniteKrylovWavefn_tendsto b hα hγ hb_nn_all hb_lin_all
  have hode_N_plain : ∀ N m, m ≤ N → ∀ t,
      HasDerivAt (realFiniteKrylovWavefn b N m)
        (b m * realFiniteKrylovWavefn b N (m - 1) t -
         b (m + 1) * realFiniteKrylovWavefn b N (m + 1) t) t := by
    intro N m hm t
    have h := realFiniteKrylovWavefn_ode b N m hm t
    convert h using 1
    have h1 : b m * realFiniteKrylovWavefn b N (m - 1) t =
        (if m = 0 then 0 else b m) * realFiniteKrylovWavefn b N (m - 1) t := by
      split_ifs with hm0
      · subst hm0; rw [hb0, zero_mul]
      · rfl
    have h2 : b (m + 1) * realFiniteKrylovWavefn b N (m + 1) t =
        (if m = N then 0 else b (m + 1)) * realFiniteKrylovWavefn b N (m + 1) t := by
      split_ifs with hmN
      · subst hmN
        have hzero : realFiniteKrylovWavefn b m (m + 1) t = 0 := by
          unfold realFiniteKrylovWavefn; rw [dif_neg (Nat.not_succ_le_self m)]
        rw [hzero, mul_zero, zero_mul]
      · rfl
    rw [h1, h2]
  have hode_all := infinite_krylov_ode_of_pointwise_limit b (realFiniteKrylovWavefn b) φ
    hode_N_plain (realFiniteKrylovWavefn_init b) (realFiniteKrylovWavefn_abs_le_one b) htendsto
  have hprob : ∀ t : ℝ, Summable (fun m : ℕ ↦ (φ m t) ^ 2) ∧ ∑' m : ℕ, (φ m t) ^ 2 = 1 := by
    intro t
    have hsq : (fun m : ℕ ↦ (φ m t) ^ 2) = fun m ↦ ‖infiniteKrylovWavefn b t m‖ ^ 2 := by
      funext m; exact realInfiniteKrylovWavefn_sq_eq_normSq b hα hγ hb_nn_all hb_lin_all m t
    rw [hsq]
    rcases le_or_gt 0 t with ht | ht
    · have hu := theorem_1_1a_infinite_unconditional b hα hγ ht (by norm_num : (0 : ℝ) < 1)
        hb_nn_all hb_lin_all
      exact ⟨hu.1, hu.2.1⟩
    · have hpos : 0 ≤ -t := by linarith
      have hu := theorem_1_1a_infinite_unconditional b hα hγ hpos (by norm_num : (0 : ℝ) < 1)
        hb_nn_all hb_lin_all
      have hsame : (fun m : ℕ ↦ ‖infiniteKrylovWavefn b t m‖ ^ 2) =
          fun m ↦ ‖infiniteKrylovWavefn b (-t) m‖ ^ 2 := by
        funext m
        rw [infiniteKrylovWavefn_neg_t b hα hγ hb_nn_all hb_lin_all t m,
          norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [hsame]
      exact ⟨hu.1, hu.2.1⟩
  have huniq : ∀ (ψ : ℕ → ℝ → ℝ) (T C : ℝ), 0 ≤ T → 0 ≤ C →
      (∀ m s, HasDerivAt (ψ m) (b m * ψ (m - 1) s - b (m + 1) * ψ (m + 1) s) s) →
      (∀ m, ψ m 0 = if m = 0 then 1 else 0) →
      (∀ s ∈ Set.Icc 0 T, Summable (fun m ↦ (ψ m s) ^ 2) ∧ ∑' m, (ψ m s) ^ 2 ≤ C) →
      ∀ t ∈ Set.Icc 0 T, ∀ m : ℕ, ψ m t = φ m t := by
    intro ψ T C hT hC hode_ψ hinit_ψ hl2_ψ
    refine infinite_krylov_ode_linear_growth_l2_unique hα.le hγ hb0 hb_nn_all hb_lin ψ φ
      hT (by linarith : 0 ≤ 2 * C + 2) hode_ψ hode_all.2.2 (fun m ↦ by rw [hinit_ψ m, hode_all.1 m]) ?_
    intro s hs
    have hdom : ∀ m : ℕ, (ψ m s - φ m s) ^ 2 ≤ 2 * (ψ m s) ^ 2 + 2 * (φ m s) ^ 2 := by
      intro m; nlinarith [sq_nonneg (ψ m s + φ m s)]
    have hsum_rhs : Summable (fun m : ℕ ↦ 2 * (ψ m s) ^ 2 + 2 * (φ m s) ^ 2) :=
      ((hl2_ψ s hs).1.mul_left 2).add ((hprob s).1.mul_left 2)
    have hsum_diff : Summable (fun m : ℕ ↦ (ψ m s - φ m s) ^ 2) :=
      Summable.of_nonneg_of_le (fun m ↦ sq_nonneg _) hdom hsum_rhs
    refine ⟨hsum_diff, ?_⟩
    calc ∑' m : ℕ, (ψ m s - φ m s) ^ 2
        ≤ ∑' m : ℕ, (2 * (ψ m s) ^ 2 + 2 * (φ m s) ^ 2) := hsum_diff.tsum_le_tsum hdom hsum_rhs
      _ = 2 * (∑' m : ℕ, (ψ m s) ^ 2) + 2 * (∑' m : ℕ, (φ m s) ^ 2) := by
          rw [Summable.tsum_add ((hl2_ψ s hs).1.mul_left 2) ((hprob s).1.mul_left 2),
            tsum_mul_left, tsum_mul_left]
      _ ≤ 2 * C + 2 * 1 := by
          rw [(hprob s).2]; linarith [(hl2_ψ s hs).2]
      _ = 2 * C + 2 := by ring
  have hfatou : ∀ θ₀ : ℝ, 0 < θ₀ →
      (∀ t ≥ 0,
        (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
          Real.exp ((1 / 2 + γ / α) * θ₀) *
            Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
        (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2 ≤
          (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
            Real.exp (2 * α * t))) ∧
      Filter.limsup (fun t : ℝ ↦ Real.log (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2) / t) Filter.atTop ≤ 2 * α := by
    intro θ₀ hθ₀
    exact theorem_1_1a_infinite_fatou_exact_single_exp b (realFiniteKrylovWavefn b) φ
      hα hγ hθ₀ hb0 hb_nn hb_lin (realFiniteKrylovWavefn_ode b)
      (realFiniteKrylovWavefn_init b) htendsto
  exact ⟨⟨hode_all.1, hode_all.2.1, hode_all.2.2, hprob⟩, huniq,
    fun θ₀ hθ₀ ↦ (hfatou θ₀ hθ₀).1, (hfatou 1 one_pos).2⟩

end HeadlineInfiniteChainTheorem

end KrylovChaos
