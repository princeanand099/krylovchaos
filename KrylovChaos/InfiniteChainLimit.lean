/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.JacobiSemigroup
import KrylovChaos.KrylovTail
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Unconditional Infinite-Chain Limit & Pointwise Convergence on ℓ²(ℕ) (Theorem 1.1(a))

Eliminates the `hlim` and `hfatou` hypotheses from infinite-chain Theorem 1.1(a) completely
from first principles on Mathlib `v4.35.0`:
1. **Complex Finite-Chain MGF Bound (`complex_finite_chain_mgf_bound`)**:
   Proves the time-dependent `charTheta α θ₀ s` MGF bound directly for the unitary
   complex Krylov wavefunction `jacobiWavefn hD b s = exp(i s T_D) e_0` when
   `0 ≤ b n ≤ α n + γ`.
2. **Finite-Truncation Difference Bound (`jacobiWavefn_trunc_diff_bound`)**:
   For `1 ≤ D ≤ M`, proves via the exact Lanczos ODE, self-adjointness of `jacobiCLM M b`,
   Cauchy–Schwarz, and `ε`-regularized square-root MVT:
   `‖jacobiWavefn hM b t - embJacobi D M hDM (jacobiWavefn hD b t)‖ ≤ t * |b D| * sup_{s∈[0,t]} |φ^{(D)}_{D-1}(s)|`.
3. **Exponential Cauchy Convergence & Existence of Infinite-Chain Wavefunction**:
   Combines (1) and (2) to prove `D ↦ (jacobiWavefn hD b t) m` is Cauchy in `ℂ`, defines
   `infiniteKrylovWavefn b t m : ℂ`, proves `infiniteKrylovWavefn_tendsto` (zero `hlim`),
   `infiniteKrylovWavefn_norm_one` (`∑' m, ‖φ_m(t)‖² = 1`), and
   `theorem_1_1a_infinite_unconditional` (zero `hlim`, zero `hfatou`).
-/

namespace KrylovChaos

section Helpers

/-- Finite-chain Krylov wavefunction `φ^{(D)}(t) = exp(i t T_D) e_0 ∈ ℂ^D`. -/
noncomputable def jacobiWavefn {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ (Fin D) :=
  jacobiUnitary D b t (EuclideanSpace.single ⟨0, hD⟩ (1 : ℂ))

private lemma jacobiCLM_apply_tridiag (D : ℕ) (b : ℕ → ℝ)
    (v : EuclideanSpace ℂ (Fin D)) (n : Fin D) :
    (jacobiCLM D b v) n =
    (if h0 : 0 < n.1 then (b n.1 : ℂ) * v ⟨n.1 - 1, by omega⟩ else 0) +
    (if h1 : n.1 + 1 < D then (b (n.1 + 1) : ℂ) * v ⟨n.1 + 1, h1⟩ else 0) := by
  change ∑ j : Fin D, (jacobiMat D b n j : ℂ) * v j = _
  have hsplit : ∀ j : Fin D, (jacobiMat D b n j : ℂ) * v j =
      (if j.1 + 1 = n.1 then (b n.1 : ℂ) * v j else 0) +
      (if n.1 + 1 = j.1 then (b (n.1 + 1) : ℂ) * v j else 0) := by
    intro j
    unfold jacobiMat
    by_cases h1 : j.1 + 1 = n.1
    · have h2 : ¬ (n.1 + 1 = j.1) := by omega
      simp [h1, h2]
    · by_cases h2 : n.1 + 1 = j.1
      · simp [h1, h2]
      · simp [h1, h2]
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · by_cases h0 : 0 < n.1
    · rw [dif_pos h0]
      have hsub : ∀ j : Fin D,
          (if j.1 + 1 = n.1 then (b n.1 : ℂ) * v j else 0) =
          if j = ⟨n.1 - 1, by omega⟩ then (b n.1 : ℂ) * v j else 0 := by
        intro j
        by_cases hj : j = ⟨n.1 - 1, by omega⟩
        · subst hj; rw [if_pos (by simp; omega), if_pos rfl]
        · have hne : j.1 + 1 ≠ n.1 := by
            intro heq; apply hj; ext; dsimp; omega
          rw [if_neg hne, if_neg hj]
      simp_rw [hsub]
      simp
    · rw [dif_neg h0]
      apply Finset.sum_eq_zero; intro j _
      rw [if_neg (by omega)]
  · by_cases h1 : n.1 + 1 < D
    · rw [dif_pos h1]
      have hsub : ∀ j : Fin D,
          (if n.1 + 1 = j.1 then (b (n.1 + 1) : ℂ) * v j else 0) =
          if j = ⟨n.1 + 1, h1⟩ then (b (n.1 + 1) : ℂ) * v j else 0 := by
        intro j
        by_cases hj : j = ⟨n.1 + 1, h1⟩
        · subst hj; rw [if_pos (by simp), if_pos rfl]
        · have hne : n.1 + 1 ≠ j.1 := by
            intro heq; apply hj; ext; dsimp; omega
          rw [if_neg hne, if_neg hj]
      simp_rw [hsub]
      simp
    · rw [dif_neg h1]
      apply Finset.sum_eq_zero; intro j _
      rw [if_neg (by omega)]

private lemma single_apply_eq {D : ℕ} (i j : Fin D) (c : ℂ) :
    (EuclideanSpace.single i c : EuclideanSpace ℂ (Fin D)) j = if j = i then c else 0 := by
  simp [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]

private lemma norm_single_one {D : ℕ} (i : Fin D) :
    ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin D))‖ = 1 := by
  have hsq : ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin D))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ∀ j : Fin D, ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin D)) j‖ ^ 2 =
        if j = i then (1 : ℝ) else 0 := by
      intro j; rw [single_apply_eq]; split_ifs <;> simp
    simp_rw [this]
    simp
  have hnn : 0 ≤ ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin D))‖ := norm_nonneg _
  nlinarith

private lemma real_inner_eq_re_complex {D : ℕ} (u v : EuclideanSpace ℂ (Fin D)) :
    @inner ℝ _ _ u v = (inner ℂ u v).re := by
  simp [PiLp.inner_apply, Complex.inner, RCLike.inner_apply]

end Helpers

section ComplexFiniteMGF

private lemma coord_hasDerivAt_wavefn {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) (n : Fin D) :
    HasDerivAt (fun s : ℝ ↦ jacobiWavefn hD b s n)
      (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b t)) n) t := by
  have hode := jacobiWavefn_ode hD b t
  let L : EuclideanSpace ℂ (Fin D) →L[ℝ] ℂ :=
    (EuclideanSpace.proj n : EuclideanSpace ℂ (Fin D) →L[ℂ] ℂ).restrictScalars ℝ
  exact L.hasDerivAt.comp t hode

private lemma coord_normSq_hasDerivAt {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) (t : ℝ) (n : Fin D) :
    HasDerivAt (fun s : ℝ ↦ ‖jacobiWavefn hD b s n‖ ^ 2)
      (2 * ((jacobiWavefn hD b t n).re * (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b t)) n).re +
            (jacobiWavefn hD b t n).im * (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b t)) n).im))
      t := by
  have hz := coord_hasDerivAt_wavefn hD b t n
  have hre : HasDerivAt (fun s : ℝ ↦ (jacobiWavefn hD b s n).re)
      (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b t) n).re) t :=
    (Complex.reCLM.hasDerivAt).comp t hz
  have him : HasDerivAt (fun s : ℝ ↦ (jacobiWavefn hD b s n).im)
      (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b t) n).im) t :=
    (Complex.imCLM.hasDerivAt).comp t hz
  have hnorm : (fun s : ℝ ↦ ‖jacobiWavefn hD b s n‖ ^ 2) =
      (fun s : ℝ ↦ (jacobiWavefn hD b s n).re ^ 2 + (jacobiWavefn hD b s n).im ^ 2) := by
    ext s; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hnorm]
  have h1 := hre.fun_pow 2
  have h2 := him.fun_pow 2
  convert h1.add h2 using 1
  ring

private lemma jacobi_coord_normSq_deriv_formula (D : ℕ) (b : ℕ → ℝ)
    (v : EuclideanSpace ℂ (Fin D)) (n : Fin D) :
    2 * ((v n).re * (((Complex.I • jacobiCLM D b) v) n).re +
         (v n).im * (((Complex.I • jacobiCLM D b) v) n).im) =
    (if h0 : 0 < n.1 then -2 * b n.1 * (star (v n) * v ⟨n.1 - 1, by omega⟩).im else 0) +
    (if h1 : n.1 + 1 < D then -2 * b (n.1 + 1) * (star (v n) * v ⟨n.1 + 1, h1⟩).im else 0) := by
  have hclm : ((Complex.I • jacobiCLM D b) v) n =
      Complex.I *
        ((if h0 : 0 < n.1 then (b n.1 : ℂ) * v ⟨n.1 - 1, by omega⟩ else 0) +
         (if h1 : n.1 + 1 < D then (b (n.1 + 1) : ℂ) * v ⟨n.1 + 1, h1⟩ else 0)) := by
    rw [ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, jacobiCLM_apply_tridiag]
  rw [hclm]
  have hre_im : ∀ (z w : ℂ),
      2 * (z.re * (Complex.I * w).re + z.im * (Complex.I * w).im) = -2 * (star z * w).im := by
    intro z w
    simp [Complex.star_def]
    ring
  rw [hre_im, mul_add, Complex.add_im]
  have hterm : ∀ (r : ℝ) (u : ℂ),
      -2 * (star (v n) * ((r : ℂ) * u)).im = -2 * r * (star (v n) * u).im := by
    intro r u
    have : star (v n) * ((r : ℂ) * u) = (r : ℂ) * (star (v n) * u) := by ring
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  split_ifs with h0 h1 <;> simp [hterm] <;> ring

/-- **Complex Finite-Chain MGF Bound**:
For any `0 < D`, `α > 0`, `γ ≥ 0`, `θ₀ > 0`, and Lanczos sequence `0 ≤ b n ≤ α n + γ`,
`∑_{n=0}^{D-1} exp(charTheta α θ₀ s * n) * ‖φ^{(D)}_n(s)‖² ≤ exp((1/2 + γ/α) * θ₀)`. -/
theorem complex_finite_chain_mgf_bound {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) {α γ θ₀ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∑ n : Fin D, Real.exp (charTheta α θ₀ s * (n.1 : ℝ)) * ‖jacobiWavefn hD b s n‖ ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) := by
  let G : ℝ → ℝ := fun u ↦
    ∑ n : Fin D, Real.exp (charTheta α θ₀ u * (n.1 : ℝ)) * ‖jacobiWavefn hD b u n‖ ^ 2
  let G' : ℝ → ℝ := fun u ↦
    ∑ n : Fin D,
      ((-4 * α * Real.sinh (charTheta α θ₀ u / 2) * (n.1 : ℝ)) *
          Real.exp (charTheta α θ₀ u * (n.1 : ℝ)) * ‖jacobiWavefn hD b u n‖ ^ 2 +
       Real.exp (charTheta α θ₀ u * (n.1 : ℝ)) *
         (2 * ((jacobiWavefn hD b u n).re * (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b u)) n).re +
               (jacobiWavefn hD b u n).im * (((Complex.I • jacobiCLM D b) (jacobiWavefn hD b u)) n).im)))
  have hderiv : ∀ u ≥ 0, HasDerivAt G (G' u) u := by
    intro u hu
    apply HasDerivAt.sum
    intro n _
    have hθd := hasDerivAt_charTheta hα hθ₀ hu
    have hexp : HasDerivAt (fun r ↦ Real.exp (charTheta α θ₀ r * (n.1 : ℝ)))
        ((-4 * α * Real.sinh (charTheta α θ₀ u / 2) * (n.1 : ℝ)) *
          Real.exp (charTheta α θ₀ u * (n.1 : ℝ))) u := by
      simpa [mul_comm, mul_assoc] using (hθd.mul_const (n.1 : ℝ)).exp
    have hsq := coord_normSq_hasDerivAt hD b u n
    convert hexp.fun_mul hsq using 1
    ring
  have hdiff_ineq : ∀ u ≥ 0, G' u ≤ 2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ u / 2) * G u := by
    intro u hu
    simp only [G']
    set θ := charTheta α θ₀ u with hθ_def
    have hθpos : 0 < θ := charTheta_pos hα hθ₀ hu
    have hsinh_pos : 0 < Real.sinh (θ / 2) := sinh_pos_of_pos (by linarith)
    rw [Finset.sum_add_distrib]
    have htime_eq :
        ∑ n : Fin D,
          (-4 * α * Real.sinh (θ / 2) * (n.1 : ℝ)) *
            Real.exp (θ * (n.1 : ℝ)) * ‖jacobiWavefn hD b u n‖ ^ 2 =
        -4 * α * Real.sinh (θ / 2) *
          ∑ n : Fin D, (n.1 : ℝ) * Real.exp (θ * (n.1 : ℝ)) * ‖jacobiWavefn hD b u n‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [htime_eq]
    obtain ⟨D', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
    have h2_eq_range :
        ∑ n : Fin (D' + 1),
          Real.exp (θ * (n.1 : ℝ)) *
            (2 * ((jacobiWavefn hD b u n).re * (((Complex.I • jacobiCLM (D' + 1) b) (jacobiWavefn hD b u)) n).re +
                  (jacobiWavefn hD b u n).im * (((Complex.I • jacobiCLM (D' + 1) b) (jacobiWavefn hD b u)) n).im)) =
        ∑ k ∈ Finset.range D',
          2 * b (k + 1) * (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
            (-(star (jacobiWavefn hD b u ⟨k + 1, by omega⟩) * jacobiWavefn hD b u ⟨k, by omega⟩).im) := by
      have hsub : ∀ n : Fin (D' + 1),
          2 * ((jacobiWavefn hD b u n).re * (((Complex.I • jacobiCLM (D' + 1) b) (jacobiWavefn hD b u)) n).re +
               (jacobiWavefn hD b u n).im * (((Complex.I • jacobiCLM (D' + 1) b) (jacobiWavefn hD b u)) n).im) =
          (if h0 : 0 < n.1 then
            -2 * b n.1 * (star (jacobiWavefn hD b u n) * jacobiWavefn hD b u ⟨n.1 - 1, by omega⟩).im
           else 0) +
          (if h1 : n.1 + 1 < D' + 1 then
            -2 * b (n.1 + 1) * (star (jacobiWavefn hD b u n) * jacobiWavefn hD b u ⟨n.1 + 1, h1⟩).im
           else 0) :=
        fun n ↦ jacobi_coord_normSq_deriv_formula (D' + 1) b (jacobiWavefn hD b u) n
      simp_rw [hsub, mul_add, Finset.sum_add_distrib]
      rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
      have hpart1 :
          ∑ n ∈ Finset.range (D' + 1),
            (if hn : n < D' + 1 then
              Real.exp (θ * (n : ℝ)) *
                if h0 : 0 < n then
                  -2 * b n * (star (jacobiWavefn hD b u ⟨n, hn⟩) *
                    jacobiWavefn hD b u ⟨n - 1, by omega⟩).im
                else 0
             else 0) =
          ∑ k ∈ Finset.range D',
            Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
              (-2 * b (k + 1) * (star (jacobiWavefn hD b u ⟨k + 1, by omega⟩) *
                jacobiWavefn hD b u ⟨k, by omega⟩).im) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.not_lt_zero, ↓reduceDIte, zero_lt_one, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < D' := Finset.mem_range.mp hk
        rw [dif_pos (by omega), dif_pos (Nat.succ_pos k)]
        rfl
      have hpart2 :
          ∑ n ∈ Finset.range (D' + 1),
            (if hn : n < D' + 1 then
              Real.exp (θ * (n : ℝ)) *
                if h1 : n + 1 < D' + 1 then
                  -2 * b (n + 1) * (star (jacobiWavefn hD b u ⟨n, hn⟩) *
                    jacobiWavefn hD b u ⟨n + 1, h1⟩).im
                else 0
             else 0) =
          ∑ k ∈ Finset.range D',
            Real.exp (θ * (k : ℝ)) *
              (2 * b (k + 1) * (star (jacobiWavefn hD b u ⟨k + 1, by omega⟩) *
                jacobiWavefn hD b u ⟨k, by omega⟩).im) := by
        rw [Finset.sum_range_succ]
        simp only [lt_self_iff_false, ↓reduceDIte, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < D' := Finset.mem_range.mp hk
        rw [dif_pos (by omega), dif_pos (by omega)]
        have him_conj : (star (jacobiWavefn hD b u ⟨k, by omega⟩) *
            jacobiWavefn hD b u ⟨k + 1, by omega⟩).im =
            -(star (jacobiWavefn hD b u ⟨k + 1, by omega⟩) *
              jacobiWavefn hD b u ⟨k, by omega⟩).im := by
          simp [Complex.star_def]; ring
        rw [him_conj]; ring
      rw [hpart1, hpart2, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [h2_eq_range]
    have hterm_le : ∀ k ∈ Finset.range D',
        2 * b (k + 1) * (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
          (-(star (jacobiWavefn hD b u ⟨k + 1, by omega⟩) *
            jacobiWavefn hD b u ⟨k, by omega⟩).im) ≤
        2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
          (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 +
           Real.exp (θ * (k : ℝ)) * ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2) := by
      intro k hk
      have hkD : k + 1 < D' + 1 := by have := Finset.mem_range.mp hk; omega
      have hdiff_exp :
          Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ)) =
          2 * Real.sinh (θ / 2) * Real.exp (θ * ((k : ℝ) + 1 / 2)) := by
        rw [Real.sinh_eq]
        have h1 : Real.exp (θ / 2) * Real.exp (θ * ((k : ℝ) + 1 / 2)) =
            Real.exp (θ * ((k + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring
        have h2 : Real.exp (-(θ / 2)) * Real.exp (θ * ((k : ℝ) + 1 / 2)) =
            Real.exp (θ * (k : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
        linarith
      have hprod_exp :
          Real.exp (θ * ((k : ℝ) + 1 / 2)) =
          Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) * Real.exp (θ * (k : ℝ) / 2) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      set z1 := jacobiWavefn hD b u ⟨k + 1, hkD⟩
      set z0 := jacobiWavefn hD b u ⟨k, by omega⟩
      have him_abs : -(star z1 * z0).im ≤ ‖z1‖ * ‖z0‖ := by
        have h1 : -(star z1 * z0).im ≤ ‖star z1 * z0‖ := by
          calc -(star z1 * z0).im ≤ |-(star z1 * z0).im| := le_abs_self _
            _ = |(star z1 * z0).im| := abs_neg _
            _ ≤ ‖star z1 * z0‖ := Complex.abs_im_le_norm _
        have h2 : ‖star z1 * z0‖ = ‖z1‖ * ‖z0‖ := by
          rw [norm_mul, Complex.norm_conj]
        linarith
      have hexp_diff_nn : 0 ≤ Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ)) := by
        have : θ * (k : ℝ) ≤ θ * ((k + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) hθpos.le
        linarith [Real.exp_le_exp.mpr this]
      have hstep1 :
          2 * b (k + 1) * (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
            (-(star z1 * z0).im) ≤
          2 * (α * ((k + 1 : ℕ) : ℝ) + γ) *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
            (‖z1‖ * ‖z0‖) := by
        have hb1 : 0 ≤ 2 * b (k + 1) := by linarith [hb_nn (k + 1)]
        have h1 := mul_le_mul_of_nonneg_left him_abs (mul_nonneg hb1 hexp_diff_nn)
        have h2 : 2 * b (k + 1) ≤ 2 * (α * ((k + 1 : ℕ) : ℝ) + γ) := by linarith [hb_lin (k + 1)]
        have h3 : 0 ≤ (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
            (‖z1‖ * ‖z0‖) := by positivity
        nlinarith
      have hamgm :
          2 * Real.exp (θ * ((k : ℝ) + 1 / 2)) * (‖z1‖ * ‖z0‖) ≤
          Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * ‖z1‖ ^ 2 +
          Real.exp (θ * (k : ℝ)) * ‖z0‖ ^ 2 := by
        rw [hprod_exp]
        set U := Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) * ‖z1‖
        set V := Real.exp (θ * (k : ℝ) / 2) * ‖z0‖
        have hU2 : U ^ 2 = Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * ‖z1‖ ^ 2 := by
          dsimp [U]; rw [mul_pow, ← Real.exp_add]; congr 1; ring_nf
        have hV2 : V ^ 2 = Real.exp (θ * (k : ℝ)) * ‖z0‖ ^ 2 := by
          dsimp [V]; rw [mul_pow, ← Real.exp_add]; congr 1; ring_nf
        have hsq : 0 ≤ (U - V) ^ 2 := sq_nonneg _
        have hUV : 2 * U * V ≤ U ^ 2 + V ^ 2 := by linarith
        rw [hU2, hV2] at hUV
        linarith [show 2 * (Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) * Real.exp (θ * (k : ℝ) / 2)) *
            (‖z1‖ * ‖z0‖) = 2 * U * V by dsimp [U, V]; ring]
      have hstep2 :
          2 * (α * ((k + 1 : ℕ) : ℝ) + γ) *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) *
            (‖z1‖ * ‖z0‖) ≤
          2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * ‖z1‖ ^ 2 +
             Real.exp (θ * (k : ℝ)) * ‖z0‖ ^ 2) := by
        rw [hdiff_exp]
        have hcoeff : 0 ≤ 2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) := by positivity
        calc 2 * (α * ((k + 1 : ℕ) : ℝ) + γ) *
              (2 * Real.sinh (θ / 2) * Real.exp (θ * ((k : ℝ) + 1 / 2))) * (‖z1‖ * ‖z0‖)
            = (2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ)) *
                (2 * Real.exp (θ * ((k : ℝ) + 1 / 2)) * (‖z1‖ * ‖z0‖)) := by ring
          _ ≤ (2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ)) *
                (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * ‖z1‖ ^ 2 +
                 Real.exp (θ * (k : ℝ)) * ‖z0‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hamgm hcoeff
      exact le_trans hstep1 hstep2
    have hsum_le := Finset.sum_le_sum hterm_le
    have hGs_eq : G u = ∑ n : Fin (D' + 1), Real.exp (θ * (n.1 : ℝ)) * ‖jacobiWavefn hD b u n‖ ^ 2 := by
      simp only [G, ← hθ_def]
    have hterm_re : ∀ k ∈ Finset.range D',
        2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
          (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 +
           Real.exp (θ * (k : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2) =
        (2 * α * Real.sinh (θ / 2) * ((k + 1 : ℕ) : ℝ) *
          Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
          ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 +
         2 * α * Real.sinh (θ / 2) * (k : ℝ) *
          Real.exp (θ * (k : ℝ)) *
          ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2) +
        (2 * γ * Real.sinh (θ / 2) *
          Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
          ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 +
         2 * (α + γ) * Real.sinh (θ / 2) *
          Real.exp (θ * (k : ℝ)) *
          ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2) := by
      intro k _; push_cast; ring
    have hGu_range :
        G u = ∑ k ∈ Finset.range (D' + 1),
          (if hk : k < D' + 1 then
            Real.exp (θ * (k : ℝ)) * ‖jacobiWavefn hD b u ⟨k, hk⟩‖ ^ 2 else 0) := by
      rw [hGs_eq, Fin.sum_univ_eq_sum_range]
    have hWu_range :
        ∑ n : Fin (D' + 1), (n.1 : ℝ) * Real.exp (θ * (n.1 : ℝ)) *
            ‖jacobiWavefn hD b u n‖ ^ 2 =
        ∑ k ∈ Finset.range (D' + 1),
          (if hk : k < D' + 1 then
            (k : ℝ) * Real.exp (θ * (k : ℝ)) * ‖jacobiWavefn hD b u ⟨k, hk⟩‖ ^ 2
           else 0) := by
      rw [Fin.sum_univ_eq_sum_range]
    have ha1 :
        ∑ k ∈ Finset.range D',
          2 * α * Real.sinh (θ / 2) * ((k + 1 : ℕ) : ℝ) *
            Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 ≤
        2 * α * Real.sinh (θ / 2) *
          ∑ n : Fin (D' + 1), (n.1 : ℝ) * Real.exp (θ * (n.1 : ℝ)) *
            ‖jacobiWavefn hD b u n‖ ^ 2 := by
      rw [hWu_range, Finset.sum_range_succ', Finset.mul_sum]
      simp only [Nat.cast_zero, zero_mul, dite_eq_ite, ite_self, add_zero]
      apply Finset.sum_le_sum; intro k hk
      have hk' : k < D' := Finset.mem_range.mp hk
      rw [if_pos (by omega)]; ring_nf; exact le_refl _
    have ha2 :
        ∑ k ∈ Finset.range D',
          2 * α * Real.sinh (θ / 2) * (k : ℝ) *
            Real.exp (θ * (k : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2 ≤
        2 * α * Real.sinh (θ / 2) *
          ∑ n : Fin (D' + 1), (n.1 : ℝ) * Real.exp (θ * (n.1 : ℝ)) *
            ‖jacobiWavefn hD b u n‖ ^ 2 := by
      rw [hWu_range, Finset.sum_range_succ, Finset.mul_sum]
      have hlast : 0 ≤ (if h : D' < D' + 1 then
          (D' : ℝ) * Real.exp (θ * (D' : ℝ)) * ‖jacobiWavefn hD b u ⟨D', h⟩‖ ^ 2
        else 0) := by split_ifs <;> positivity
      have hle1 : ∑ k ∈ Finset.range D',
          2 * α * Real.sinh (θ / 2) * (k : ℝ) *
            Real.exp (θ * (k : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2 =
          ∑ k ∈ Finset.range D',
            2 * α * Real.sinh (θ / 2) *
              (if hk : k < D' + 1 then
                (k : ℝ) * Real.exp (θ * (k : ℝ)) *
                  ‖jacobiWavefn hD b u ⟨k, hk⟩‖ ^ 2 else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        have hk' : k < D' := Finset.mem_range.mp hk
        rw [if_pos (by omega)]; ring
      rw [mul_add, hle1]
      have : 0 ≤ 2 * α * Real.sinh (θ / 2) * (if h : D' < D' + 1 then
          (D' : ℝ) * Real.exp (θ * (D' : ℝ)) * ‖jacobiWavefn hD b u ⟨D', h⟩‖ ^ 2 else 0) := by
        apply mul_nonneg (by positivity) hlast
      linarith
    have hg1 :
        ∑ k ∈ Finset.range D',
          2 * γ * Real.sinh (θ / 2) *
            Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 ≤
        2 * γ * Real.sinh (θ / 2) * G u := by
      rw [hGu_range, Finset.sum_range_succ', Finset.mul_sum]
      have h0nn : 0 ≤ 2 * γ * Real.sinh (θ / 2) *
          (if h : 0 < D' + 1 then
            Real.exp (θ * (0 : ℝ)) * ‖jacobiWavefn hD b u ⟨0, h⟩‖ ^ 2 else 0) := by
        split_ifs <;> positivity
      have hsum_eq :
          ∑ k ∈ Finset.range D',
            2 * γ * Real.sinh (θ / 2) *
              Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
              ‖jacobiWavefn hD b u ⟨k + 1, by omega⟩‖ ^ 2 =
          ∑ k ∈ Finset.range D',
            2 * γ * Real.sinh (θ / 2) *
              (if hk : k + 1 < D' + 1 then
                Real.exp (θ * ((k + 1 : ℕ) : ℝ)) *
                  ‖jacobiWavefn hD b u ⟨k + 1, hk⟩‖ ^ 2 else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        have hk' : k < D' := Finset.mem_range.mp hk
        rw [if_pos (by omega)]; ring
      rw [mul_add, hsum_eq]; linarith
    have hg2 :
        ∑ k ∈ Finset.range D',
          2 * (α + γ) * Real.sinh (θ / 2) *
            Real.exp (θ * (k : ℝ)) *
            ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2 ≤
        2 * (α + γ) * Real.sinh (θ / 2) * G u := by
      rw [hGu_range, Finset.sum_range_succ, Finset.mul_sum]
      have hlnn : 0 ≤ 2 * (α + γ) * Real.sinh (θ / 2) *
          (if h : D' < D' + 1 then
            Real.exp (θ * (D' : ℝ)) * ‖jacobiWavefn hD b u ⟨D', h⟩‖ ^ 2 else 0) := by
        split_ifs <;> positivity
      have hsum_eq :
          ∑ k ∈ Finset.range D',
            2 * (α + γ) * Real.sinh (θ / 2) *
              Real.exp (θ * (k : ℝ)) *
              ‖jacobiWavefn hD b u ⟨k, by omega⟩‖ ^ 2 =
          ∑ k ∈ Finset.range D',
            2 * (α + γ) * Real.sinh (θ / 2) *
              (if hk : k < D' + 1 then
                Real.exp (θ * (k : ℝ)) *
                  ‖jacobiWavefn hD b u ⟨k, hk⟩‖ ^ 2 else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        have hk' : k < D' := Finset.mem_range.mp hk
        rw [if_pos (by omega)]; ring
      rw [mul_add, hsum_eq]; linarith
    rw [Finset.sum_congr rfl hterm_re, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at hsum_le
    linarith
  set c : ℝ := 1 / 2 + γ / α
  let H : ℝ → ℝ := fun u ↦ G u * Real.exp (c * charTheta α θ₀ u)
  have hH_deriv : ∀ u ≥ 0, ∃ H' ≤ 0, HasDerivAt H H' u := by
    intro u hu
    have hGu := hderiv u hu
    have hθu := hasDerivAt_charTheta hα hθ₀ hu
    have hexpu : HasDerivAt (fun r ↦ Real.exp (c * charTheta α θ₀ r))
        ((c * (-4 * α * Real.sinh (charTheta α θ₀ u / 2))) *
          Real.exp (c * charTheta α θ₀ u)) u :=
      (hθu.const_mul c).exp
    refine ⟨G' u * Real.exp (c * charTheta α θ₀ u) +
        G u * (c * (-4 * α * Real.sinh (charTheta α θ₀ u / 2)) *
          Real.exp (c * charTheta α θ₀ u)), ?_, hGu.mul hexpu⟩
    have hc_eq : c * (-4 * α) = -2 * (α + 2 * γ) := by
      dsimp [c]; field_simp [hα.ne']; ring
    have hineq := hdiff_ineq u hu
    have hexp_pos : 0 < Real.exp (c * charTheta α θ₀ u) := Real.exp_pos _
    have hcalc : G' u * Real.exp (c * charTheta α θ₀ u) +
        G u * (c * (-4 * α * Real.sinh (charTheta α θ₀ u / 2)) *
          Real.exp (c * charTheta α θ₀ u)) =
        (G' u - 2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ u / 2) * G u) *
          Real.exp (c * charTheta α θ₀ u) := by
      have : c * (-4 * α * Real.sinh (charTheta α θ₀ u / 2)) =
          -2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ u / 2) := by
        calc c * (-4 * α * Real.sinh (charTheta α θ₀ u / 2))
            = (c * (-4 * α)) * Real.sinh (charTheta α θ₀ u / 2) := by ring
          _ = -2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ u / 2) := by rw [hc_eq]
      rw [this]; ring
    rw [hcalc]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hineq) hexp_pos.le
  have hHs_le : H s ≤ H 0 := by
    by_cases hs0 : s = 0
    · rw [hs0]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hcont : ContinuousOn H (Set.Icc 0 s) := fun u hu ↦
        (hH_deriv u hu.1).choose_spec.2.continuousAt.continuousWithinAt
      have hdiff_on : DifferentiableOn ℝ H (Set.Ioo 0 s) := fun u hu ↦
        (hH_deriv u hu.1.le).choose_spec.2.differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope H hs_pos hcont hdiff_on
      have hle0 : deriv H ξ ≤ 0 := by
        obtain ⟨H', hH'0, hHd⟩ := hH_deriv ξ hξ.1.le
        rw [hHd.deriv]; exact hH'0
      rw [hslope, sub_zero, div_nonpos_iff] at hle0
      rcases hle0 with ⟨hnum, _⟩ | ⟨_, hden⟩
      · linarith
      · linarith
  have hH0 : H 0 = G 0 * Real.exp (c * θ₀) := by
    dsimp [H]; rw [charTheta_zero hθ₀]
  have hG0 : G 0 ≤ 1 := by
    dsimp [G]
    rw [charTheta_zero hθ₀]
    calc ∑ n : Fin D, Real.exp (θ₀ * (n.1 : ℝ)) * ‖jacobiWavefn hD b 0 n‖ ^ 2
        = ∑ n : Fin D, if n = ⟨0, hD⟩ then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl; intro n _
            have h0 : jacobiWavefn hD b 0 n =
                (EuclideanSpace.single ⟨0, hD⟩ (1 : ℂ) : EuclideanSpace ℂ (Fin D)) n := by
              unfold jacobiWavefn; rw [jacobiUnitary_zero]; simp
            rw [h0, single_apply_eq]
            by_cases hn : n = ⟨0, hD⟩
            · subst hn; simp
            · simp [hn]
      _ = 1 := by simp
  have hH0_le : H 0 ≤ Real.exp (c * θ₀) := by
    rw [hH0]; exact mul_le_of_le_one_left (Real.exp_pos _).le hG0
  have hθs_pos : 0 < charTheta α θ₀ s := charTheta_pos hα hθ₀ hs
  have hc_nn : 0 ≤ c := by dsimp [c]; positivity
  have h1_le_exp : 1 ≤ Real.exp (c * charTheta α θ₀ s) :=
    Real.one_le_exp (mul_nonneg hc_nn hθs_pos.le)
  have hG_nn : 0 ≤ G s :=
    Finset.sum_nonneg fun n _ ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  calc G s = G s * 1 := (mul_one _).symm
    _ ≤ G s * Real.exp (c * charTheta α θ₀ s) := mul_le_mul_of_nonneg_left h1_le_exp hG_nn
    _ = H s := rfl
    _ ≤ H 0 := hHs_le
    _ ≤ Real.exp (c * θ₀) := hH0_le

end ComplexFiniteMGF

section FiniteTruncationCauchy

/-- Zero-padding embedding `EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin M)` for `D ≤ M`. -/
noncomputable def embJacobi (D M : ℕ) (hDM : D ≤ M) :
    EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin M) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ WithLp.toLp 2 (fun k : Fin M ↦ if hk : k.1 < D then v ⟨k.1, hk⟩ else 0)
      map_add' := fun u v ↦ by
        ext k
        simp only [PiLp.add_apply, WithLp.ofLp_toLp]
        split_ifs <;> simp
      map_smul' := fun c v ↦ by
        ext k
        simp only [PiLp.smul_apply, WithLp.ofLp_toLp, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }

lemma embJacobi_apply (D M : ℕ) (hDM : D ≤ M) (v : EuclideanSpace ℂ (Fin D)) (k : Fin M) :
    embJacobi D M hDM v k = if hk : k.1 < D then v ⟨k.1, hk⟩ else 0 := rfl

lemma embJacobi_single_zero {D M : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    embJacobi D M hDM (EuclideanSpace.single ⟨0, hD⟩ (1 : ℂ)) =
      EuclideanSpace.single ⟨0, lt_of_lt_of_le hD hDM⟩ (1 : ℂ) := by
  ext k
  rw [embJacobi_apply, single_apply_eq]
  by_cases hk : k.1 < D
  · rw [dif_pos hk, single_apply_eq]
    by_cases hk0 : k.1 = 0
    · have h1 : (⟨k.1, hk⟩ : Fin D) = ⟨0, hD⟩ := Fin.ext hk0
      have h2 : k = ⟨0, lt_of_lt_of_le hD hDM⟩ := Fin.ext hk0
      rw [if_pos h1, if_pos h2]
    · have h1 : (⟨k.1, hk⟩ : Fin D) ≠ ⟨0, hD⟩ := fun heq ↦ hk0 (congrArg Fin.val heq)
      have h2 : k ≠ ⟨0, lt_of_lt_of_le hD hDM⟩ := fun heq ↦ hk0 (congrArg Fin.val heq)
      rw [if_neg h1, if_neg h2]
  · rw [dif_neg hk]
    have hkne : k ≠ ⟨0, lt_of_lt_of_le hD hDM⟩ := by
      intro heq; rw [heq] at hk; exact hk hD
    rw [if_neg hkne]

/-- Exact commutator defect `(T_M ∘ emb - emb ∘ T_D) v` is supported on the single site `D`. -/
lemma jacobiCLM_emb_defect {D M : ℕ} (b : ℕ → ℝ) (hD : 0 < D) (hDM : D ≤ M)
    (v : EuclideanSpace ℂ (Fin D)) :
    jacobiCLM M b (embJacobi D M hDM v) - embJacobi D M hDM (jacobiCLM D b v) =
    if hlt : D < M then
      ((b D : ℂ) * v ⟨D - 1, by omega⟩) • EuclideanSpace.single ⟨D, hlt⟩ (1 : ℂ)
    else 0 := by
  ext k
  rw [PiLp.sub_apply, jacobiCLM_apply_tridiag, embJacobi_apply]
  by_cases hlt : D < M
  · rw [dif_pos hlt, PiLp.smul_apply, smul_eq_mul, single_apply_eq]
    by_cases hkD : k.1 < D
    · rw [dif_pos hkD, jacobiCLM_apply_tridiag]
      have hkne : k ≠ ⟨D, hlt⟩ := fun heq ↦ by rw [heq] at hkD; exact lt_irrefl D hkD
      rw [if_neg hkne, mul_zero]
      have hleft :
          (if h0 : 0 < k.1 then (b k.1 : ℂ) * embJacobi D M hDM v ⟨k.1 - 1, by omega⟩ else 0) =
          (if h0 : 0 < k.1 then (b k.1 : ℂ) * v ⟨k.1 - 1, by omega⟩ else 0) := by
        split_ifs with h0
        · rw [embJacobi_apply, dif_pos (by omega)]
        · rfl
      have hright :
          (if h1 : k.1 + 1 < M then (b (k.1 + 1) : ℂ) * embJacobi D M hDM v ⟨k.1 + 1, h1⟩ else 0) =
          (if h1 : k.1 + 1 < D then (b (k.1 + 1) : ℂ) * v ⟨k.1 + 1, h1⟩ else 0) := by
        by_cases hk1 : k.1 + 1 < D
        · rw [dif_pos (by omega), dif_pos hk1, embJacobi_apply, dif_pos hk1]
        · rw [dif_pos (by omega), dif_neg hk1, embJacobi_apply, dif_neg hk1, mul_zero]
      rw [hleft, hright, sub_self]
    · rw [dif_neg hkD, sub_zero]
      by_cases hkeq : k.1 = D
      · have hkeq' : k = ⟨D, hlt⟩ := Fin.ext hkeq
        rw [if_pos hkeq', mul_one]
        have hleft :
            (if h0 : 0 < k.1 then (b k.1 : ℂ) * embJacobi D M hDM v ⟨k.1 - 1, by omega⟩ else 0) =
            (b D : ℂ) * v ⟨D - 1, by omega⟩ := by
          rw [dif_pos (by omega), embJacobi_apply, dif_pos (by omega)]
          simp [hkeq]
        have hright :
            (if h1 : k.1 + 1 < M then (b (k.1 + 1) : ℂ) * embJacobi D M hDM v ⟨k.1 + 1, h1⟩ else 0) = 0 := by
          split_ifs with h1
          · rw [embJacobi_apply, dif_neg (by omega), mul_zero]
          · rfl
        rw [hleft, hright, add_zero]
      · have hkne : k ≠ ⟨D, hlt⟩ := fun heq ↦ hkeq (congrArg Fin.val heq)
        rw [if_neg hkne, mul_zero]
        have hleft :
            (if h0 : 0 < k.1 then (b k.1 : ℂ) * embJacobi D M hDM v ⟨k.1 - 1, by omega⟩ else 0) = 0 := by
          split_ifs with h0
          · rw [embJacobi_apply, dif_neg (by omega), mul_zero]
          · rfl
        have hright :
            (if h1 : k.1 + 1 < M then (b (k.1 + 1) : ℂ) * embJacobi D M hDM v ⟨k.1 + 1, h1⟩ else 0) = 0 := by
          split_ifs with h1
          · rw [embJacobi_apply, dif_neg (by omega), mul_zero]
          · rfl
        rw [hleft, hright, add_zero]
  · have hDM_eq : D = M := by omega
    subst hDM_eq
    rw [dif_neg (lt_irrefl D), PiLp.zero_apply, dif_pos k.2, jacobiCLM_apply_tridiag]
    have hleft :
        (if h0 : 0 < k.1 then (b k.1 : ℂ) * embJacobi D D (le_refl D) v ⟨k.1 - 1, by omega⟩ else 0) =
        (if h0 : 0 < k.1 then (b k.1 : ℂ) * v ⟨k.1 - 1, by omega⟩ else 0) := by
      split_ifs with h0
      · rw [embJacobi_apply, dif_pos (by omega)]
      · rfl
    have hright :
        (if h1 : k.1 + 1 < D then (b (k.1 + 1) : ℂ) * embJacobi D D (le_refl D) v ⟨k.1 + 1, h1⟩ else 0) =
        (if h1 : k.1 + 1 < D then (b (k.1 + 1) : ℂ) * v ⟨k.1 + 1, h1⟩ else 0) := by
      split_ifs with h1
      · rw [embJacobi_apply, dif_pos h1]
      · rfl
    rw [hleft, hright, sub_self]

/-- **Finite-Truncation Difference Bound**:
For `0 < D ≤ M`, `0 ≤ t`, and any uniform bound `B ≥ 0` with
`∀ s ∈ Set.Icc 0 t, |b D| * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ≤ B`:
`‖jacobiWavefn hM b t - embJacobi D M hDM (jacobiWavefn hD b t)‖ ≤ B * t`. -/
theorem jacobiWavefn_trunc_diff_bound {D M : ℕ} (b : ℕ → ℝ) (hD : 0 < D) (hDM : D ≤ M)
    {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hbdry : ∀ s ∈ Set.Icc 0 t, |b D| * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ≤ B) :
    ‖jacobiWavefn (lt_of_lt_of_le hD hDM) b t - embJacobi D M hDM (jacobiWavefn hD b t)‖ ≤ B * t := by
  have hM : 0 < M := lt_of_lt_of_le hD hDM
  let w : ℝ → EuclideanSpace ℂ (Fin M) :=
    fun s ↦ jacobiWavefn hM b s - embJacobi D M hDM (jacobiWavefn hD b s)
  let defect : ℝ → EuclideanSpace ℂ (Fin M) :=
    fun s ↦ Complex.I • (jacobiCLM M b (embJacobi D M hDM (jacobiWavefn hD b s)) -
      embJacobi D M hDM (jacobiCLM D b (jacobiWavefn hD b s)))
  have hw0 : w 0 = 0 := by
    dsimp [w]
    unfold jacobiWavefn
    rw [jacobiUnitary_zero, jacobiUnitary_zero]
    simp only [ContinuousLinearMap.one_apply]
    rw [embJacobi_single_zero hD hDM, sub_self]
  have hw_deriv : ∀ s : ℝ,
      HasDerivAt w ((Complex.I • jacobiCLM M b) (w s) + defect s) s := by
    intro s
    have hM_ode := jacobiWavefn_ode hM b s
    have hD_ode := jacobiWavefn_ode hD b s
    have hD_emb : HasDerivAt (fun r ↦ embJacobi D M hDM (jacobiWavefn hD b r))
        (embJacobi D M hDM ((Complex.I • jacobiCLM D b) (jacobiWavefn hD b s))) s :=
      ((embJacobi D M hDM).restrictScalars ℝ).hasDerivAt.comp s hD_ode
    convert hM_ode.sub hD_emb using 1
    dsimp [w, defect]
    simp only [map_sub, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      map_smul, smul_sub]
    abel
  have hnorm_defect : ∀ s ∈ Set.Icc 0 t, ‖defect s‖ ≤ B := by
    intro s hs
    have h1 : ‖defect s‖ =
        ‖jacobiCLM M b (embJacobi D M hDM (jacobiWavefn hD b s)) -
          embJacobi D M hDM (jacobiCLM D b (jacobiWavefn hD b s))‖ := by
      dsimp [defect]
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [h1, jacobiCLM_emb_defect b hD hDM]
    split_ifs with hlt
    · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_single_one, mul_one]
      exact hbdry s hs
    · simpa using hB
  have hnormSq_deriv : ∀ s : ℝ,
      HasDerivAt (fun r ↦ ‖w r‖ ^ 2) (2 * @inner ℝ _ _ (w s) (defect s)) s := by
    intro s
    have hinner := HasDerivAt.inner ℝ (hw_deriv s) (hw_deriv s)
    have hnorm_eq : (fun r ↦ ‖w r‖ ^ 2) = (fun r ↦ @inner ℝ _ _ (w r) (w r)) := by
      ext r; exact (real_inner_self_eq_norm_sq (w r)).symm
    rw [hnorm_eq]
    have hskew : @inner ℝ _ _ (w s) ((Complex.I • jacobiCLM M b) (w s)) = 0 := by
      rw [real_inner_eq_re_complex, ContinuousLinearMap.smul_apply, inner_smul_right,
        Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      have hreal : (inner ℂ (w s) (jacobiCLM M b (w s))).im = 0 := by
        have hsa := jacobiCLM_selfAdjoint M b (w s) (w s)
        have hconj := congrArg Complex.im (inner_conj_symm (jacobiCLM M b (w s)) (w s))
        rw [hsa, Complex.conj_im] at hconj
        linarith
      linarith
    convert hinner using 1
    rw [real_inner_comm ((Complex.I • jacobiCLM M b) (w s) + defect s) (w s),
      inner_add_right, hskew, zero_add]
    ring
  have heps : ∀ ε : ℝ, 0 < ε → ‖w t‖ ≤ B * t + ε := by
    intro ε hε
    let g : ℝ → ℝ := fun r ↦ Real.sqrt (‖w r‖ ^ 2 + ε ^ 2) - ε
    have hg_deriv : ∀ s ∈ Set.Icc 0 t,
        HasDerivAt g ((2 * @inner ℝ _ _ (w s) (defect s)) /
          (2 * Real.sqrt (‖w s‖ ^ 2 + ε ^ 2))) s ∧
        (2 * @inner ℝ _ _ (w s) (defect s)) /
          (2 * Real.sqrt (‖w s‖ ^ 2 + ε ^ 2)) ≤ B := by
      intro s hs
      have hpos : 0 < ‖w s‖ ^ 2 + ε ^ 2 := by positivity
      have hd : HasDerivAt g
          ((2 * @inner ℝ _ _ (w s) (defect s)) / (2 * Real.sqrt (‖w s‖ ^ 2 + ε ^ 2))) s :=
        ((hnormSq_deriv s).add_const (ε ^ 2)).sqrt hpos.ne' |>.sub_const ε
      refine ⟨hd, ?_⟩
      have hcs : @inner ℝ _ _ (w s) (defect s) ≤ ‖w s‖ * ‖defect s‖ :=
        real_inner_le_norm (w s) (defect s)
      have hle_sqrt : ‖w s‖ ≤ Real.sqrt (‖w s‖ ^ 2 + ε ^ 2) := by
        calc ‖w s‖ = Real.sqrt (‖w s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖w s‖ ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
      have hden_pos : 0 < Real.sqrt (‖w s‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hpos
      rw [div_le_iff₀ (by positivity)]
      calc 2 * @inner ℝ _ _ (w s) (defect s)
          ≤ 2 * (‖w s‖ * ‖defect s‖) := by linarith
        _ ≤ 2 * (Real.sqrt (‖w s‖ ^ 2 + ε ^ 2) * B) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul hle_sqrt (hnorm_defect s hs) (norm_nonneg _) hden_pos.le
        _ = B * (2 * Real.sqrt (‖w s‖ ^ 2 + ε ^ 2)) := by ring
    have hgt_le : g t ≤ B * t := by
      by_cases ht0 : t = 0
      · rw [ht0]; dsimp [g]; rw [hw0]; simp [Real.sqrt_sq hε.le]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        have hcont : ContinuousOn g (Set.Icc 0 t) := fun s hs ↦
          (hg_deriv s hs).1.continuousAt.continuousWithinAt
        have hdiff_on : DifferentiableOn ℝ g (Set.Ioo 0 t) := fun s hs ↦
          (hg_deriv s ⟨hs.1.le, hs.2.le⟩).1.differentiableAt.differentiableWithinAt
        obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope g ht_pos hcont hdiff_on
        have hleB : deriv g ξ ≤ B := by
          have := (hg_deriv ξ ⟨hξ.1.le, hξ.2.le⟩).1.deriv
          rw [this]
          exact (hg_deriv ξ ⟨hξ.1.le, hξ.2.le⟩).2
        have hg0 : g 0 = 0 := by
          dsimp [g]; rw [hw0]; simp [Real.sqrt_sq hε.le]
        rw [hg0, sub_zero, sub_zero] at hslope
        rw [hslope, div_le_iff₀ ht_pos] at hleB
        exact hleB
    have hwt_le : ‖w t‖ ≤ g t + ε := by
      dsimp [g]
      have h1 : ‖w t‖ ≤ Real.sqrt (‖w t‖ ^ 2 + ε ^ 2) := by
        calc ‖w t‖ = Real.sqrt (‖w t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖w t‖ ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
      linarith
    linarith
  exact le_of_forall_pos_le_add fun ε hε ↦ heps ε hε

end FiniteTruncationCauchy

section InfiniteChainUnconditional

/-- For any Lanczos sequence `0 ≤ b n ≤ α n + γ` (`α > 0`, `γ ≥ 0`) and `t ≥ 0`,
each coordinate `D ↦ jacobiWavefn hD b t m` is Cauchy in `ℂ` (exponentially fast in `D`). -/
theorem jacobiWavefn_coord_cauchy (b : ℕ → ℝ) {α γ t : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ)
    (m : ℕ) :
    CauchySeq (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (by omega) b t ⟨m, hm⟩ else 0) := by
  set θt := charTheta α 4 t
  have hθt_pos : 0 < θt := charTheta_pos hα (by norm_num) ht
  set C0 : ℝ := Real.exp ((1 / 2 + γ / α) * 4)
  set C_t : ℝ := Real.sqrt C0 * Real.exp (θt / 2)
  have hC0_pos : 0 < C0 := Real.exp_pos _
  have hbdry_bound : ∀ D (hD : 0 < D), ∀ s ∈ Set.Icc 0 t,
      |b D| * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ≤
      (α * (D : ℝ) + γ) * C_t * Real.exp (-(θt / 2) * (D : ℝ)) := by
    intro D hD s hs
    have hmgf := complex_finite_chain_mgf_bound hD b hα hγ (by norm_num : (0 : ℝ) < 4)
      hb_nn hb_lin hs.1
    have hsingle : Real.exp (charTheta α 4 s * ((D - 1 : ℕ) : ℝ)) *
        ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ^ 2 ≤ C0 := by
      have hmem : (⟨D - 1, by omega⟩ : Fin D) ∈ Finset.univ := Finset.mem_univ _
      exact le_trans (Finset.single_le_sum (f := fun n : Fin D ↦
        Real.exp (charTheta α 4 s * (n.1 : ℝ)) * ‖jacobiWavefn hD b s n‖ ^ 2)
        (fun n _ ↦ by positivity) hmem) hmgf
    have hθs_ge : θt ≤ charTheta α 4 s := by
      have hU_le : charU α 4 t ≤ charU α 4 s := by
        unfold charU
        apply mul_le_mul_of_nonneg_left _ (tanh_pos_of_pos (by norm_num)).le
        exact Real.exp_le_exp.mpr (by nlinarith [hs.2])
      have hU_s1 : charU α 4 s < 1 := charU_lt_one hα (by norm_num) hs.1
      have hU_t1 : charU α 4 t < 1 := charU_lt_one hα (by norm_num) ht
      have hU_tnn : 0 ≤ charU α 4 t := (charU_pos hα (by norm_num) ht).le
      unfold charTheta
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log
      · exact div_pos (by linarith) (by linarith)
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have hexp_ge : Real.exp (θt * ((D : ℝ) - 1)) ≤
        Real.exp (charTheta α 4 s * ((D - 1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      exact mul_le_mul_of_nonneg_right hθs_ge (by
        have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        linarith)
    have hsq_le : ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ^ 2 ≤
        C0 * Real.exp (-(θt * ((D : ℝ) - 1))) := by
      have h1 : Real.exp (θt * ((D : ℝ) - 1)) * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ^ 2 ≤ C0 :=
        le_trans (mul_le_mul_of_nonneg_right hexp_ge (sq_nonneg _)) hsingle
      rw [← Real.exp_neg]
      calc ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ^ 2
          = (Real.exp (θt * ((D : ℝ) - 1)))⁻¹ *
              (Real.exp (θt * ((D : ℝ) - 1)) * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
        _ ≤ (Real.exp (θt * ((D : ℝ) - 1)))⁻¹ * C0 :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Real.exp_pos _).le)
        _ = C0 * (Real.exp (θt * ((D : ℝ) - 1)))⁻¹ := mul_comm _ _
    have hnorm_le : ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖ ≤
        C_t * Real.exp (-(θt / 2) * (D : ℝ)) := by
      have hsqrt := Real.sqrt_le_sqrt hsq_le
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hC0_pos.le] at hsqrt
      have hsqrt_exp : Real.sqrt (Real.exp (-(θt * ((D : ℝ) - 1)))) =
          Real.exp (θt / 2) * Real.exp (-(θt / 2) * (D : ℝ)) := by
        have hsq' : (Real.exp (θt / 2) * Real.exp (-(θt / 2) * (D : ℝ))) ^ 2 =
            Real.exp (-(θt * ((D : ℝ) - 1))) := by
          rw [mul_pow, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [← hsq', Real.sqrt_sq (by positivity)]
      rw [hsqrt_exp] at hsqrt
      calc ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖
          ≤ Real.sqrt C0 * (Real.exp (θt / 2) * Real.exp (-(θt / 2) * (D : ℝ))) := hsqrt
        _ = C_t * Real.exp (-(θt / 2) * (D : ℝ)) := by dsimp [C_t]; ring
    have hbD : |b D| ≤ α * (D : ℝ) + γ := by
      rw [abs_of_nonneg (hb_nn D)]; exact hb_lin D
    have hlin_nn : 0 ≤ α * (D : ℝ) + γ := by positivity
    calc |b D| * ‖jacobiWavefn hD b s ⟨D - 1, by omega⟩‖
        ≤ (α * (D : ℝ) + γ) * (C_t * Real.exp (-(θt / 2) * (D : ℝ))) :=
          mul_le_mul hbD hnorm_le (norm_nonneg _) hlin_nn
      _ = (α * (D : ℝ) + γ) * C_t * Real.exp (-(θt / 2) * (D : ℝ)) := by ring
  have htend : Filter.Tendsto
      (fun D : ℕ ↦ (α * (D : ℝ) + γ) * C_t * Real.exp (-(θt / 2) * (D : ℝ)) * t)
      Filter.atTop (nhds 0) := by
    have hpow1 : Filter.Tendsto (fun D : ℕ ↦ ((D : ℝ) ^ 1) * Real.exp (-(θt / 2) * (D : ℝ)))
        Filter.atTop (nhds 0) := by
      have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (Filter.Tendsto.const_mul_atTop (by positivity : 0 < θt / 2) tendsto_natCast_atTop_atTop)
      have h2 := h1.const_mul ((θt / 2)⁻¹)
      rw [mul_zero] at h2
      refine h2.congr fun D ↦ ?_
      simp only [Function.comp_apply, pow_one]
      have hne : θt / 2 ≠ 0 := by positivity
      field_simp [hne]
      congr 1; ring
    have hpow0 : Filter.Tendsto (fun D : ℕ ↦ Real.exp (-(θt / 2) * (D : ℝ)))
        Filter.atTop (nhds 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop (by positivity : 0 < θt / 2)
          tendsto_natCast_atTop_atTop)).congr fun D ↦ by simp [mul_comm, neg_mul]
    have hcomb := (hpow1.const_mul (α * C_t * t)).add (hpow0.const_mul (γ * C_t * t))
    simpa [add_zero] using hcomb.congr fun D ↦ by simp; ring
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htend) ε hε
  refine ⟨max N₀ (m + 1), fun D hD M hM ↦ ?_⟩
  have hpair : ∀ {A B : ℕ}, max N₀ (m + 1) ≤ A → A ≤ B →
      dist (if hm : m < B then jacobiWavefn (by omega) b t ⟨m, hm⟩ else 0)
           (if hm : m < A then jacobiWavefn (by omega) b t ⟨m, hm⟩ else 0) < ε := by
    intro A B hA hAB
    have hAm : m < A := by omega
    have hBm : m < B := by omega
    have hA1 : 0 < A := by omega
    rw [dif_pos hBm, dif_pos hAm, dist_eq_norm]
    have hcoord : ‖jacobiWavefn (by omega) b t ⟨m, hBm⟩ - jacobiWavefn hA1 b t ⟨m, hAm⟩‖ ≤
        ‖jacobiWavefn (lt_of_lt_of_le hA1 hAB) b t - embJacobi A B hAB (jacobiWavefn hA1 b t)‖ := by
      have heq : jacobiWavefn (by omega) b t ⟨m, hBm⟩ - jacobiWavefn hA1 b t ⟨m, hAm⟩ =
          (jacobiWavefn (lt_of_lt_of_le hA1 hAB) b t - embJacobi A B hAB (jacobiWavefn hA1 b t)) ⟨m, hBm⟩ := by
        simp [embJacobi_apply, hAm]
      rw [heq]
      exact PiLp.norm_apply_le _ ⟨m, hBm⟩
    have hdiff := jacobiWavefn_trunc_diff_bound b hA1 hAB ht (by positivity) (hbdry_bound A hA1)
    have hltε : (α * (A : ℝ) + γ) * C_t * Real.exp (-(θt / 2) * (A : ℝ)) * t < ε := by
      have hAN : N₀ ≤ A := le_trans (le_max_left _ _) hA
      have h1 := hN₀ A hAN
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
      exact h1
    linarith
  rcases le_total D M with hDM | hMD
  · rw [dist_comm]; exact hpair hD hDM
  · exact hpair hM hMD

/-- **Unconditional Infinite-Chain Krylov Wavefunction** `φ_m(t) = lim_{D→∞} φ^{(D)}_m(t)`. -/
noncomputable def infiniteKrylovWavefn (b : ℕ → ℝ) (t : ℝ) (m : ℕ) : ℂ :=
  Filter.limUnder Filter.atTop
    (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (by omega) b t ⟨m, hm⟩ else 0)

/-- Pointwise convergence `φ^{(D)}_m(t) → φ_m(t)` (discharging `hlim` completely!). -/
theorem infiniteKrylovWavefn_tendsto (b : ℕ → ℝ) {α γ t : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ) (m : ℕ) :
    Filter.Tendsto
      (fun D : ℕ ↦ if hm : m < D then jacobiWavefn (by omega) b t ⟨m, hm⟩ else 0)
      Filter.atTop (nhds (infiniteKrylovWavefn b t m)) := by
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (jacobiWavefn_coord_cauchy b hα hγ ht hb_nn hb_lin m)
  unfold infiniteKrylovWavefn
  rw [hz.limUnder_eq]
  exact hz

/-- Pointwise squared-modulus convergence `‖φ^{(D)}_m(t)‖² → ‖φ_m(t)‖²`. -/
theorem infiniteKrylovWavefn_normSq_tendsto (b : ℕ → ℝ) {α γ t : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ) (m : ℕ) :
    Filter.Tendsto
      (fun D : ℕ ↦ if hm : m < D then ‖jacobiWavefn (by omega) b t ⟨m, hm⟩‖ ^ 2 else 0)
      Filter.atTop (nhds (‖infiniteKrylovWavefn b t m‖ ^ 2)) := by
  have h1 := ((infiniteKrylovWavefn_tendsto b hα hγ ht hb_nn hb_lin m).norm).pow 2
  refine h1.congr fun D ↦ ?_
  split_ifs <;> simp

/-- **Unconditional Infinite-Chain Theorem 1.1(a)** (Zero `hlim`, Zero `hfatou`):
For ANY Lanczos sequence `0 ≤ b n ≤ α n + γ` (`α > 0, γ ≥ 0`) and ANY `t ≥ 0, θ₀ > 0`,
the infinite-chain Krylov wavefunction `φ_m(t) = lim_{D→∞} φ^{(D)}_m(t)` unconditionally satisfies:
1. Probability conservation: `∑' m : ℕ, ‖φ_m(t)‖² = 1`,
2. Summability & MGF bound: `∑' m : ℕ, exp(θ_t m) ‖φ_m(t)‖² ≤ exp((1/2 + γ/α) θ₀)`,
3. Exponential tail bound: `∀ M₀, ∑' m, (if M₀ ≤ m then ‖φ_m(t)‖² else 0) ≤ exp(-θ_t M₀ + (1/2 + γ/α) θ₀)`,
4. Krylov complexity bound: `∑' m : ℕ, m * ‖φ_m(t)‖² ≤ (1/θ_t) * ((1/2 + γ/α) θ₀ + 1)`. -/
theorem theorem_1_1a_infinite_unconditional (b : ℕ → ℝ) {α γ t θ₀ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hθ₀ : 0 < θ₀)
    (hb_nn : ∀ n, 0 ≤ b n) (hb_lin : ∀ n, b n ≤ α * (n : ℝ) + γ) :
    let θ := charTheta α θ₀ t
    let A := (1 / 2 + γ / α) * θ₀
    let p : ℕ → ℝ := fun m ↦ ‖infiniteKrylovWavefn b t m‖ ^ 2
    Summable p ∧ (∑' m : ℕ, p m) = 1 ∧
    Summable (fun m : ℕ ↦ Real.exp (θ * (m : ℝ)) * p m) ∧
    (∑' m : ℕ, Real.exp (θ * (m : ℝ)) * p m) ≤ Real.exp A ∧
    (∀ M₀ : ℕ, (∑' m : ℕ, if M₀ ≤ m then p m else 0) ≤ Real.exp (-(θ * (M₀ : ℝ)) + A)) ∧
    Summable (fun m : ℕ ↦ (m : ℝ) * p m) ∧
    (∑' m : ℕ, (m : ℝ) * p m) ≤ (1 / θ) * (A + 1) := by
  intro θ A p
  let pN : ℕ → ℕ → ℝ := fun D m ↦ if hm : m < D then ‖jacobiWavefn (by omega) b t ⟨m, hm⟩‖ ^ 2 else 0
  have hθ_pos : 0 < θ := charTheta_pos hα hθ₀ ht
  have hA_nn : 0 ≤ A := by dsimp [A]; positivity
  have hpN_nn : ∀ D m, 0 ≤ pN D m := fun D m ↦ by dsimp [pN]; split_ifs <;> positivity
  have hlim : ∀ m, Filter.Tendsto (fun D ↦ pN D m) Filter.atTop (nhds (p m)) :=
    infiniteKrylovWavefn_normSq_tendsto b hα hγ ht hb_nn hb_lin
  have hunit_eq : ∀ D (hD : 0 < D), ∑ m ∈ Finset.range D, pN D m = 1 := by
    intro D hD
    have h1 : ∑ m ∈ Finset.range D, pN D m = ∑ m : Fin D, ‖jacobiWavefn hD b t m‖ ^ 2 := by
      rw [Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro m hm
      have hm' : m < D := Finset.mem_range.mp hm
      simp [pN, hm']
    rw [h1]
    have hnorm : ‖jacobiWavefn hD b t‖ ^ 2 = 1 := by
      unfold jacobiWavefn
      rw [jacobiUnitary_norm_preserve, norm_single_one, one_pow]
    rw [← hnorm, EuclideanSpace.norm_sq_eq]
  have hunit_le : ∀ D, ∑ m ∈ Finset.range D, pN D m ≤ 1 := by
    intro D
    cases D with
    | zero => simp
    | succ D' => exact (hunit_eq (D' + 1) (Nat.succ_pos D')).le
  have hmgf_bound : ∀ D, ∑ m ∈ Finset.range D, Real.exp (θ * (m : ℝ)) * pN D m ≤ Real.exp A := by
    intro D
    cases D with
    | zero => simp; exact (Real.exp_pos _).le
    | succ D' =>
      have hD : 0 < D' + 1 := Nat.succ_pos D'
      have h1 : ∑ m ∈ Finset.range (D' + 1), Real.exp (θ * (m : ℝ)) * pN (D' + 1) m =
          ∑ m : Fin (D' + 1), Real.exp (θ * (m.1 : ℝ)) * ‖jacobiWavefn hD b t m‖ ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl; intro m hm
        have hm' : m < D' + 1 := Finset.mem_range.mp hm
        simp [pN, hm']
      rw [h1]
      exact complex_finite_chain_mgf_bound hD b hα hγ hθ₀ hb_nn hb_lin ht
  have hfat_mgf := fatou_tsum_le_of_pointwise_tendsto pN p
    (fun m ↦ Real.exp (θ * (m : ℝ))) (Real.exp A) hpN_nn
    (fun _ ↦ (Real.exp_pos _).le) hlim hmgf_bound
  have hfat_prob := fatou_tsum_le_of_pointwise_tendsto pN p
    (fun _ ↦ 1) 1 hpN_nn (fun _ ↦ by norm_num) hlim (by simpa using hunit_le)
  have hp_nn : ∀ m, 0 ≤ p m := fun m ↦ ge_of_tendsto' (hlim m) (fun D ↦ hpN_nn D m)
  have htail : ∀ M₀ : ℕ,
      (∑' m : ℕ, if M₀ ≤ m then p m else 0) ≤ Real.exp (-(θ * (M₀ : ℝ)) + A) := by
    intro M₀
    have hdom : ∀ m : ℕ,
        (if M₀ ≤ m then p m else 0) ≤
        Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) := by
      intro m
      split_ifs with hm
      · have h1 : 1 ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by
            have : (M₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
            nlinarith)
        calc p m = 1 * p m := (one_mul _).symm
          _ ≤ (Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ))) * p m :=
                mul_le_mul_of_nonneg_right h1 (hp_nn m)
          _ = Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) := by ring
      · positivity
    have hsumm_t : Summable (fun m : ℕ ↦ if M₀ ≤ m then p m else 0) :=
      Summable.of_nonneg_of_le (fun m ↦ by split_ifs <;> [exact hp_nn m; exact le_refl 0])
        hdom (hfat_mgf.2.1.mul_left _)
    calc ∑' m : ℕ, (if M₀ ≤ m then p m else 0)
        ≤ ∑' m : ℕ, Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * p m) :=
            hsumm_t.tsum_le_tsum hdom (hfat_mgf.2.1.mul_left _)
      _ = Real.exp (-(θ * (M₀ : ℝ))) * ∑' m : ℕ, Real.exp (θ * (m : ℝ)) * p m := tsum_mul_left
      _ ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp A :=
            mul_le_mul_of_nonneg_left hfat_mgf.2.2 (Real.exp_pos _).le
      _ = Real.exp (-(θ * (M₀ : ℝ)) + A) := (Real.exp_add _ _).symm
  have hp_summ : Summable p := by simpa using hfat_prob.2.1
  have hp_le1 : ∑' m : ℕ, p m ≤ 1 := by simpa using hfat_prob.2.2
  have hp_ge1 : 1 ≤ ∑' m : ℕ, p m := by
    have hpartial_ge : ∀ M₀ : ℕ, 1 ≤ M₀ →
        1 - Real.exp (-(θ * (M₀ : ℝ)) + A) ≤ ∑ m ∈ Finset.range M₀, p m := by
      intro M₀ hM₀
      have htend_part : Filter.Tendsto (fun D ↦ ∑ m ∈ Finset.range M₀, pN D m)
          Filter.atTop (nhds (∑ m ∈ Finset.range M₀, p m)) :=
        tendsto_finset_sum _ fun m _ ↦ hlim m
      apply ge_of_tendsto htend_part
      rw [Filter.eventually_atTop]
      refine ⟨M₀, fun D hDM ↦ ?_⟩
      have hD1 : 0 < D := lt_of_lt_of_le hM₀ hDM
      have hsplit : ∑ m ∈ Finset.range D, pN D m =
          ∑ m ∈ Finset.range M₀, pN D m +
          ∑ m ∈ Finset.Ico M₀ D, pN D m := by
        rw [← Finset.sum_Ico_consecutive pN (Nat.zero_le M₀) hDM]
        simp [Finset.Ico_zero_eq_range]
      have htailD : ∑ m ∈ Finset.Ico M₀ D, pN D m ≤ Real.exp (-(θ * (M₀ : ℝ)) + A) := by
        have hdomD : ∑ m ∈ Finset.Ico M₀ D, pN D m ≤
            Real.exp (-(θ * (M₀ : ℝ))) * ∑ m ∈ Finset.Ico M₀ D, Real.exp (θ * (m : ℝ)) * pN D m := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro m hm
          have hm0 : M₀ ≤ m := (Finset.mem_Ico.mp hm).1
          have h1 : 1 ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ)) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by
              have : (M₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
              nlinarith)
          calc pN D m = 1 * pN D m := (one_mul _).symm
            _ ≤ (Real.exp (-(θ * (M₀ : ℝ))) * Real.exp (θ * (m : ℝ))) * pN D m :=
                mul_le_mul_of_nonneg_right h1 (hpN_nn D m)
            _ = Real.exp (-(θ * (M₀ : ℝ))) * (Real.exp (θ * (m : ℝ)) * pN D m) := by ring
        have hsubD : ∑ m ∈ Finset.Ico M₀ D, Real.exp (θ * (m : ℝ)) * pN D m ≤ Real.exp A := by
          calc ∑ m ∈ Finset.Ico M₀ D, Real.exp (θ * (m : ℝ)) * pN D m
              ≤ ∑ m ∈ Finset.range D, Real.exp (θ * (m : ℝ)) * pN D m :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_range _ _)
                  fun m _ _ ↦ mul_nonneg (Real.exp_pos _).le (hpN_nn D m)
            _ ≤ Real.exp A := hmgf_bound D
        calc ∑ m ∈ Finset.Ico M₀ D, pN D m
            ≤ Real.exp (-(θ * (M₀ : ℝ))) * Real.exp A :=
              le_trans hdomD (mul_le_mul_of_nonneg_left hsubD (Real.exp_pos _).le)
          _ = Real.exp (-(θ * (M₀ : ℝ)) + A) := (Real.exp_add _ _).symm
      linarith [hunit_eq D hD1]
    have htend_rhs : Filter.Tendsto (fun M₀ : ℕ ↦ 1 - Real.exp (-(θ * (M₀ : ℝ)) + A))
        Filter.atTop (nhds 1) := by
      have hexp0 : Filter.Tendsto (fun M₀ : ℕ ↦ Real.exp (-(θ * (M₀ : ℝ)) + A))
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun M₀ : ℕ ↦ Real.exp (-(θ * (M₀ : ℝ))))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (Filter.Tendsto.const_mul_atTop hθ_pos tendsto_natCast_atTop_atTop)
        simpa [Real.exp_add, mul_zero] using (h1.mul_const (Real.exp A)).congr
          fun M₀ ↦ by rw [← Real.exp_add]
      simpa using tendsto_const_nhds.sub hexp0
    have htsum_ge : ∀ M₀ : ℕ, 1 ≤ M₀ →
        1 - Real.exp (-(θ * (M₀ : ℝ)) + A) ≤ ∑' m : ℕ, p m := fun M₀ hM₀ ↦
      le_trans (hpartial_ge M₀ hM₀) (hp_summ.sum_le_tsum _ fun m _ ↦ hp_nn m)
    exact ge_of_tendsto htend_rhs
      (Filter.eventually_atTop.mpr ⟨1, fun M₀ hM₀ ↦ htsum_ge M₀ hM₀⟩)
  have hcomp_partial : ∀ M : ℕ, ∑ m ∈ Finset.range M, (m : ℝ) * p m ≤ (1 / θ) * (A + 1) := by
    intro M
    have hstep : ∀ m : ℕ,
        θ * ((m : ℝ) * p m) ≤ A * p m + (Real.exp A)⁻¹ * (Real.exp (θ * (m : ℝ)) * p m) := by
      intro m
      have hexp : θ * (m : ℝ) - A ≤ Real.exp (θ * (m : ℝ) - A) := by
        linarith [Real.add_one_le_exp (θ * (m : ℝ) - A)]
      rw [Real.exp_sub, div_eq_inv_mul] at hexp
      have h1 : θ * (m : ℝ) ≤ A + (Real.exp A)⁻¹ * Real.exp (θ * (m : ℝ)) := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 (hp_nn m)
      linarith
    have hsum_θ :
        θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m) ≤
        A * (∑ m ∈ Finset.range M, p m) +
        (Real.exp A)⁻¹ * (∑ m ∈ Finset.range M, Real.exp (θ * (m : ℝ)) * p m) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun m _ ↦ hstep m
    have hp_le : ∑ m ∈ Finset.range M, p m ≤ 1 := by simpa using hfat_prob.1 M
    have hm_le : ∑ m ∈ Finset.range M, Real.exp (θ * (m : ℝ)) * p m ≤ Real.exp A := hfat_mgf.1 M
    have hbound : θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m) ≤ A + 1 := by
      calc θ * (∑ m ∈ Finset.range M, (m : ℝ) * p m)
          ≤ A * 1 + (Real.exp A)⁻¹ * Real.exp A := by
              have h1 := mul_le_mul_of_nonneg_left hp_le hA_nn
              have h2 := mul_le_mul_of_nonneg_left hm_le (inv_nonneg.mpr (Real.exp_pos A).le)
              linarith
        _ = A + 1 := by rw [mul_one, inv_mul_cancel₀ (Real.exp_pos A).ne']
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hθ_pos]
    linarith
  have hcomp_summ : Summable (fun m : ℕ ↦ (m : ℝ) * p m) :=
    summable_of_sum_range_le (fun m ↦ mul_nonneg (Nat.cast_nonneg m) (hp_nn m)) hcomp_partial
  have hcomp_tsum : ∑' m : ℕ, (m : ℝ) * p m ≤ (1 / θ) * (A + 1) :=
    le_of_tendsto (hcomp_summ.hasSum.tendsto_sum_nat)
      (Filter.Eventually.of_forall hcomp_partial)
  exact ⟨hp_summ, le_antisymm hp_le1 hp_ge1, hfat_mgf.2.1, hfat_mgf.2.2, htail,
    hcomp_summ, hcomp_tsum⟩

end InfiniteChainUnconditional

end KrylovChaos
