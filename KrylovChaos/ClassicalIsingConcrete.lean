/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.ClassicalIsing
import KrylovChaos.OperatorBridges
import Mathlib.Tactic

/-!
# Concrete Classical Ising Gibbs Measure, Glauber Dirichlet Form & Reverse Poincaré (Flaw #8)

Formalizes Section 8.2 directly on `SpinConfig N := Fin N → Bool` (encoding `{-1, +1}^N`):
1. **Product Bernoulli Measure `prodBernoulli h`** and **`p`-biased orthonormal Fourier basis
   `chiBasis h S`** with exact proofs of normalization, orthonormality, and completeness.
2. **Concrete Glauber Dirichlet Form `glauberDirichlet μ f`** and **Concrete Degree-Filtration
   Quadratic Form `degreeFiltrationQ μ f = ∑_{k=0}^{N-1} inf_{g ∈ 𝒱_k} ‖f - g‖_{L^2(μ)}²`**.
3. **Concrete Product-Bernoulli Reverse Poincaré (`prodBernoulli_discrete_grad_le_Q`)**:
   `∑ i, ∑ z, prodBernoulli h z * ((f z - f (flipSpin z i)) / 2)² ≤ (cosh Φmax)² * degreeFiltrationQ (prodBernoulli h) f`.
4. **Concrete Convex-Mixture Reverse Poincaré (`prop_8_3_concrete_convex_mixture_reverse_poincare`)**:
   For ANY convex mixture `μ z = ∑ ξ, w ξ * prodBernoulli (h ξ) z` (in particular the
   Hubbard–Stratonovich decomposition of the classical Ising Gibbs measure `μ_β` from
   `lemma_8_2_multi_edge_hs`), proves directly:
   `glauberDirichlet μ f ≤ (cosh Φmax)² * degreeFiltrationQ μ f`.
-/

namespace KrylovChaos

section ConcreteIsingSetup

/-- Classical spin configuration `z ∈ {-1, +1}^N` encoded as `Fin N → Bool`. -/
abbrev SpinConfig (N : ℕ) := Fin N → Bool

/-- Flip spin at coordinate `i`. -/
def flipSpin {N : ℕ} (z : SpinConfig N) (i : Fin N) : SpinConfig N :=
  Function.update z i (!(z i))

/-- Single-site Bernoulli probability `p_i(b) = exp(h_i * σ(b)) / (2 cosh h_i)`. -/
noncomputable def siteBernoulli (h : ℝ) (b : Bool) : ℝ :=
  Real.exp (h * spinVal b) / (2 * Real.cosh h)

lemma siteBernoulli_pos (h : ℝ) (b : Bool) : 0 < siteBernoulli h b :=
  div_pos (Real.exp_pos _) (by positivity [Real.cosh_pos h])

lemma siteBernoulli_sum (h : ℝ) : ∑ b : Bool, siteBernoulli h b = 1 := by
  simp only [Fintype.sum_bool, siteBernoulli, spinVal, ↓reduceIte, Bool.false_eq_true,
    mul_one, mul_neg]
  rw [← add_div, Real.cosh_eq]
  have hpos : (0 : ℝ) < 2 * ((Real.exp h + Real.exp (-h)) / 2) := by
    have := Real.exp_pos h; have := Real.exp_pos (-h); linarith
  field_simp [hpos.ne']

lemma siteBernoulli_mean (h : ℝ) :
    ∑ b : Bool, siteBernoulli h b * spinVal b = Real.tanh h := by
  simp only [Fintype.sum_bool, siteBernoulli, spinVal, ↓reduceIte, Bool.false_eq_true,
    mul_one, mul_neg]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : (0 : ℝ) < Real.exp h + Real.exp (-h) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  field_simp [hpos.ne']
  ring

/-- Concrete product Bernoulli probability measure on `SpinConfig N`. -/
noncomputable def prodBernoulli {N : ℕ} (h : Fin N → ℝ) (z : SpinConfig N) : ℝ :=
  ∏ i : Fin N, siteBernoulli (h i) (z i)

lemma prodBernoulli_pos {N : ℕ} (h : Fin N → ℝ) (z : SpinConfig N) :
    0 < prodBernoulli h z :=
  Finset.prod_pos fun i _ ↦ siteBernoulli_pos (h i) (z i)

lemma prodBernoulli_sum {N : ℕ} (h : Fin N → ℝ) :
    ∑ z : SpinConfig N, prodBernoulli h z = 1 := by
  unfold prodBernoulli
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) ↦ siteBernoulli (h i) b)]
  exact Finset.prod_eq_one fun i _ ↦ siteBernoulli_sum (h i)

/-- Single-site `p`-biased orthonormal character `χ_i(b) = (σ(b) - tanh h) / √(1 - tanh² h)`. -/
noncomputable def siteChi (h : ℝ) (b : Bool) : ℝ :=
  (spinVal b - Real.tanh h) / Real.sqrt (1 - (Real.tanh h) ^ 2)

lemma one_sub_tanh_sq_pos (h : ℝ) : 0 < 1 - (Real.tanh h) ^ 2 := by
  have h1 : |Real.tanh h| < 1 := by
    rw [abs_lt]
    have hch : 0 < Real.cosh h := Real.cosh_pos h
    rw [Real.tanh_eq_sinh_div_cosh, lt_div_iff₀ hch, div_lt_iff₀ hch]
    rw [Real.sinh_eq, Real.cosh_eq]
    have he1 := Real.exp_pos h
    have he2 := Real.exp_pos (-h)
    constructor <;> linarith
  have hlt := abs_lt.mp h1
  nlinarith

lemma siteChi_mean (h : ℝ) : ∑ b : Bool, siteBernoulli h b * siteChi h b = 0 := by
  unfold siteChi
  simp_rw [mul_div_assoc', ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, siteBernoulli_mean, siteBernoulli_sum, one_mul, sub_self, zero_div]

lemma siteChi_sq_mean (h : ℝ) : ∑ b : Bool, siteBernoulli h b * (siteChi h b) ^ 2 = 1 := by
  have hpos := one_sub_tanh_sq_pos h
  unfold siteChi
  simp_rw [div_pow, Real.sq_sqrt hpos.le, mul_div_assoc', ← Finset.sum_div]
  have hnum : ∑ b : Bool, siteBernoulli h b * (spinVal b - Real.tanh h) ^ 2 =
      1 - (Real.tanh h) ^ 2 := by
    have hexp : ∀ b : Bool,
        siteBernoulli h b * (spinVal b - Real.tanh h) ^ 2 =
        siteBernoulli h b - 2 * Real.tanh h * (siteBernoulli h b * spinVal b) +
          (Real.tanh h) ^ 2 * siteBernoulli h b := by
      intro b
      have hsq : (spinVal b) ^ 2 = 1 := by cases b <;> simp [spinVal]
      linear_combination siteBernoulli h b * hsq
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      siteBernoulli_sum, siteBernoulli_mean]
    ring
  rw [hnum, div_self hpos.ne']

/-- Concrete `p`-biased orthonormal Fourier basis `χ_S^{(h)}(z) = ∏_{i ∈ S} χ_i(z_i)`. -/
noncomputable def chiBasis {N : ℕ} (h : Fin N → ℝ) (S : Finset (Fin N)) (z : SpinConfig N) : ℝ :=
  ∏ i ∈ S, siteChi (h i) (z i)

/-- **Exact Orthonormality of `chiBasis`**:
`∑_z ν_h(z) χ_S^{(h)}(z) χ_T^{(h)}(z) = δ_{S,T}`. -/
theorem chiBasis_orthonormal {N : ℕ} (h : Fin N → ℝ) (S T : Finset (Fin N)) :
    ∑ z : SpinConfig N, prodBernoulli h z * chiBasis h S z * chiBasis h T z =
      if S = T then 1 else 0 := by
  have hfac : ∀ z : SpinConfig N,
      prodBernoulli h z * chiBasis h S z * chiBasis h T z =
      ∏ i : Fin N, siteBernoulli (h i) (z i) *
        (if i ∈ S then siteChi (h i) (z i) else 1) *
        (if i ∈ T then siteChi (h i) (z i) else 1) := by
    intro z
    unfold prodBernoulli chiBasis
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_filter,
      ← Finset.prod_filter]
    congr 1
    · congr 1; congr 1; ext i; simp
    · congr 1; ext i; simp
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) ↦
    siteBernoulli (h i) b *
      (if i ∈ S then siteChi (h i) b else 1) *
      (if i ∈ T then siteChi (h i) b else 1))]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    apply Finset.prod_eq_one; intro i _
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      have hsq : ∀ b : Bool, siteBernoulli (h i) b * siteChi (h i) b * siteChi (h i) b =
          siteBernoulli (h i) b * (siteChi (h i) b) ^ 2 := fun b ↦ by ring
      simp_rw [hsq]
      exact siteChi_sq_mean (h i)
    · simp only [hi, ↓reduceIte, mul_one]
      exact siteBernoulli_sum (h i)
  · rw [if_neg hST]
    have hex : ∃ i : Fin N, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
      by_contra hall
      push Not at hall
      apply hST; ext i
      exact ⟨fun hiS ↦ (hall i).1 hiS, fun hiT ↦ by by_contra hiS; exact (hall i).2 hiS hiT⟩
    rcases hex with ⟨i₀, ⟨hiS, hiT⟩ | ⟨hiS, hiT⟩⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      simp only [hiS, hiT, ↓reduceIte, mul_one]
      exact siteChi_mean (h i₀)
    · apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      simp only [hiS, hiT, ↓reduceIte, mul_one]
      exact siteChi_mean (h i₀)

/-- Fourier coefficient `f̂_h(S) = ∑_z ν_h(z) f(z) χ_S^{(h)}(z)`. -/
noncomputable def bernoulliFourierCoeff {N : ℕ} (h : Fin N → ℝ)
    (f : SpinConfig N → ℝ) (S : Finset (Fin N)) : ℝ :=
  ∑ z : SpinConfig N, prodBernoulli h z * f z * chiBasis h S z

/-- Single-site conditional expectation under a strictly positive measure `μ` on `SpinConfig N`. -/
noncomputable def condExpSite {N : ℕ} (μ : SpinConfig N → ℝ) (i : Fin N)
    (f : SpinConfig N → ℝ) (z : SpinConfig N) : ℝ :=
  (μ z * f z + μ (flipSpin z i) * f (flipSpin z i)) / (μ z + μ (flipSpin z i))

/-- Concrete Glauber Dirichlet form `ℰ_μ(f, f) = ∑_{i=1}^N ∑_z μ(z) (f(z) - (E_i f)(z))²`. -/
noncomputable def glauberDirichlet {N : ℕ} (μ : SpinConfig N → ℝ) (f : SpinConfig N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ z : SpinConfig N, μ z * (f z - condExpSite μ i f z) ^ 2

/-- Subspace `𝒱_k^{cl}` of classical functions of Fourier degree `≤ k`. -/
def classicalDegreeSubspace (N k : ℕ) : Submodule ℝ (SpinConfig N → ℝ) :=
  Submodule.span ℝ { g : SpinConfig N → ℝ |
    ∃ S : Finset (Fin N), S.card ≤ k ∧ g = fun z ↦ ∏ i ∈ S, spinVal (z i) }

/-- Concrete `L^2(μ)` distance squared to `𝒱_k^{cl}`. -/
noncomputable def distSqDegree {N : ℕ} (μ : SpinConfig N → ℝ) (k : ℕ)
    (f : SpinConfig N → ℝ) : ℝ :=
  sInf { r : ℝ | ∃ g ∈ classicalDegreeSubspace N k,
    r = ∑ z : SpinConfig N, μ z * (f z - g z) ^ 2 }

/-- Concrete degree-filtration quadratic form `𝒬_μ(f, f) = ∑_{k=0}^{N-1} distSqDegree μ k f`. -/
noncomputable def degreeFiltrationQ {N : ℕ} (μ : SpinConfig N → ℝ) (f : SpinConfig N → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, distSqDegree μ k f

theorem distSqDegree_convex_mixture_ge {N : ℕ} {Ξ : Type*} [Fintype Ξ]
    (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (ν : Ξ → SpinConfig N → ℝ) (hν : ∀ ξ z, 0 ≤ ν ξ z)
    (k : ℕ) (f : SpinConfig N → ℝ) :
    ∑ ξ : Ξ, w ξ * distSqDegree (ν ξ) k f ≤
      distSqDegree (fun z ↦ ∑ ξ : Ξ, w ξ * ν ξ z) k f := by
  unfold distSqDegree
  apply le_csInf
  · refine ⟨∑ z : SpinConfig N, (∑ ξ : Ξ, w ξ * ν ξ z) * (f z - 0) ^ 2,
      0, Submodule.zero_mem _, rfl⟩
  · rintro r ⟨g, hg, rfl⟩
    have hswap : ∑ z : SpinConfig N, (∑ ξ : Ξ, w ξ * ν ξ z) * (f z - g z) ^ 2 =
        ∑ ξ : Ξ, w ξ * (∑ z : SpinConfig N, ν ξ z * (f z - g z) ^ 2) := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro ξ _
      rw [← Finset.mul_sum]
    rw [hswap]
    apply Finset.sum_le_sum; intro ξ _
    apply mul_le_mul_of_nonneg_left _ (hw ξ)
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨g', _, rfl⟩
      exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (hν ξ z) (sq_nonneg _)
    · exact ⟨g, hg, rfl⟩

theorem degreeFiltrationQ_convex_mixture_ge {N : ℕ} {Ξ : Type*} [Fintype Ξ]
    (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (ν : Ξ → SpinConfig N → ℝ) (hν : ∀ ξ z, 0 ≤ ν ξ z)
    (f : SpinConfig N → ℝ) :
    ∑ ξ : Ξ, w ξ * degreeFiltrationQ (ν ξ) f ≤
      degreeFiltrationQ (fun z ↦ ∑ ξ : Ξ, w ξ * ν ξ z) f := by
  unfold degreeFiltrationQ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun k _ ↦ distSqDegree_convex_mixture_ge w hw ν hν k f

lemma glauberDirichlet_eq_discrete_grad {N : ℕ} (μ : SpinConfig N → ℝ)
    (hμ : ∀ z, 0 < μ z) (f : SpinConfig N → ℝ) :
    glauberDirichlet μ f =
      ∑ i : Fin N, ∑ z : SpinConfig N,
        (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) *
          ((f z - f (flipSpin z i)) ^ 2 / 2) := by
  unfold glauberDirichlet condExpSite
  apply Finset.sum_congr rfl; intro i _
  have hinv : ∀ z : SpinConfig N, flipSpin (flipSpin z i) i = z := by
    intro z; ext j
    by_cases hj : j = i
    · subst hj; simp [flipSpin]
    · simp [flipSpin, hj]
  have hpair : ∀ z : SpinConfig N,
      μ z * (f z - (μ z * f z + μ (flipSpin z i) * f (flipSpin z i)) /
        (μ z + μ (flipSpin z i))) ^ 2 =
      (μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
        (f z - f (flipSpin z i)) ^ 2 := by
    intro z
    have hpos : 0 < μ z + μ (flipSpin z i) := add_pos (hμ z) (hμ (flipSpin z i))
    field_simp [hpos.ne']
    ring
  simp_rw [hpair]
  have hsym : ∑ z : SpinConfig N,
      (μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
        (f z - f (flipSpin z i)) ^ 2 =
      ∑ z : SpinConfig N,
      (μ (flipSpin z i) * μ z ^ 2 / (μ (flipSpin z i) + μ z) ^ 2) *
        (f (flipSpin z i) - f z) ^ 2 := by
    refine Finset.sum_bij (fun z _ ↦ flipSpin z i) (fun _ _ ↦ Finset.mem_univ _)
      (fun z₁ _ z₂ _ h ↦ by have := congrArg (fun w ↦ flipSpin w i) h; rwa [hinv, hinv] at this)
      (fun z _ ↦ ⟨flipSpin z i, Finset.mem_univ _, hinv z⟩)
      (fun z _ ↦ by rw [hinv])
  have havg : 2 * ∑ z : SpinConfig N,
      (μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
        (f z - f (flipSpin z i)) ^ 2 =
      ∑ z : SpinConfig N,
        (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) *
          (f z - f (flipSpin z i)) ^ 2 := by
    calc 2 * ∑ z : SpinConfig N,
          (μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
            (f z - f (flipSpin z i)) ^ 2
        = (∑ z : SpinConfig N,
            (μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
              (f z - f (flipSpin z i)) ^ 2) +
          (∑ z : SpinConfig N,
            (μ (flipSpin z i) * μ z ^ 2 / (μ (flipSpin z i) + μ z) ^ 2) *
              (f (flipSpin z i) - f z) ^ 2) := by
          rw [two_mul]; congr 1
      _ = ∑ z : SpinConfig N,
            ((μ z * μ (flipSpin z i) ^ 2 / (μ z + μ (flipSpin z i)) ^ 2) *
              (f z - f (flipSpin z i)) ^ 2 +
            (μ (flipSpin z i) * μ z ^ 2 / (μ (flipSpin z i) + μ z) ^ 2) *
              (f (flipSpin z i) - f z) ^ 2) := by
          rw [← Finset.sum_add_distrib]
      _ = ∑ z : SpinConfig N,
            (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) *
              (f z - f (flipSpin z i)) ^ 2 := by
          apply Finset.sum_congr rfl; intro z _
          have hpos : 0 < μ z + μ (flipSpin z i) := add_pos (hμ z) (hμ (flipSpin z i))
          have hpos2 : 0 < μ (flipSpin z i) + μ z := by linarith
          field_simp [hpos.ne', hpos2.ne']
          ring
  have hhalf : ∑ z : SpinConfig N,
      (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) *
        ((f z - f (flipSpin z i)) ^ 2 / 2) =
      (1 / 2 : ℝ) * ∑ z : SpinConfig N,
        (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) *
          (f z - f (flipSpin z i)) ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hhalf, ← havg]; ring

theorem glauberDirichlet_le_discrete_grad_avg {N : ℕ} (μ : SpinConfig N → ℝ)
    (hμ : ∀ z, 0 < μ z) (f : SpinConfig N → ℝ) :
    glauberDirichlet μ f ≤
      ∑ i : Fin N, ∑ z : SpinConfig N,
        μ z * ((f z - f (flipSpin z i)) / 2) ^ 2 := by
  rw [glauberDirichlet_eq_discrete_grad μ hμ f]
  apply Finset.sum_le_sum; intro i _
  have hinv : ∀ z : SpinConfig N, flipSpin (flipSpin z i) i = z := by
    intro z; ext j
    by_cases hj : j = i
    · subst hj; simp [flipSpin]
    · simp [flipSpin, hj]
  have ham_hm : ∀ z : SpinConfig N,
      (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) * ((f z - f (flipSpin z i)) ^ 2 / 2) ≤
      ((μ z + μ (flipSpin z i)) / 4) * ((f z - f (flipSpin z i)) ^ 2 / 2) := by
    intro z
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hpos : 0 < μ z + μ (flipSpin z i) := add_pos (hμ z) (hμ (flipSpin z i))
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [sq_nonneg (μ z - μ (flipSpin z i))]
  calc ∑ z : SpinConfig N,
        (μ z * μ (flipSpin z i) / (μ z + μ (flipSpin z i))) * ((f z - f (flipSpin z i)) ^ 2 / 2)
      ≤ ∑ z : SpinConfig N,
        ((μ z + μ (flipSpin z i)) / 4) * ((f z - f (flipSpin z i)) ^ 2 / 2) :=
        Finset.sum_le_sum fun z _ ↦ ham_hm z
    _ = ∑ z : SpinConfig N,
        (μ z * ((f z - f (flipSpin z i)) / 2) ^ 2 / 2 +
         μ (flipSpin z i) * ((f (flipSpin z i) - f z) / 2) ^ 2 / 2) := by
        apply Finset.sum_congr rfl; intro z _; ring
    _ = (∑ z : SpinConfig N, μ z * ((f z - f (flipSpin z i)) / 2) ^ 2 / 2) +
        (∑ z : SpinConfig N, μ (flipSpin z i) * ((f (flipSpin z i) - f z) / 2) ^ 2 / 2) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ z : SpinConfig N, μ z * ((f z - f (flipSpin z i)) / 2) ^ 2 := by
        have hsym : ∑ z : SpinConfig N,
            μ (flipSpin z i) * ((f (flipSpin z i) - f z) / 2) ^ 2 / 2 =
            ∑ z : SpinConfig N, μ z * ((f z - f (flipSpin z i)) / 2) ^ 2 / 2 := by
          refine Finset.sum_bij (fun z _ ↦ flipSpin z i) (fun _ _ ↦ Finset.mem_univ _)
            (fun z₁ _ z₂ _ h ↦ by have := congrArg (fun w ↦ flipSpin w i) h; rwa [hinv, hinv] at this)
            (fun z _ ↦ ⟨flipSpin z i, Finset.mem_univ _, hinv z⟩)
            (fun z _ ↦ by rw [hinv])
        rw [hsym, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro z _; ring

end ConcreteIsingSetup

section ConcreteReversePoincare

lemma siteChi_flip_diff (h : ℝ) (b : Bool) :
    ((siteChi h b - siteChi h (!b)) / 2) ^ 2 = (1 - (Real.tanh h) ^ 2)⁻¹ := by
  have hpos := one_sub_tanh_sq_pos h
  unfold siteChi
  cases b <;> simp only [Bool.not_true, Bool.not_false, spinVal, ↓reduceIte, Bool.false_eq_true]
  · rw [← sub_div, show (-1 - Real.tanh h) - (1 - Real.tanh h) = -2 by ring,
      neg_div, neg_sq, div_div,
      show Real.sqrt (1 - (Real.tanh h) ^ 2) * 2 = 2 * Real.sqrt (1 - (Real.tanh h) ^ 2) by ring,
      mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), one_div, inv_pow, Real.sq_sqrt hpos.le]
  · rw [← sub_div, show (1 - Real.tanh h) - (-1 - Real.tanh h) = 2 by ring,
      div_div, show Real.sqrt (1 - (Real.tanh h) ^ 2) * 2 = 2 * Real.sqrt (1 - (Real.tanh h) ^ 2) by ring,
      mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), one_div, inv_pow, Real.sq_sqrt hpos.le]

theorem prodBernoulli_discrete_grad_eq {N : ℕ} (h : Fin N → ℝ)
    (fhat : Finset (Fin N) → ℝ) (i : Fin N) :
    let f : SpinConfig N → ℝ := fun z ↦ ∑ S : Finset (Fin N), fhat S * chiBasis h S z
    ∑ z : SpinConfig N, prodBernoulli h z * ((f z - f (flipSpin z i)) / 2) ^ 2 =
      (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2 := by
  intro f
  have hdiff : ∀ z : SpinConfig N,
      (f z - f (flipSpin z i)) / 2 =
        ((siteChi (h i) (z i) - siteChi (h i) (!(z i))) / 2) *
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
            fhat S * chiBasis h (S.erase i) z := by
    intro z
    simp only [f, ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
    rw [Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro S _
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      have h1 : chiBasis h S z = siteChi (h i) (z i) * chiBasis h (S.erase i) z := by
        unfold chiBasis; rw [← Finset.mul_prod_erase S _ hi]
      have h2 : chiBasis h S (flipSpin z i) =
          siteChi (h i) (!(z i)) * chiBasis h (S.erase i) z := by
        unfold chiBasis
        rw [← Finset.mul_prod_erase S _ hi]
        congr 1
        · simp [flipSpin]
        · apply Finset.prod_congr rfl; intro j hj
          simp [flipSpin, (Finset.mem_erase.mp hj).1]
      rw [h1, h2]; ring
    · rw [if_neg hi]
      have hsame : chiBasis h S (flipSpin z i) = chiBasis h S z := by
        unfold chiBasis
        apply Finset.prod_congr rfl; intro j hj
        have hji : j ≠ i := fun heq ↦ hi (heq ▸ hj)
        simp [flipSpin, hji]
      rw [hsame, sub_self, mul_zero, zero_div]
  have hsq : ∀ z : SpinConfig N,
      ((f z - f (flipSpin z i)) / 2) ^ 2 =
        (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
          (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
            fhat S * chiBasis h (S.erase i) z) ^ 2 := by
    intro z
    rw [hdiff z, mul_pow, siteChi_flip_diff]
  simp_rw [hsq, ← mul_assoc, mul_comm (prodBernoulli h _) ((1 - (Real.tanh (h i)) ^ 2)⁻¹),
    mul_assoc, ← Finset.mul_sum]
  congr 1
  have hexp : ∀ z : SpinConfig N,
      prodBernoulli h z *
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
          fhat S * chiBasis h (S.erase i) z) ^ 2 =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
        ∑ T ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
          (fhat S * fhat T) *
            (prodBernoulli h z * chiBasis h (S.erase i) z * chiBasis h (T.erase i) z) := by
    intro z
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro S _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro T _
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S hS
  rw [Finset.sum_comm]
  have hinner : ∀ T ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S),
      ∑ z : SpinConfig N,
        (fhat S * fhat T) *
          (prodBernoulli h z * chiBasis h (S.erase i) z * chiBasis h (T.erase i) z) =
      if S = T then (fhat S) ^ 2 else 0 := by
    intro T hT
    rw [← Finset.mul_sum, chiBasis_orthonormal]
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    have hiT : i ∈ T := (Finset.mem_filter.mp hT).2
    have heq : (S.erase i = T.erase i) ↔ (S = T) := by
      constructor
      · intro h; rw [← Finset.insert_erase hiS, ← Finset.insert_erase hiT, h]
      · intro h; rw [h]
    by_cases hST : S = T
    · subst hST; simp [sq]
    · rw [if_neg (fun h ↦ hST (heq.mp h)), if_neg hST, mul_zero]
  rw [Finset.sum_congr rfl hinner]
  simp [hS]

lemma chiBasis_mem_classicalDegreeSubspace {N : ℕ} (h : Fin N → ℝ)
    {k : ℕ} {S : Finset (Fin N)} (hS : S.card ≤ k) :
    chiBasis h S ∈ classicalDegreeSubspace N k := by
  have hgen : ∀ (S : Finset (Fin N)),
      chiBasis h S ∈ classicalDegreeSubspace N S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      apply Submodule.subset_span
      exact ⟨∅, le_rfl, by funext z; simp [chiBasis]⟩
    | insert a S ha ih =>
      have hfactor : chiBasis h (insert a S) =
          (1 / Real.sqrt (1 - (Real.tanh (h a)) ^ 2)) •
            (fun z ↦ spinVal (z a) * chiBasis h S z) +
          (-Real.tanh (h a) / Real.sqrt (1 - (Real.tanh (h a)) ^ 2)) •
            chiBasis h S := by
        funext z
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, chiBasis,
          Finset.prod_insert ha, siteChi]
        ring
      rw [hfactor, Finset.card_insert_of_notMem ha]
      apply Submodule.add_mem
      · apply Submodule.smul_mem
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ih
        · rintro g ⟨T, hT, rfl⟩
          by_cases haT : a ∈ T
          · have hsq : (fun z : SpinConfig N ↦ spinVal (z a) * ∏ i ∈ T, spinVal (z i)) =
                fun z ↦ ∏ i ∈ T.erase a, spinVal (z i) := by
              funext z
              rw [← Finset.mul_prod_erase T _ haT, ← mul_assoc]
              have : spinVal (z a) * spinVal (z a) = 1 := by cases z a <;> simp [spinVal]
              rw [this, one_mul]
            rw [hsq]
            apply Submodule.subset_span
            exact ⟨T.erase a, le_trans (Finset.card_erase_le) (by omega), rfl⟩
          · have hins : (fun z : SpinConfig N ↦ spinVal (z a) * ∏ i ∈ T, spinVal (z i)) =
                fun z ↦ ∏ i ∈ insert a T, spinVal (z i) := by
              funext z; rw [Finset.prod_insert haT]
            rw [hins]
            apply Submodule.subset_span
            exact ⟨insert a T, by rw [Finset.card_insert_of_notMem haT]; omega, rfl⟩
        · have : (fun z : SpinConfig N ↦ spinVal (z a) * (0 : SpinConfig N → ℝ) z) = 0 := by
            funext z; simp
          rw [this]; exact Submodule.zero_mem _
        · intro x y _ _ hx hy
          have : (fun z : SpinConfig N ↦ spinVal (z a) * (x + y) z) =
              (fun z ↦ spinVal (z a) * x z) + (fun z ↦ spinVal (z a) * y z) := by
            funext z; simp [mul_add]
          rw [this]; exact Submodule.add_mem _ hx hy
        · intro c x _ hx
          have : (fun z : SpinConfig N ↦ spinVal (z a) * (c • x) z) =
              c • (fun z ↦ spinVal (z a) * x z) := by
            funext z; simp [mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ _ hx
      · apply Submodule.smul_mem
        have hmono : classicalDegreeSubspace N S.card ≤ classicalDegreeSubspace N (S.card + 1) := by
          apply Submodule.span_le.mpr
          rintro g ⟨T, hT, rfl⟩
          exact Submodule.subset_span ⟨T, by omega, rfl⟩
        exact hmono ih
  have hmono : classicalDegreeSubspace N S.card ≤ classicalDegreeSubspace N k := by
    apply Submodule.span_le.mpr
    rintro g ⟨T, hT, rfl⟩
    exact Submodule.subset_span ⟨T, le_trans hT hS, rfl⟩
  exact hmono (hgen S)

theorem distSqDegree_prodBernoulli_eq {N : ℕ} (h : Fin N → ℝ)
    (fhat : Finset (Fin N) → ℝ) (k : ℕ) :
    let f : SpinConfig N → ℝ := fun z ↦ ∑ S : Finset (Fin N), fhat S * chiBasis h S z
    distSqDegree (prodBernoulli h) k f =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 := by
  intro f
  set g₀ : SpinConfig N → ℝ := fun z ↦
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ S.card ≤ k), fhat S * chiBasis h S z
  have hg₀_mem : g₀ ∈ classicalDegreeSubspace N k := by
    have hsum : g₀ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ S.card ≤ k),
        fhat S • chiBasis h S := by
      funext z; simp [g₀]
    rw [hsum]
    exact Submodule.sum_mem _ fun S hS ↦
      Submodule.smul_mem _ _ (chiBasis_mem_classicalDegreeSubspace h (Finset.mem_filter.mp hS).2)
  have hdiff_eq : ∀ z : SpinConfig N,
      f z - g₀ z = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card),
        fhat S * chiBasis h S z := by
    intro z
    have hpart := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset (Fin N) ↦ S.card ≤ k) (fun S ↦ fhat S * chiBasis h S z)).symm
    have hnot : Finset.univ.filter (fun S : Finset (Fin N) ↦ ¬ S.card ≤ k) =
        Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card) := by
      ext S; simp
    rw [hnot] at hpart
    dsimp only [f, g₀]
    linarith
  have hnorm_g₀ : ∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) ^ 2 =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 := by
    simp_rw [hdiff_eq]
    have hexp : ∀ z : SpinConfig N,
        prodBernoulli h z *
          (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card),
            fhat S * chiBasis h S z) ^ 2 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card),
          ∑ T ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card),
            (fhat S * fhat T) * (prodBernoulli h z * chiBasis h S z * chiBasis h T z) := by
      intro z
      rw [sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro S _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro T _
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S hS
    rw [Finset.sum_comm]
    have hinner : ∀ T ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card),
        ∑ z : SpinConfig N,
          (fhat S * fhat T) * (prodBernoulli h z * chiBasis h S z * chiBasis h T z) =
        if S = T then (fhat S) ^ 2 else 0 := by
      intro T _
      rw [← Finset.mul_sum, chiBasis_orthonormal]
      by_cases hST : S = T
      · subst hST; simp [sq]
      · rw [if_neg hST, if_neg hST, mul_zero]
    rw [Finset.sum_congr rfl hinner]
    simp [hS]
  apply le_antisymm
  · unfold distSqDegree
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨g, _, rfl⟩
      exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (prodBernoulli_pos h z).le (sq_nonneg _)
    · exact ⟨g₀, hg₀_mem, hnorm_g₀.symm⟩
  · unfold distSqDegree
    apply le_csInf
    · exact ⟨_, g₀, hg₀_mem, rfl⟩
    · rintro r ⟨g, hg, rfl⟩
      have horth : ∀ u ∈ classicalDegreeSubspace N k,
          ∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) * u z = 0 := by
        intro u hu
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨T, hT, rfl⟩
          simp_rw [hdiff_eq, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero; intro S hS
          have hSk : k < S.card := (Finset.mem_filter.mp hS).2
          have hex : ∃ i ∈ S, i ∉ T := by
            by_contra hall
            push Not at hall
            have hsub : S ⊆ T := fun i hi ↦ hall i hi
            have := Finset.card_le_card hsub
            omega
          rcases hex with ⟨i₀, hi₀S, hi₀T⟩
          have hfac : ∀ z : SpinConfig N,
              prodBernoulli h z * (fhat S * chiBasis h S z) * ∏ j ∈ T, spinVal (z j) =
              fhat S * ∏ j : Fin N,
                siteBernoulli (h j) (z j) *
                  (if j ∈ S then siteChi (h j) (z j) else 1) *
                  (if j ∈ T then spinVal (z j) else 1) := by
            intro z
            unfold prodBernoulli chiBasis
            have hprodS : (∏ i ∈ S, siteChi (h i) (z i)) =
                ∏ j : Fin N, if j ∈ S then siteChi (h j) (z j) else 1 := by
              rw [← Finset.prod_filter]; congr 1; ext j; simp
            have hprodT : (∏ j ∈ T, spinVal (z j)) =
                ∏ j : Fin N, if j ∈ T then spinVal (z j) else 1 := by
              rw [← Finset.prod_filter]; congr 1; ext j; simp
            rw [hprodS, hprodT, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            ring
          simp_rw [hfac, ← Finset.mul_sum]
          rw [← Fintype.prod_sum (fun (j : Fin N) (b : Bool) ↦
            siteBernoulli (h j) b *
              (if j ∈ S then siteChi (h j) b else 1) *
              (if j ∈ T then spinVal b else 1))]
          have hzero : (∏ j : Fin N, ∑ b : Bool,
              siteBernoulli (h j) b *
                (if j ∈ S then siteChi (h j) b else 1) *
                (if j ∈ T then spinVal b else 1)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ i₀)
            simp only [hi₀S, hi₀T, ↓reduceIte, mul_one]
            exact siteChi_mean (h i₀)
          rw [hzero, mul_zero]
        · simp
        · intro x y _ _ hx hy
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
        · intro c x _ hx
          simp only [Pi.smul_apply, smul_eq_mul]
          have : ∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) * (c * x z) =
              c * ∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) * x z := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          rw [this, hx, mul_zero]
      have hpyth : ∑ z : SpinConfig N, prodBernoulli h z * (f z - g z) ^ 2 =
          (∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) ^ 2) +
          (∑ z : SpinConfig N, prodBernoulli h z * (g₀ z - g z) ^ 2) := by
        have hcross : ∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) * (g₀ z - g z) = 0 :=
          horth (g₀ - g) (Submodule.sub_mem _ hg₀_mem hg)
        have hsplit : ∑ z : SpinConfig N, prodBernoulli h z * (f z - g z) ^ 2 =
            (∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) ^ 2) +
            2 * (∑ z : SpinConfig N, prodBernoulli h z * (f z - g₀ z) * (g₀ z - g z)) +
            (∑ z : SpinConfig N, prodBernoulli h z * (g₀ z - g z) ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro z _; ring
        rw [hsplit, hcross]; ring
      rw [hpyth, hnorm_g₀]
      have hnn : 0 ≤ ∑ z : SpinConfig N, prodBernoulli h z * (g₀ z - g z) ^ 2 :=
        Finset.sum_nonneg fun z _ ↦ mul_nonneg (prodBernoulli_pos h z).le (sq_nonneg _)
      linarith

theorem prodBernoulli_discrete_grad_le_Q {N : ℕ} {Φmax : ℝ}
    (h : Fin N → ℝ) (hh : ∀ i, |h i| ≤ Φmax) (f : SpinConfig N → ℝ) :
    (∑ i : Fin N, ∑ z : SpinConfig N,
      prodBernoulli h z * ((f z - f (flipSpin z i)) / 2) ^ 2) ≤
    (Real.cosh Φmax) ^ 2 * degreeFiltrationQ (prodBernoulli h) f := by
  set fhat := bernoulliFourierCoeff h f
  have hf_eq : f = fun z ↦ ∑ S : Finset (Fin N), fhat S * chiBasis h S z := by
    funext z
    have hdelta : ∀ z₀ : SpinConfig N,
        ∑ S : Finset (Fin N), prodBernoulli h z₀ * chiBasis h S z₀ * chiBasis h S z =
        if z₀ = z then 1 else 0 := by
      intro z₀
      have hfac : ∑ S : Finset (Fin N), prodBernoulli h z₀ * chiBasis h S z₀ * chiBasis h S z =
          ∏ i : Fin N, siteBernoulli (h i) (z₀ i) * (1 + siteChi (h i) (z₀ i) * siteChi (h i) (z i)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_one_add]
        have hpow : (Finset.univ : Finset (Fin N)).powerset = Finset.univ := by
          ext S; simp
        rw [hpow, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        unfold prodBernoulli chiBasis
        rw [Finset.prod_mul_distrib, mul_assoc]
      rw [hfac]
      have hsite : ∀ i : Fin N,
          siteBernoulli (h i) (z₀ i) * (1 + siteChi (h i) (z₀ i) * siteChi (h i) (z i)) =
          if z₀ i = z i then 1 else 0 := by
        intro i
        have hpos := one_sub_tanh_sq_pos (h i)
        have htanh : Real.tanh (h i) = Real.sinh (h i) / Real.cosh (h i) := Real.tanh_eq_sinh_div_cosh (h i)
        unfold siteBernoulli siteChi
        have hsq : Real.sqrt (1 - (Real.tanh (h i)) ^ 2) * Real.sqrt (1 - (Real.tanh (h i)) ^ 2) =
            1 - (Real.tanh (h i)) ^ 2 := Real.mul_self_sqrt hpos.le
        cases hb1 : z₀ i <;> cases hb2 : z i <;>
          simp only [spinVal, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
        · have hnum : 1 + (-1 - Real.tanh (h i)) / Real.sqrt (1 - (Real.tanh (h i)) ^ 2) *
              ((-1 - Real.tanh (h i)) / Real.sqrt (1 - (Real.tanh (h i)) ^ 2)) =
              2 / (1 - Real.tanh (h i)) := by
            rw [div_mul_div_comm, hsq]
            have hne : 1 - Real.tanh (h i) ≠ 0 := by nlinarith [sq_nonneg (Real.tanh (h i))]
            field_simp [hpos.ne', hne]; ring
          rw [hnum, mul_neg, mul_one, htanh, Real.sinh_eq, Real.cosh_eq]
          have he1 := Real.exp_pos (h i)
          have he2 := Real.exp_pos (-(h i))
          have hden : (Real.exp (h i) + Real.exp (-(h i))) ≠ 0 := (add_pos he1 he2).ne'
          field_simp [hden, he2.ne']
          ring
        · rw [div_mul_div_comm, hsq]
          field_simp [hpos.ne']
          ring
        · rw [div_mul_div_comm, hsq]
          field_simp [hpos.ne']
          ring
        · have hnum : 1 + (1 - Real.tanh (h i)) / Real.sqrt (1 - (Real.tanh (h i)) ^ 2) *
              ((1 - Real.tanh (h i)) / Real.sqrt (1 - (Real.tanh (h i)) ^ 2)) =
              2 / (1 + Real.tanh (h i)) := by
            rw [div_mul_div_comm, hsq]
            have hne : 1 + Real.tanh (h i) ≠ 0 := by nlinarith [sq_nonneg (Real.tanh (h i))]
            field_simp [hpos.ne', hne]; ring
          rw [hnum, mul_one, htanh, Real.sinh_eq, Real.cosh_eq]
          have he1 := Real.exp_pos (h i)
          have he2 := Real.exp_pos (-(h i))
          have hden : (Real.exp (h i) + Real.exp (-(h i))) ≠ 0 := (add_pos he1 he2).ne'
          field_simp [hden, he1.ne']
          ring
      simp_rw [hsite]
      by_cases hzz : z₀ = z
      · subst hzz; simp
      · rw [if_neg hzz]
        have hex : ∃ i : Fin N, z₀ i ≠ z i := by
          by_contra hall; push Not at hall; exact hzz (funext hall)
        rcases hex with ⟨i₀, hi₀⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
    have hsum : ∑ S : Finset (Fin N), fhat S * chiBasis h S z =
        ∑ z₀ : SpinConfig N, f z₀ *
          (∑ S : Finset (Fin N), prodBernoulli h z₀ * chiBasis h S z₀ * chiBasis h S z) := by
      unfold fhat bernoulliFourierCoeff
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z₀ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro S _
      ring
    rw [hsum]
    simp only [hdelta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  conv_lhs => rw [hf_eq]
  conv_rhs => rw [hf_eq]
  simp_rw [prodBernoulli_discrete_grad_eq h fhat]
  unfold degreeFiltrationQ
  simp_rw [distSqDegree_prodBernoulli_eq h fhat]
  exact prop_8_3_product_bernoulli_reverse_poincare h hh fhat

/-- **Proposition 8.3 (Full Concrete Classical Ising / Convex-Mixture Reverse Poincaré, Eq. 8.4)**:
For ANY convex mixture `μ z = ∑ ξ, w ξ * prodBernoulli (h ξ) z` (`w ξ ≥ 0`, `∀ ξ i, |h ξ i| ≤ Φmax`,
`μ z > 0`), EVERY function `f : SpinConfig N → ℝ` obeys:
`glauberDirichlet μ f ≤ (Real.cosh Φmax) ^ 2 * degreeFiltrationQ μ f`. -/
theorem prop_8_3_concrete_convex_mixture_reverse_poincare {N : ℕ} {Ξ : Type*} [Fintype Ξ]
    {Φmax : ℝ} (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (h : Ξ → Fin N → ℝ) (hh : ∀ ξ i, |h ξ i| ≤ Φmax)
    (hμ_pos : ∀ z : SpinConfig N, 0 < ∑ ξ : Ξ, w ξ * prodBernoulli (h ξ) z)
    (f : SpinConfig N → ℝ) :
    let μ : SpinConfig N → ℝ := fun z ↦ ∑ ξ : Ξ, w ξ * prodBernoulli (h ξ) z
    glauberDirichlet μ f ≤ (Real.cosh Φmax) ^ 2 * degreeFiltrationQ μ f := by
  intro μ
  have h1 := glauberDirichlet_le_discrete_grad_avg μ hμ_pos f
  have hswap : (∑ i : Fin N, ∑ z : SpinConfig N, μ z * ((f z - f (flipSpin z i)) / 2) ^ 2) =
      ∑ ξ : Ξ, w ξ * (∑ i : Fin N, ∑ z : SpinConfig N,
        prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2) := by
    simp only [μ, Finset.sum_mul, mul_assoc]
    calc ∑ i : Fin N, ∑ z : SpinConfig N,
          ∑ ξ : Ξ, w ξ * (prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2)
        = ∑ i : Fin N, ∑ ξ : Ξ, ∑ z : SpinConfig N,
          w ξ * (prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2) := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
      _ = ∑ ξ : Ξ, ∑ i : Fin N, ∑ z : SpinConfig N,
          w ξ * (prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2) := Finset.sum_comm
      _ = ∑ ξ : Ξ, w ξ * (∑ i : Fin N, ∑ z : SpinConfig N,
          prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2) := by
          apply Finset.sum_congr rfl; intro ξ _
          simp_rw [← Finset.mul_sum]
  have h2 : ∑ ξ : Ξ, w ξ * (∑ i : Fin N, ∑ z : SpinConfig N,
        prodBernoulli (h ξ) z * ((f z - f (flipSpin z i)) / 2) ^ 2) ≤
      (Real.cosh Φmax) ^ 2 * ∑ ξ : Ξ, w ξ * degreeFiltrationQ (prodBernoulli (h ξ)) f := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro ξ _
    have hle := prodBernoulli_discrete_grad_le_Q (h ξ) (hh ξ) f
    have := mul_le_mul_of_nonneg_left hle (hw ξ)
    linarith
  have h3 := degreeFiltrationQ_convex_mixture_ge w hw (fun ξ ↦ prodBernoulli (h ξ))
    (fun ξ z ↦ (prodBernoulli_pos (h ξ) z).le) f
  have h4 : (Real.cosh Φmax) ^ 2 * ∑ ξ : Ξ, w ξ * degreeFiltrationQ (prodBernoulli (h ξ)) f ≤
      (Real.cosh Φmax) ^ 2 * degreeFiltrationQ μ f :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  linarith

end ConcreteReversePoincare

end KrylovChaos
