/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialCalculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences

/-! # Bounded critical samples of a coercive polynomial regularization

For a polynomial with a real root, minimizing its square plus a positive even
power penalty gives critical samples in one fixed compact set. Along every
positive parameter sequence tending to zero, these samples have a convergent
subsequence whose limit is a root of the original polynomial. No degree or
coefficient estimate is assumed; the only geometric bound uses the given root.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoercivePolynomialSampling
open scoped Classical BigOperators Topology
open Filter Set MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def penalty (D : ℕ) (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ (2 * D + 2)

lemma power_nonneg (D : ℕ) (t : ℝ) : 0 ≤ t ^ (2 * D + 2) := by
  have he : Even (2 * D + 2) := ⟨D + 1, by omega⟩
  exact he.pow_nonneg t

lemma penalty_nonneg (D : ℕ) (x : Fin n → ℝ) : 0 ≤ penalty D x :=
  Finset.sum_nonneg fun _ _ => power_nonneg D _

lemma coordinate_le_penalty (D : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ penalty D x + 1 := by
  by_cases hi : |x i| ≤ 1
  · linarith [penalty_nonneg D x]
  · have hp : |x i| ≤ |x i| ^ (2 * D + 2) :=
      le_self_pow₀ (le_of_not_ge hi) (by omega)
    have he : |x i| ^ (2 * D + 2) = x i ^ (2 * D + 2) := by
      rw [← abs_pow, abs_of_nonneg (power_nonneg D _)]
    rw [he] at hp
    have hs : x i ^ (2 * D + 2) ≤ penalty D x :=
      Finset.single_le_sum (fun _ _ => power_nonneg D _) (Finset.mem_univ i)
    linarith

lemma continuous_penalty (D : ℕ) : Continuous (penalty (n := n) D) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).pow _

/-- The penalty sublevel is compact, including in dimension zero. -/
theorem isCompact_sublevel (D : ℕ) (P : ℝ) : IsCompact {x : Fin n → ℝ | penalty D x ≤ P} := by
  have hc : IsClosed {x : Fin n → ℝ | penalty D x ≤ P} :=
    isClosed_le (continuous_penalty D) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin n => -(P + 1)) (fun _ => P + 1))).of_isClosed_subset hc
  intro x hx
  change penalty D x ≤ P at hx
  constructor <;> intro i
  · have h : |x i| ≤ P + 1 := by linarith [coordinate_le_penalty D x i]
    exact (abs_le.mp h).1
  · have h : |x i| ≤ P + 1 := by linarith [coordinate_le_penalty D x i]
    exact (abs_le.mp h).2

noncomputable def regularization (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (s : ℝ) :
    MvPolynomial (Fin n) ℝ := q ^ 2 + C s * ∑ i : Fin n, X i ^ (2 * D + 2)

noncomputable def objective (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (s : ℝ)
    (x : Fin n → ℝ) : ℝ := (eval x q) ^ 2 + s * penalty D x

lemma eval_regularization (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (s : ℝ) (x : Fin n → ℝ) :
    eval x (regularization q D s) = objective q D s x := by
  simp [regularization, objective, penalty]

lemma continuous_objective (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (s : ℝ) :
    Continuous (objective q D s) :=
  ((MvPolynomial.continuous_eval q).pow 2).add (continuous_const.mul (continuous_penalty D))

/-- A global minimum exists in the penalty sublevel determined by a given root. -/
theorem exists_minimizer (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : eval x0 q = 0) (s : ℝ) (hs : 0 < s) :
    ∃ y : Fin n → ℝ, penalty D y ≤ penalty D x0 ∧ IsMinOn (objective q D s) univ y := by
  obtain ⟨y, hy, hmin⟩ := (isCompact_sublevel (n := n) D (penalty D x0)).exists_isMinOn
    ⟨x0, show penalty D x0 ≤ penalty D x0 from le_rfl⟩ (continuous_objective q D s).continuousOn
  refine ⟨y, hy, ?_⟩
  intro x _hx
  by_cases hx : penalty D x ≤ penalty D x0
  · exact hmin hx
  · have h0 := hmin (show x0 ∈ {x : Fin n → ℝ | penalty D x ≤ penalty D x0} by
      change penalty D x0 ≤ penalty D x0
      exact le_rfl)
    have hp : s * penalty D x0 ≤ s * penalty D x :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hx) hs.le
    change objective q D s y ≤ objective q D s x0 at h0
    simp only [objective, hroot, zero_pow (by decide : 2 ≠ 0), zero_add] at h0
    exact h0.trans (hp.trans (le_add_of_nonneg_left (sq_nonneg _)))

/-- Every global minimizer is a critical point of the actual regularized polynomial. -/
theorem critical_of_minimizer (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (s : ℝ)
    (y : Fin n → ℝ) (hy : IsMinOn (objective q D s) univ y) :
    ∀ i, eval y (pderiv i (regularization q D s)) = 0 := by
  have hm : IsLocalMin (fun x => eval x (regularization q D s)) y := by
    simpa only [eval_regularization] using hy.isLocalMin (Filter.univ_mem)
  exact (PolynomialCalculus.critical_iff (RingHom.id ℝ) (regularization q D s) y).mp hm.fderiv_eq_zero

/-- Comparing a minimum with the original root gives the quantitative residual
bound and the uniform penalty bound directly. -/
theorem minimizer_bounds (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : eval x0 q = 0) (s : ℝ) (hs : 0 < s)
    (y : Fin n → ℝ) (hy : IsMinOn (objective q D s) univ y) :
    penalty D y ≤ penalty D x0 ∧ (eval y q) ^ 2 ≤ s * penalty D x0 := by
  have h := hy (show x0 ∈ (univ : Set (Fin n → ℝ)) from mem_univ _)
  change objective q D s y ≤ objective q D s x0 at h
  simp only [objective, hroot, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  constructor
  · have hm : s * penalty D y ≤ s * penalty D x0 := (le_add_of_nonneg_left (sq_nonneg _)).trans h
    exact (mul_le_mul_iff_right₀ hs).mp hm
  · exact (le_add_of_nonneg_right (mul_nonneg hs.le (penalty_nonneg D y))).trans h

/-- Every positive parameter sequence tending to zero admits bounded critical
minimizers and a convergent subsequence with a root as its limit. -/
theorem exists_minimizers_subsequence (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : eval x0 q = 0)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Fin n → ℝ) (φ : ℕ → ℕ),
      (∀ k, IsMinOn (objective q D (s k)) univ (y k)) ∧
      (∀ k i, eval (y k) (pderiv i (regularization q D (s k))) = 0) ∧
      (∀ k, penalty D (y k) ≤ penalty D x0) ∧
      StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 a) ∧
      penalty D a ≤ penalty D x0 ∧ eval a q = 0 := by
  choose y hy hmin using fun k => exists_minimizer q D x0 hroot (s k) (hs k)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_sublevel (n := n) D (penalty D x0)).tendsto_subseq hy
  refine ⟨y, a, φ, hmin, fun k => critical_of_minimizer q D (s k) (y k) (hmin k),
    hy, hφ, hlim, ha, ?_⟩
  have hq : Tendsto (fun k => (eval (y (φ k)) q) ^ 2) atTop (𝓝 ((eval a q) ^ 2)) :=
    ((MvPolynomial.continuous_eval q).continuousAt.tendsto.comp hlim).pow 2
  have hz : Tendsto (fun k => s (φ k) * penalty D x0) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using (hs0.comp hφ.tendsto_atTop).mul_const (penalty D x0)
  have hle : (eval a q) ^ 2 ≤ 0 := le_of_tendsto_of_tendsto hq hz (Eventually.of_forall fun k =>
    (minimizer_bounds q D x0 hroot (s (φ k)) (hs (φ k)) (y (φ k)) (hmin (φ k))).2)
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))


/-- Concrete critical samples for `s_k = 1 / (k+1)`. Their entire sequence has
a coordinate bound determined by the given root; a subsequence converges to a
root of the original polynomial. -/
theorem exists_critical_samples (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : eval x0 q = 0) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Fin n → ℝ) (φ : ℕ → ℕ),
      (∀ k : ℕ, IsMinOn (objective q D (1 / ((k : ℝ) + 1))) univ (y k)) ∧
      (∀ k i, eval (y k) (pderiv i (regularization q D (1 / ((k : ℝ) + 1)))) = 0) ∧
      (∀ k, penalty D (y k) ≤ penalty D x0) ∧
      (∀ k i, |y k i| ≤ penalty D x0 + 1) ∧
      StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 a) ∧
      penalty D a ≤ penalty D x0 ∧ eval a q = 0 := by
  obtain ⟨y, a, φ, hm, hc, hb, hφ, hlim, ha, hq⟩ :=
    exists_minimizers_subsequence q D x0 hroot (fun k => 1 / ((k : ℝ) + 1))
      (fun k => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨y, a, φ, hm, hc, hb, ?_, hφ, hlim, ha, hq⟩
  intro k i
  linarith [coordinate_le_penalty D (y k) i, hb k]


/-- A simultaneous minimizer, critical-point, penalty, and residual certificate
for each positive regularization parameter. -/
theorem exists_critical_minimizer (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : eval x0 q = 0) (s : ℝ) (hs : 0 < s) :
    ∃ y : Fin n → ℝ, IsMinOn (objective q D s) univ y ∧
      (∀ i, eval y (pderiv i (regularization q D s)) = 0) ∧
      penalty D y ≤ penalty D x0 ∧ (eval y q) ^ 2 ≤ s * penalty D x0 := by
  obtain ⟨y, _, hm⟩ := exists_minimizer q D x0 hroot s hs
  exact ⟨y, hm, critical_of_minimizer q D s y hm, minimizer_bounds q D x0 hroot s hs y hm⟩

end LeanCanny.Geometry.CoercivePolynomialSampling
