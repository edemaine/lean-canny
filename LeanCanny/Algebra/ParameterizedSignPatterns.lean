/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ParameterizedTarski
public import LeanCanny.Algebra.SignQueryBounds

/-! # A common interval of stability for finite root-sign patterns

The finite family of ternary product queries determines every sign-pattern
count. A maximum of their polynomial-test budgets gives one dyadic interval,
independent of the requested pattern. These symbolic budgets still need FP
upper bounds from source metadata before this supplies a space algorithm for
the infinitesimal root-sign problem.
-/

@[expose] public section

namespace LeanCanny.Algebra.ParameterTarski
open Polynomial RootSignQueries
open scoped BigOperators Classical

noncomputable def patternBudget {J : Type*} [Fintype J]
    (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) : ℕ := by
  classical
  exact Finset.univ.sup fun e : J → Fin 3 => budget p (queryPolynomial Q e)

theorem pattern_bounded {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (e : J → Fin 3) :
    Bounded p (queryPolynomial Q e) (patternBudget p Q) := by
  classical
  apply (budget_bounded p (queryPolynomial Q e)).mono
  unfold patternBudget
  exact Finset.le_sup (f := fun e : J → Fin 3 => budget p (queryPolynomial Q e)) (Finset.mem_univ e)

noncomputable def scaledValue {J : Type*} [Fintype J]
    (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType) : ℤ :=
  ∑ e : J → Fin 3, patternWeight σ e * value p (queryPolynomial Q e)

theorem scaled_eq_value_of_bounded {J : Type*} [Fintype J]
    (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType) (b s : ℕ)
    (h : ∀ e : J → Fin 3, Bounded p (queryPolynomial Q e) b) (hs : b < s)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic s) :
    scaledRootCount (p.map (evalHom x)) (fun i => (Q i).map (evalHom x)) σ = scaledValue p Q σ := by
  classical
  unfold scaledRootCount scaledValue
  apply Finset.sum_congr rfl
  intro e _
  rw [← map_queryPolynomial]
  exact congrArg (patternWeight σ e * ·) (query_eq_value p (queryPolynomial Q e) b s (h e) hs x hx hxs)

theorem scaled_eq_value {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    scaledRootCount (p.map (evalHom x)) (fun i => (Q i).map (evalHom x)) σ = scaledValue p Q σ :=
  scaled_eq_value_of_bounded p Q σ _ _ (pattern_bounded p Q) (Nat.lt_succ_self _) x hx hxs

theorem rootCount_eq_reference {J : Type*} [Fintype J]
    (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType) (b s : ℕ)
    (h : ∀ e : J → Fin 3, Bounded p (queryPolynomial Q e) b) (hs : b < s)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic s) :
    signCount (p.map (evalHom x)).roots.toFinset (fun i => (Q i).map (evalHom x)) σ =
      signCount (p.map (evalHom (InfinitesimalSign.dyadic (patternBudget p Q + 1)))).roots.toFinset
        (fun i => (Q i).map (evalHom (InfinitesimalSign.dyadic (patternBudget p Q + 1)))) σ := by
  have he := (scaled_eq_value_of_bounded p Q σ b s h hs x hx hxs).trans
    (scaled_eq_value p Q σ _ (InfinitesimalSign.dyadic_pos _) le_rfl).symm
  rw [scaledRootCount_eq, scaledRootCount_eq] at he
  exact Int.natCast_inj.mp (mul_left_cancel₀ (pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0)) he)

theorem scaled_stable {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1))
    (hys : y ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    scaledRootCount (p.map (evalHom x)) (fun i => (Q i).map (evalHom x)) σ =
      scaledRootCount (p.map (evalHom y)) (fun i => (Q i).map (evalHom y)) σ :=
  (scaled_eq_value p Q σ x hx hxs).trans (scaled_eq_value p Q σ y hy hys).symm

/-- Every pattern has the same number of distinct roots throughout a common
interval. The zero root polynomial follows the finite-root convention. -/
theorem rootCount_stable {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1))
    (hys : y ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    signCount (p.map (evalHom x)).roots.toFinset (fun i => (Q i).map (evalHom x)) σ =
      signCount (p.map (evalHom y)).roots.toFinset (fun i => (Q i).map (evalHom y)) σ := by
  have h := scaled_stable p Q σ x y hx hy hxs hys
  rw [scaledRootCount_eq, scaledRootCount_eq] at h
  exact Int.natCast_inj.mp (mul_left_cancel₀ (pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0)) h)

theorem rootCount_eq_dyadic {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (σ : J → SignType)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    signCount (p.map (evalHom x)).roots.toFinset (fun i => (Q i).map (evalHom x)) σ =
      signCount (p.map (evalHom (InfinitesimalSign.dyadic (patternBudget p Q + 1)))).roots.toFinset
        (fun i => (Q i).map (evalHom (InfinitesimalSign.dyadic (patternBudget p Q + 1)))) σ :=
  rootCount_stable p Q σ _ _ hx (InfinitesimalSign.dyadic_pos _) hxs le_rfl

theorem map_ne_zero_on_interval {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (hp : p ≠ 0)
    (Q : J → (ℤ[X])[X]) (x : ℝ) (hx : 0 < x)
    (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) : p.map (evalHom x) ≠ 0 := by
  have hm := (pattern_bounded p Q (fun _ => 0)).head
  have he := InfinitesimalSign.integer_sign_eval_le_dyadic p.leadingCoeff _ _ hm (Nat.lt_succ_self _) x hx hxs
  have ht : p.leadingCoeff.trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.mpr (leadingCoeff_ne_zero.mpr hp)
  intro hz
  have hc := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hz
  rw [coeff_map, coeff_natDegree, coeff_zero] at hc
  change SignType.sign (evalHom x p.leadingCoeff) = _ at he
  rw [hc, sign_zero] at he
  exact ht (sign_eq_zero_iff.mp he.symm)

/-- For a nonzero symbolic root polynomial, realizability itself is constant.
This excludes the zero polynomial's infinite real zero set. -/
theorem realizable_stable {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (hp : p ≠ 0)
    (Q : J → (ℤ[X])[X]) (σ : J → SignType) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1))
    (hys : y ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    (∃ a : ℝ, (p.map (evalHom x)).eval a = 0 ∧
      ∀ i, SignType.sign (((Q i).map (evalHom x)).eval a) = σ i) ↔
    (∃ a : ℝ, (p.map (evalHom y)).eval a = 0 ∧
      ∀ i, SignType.sign (((Q i).map (evalHom y)).eval a) = σ i) := by
  rw [← root_signCount_pos _ (map_ne_zero_on_interval p hp Q x hx hxs),
    ← root_signCount_pos _ (map_ne_zero_on_interval p hp Q y hy hys), rootCount_stable p Q σ x y hx hy hxs hys]

end LeanCanny.Algebra.ParameterTarski
