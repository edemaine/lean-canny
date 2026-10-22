/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCriticalHomogenization

/-! # Actual bivariate coefficients of coercive homogeneous rows -/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveHomogeneousCoefficient
open MvPolynomial CoerciveCriticalHomogenization
open scoped Classical
variable {σ : Type*} [Fintype σ]

private theorem scalar_zero (a : ℤ) (s t : ℕ) :
    (((Polynomial.C (Polynomial.C a) : Coefficient).coeff s).coeff t) =
      if s = 0 ∧ t = 0 then a else 0 := by
  by_cases hs : s = 0
  · subst s
    rw [Polynomial.coeff_C_zero, Polynomial.coeff_C]
    simp
  · rw [Polynomial.coeff_C_of_ne_zero hs, Polynomial.coeff_zero]
    simp only [hs, false_and, ite_false]

private theorem scalar_s (a : ℤ) (s t : ℕ) :
    (((Polynomial.monomial 1 (Polynomial.C a) : Coefficient).coeff s).coeff t) =
      if s = 1 ∧ t = 0 then a else 0 := by
  by_cases hs : s = 1
  · subst s
    rw [Polynomial.coeff_monomial_same, Polynomial.coeff_C]
    simp
  · rw [Polynomial.coeff_monomial_of_ne (Polynomial.C a) hs, Polynomial.coeff_zero]
    simp only [hs, false_and, ite_false]

private theorem scalar_t (s t : ℕ) :
    (((Polynomial.C Polynomial.X : Coefficient).coeff s).coeff t) =
      if s = 0 ∧ t = 1 then (1 : ℤ) else 0 := by
  by_cases hs : s = 0
  · subst s
    rw [Polynomial.coeff_C_zero, Polynomial.coeff_X]
    simp only [eq_comm, true_and]
  · rw [Polynomial.coeff_C_of_ne_zero hs, Polynomial.coeff_zero]
    simp only [hs, false_and, ite_false]

private theorem nested_gradient (a z : ℤ) (P Q : Prop) [Decidable P] [Decidable Q] (s t : ℕ) :
    ((((if P then Polynomial.C (Polynomial.C a) else 0) +
      (if Q then Polynomial.monomial 1 (Polynomial.C z) else 0) : Coefficient).coeff s).coeff t) =
      (if s = 0 ∧ t = 0 ∧ P then a else 0) + (if s = 1 ∧ t = 0 ∧ Q then z else 0) := by
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  by_cases hp : P <;> by_cases hq : Q <;>
    simp only [hp, hq, ite_true, ite_false, and_true, and_false, scalar_zero, scalar_s,
      Polynomial.coeff_zero, add_zero, zero_add]

private theorem nested_coordinate (P Q : Prop) [Decidable P] [Decidable Q] (s t : ℕ) :
    ((((if P then Polynomial.C Polynomial.X else 0) -
      (if Q then Polynomial.C (Polynomial.C 1) else 0) : Coefficient).coeff s).coeff t) =
      (if s = 0 ∧ t = 1 ∧ P then (1 : ℤ) else 0) - (if s = 0 ∧ t = 0 ∧ Q then 1 else 0) := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
  by_cases hp : P <;> by_cases hq : Q <;>
    simp only [hp, hq, ite_true, ite_false, and_true, and_false, scalar_zero, scalar_t,
      Polynomial.coeff_zero, sub_zero, zero_sub, sub_self]

/-- The ordinary gradient coefficient occurs only at parameter bidegree (0,0),
and the diagonal leading power occurs only at (s,T)-bidegree (1,0). -/
theorem gradient (q : MvPolynomial σ ℤ) (D : ℕ) (coordinate j : σ)
    (e : Option σ →₀ ℕ) (s t : ℕ) :
    ((((system q D coordinate (some j)).coeff e).coeff s).coeff t) =
      (if s = 0 ∧ t = 0 ∧ Finsupp.weight (WeightedHomogenization.weights (fun _ : σ => 1)) e = 2 * D + 1
        then (pderiv j (q ^ 2)).coeff e.some else 0) +
      (if s = 1 ∧ t = 0 ∧ e = Finsupp.single (some j) (2 * D + 1)
        then ((2 * D + 2 : ℕ) : ℤ) else 0) := by
  have hg : pderiv j ((q.map (Int.castRingHom Coefficient)) ^ 2) =
      (pderiv j (q ^ 2)).map (Int.castRingHom Coefficient) := by
    rw [← map_pow, ← pderiv_map]
  rw [system, nativeSystem, hg, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, WeightedHomogenization.coefficient,
    MvPolynomial.coeff_map, MvPolynomial.coeff_monomial]
  let a : ℤ := (pderiv j (q ^ 2)).coeff e.some
  let z : ℤ := ((2 * D + 2 : ℕ) : ℤ)
  change (((if Finsupp.weight (WeightedHomogenization.weights (fun _ : σ => 1)) e = 2 * D + 1
    then (a : Coefficient) else 0) +
    (if Finsupp.single (some j) (2 * D + 1) = e then (z : Coefficient) * sParameter else 0)).coeff s).coeff t = _
  have ha : (a : Coefficient) = Polynomial.C (Polynomial.C a) := by simp
  have hz : (z : Coefficient) = Polynomial.C (Polynomial.C z) := by simp
  rw [ha, hz, sParameter, Polynomial.C_mul_X_eq_monomial]
  clear ha hz hg
  simpa only [a, z, eq_comm] using nested_gradient a z
    (Finsupp.weight (WeightedHomogenization.weights (fun _ : σ => 1)) e = 2 * D + 1)
    (Finsupp.single (some j) (2 * D + 1) = e) s t

omit [Fintype σ] in
/-- The coordinate row is T X₀−Xᵢ. -/
theorem coordinate (q : MvPolynomial σ ℤ) (D : ℕ) (i : σ)
    (e : Option σ →₀ ℕ) (s t : ℕ) :
    ((((system q D i none).coeff e).coeff s).coeff t) =
      (if s = 0 ∧ t = 1 ∧ e = Finsupp.single none 1 then (1 : ℤ) else 0) -
      (if s = 0 ∧ t = 0 ∧ e = Finsupp.single (some i) 1 then (1 : ℤ) else 0) := by
  rw [system, nativeSystem]
  change (((C tParameter * monomial (Finsupp.single none 1) 1 -
    monomial (Finsupp.single (some i) 1) 1 : MvPolynomial (Option σ) Coefficient).coeff e).coeff s).coeff t = _
  rw [C_mul_monomial, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_monomial]
  have hone : (1 : Coefficient) = Polynomial.C (Polynomial.C (1 : ℤ)) := by simp
  rw [hone, tParameter]
  clear hone
  simpa only [eq_comm] using nested_coordinate
    (Finsupp.single (none : Option σ) 1 = e) (Finsupp.single (some i) 1 = e) s t

end LeanCanny.Algebra.CoerciveHomogeneousCoefficient
