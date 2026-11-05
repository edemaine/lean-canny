/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
/-! # Literal perturbation and target coefficients of the tilted system

The coefficient ring is retained. The tilt occurs in perturbation degree one,
and the diagonal coercive term in degree two.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParametricTiltedCoerciveCoefficient
open MvPolynomial
open scoped Classical
variable {R : Type*} [CommRing R] {n : ℕ}

private theorem scalar (a : R) (s t : ℕ) :
    (((Polynomial.C (Polynomial.C a) : Polynomial (Polynomial R)).coeff s).coeff t) =
      if s = 0 ∧ t = 0 then a else 0 := by
  by_cases hs : s = 0
  · subst s; simp [Polynomial.coeff_C]
  · simp only [Polynomial.coeff_C_of_ne_zero hs, Polynomial.coeff_zero, hs, false_and, ite_false]

private theorem parameter (k : ℕ) (a : R) (s t : ℕ) :
    (((Polynomial.monomial k (Polynomial.C a) : Polynomial (Polynomial R)).coeff s).coeff t) =
      if s = k ∧ t = 0 then a else 0 := by
  by_cases hs : s = k
  · subst s; simp only [Polynomial.coeff_monomial_same, Polynomial.coeff_C, true_and]
  · simp only [Polynomial.coeff_monomial_of_ne _ hs, Polynomial.coeff_zero, hs, false_and, ite_false]

theorem gradient (q : MvPolynomial (Fin n) R) (D : ℕ) (u j : Fin n)
    (e : Option (Fin n) →₀ ℕ) (s t : ℕ) :
    ((((TiltedCoerciveCriticalFibers.nativeSystem
      (q.map ParametricTiltedCoerciveEliminant.constants) D u Polynomial.X
      (Polynomial.C Polynomial.X) u (some j)).coeff e).coeff s).coeff t) =
      (if Finsupp.weight (WeightedHomogenization.weights (fun _ : Fin n => 1)) e = 2 * D + 1
        then (if s = 0 ∧ t = 0 then (pderiv j (q ^ 2)).coeff e.some else 0) -
          (if j = u then (if e.some = 0 then (if s = 1 ∧ t = 0 then 1 else 0) else 0) else 0)
        else 0) +
      (if Finsupp.single (some j) (2 * D + 1) = e
        then (if s = 2 ∧ t = 0 then ((2 * D + 2 : ℕ) : R) else 0) else 0) := by
  have hg : pderiv j ((q.map ParametricTiltedCoerciveEliminant.constants) ^ 2) =
      (pderiv j (q ^ 2)).map ParametricTiltedCoerciveEliminant.constants := by
    rw [← map_pow, ← pderiv_map]
  have hz : (((2 * D + 2 : ℕ) : Polynomial (Polynomial R)) * Polynomial.X ^ 2) =
      Polynomial.monomial 2 (Polynomial.C ((2 * D + 2 : ℕ) : R)) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_natCast]
  rw [TiltedCoerciveCriticalFibers.nativeSystem, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, Polynomial.coeff_add, Polynomial.coeff_add]
  apply congrArg₂ (· + ·)
  · rw [WeightedHomogenization.coefficient]
    by_cases hw : Finsupp.weight (WeightedHomogenization.weights (fun _ : Fin n => 1)) e = 2 * D + 1
    · rw [ite_eq_left hw, ite_eq_left hw, TiltedCoerciveCriticalFibers.lower, hg,
        AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Polynomial.coeff_sub,
        Polynomial.coeff_sub, MvPolynomial.coeff_map]
      apply congrArg₂ (· - ·)
      · exact scalar _ s t
      · by_cases hj : j = u
        · rw [TiltedCoerciveCriticalFibers.tilt, ite_eq_left hj, ite_eq_left hj, coeff_C]
          by_cases he : e.some = 0
          · rw [ite_eq_left he, ite_eq_left he.symm]
            have HX : (Polynomial.X : Polynomial (Polynomial R)) =
                Polynomial.monomial 1 (Polynomial.C (1 : R)) := by
              rw [map_one, Polynomial.monomial_one_one_eq_X]
            rw [HX]
            exact parameter 1 1 s t
          · rw [ite_eq_right he, ite_eq_right (Ne.symm he)]
            simp only [Polynomial.coeff_zero]
        · rw [TiltedCoerciveCriticalFibers.tilt, ite_eq_right hj, ite_eq_right hj]
          simp only [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Polynomial.coeff_zero]
    · rw [ite_eq_right hw, ite_eq_right hw]
      simp only [Polynomial.coeff_zero]
  · rw [MvPolynomial.coeff_monomial, hz]
    by_cases he : Finsupp.single (some j) (2 * D + 1) = e
    · rw [ite_eq_left he, ite_eq_left he]
      exact parameter 2 _ s t
    · rw [ite_eq_right he, ite_eq_right he]
      simp only [Polynomial.coeff_zero]


theorem coordinate (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n)
    (e : Option (Fin n) →₀ ℕ) (s t : ℕ) :
    ((((TiltedCoerciveCriticalFibers.nativeSystem
      (q.map ParametricTiltedCoerciveEliminant.constants) D u Polynomial.X
      (Polynomial.C Polynomial.X) i none).coeff e).coeff s).coeff t) =
      (if s = 0 ∧ t = 1 ∧ e = Finsupp.single none 1 then (1 : R) else 0) -
      (if s = 0 ∧ t = 0 ∧ e = Finsupp.single (some i) 1 then (1 : R) else 0) := by
  change (((C (Polynomial.C (Polynomial.X : Polynomial R)) * monomial (Finsupp.single none 1) 1 -
    monomial (Finsupp.single (some i) 1) 1 :
      MvPolynomial (Option (Fin n)) (Polynomial (Polynomial R))).coeff e).coeff s).coeff t = _
  rw [C_mul_monomial, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    coeff_monomial, coeff_monomial]
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
  apply congrArg₂ (· - ·)
  · by_cases he : Finsupp.single (none : Option (Fin n)) 1 = e
    · rw [ite_eq_left he]
      by_cases hs : s = 0
      · subst s
        simp only [Polynomial.coeff_C_zero, Polynomial.coeff_X, true_and]
        simp only [← he, eq_self, and_true, eq_comm]
      · rw [Polynomial.coeff_C_of_ne_zero hs, Polynomial.coeff_zero]
        simp only [hs, false_and, ite_false]
    · rw [ite_eq_right he]
      simp only [Polynomial.coeff_zero, Ne.symm he, and_false, ite_false]
  · by_cases he : Finsupp.single (some i) 1 = e
    · rw [ite_eq_left he]
      change (((Polynomial.C (Polynomial.C (1 : R))).coeff s).coeff t) = _
      rw [scalar]
      simp only [← he, eq_self, and_true]
    · rw [ite_eq_right he]
      simp only [Polynomial.coeff_zero, Ne.symm he, and_false, ite_false]


end LeanCanny.Algebra.ParametricTiltedCoerciveCoefficient
