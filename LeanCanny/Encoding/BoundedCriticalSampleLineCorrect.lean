/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLineCoordinates

/-! # Exact line-coordinate semantics at actual sample parameters -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleLineCoordinates
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open scoped Classical

theorem denominator_nonzero (P : Readers) (f : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) (i : ℕ) :
    (((family P f false).polynomial (pair c r) i).map
      (ParameterTarski.evalHom (BoundedCriticalSampleLabels.parameter P c x).val)).eval t ≠ 0 := by
  by_cases hi : i = f (pair c r)
  · simp only [family, polynomial, hi, ite_true, freePolynomial, Bool.false_eq_true, ite_false,
      Polynomial.map_one, Polynomial.eval_one, ne_eq, one_ne_zero, not_false_eq_true]
  · simpa only [family, polynomial, hi, ite_false, Polynomial.map_C, Polynomial.eval_C, base,
      Bool.false_eq_true, ParameterTarski.evalHom, Polynomial.coe_eval₂RingHom] using
        BoundedCriticalSampleTermCoordinates.denominator_nonzero P c r x i

theorem coordinate_eval (P : Readers) (f : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) (i : ℕ) :
    (((family P f true).polynomial (pair c r) i).map
      (ParameterTarski.evalHom (BoundedCriticalSampleLabels.parameter P c x).val)).eval t /
      (((family P f false).polynomial (pair c r) i).map
        (ParameterTarski.evalHom (BoundedCriticalSampleLabels.parameter P c x).val)).eval t =
          Function.update (Formula.extend x.val) (f (pair c r)) t i := by
  by_cases hi : i = f (pair c r)
  · subst i
    simp only [family, polynomial, ite_true, freePolynomial, Bool.false_eq_true, ite_false,
      Polynomial.map_X, Polynomial.map_one, Polynomial.eval_X, Polynomial.eval_one, div_one, Function.update_self]
  · rw [Function.update_of_ne hi]
    simpa only [family, polynomial, hi, ite_false, Polynomial.map_C, Polynomial.eval_C, base,
      Bool.true_eq, Bool.false_eq_true, ite_true, ParameterTarski.evalHom, Polynomial.coe_eval₂RingHom] using
        BoundedCriticalSampleTermCoordinates.coordinate_eval P c r x i

theorem environment_sample (P : Readers) (f : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) :
    BivariateRationalTermReader.environment (family P f true) (family P f false) (pair c r)
      (BoundedCriticalSampleLabels.parameter P c x).val t =
        Function.update (Formula.extend x.val) (f (pair c r)) t := by
  funext i
  exact coordinate_eval P f c r x t i

theorem extend_update {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    Function.update (Formula.extend x) j.val t = Formula.extend (Function.update x j t) := by
  funext i
  by_cases hi : i < n
  · by_cases hj : i = j.val
    · subst i
      simp only [Function.update_self, Formula.extend, j.isLt, dite_true]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ j := fun h => hj (congrArg Fin.val h)
      simp only [Function.update_of_ne hj, Formula.extend, hi, dite_true, Function.update_of_ne hfin]
  · have hj : i ≠ j.val := by intro h; subst i; exact hi j.isLt
    simp only [Function.update_of_ne hj, Formula.extend, hi, dite_false]

theorem environment_finite_sample (P : Readers) (f : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) (hi : f (pair c r) < P.dim c + 4) :
    BivariateRationalTermReader.environment (family P f true) (family P f false) (pair c r)
      (BoundedCriticalSampleLabels.parameter P c x).val t =
        Formula.extend (Function.update x.val ⟨f (pair c r), hi⟩ t) := by
  rw [environment_sample]
  exact extend_update x.val ⟨f (pair c r), hi⟩ t

end LeanCanny.Encoding.BoundedCriticalSampleLineCoordinates
