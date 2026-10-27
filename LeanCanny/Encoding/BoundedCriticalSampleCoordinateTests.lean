/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTestMoments

/-! # Native numerator and denominator tests for actual sample coordinates

The test context is `pair source coordinateIndex`. Both polynomials have
native modular readers and source-derived bounds. At the parameter of an
actual sample, their quotient is the original sample coordinate.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleCoordinateTests
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleTestMoments
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate
  BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass PrimitivePairBits.coefficient

noncomputable def numerator (P : Readers) : Test where
  polynomial u := (BoundedCriticalRationalCoordinates.coordinate P u).numerator
  degree u := BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)
  mass u := BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)
  polynomial_degree u := (Nat.le_max_left _ _).trans (BoundedCriticalRationalCoordinates.coordinate_bounds P u).1
  polynomial_mass u := (BoundedCriticalRationalCoordinates.coordinate_bounds P u).2.1

noncomputable def denominator (P : Readers) : Test where
  polynomial u := (BoundedCriticalRationalCoordinates.coordinate P u).denominator
  degree u := BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)
  mass u := BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)
  polynomial_degree u := (Nat.le_max_right _ _).trans (BoundedCriticalRationalCoordinates.coordinate_bounds P u).1
  polynomial_mass u := (BoundedCriticalRationalCoordinates.coordinate_bounds P u).2.2

noncomputable def numeratorAccess {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (numerator P).Access := by
  have hd : BinaryFn (fun u => BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)) :=
    (BoundedCriticalRationalCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (fun u => BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)) :=
    (BoundedCriticalRationalCoordinates.coordinateMass_binary h).comp pairFst_mem_FP
  exact Test.Access.ofPrimitive hd hm (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).1

noncomputable def denominatorAccess {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (denominator P).Access := by
  have hd : BinaryFn (fun u => BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)) :=
    (BoundedCriticalRationalCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (fun u => BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)) :=
    (BoundedCriticalRationalCoordinates.coordinateMass_binary h).comp pairFst_mem_FP
  exact Test.Access.ofPrimitive hd hm (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).2

theorem decode_parameter (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalParameterRoots.decode P c (BoundedCriticalSampleLabels.parameter P c x).val = x.val := by
  have H := congrArg Subtype.val ((BoundedCriticalSampleLabels.rootEquiv P c).apply_symm_apply x)
  exact H

theorem coordinate_eval (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (i : Fin (P.dim c + 4)) :
    (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i.val))).eval
      (BoundedCriticalSampleLabels.parameter P c x).val = x.val i :=
  congrFun (decode_parameter P c x) i

theorem denominator_nonzero (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (i : Fin (P.dim c + 4)) :
    (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂
      (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val ≠ 0 := by
  have hr := ((BoundedCriticalSampleLabels.mem_rootSet P c _).mp (BoundedCriticalSampleLabels.parameter P c x).property).1
  exact BoundedCriticalParameterRoots.denominator_ne_zero P c _ hr i

theorem sign_quotient (a b : ℝ) : SignType.sign (a / b) = SignType.sign a * SignType.sign b := by
  rw [div_eq_mul_inv, sign_mul]
  congr 1
  simp only [sign_apply, inv_pos, inv_lt_zero]

theorem coordinate_sign (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (i : Fin (P.dim c + 4)) :
    sign (numerator P) (pair c (BinaryNatCode.encode i.val)) (BoundedCriticalSampleLabels.parameter P c x).val *
      sign (denominator P) (pair c (BinaryNatCode.encode i.val)) (BoundedCriticalSampleLabels.parameter P c x).val =
        SignType.sign (x.val i) := by
  rw [← coordinate_eval P c x i]
  simp only [sign, numerator, denominator, Polynomial.eval_map, UnivariateRational.Coordinate.eval, sign_quotient]

end LeanCanny.Encoding.BoundedCriticalSampleCoordinateTests
