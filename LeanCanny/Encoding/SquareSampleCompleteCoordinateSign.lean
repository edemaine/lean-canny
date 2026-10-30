/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
public import LeanCanny.Algebra.ClearingMatrixSpace
public import LeanCanny.Algebra.LinearCoefficientBounds

/-! # Native signs of individual complete-root coordinates -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteCoordinateSign
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def identitySource : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := (Polynomial.X : Polynomial ℤ) ^ 1
  degree _ := 1
  mass _ := 0
  degree_bound _ := by simp only [pow_one, Polynomial.natDegree_X]; exact le_rfl
  mass_bound _ := by simp only [coefficientMass_X_pow, pow_zero]; exact le_rfl

theorem identityAccess : IntegerPolynomialRootQueriesBits.Access identitySource :=
  ⟨ClearingMatrixBits.monomialEvaluator (fun _ => 1) (BinaryFn.const 1), BinaryFn.const 1, BinaryFn.const 0⟩

theorem coordinate_unary {F : Inputs} (h : F.Access) :
    UnaryFn (fun z => (SquareSampleInput.selected F (pairFst z) (pairSnd z)).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((h.count.comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def value (F : Inputs) : List Bool → List Bool :=
  SquareSampleCompleteUnivariateTest.value F identitySource (SquareSampleInput.selected F)
theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  SquareSampleCompleteUnivariateTest.evaluator h identityAccess (SquareSampleInput.selected F) (coordinate_unary h)

theorem packet (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (i : Fin (F.count c)) :
    value F (pair (pair c w) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign ((SquareSampleCompleteVertices.candidate F c w hw).val i)) := by
  have HI : SquareSampleInput.selected F c (BinaryNatCode.encode i.val) = i := by
    apply Fin.ext
    simp only [SquareSampleInput.selected, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.min_eq_left (by have := i.isLt; omega)
  rw [value, SquareSampleCompleteUnivariateTest.packet F identitySource _ c w _ hw]
  simp only [identitySource, Polynomial.eval₂_X, pow_one, HI]

end LeanCanny.Encoding.SquareSampleCompleteCoordinateSign
