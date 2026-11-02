/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Algebra.ModularResidueSpace
/-! # The constant original source X, including exact caller-modulus access -/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialZeroRootSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

private theorem natural_evaluator {a : List Bool→ℕ} (ha : BinaryFn a) :
    SpaceFunction (fun q=>residueBits (a q : ZMod (RationalSubstitution.IntegerBits.mValue q))) := by
  have HM:=(BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  have E:=SpaceFunction.ofFP _ (ha.mod HM).bits_mem_FP
  exact E.congr (funext fun q=>by simp only [residueBits,ZMod.val_natCast])

noncomputable def source : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := Polynomial.X
  degree _ := 1
  mass _ := 0
  degree_bound _ := by simp only [Polynomial.natDegree_X]; exact le_rfl
  mass_bound _ := by simp [coefficientMass]

theorem access : IntegerPolynomialRootQueriesBits.Access source where
  degree := BinaryFn.const 1
  mass := BinaryFn.const 0
  coefficient := by
    have HK := BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
    have EO := natural_evaluator (BinaryFn.const 1)
    have EZ := natural_evaluator (BinaryFn.const 0)
    have E := ModularResidueSpace.branchEvaluator pairSnd _ _ _ (HK.eq (BinaryFn.const 1)) EO EZ
    refine E.congr (funext fun q => ?_)
    unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
    simp only [source,Polynomial.coeff_X]
    split_ifs <;> simp only [Int.cast_one,Nat.cast_one,Int.cast_zero,Nat.cast_zero] <;> omega

end LeanCanny.Algebra.IntegerPolynomialZeroRootSource
