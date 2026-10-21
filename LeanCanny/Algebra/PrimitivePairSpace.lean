/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Complete native readers for the explicit primitive-pair coordinates

The denominator, right numerator, and left numerator include every source,
shift, binomial, and subresultant child. Binary predecessor and modular direction
arithmetic prepare the two extra terms of the left numerator.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
attribute [local irreducible] BinaryNat.sub BinaryNat.mod BinaryNat.succ

theorem numeratorEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (coefficient (fun c => coordinateNumerator (S.left c) (S.right c) (S.direction c))) := by
  have E := coordinateEvaluator S A 0
  exact E.congr (congrArg coefficient (funext fun c => coordinateCoefficient_zero _ _ _))

theorem denominatorEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (coefficient (fun c => PrimitivePair.denominator (S.left c) (S.right c) (S.direction c))) := by
  have E := coordinateEvaluator S A 1
  exact E.congr (congrArg coefficient (funext fun c => coordinateCoefficient_one _ _ _))

theorem rightNumeratorEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (coefficient (fun c => PrimitivePair.rightNumerator (S.left c) (S.right c) (S.direction c))) := by
  have N := numeratorEvaluator S A
  let E := ModularResidueSpace.negEvaluator pairSnd
    (fun p => (((coordinateNumerator (S.left (context p)) (S.right (context p)) (S.direction (context p))).coeff
      (Nat.fromBitsLE (selectedDegree p)) : ℤ) : ZMod (mValue p))) pairSnd_mem_FP N
  refine E.congr (funext fun p => ?_)
  simp only [coefficient, coefficientResidue, PrimitivePair.rightNumerator, Polynomial.coeff_neg, Int.cast_neg]

def previousQuery (p : List Bool) : List Bool :=
  pair (pair (context p) (BinaryNat.sub (pair (selectedDegree p) (BinaryNatCode.encode 1)))) (pairSnd p)

theorem previousQuery_FP : previousQuery ∈ FP := by
  have hi := mem_FP_comp (mem_FP_pair RationalSubstitution.IntegerBits.selectedDegree_mem_FP
    (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  have h := mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP hi) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem coefficient_previous (P : List Bool → Polynomial ℤ) (p : List Bool) :
    coefficient P (previousQuery p) = coefficientResidue
      ((P (context p)).coeff (Nat.fromBitsLE (selectedDegree p) - 1)) (mValue p) := by
  simp only [coefficient, previousQuery, context, selectedDegree, mValue, pairFst_pair, pairSnd_pair,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem directionEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (fun p => residueBits ((S.direction (context p) : ℕ) : ZMod (mValue p))) := by
  let reduce := fun p => BinaryNat.mod (pair (A.direction (context p)) (BinaryNat.succ (pairSnd p)))
  have hd := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP A.directionFP
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have he := mem_FP_comp (mem_FP_pair hd hm) BinaryNat.mod_mem_FP
  let E := SpaceFunction.ofFP reduce (mem_FP_of_eq he (fun _ => rfl))
  refine E.congr (funext fun p => ?_)
  simp only [reduce, A.direction_eq, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast, mValue]

theorem leftNumeratorEvaluator (S : Source) (A : Readers S) :
    SpaceFunction (coefficient (fun c => PrimitivePair.leftNumerator (S.left c) (S.right c) (S.direction c))) := by
  let D := denominatorEvaluator S A
  let DP := D.precompose previousQuery previousQuery_FP
  have P : SpaceFunction (fun p => coefficientResidue
      ((PrimitivePair.denominator (S.left (context p)) (S.right (context p)) (S.direction (context p))).coeff
        (Nat.fromBitsLE (selectedDegree p) - 1)) (mValue p)) :=
    DP.congr (funext (coefficient_previous _))
  have Z : SpaceFunction (fun p => residueBits (0 : ZMod (mValue p))) := by
    let E := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
    exact E.congr (funext fun _ => by simp [residueBits, BinaryNatCode.encode])
  have hp := BinaryNat.le_fppred (constFn_mem_FP [true]) RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  let SD := ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun p => 1 ≤ Nat.fromBitsLE (selectedDegree p)) hp P Z
  let CN := ModularResidueSpace.mulEvaluator pairSnd _ _ pairSnd_mem_FP (directionEvaluator S A) (numeratorEvaluator S A)
  let E := ModularResidueSpace.addEvaluator pairSnd _ _ pairSnd_mem_FP SD CN
  refine E.congr (funext fun p => ?_)
  by_cases h : 1 ≤ Nat.fromBitsLE (selectedDegree p) <;>
    simp only [coefficient, coefficientResidue, PrimitivePair.leftNumerator_coeff, h, ite_true, ite_false,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_zero]

end LeanCanny.Algebra.PrimitivePairBits
