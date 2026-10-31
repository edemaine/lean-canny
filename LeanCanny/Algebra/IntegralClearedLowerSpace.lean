/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenPowerConstantSpace
public import LeanCanny.Algebra.ModularAddFP

/-! # Native actual Fermat lower coefficients on frozen slices

The original spatial source is cleared integrally and the frozen Fermat
power constant is added. The resulting program computes the actual
ClearedCoordinateBlock.lower polynomial from the original coefficient,
height, common-denominator, and integer-leading readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.lowerPolynomial (S : Source) (c : List Bool) :
    letI := S.ring c
    MvPolynomial (Fin (S.free c)) (S.carrier c) := by
  letI := S.ring c
  exact ClearedCoordinateBlock.lower (S.allowance c) (S.denominator c : S.carrier c)
    (S.height c) (S.offset c) (S.free c) (S.polynomial c) (S.leading c : S.carrier c)

noncomputable def Source.lowerValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c) ((S.lowerPolynomial c).coeff (S.toSource.targetExponent c))
    (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

def addPost (S : Source) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNatCode.encode (S.modulus (pairFst z))) (pairSnd z))

attribute [local irreducible] ArithmeticBits.addMod

theorem addPost_FP (S : Source) (a : Access S) : addPost S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HF : (fun z => pair (BinaryNatCode.encode (S.modulus (pairFst z))) (pairSnd z)) ∈ FP :=
    mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP
  have HG := mem_FP_comp HF ArithmeticBits.addMod_mem_FP
  exact mem_FP_of_eq HG (fun _ => rfl)

theorem lower_value (S : Source) (c : List Bool) :
    addPost S (pair c (pair (S.toSource.value c) (S.constantValue c))) = S.lowerValue c := by
  let := S.ring c
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  unfold addPost
  rw [pairFst_pair, pairSnd_pair]
  unfold IntegralClearedCoefficientBits.Source.value Source.constantValue Source.lowerValue Source.lowerPolynomial
  rw [ClearedCoordinateBlock.lower, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, Matrix.add_apply, Int.cast_add]
  exact ArithmeticBits.addMod_residueBits _ _ _

attribute [local irreducible] Source.lowerValue Source.constantValue IntegralClearedCoefficientBits.Source.value addPost

theorem lower_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction S.lowerValue := by
  have EP := IntegralClearedCoefficientBits.evaluator S.toSource a.toAccess EC EH EQ
  have EF := constant_evaluator S a EH EA
  refine ((EP.pairOutputs EF).withInput.postcompose (addPost S) (addPost_FP S a)).congr (funext fun c => ?_)
  exact lower_value S c

end LeanCanny.Algebra.IntegralFrozenPowerBits
