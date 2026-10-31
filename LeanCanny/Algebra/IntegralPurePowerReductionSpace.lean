/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPurePowerReductionCorrect

/-! # Actual relative annihilator coefficients from original lower-polynomial readers

The lower-coefficient and common integer-leading readers construct the
reduction matrix, its shifted action, the relative characteristic polynomial,
and the scalar rescaling. Every intermediate reader is derived internally;
the two supplied readers' complete space costs are charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPurePowerActionBits (Source reductionSource)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem dimension_binary (S : Source) (a : Access S) : BinaryFn (reductionSource S).dimension :=
  BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP a.layout.arity a.layout.width)
    (fun c => FixedWidthPolynomial.countCode_code _ _ c))

noncomputable def reductionAccess (S : Source) (a : Access S) :
    IntegralBerkowitzBlockBits.Access (reductionSource S).toSource where
  dimension := dimension_binary S a
  rank := a.rank
  modulus := a.modulus
  coefficient := a.coefficient
  basisRow := a.basisRow
  basisCol := a.basisCol
  entry := entryProgram S a
  entry_eq := entry_correct S a

attribute [local irreducible] IntegralPurePowerActionBits.Source.value entryProgram

theorem evaluator (S : Source) (a : Access S) (EL : SpaceFunction a.low) (EC : SpaceFunction a.leading) :
    SpaceFunction S.value := by
  have HE : SpaceFunction (reductionAccess S a).entry := by
    change SpaceFunction (entryProgram S a)
    exact entry_evaluator S a EL EC
  have HC : SpaceFunction (fun c => residueBits (S.leading c : ZMod (S.modulus c))) :=
    EC.congr (funext a.leading_eq)
  exact IntegralPurePowerActionBits.polynomial_evaluator S (reductionAccess S a)
    a.layout a.coordinate a.bound HE HC

end LeanCanny.Algebra.IntegralPurePowerReductionBits
