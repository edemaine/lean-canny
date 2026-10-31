/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermCorrect
public import LeanCanny.Algebra.IntegralMonomialTermValue

/-! # Native cleared-monomial terms from original readers

The original coefficient, integer denominator, and retained-height readers
construct every factor power and the actual term product. Their full space
costs are included; no multiplication-matrix product reader is supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def familyAccess (S : Source) (a : Access S) : IntegralPowerProductBits.Access (family S) where
  rank := a.rank
  count := (BinaryFn.ofUnary a.arity).add (BinaryFn.const 2)
  modulus := a.modulus
  row := a.row
  col := a.col
  exponent := factorExponent_binary S a
  entry := entryProgram S a
  entry_eq := entry_correct S a

attribute [local irreducible] Source.value entryProgram

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction S.value := by
  have HE : SpaceFunction (familyAccess S a).entry := by
    change SpaceFunction (entryProgram S a)
    exact entry_evaluator S a EC EH EQ
  exact (IntegralPowerProductBits.evaluator (family S) (familyAccess S a) HE).congr (family_value S)

end LeanCanny.Algebra.IntegralMonomialTermBits
