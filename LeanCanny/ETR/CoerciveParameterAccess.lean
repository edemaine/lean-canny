/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveParameterCoefficient
public import LeanCanny.ETR.CoerciveInfinitesimalFamily

/-! # Native root-family access for the actual coercive primitive parameter -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.ETR.CoerciveParameterAccess
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveInfinitesimalFamily (rootFamily)
attribute [local irreducible] CoercivePreparationControls.family RationalSubstitutionBits.compiledTerm Matrix.det

noncomputable def access : CertifiedPolynomial.BivariateReader rootFamily.polynomial where
  coefficient := SymbolicFixedTableEntryBits.coefficient
    (fun bits => (CoercivePreparationControls.family bits).parameter)
  evaluator := CoerciveParameterCoefficient.evaluator
  coefficient_eq q u v := by
    simp only [SymbolicFixedTableEntryBits.coefficient, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl

theorem evaluator : SpaceFunction access.coefficient :=
  access.evaluator

end LeanCanny.ETR.CoerciveParameterAccess
