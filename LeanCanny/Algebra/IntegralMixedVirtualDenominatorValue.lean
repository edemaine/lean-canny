/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeHeight
public import LeanCanny.Algebra.IntegralMixedVirtualGridModel
/-! # Actual scalar common-denominator values under virtual queries

This module proves value identities only. It gives no FP or space certificate
for the common denominator; the scalar routine computes it recursively.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def valueAt (F : Family) (key : List Bool) (m : ℕ) : List Bool :=
  residueBits (IntegralMixedVirtualSweepSource.denominator F key : ZMod m)
noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((IntegralMixedVirtualTaskBits.source P F).denominator q : ZMod (modulus P q))

theorem snapshot (P : Parameters) (F : Family) (q : List Bool) :
    value P F q = valueAt F (IntegralMixedVirtualTaskBits.saved P q) (modulus P q) := rfl

theorem scalar_child (P : Parameters) (F : Family) (q : List Bool) :
    value P F (IntegralMixedScalarQueryBits.commonDenominator P q) = value P F q := by
  rw [snapshot, snapshot]
  have HS := IntegralMixedRoutineTaskBits.query_saved P .scalar .derivativeCoefficient q
  have HM : modulus P (IntegralMixedScalarQueryBits.commonDenominator P q) = modulus P q := by
    unfold IntegralMixedScalarQueryBits.commonDenominator modulus
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  exact congrArg₂ (valueAt F) HS HM

theorem monomial_denominator (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralMixedVirtualMonomialBits.source P F).denominator q = (IntegralMixedVirtualTaskBits.source P F).denominator q := by
  change (IntegralMixedVirtualTaskBits.arithmetic P F).denominator (pairFst (IntegralCriticalFlatGridBits.termInput P q)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem monomial_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) (q : List Bool) :
    value P F q = (IntegralMixedVirtualMonomialBits.access P a F h).denominator q := by
  rw [(IntegralMixedVirtualMonomialBits.access P a F h).denominator_eq]
  change value P F q = residueBits ((IntegralMixedVirtualMonomialBits.source P F).denominator q : ZMod ((IntegralMixedVirtualMonomialBits.source P F).modulus q))
  rw [monomial_denominator, IntegralMixedVirtualGridBits.source_modulus]
  rfl
end LeanCanny.Algebra.IntegralMixedVirtualDenominatorBits
