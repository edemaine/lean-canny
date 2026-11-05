/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicPlanning
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityCatalog

/-! # Installed field comparisons use the unchanged base characteristic

Only explicit old saved keys are transported. The actual contexts and own
words remain literal; no parsed parent or modulus packet is identified.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data factor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

theorem source_polynomial_base (c : List Bool) :
    (originalSource hn ht ha hR).polynomial c = IntegralMixedFramedCoordinateCharacteristicBits.polynomial
      (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) c := by
  rw [source_polynomial_catalog]
  exact IntegralMixedFramedCoordinateCharacteristicBits.polynomial_planned (parameters hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (fun _ => 3) (factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) c

theorem old_polynomial_base (z : List Bool) :
    (originalSource hn ht ha hR).polynomial (oldArgument hn ht ha hR z) =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (catalogOldArgument n z) := by
  rw [source_polynomial_base, oldArgument_catalog]

theorem derivative_polynomial_base (right : Bool) (z : List Bool) (k : ℕ) :
    (derivatives hn ht ha hR).polynomial (probe hn ht ha hR right (pair z (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (catalogOldArgument n z)) := by
  rw [derivative_polynomial_catalog,
    IntegralMixedFramedCoordinateCharacteristicBits.polynomial_planned]

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
