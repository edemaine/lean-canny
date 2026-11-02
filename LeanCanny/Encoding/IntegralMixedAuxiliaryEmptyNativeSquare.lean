/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptySquareSample
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyCompanionSpace
public import LeanCanny.Encoding.IntegralFramedCompleteSquareSpace

/-! # Original-only native complete sampling of actual auxiliary prefixes

The original dimension, term syntax and positive saved-prefix selector derive
row readers, numeric bounds, coordinate annihilators and complete sampling.
No coefficient, matrix, companion or interpreted-state evaluator is supplied.
The returned roots are roots of the JOINT canonical prefix equations; original
bank-coordinate formula filtering is a separate step.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

 theorem square_row_space (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) :
    SpaceFunction (SquareSampleInput.rowCoefficient (squareInput hn ht ha key hpos)) :=
  IntegralFramedCompleteSquare.row_evaluator (parameters n t) (access hn ht) (plan hn ht ha) (data hn ht ha)
    (fun _=>1) (IntegralMixedAuxiliarySchedule.factor n t) (IntegralMixedAuxiliarySchedule.seed n t)
    (familyInputs hn ht ha) key hk
    (fun u=>(hpos u).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (plan hn ht ha) (data hn ht ha) (key u)).symm) (companion_value_space hn ht ha)

theorem square_native_access (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) :
    (squareInput hn ht ha key hpos).Access :=
  square_access hn ht ha key hk hpos (square_row_space hn ht ha key hk hpos)

theorem square_native_count_evaluator (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (squareInput hn ht ha key hpos) u)) :=
  SquareSampleComplete.count_evaluator (square_native_access hn ht ha key hk hpos) (square_complete hn ht ha key hpos)

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
