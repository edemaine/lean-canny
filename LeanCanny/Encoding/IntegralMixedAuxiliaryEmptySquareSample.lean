/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyRowMass
public import LeanCanny.Encoding.IntegralFramedCompleteSquare

/-! # Complete square sampling for positive actual auxiliary prefixes

The original dimension and term supply every numeric, source, degree and
mass bound. A positive saved-prefix selector and its literal row reader
instantiate all-root native sampling. No singular roots are discarded.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

noncomputable def squareInput (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) : SquareSampleInput.Inputs :=
  IntegralFramedCompleteSquare.input (parameters n t) (plan hn ht ha) (data hn ht ha)
    (fun _=>1) (factor n t) (seed n t) (familyInputs hn ht ha) key
    (fun u=>(hpos u).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (plan hn ht ha) (data hn ht ha) (key u)).symm)

theorem square_complete (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) :
    SquareSampleComplete.Complete (squareInput hn ht ha key hpos) :=
  IntegralFramedCompleteSquare.complete _ _ _ _ _ _ _ _ _

theorem square_rows (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u)) (u : List Bool) :
    HEq ((squareInput hn ht ha key hpos).system u)
      (((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (plan hn ht ha) (data hn ht ha)).state (key u)).sampler.scalarPrefix.rows) :=
  IntegralFramedCompleteSquare.rows_heq _ _ _ _ _ _ _ _ _ _

theorem square_access (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (squareInput hn ht ha key hpos))) :
    (squareInput hn ht ha key hpos).Access :=
  IntegralFramedCompleteSquare.access (parameters n t) (IntegralMixedAuxiliaryParameters.access hn ht)
    (plan hn ht ha) (data hn ht ha) (fun _=>1) (factor n t) (seed n t) (familyInputs hn ht ha)
    (BinaryFn.const 1) (factor_binary hn ht) (seed_binary hn ht) key hk _ ER

theorem square_count_evaluator (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key u))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (squareInput hn ht ha key hpos))) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (squareInput hn ht ha key hpos) u)) :=
  SquareSampleComplete.count_evaluator (square_access hn ht ha key hk hpos ER) (square_complete hn ht ha key hpos)

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
