/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoercivePairRouting
public import LeanCanny.ETR.CoerciveTableCorrectness
public import LeanCanny.ETR.CoerciveNodeCoefficient
public import LeanCanny.Algebra.SymbolicPrimitivePairSelectedSpace

/-! # Prepared native pair readers supply the actual coordinate path factors -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveCoordinatePairReaders
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling CoercivePreparationControls CoerciveIntegerPreparation
open SymbolicScaledSquarefree SymbolicFixedTable
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
  CoerciveNativeAnnihilators.original CoerciveNativeAnnihilators.degreeBound
  CoerciveNativeAnnihilators.massExponent CoerciveSourceSampling.dimension
  LeanCanny.pair pairFst pairSnd CoerciveIntegerPreparation.tablePrepare
  CoerciveIntegerPreparation.prepare CoercivePairRouting.parent
set_option backward.isDefEq.respectTransparency false

/-- An indexed path-factor context retains its raw leaf and stage words. -/
noncomputable def preparedContext (p : List Bool) : List Bool :=
  pair (pair (tablePrepare (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)

theorem preparedContextEvaluator : SpaceFunction preparedContext := by
  have h := tablePrepareEvaluator.computable
  constructor
  unfold preparedContext
  fun_prop

lemma table_prepared (p : List Bool) : CoercivePairRouting.table (preparedContext p) = tablePrepare (pairFst (pairFst p)) := by
  simp only [CoercivePairRouting.table, preparedContext, pairFst_pair]

lemma bits_prepared (p : List Bool) : CoercivePairRouting.bits (preparedContext p) = pairFst (pairFst p) := by
  simp only [CoercivePairRouting.bits, table_prepared, CoerciveTableCorrectness.tablePrepare_source, prepare_source]

lemma leaf_prepared (p : List Bool) : CoercivePairRouting.leaf (preparedContext p) =
    CoerciveCoordinatePathSource.leaf (pairFst p) := by
  simp only [CoercivePairRouting.leaf, bits_prepared]
  simp only [CoercivePairRouting.leafWord, preparedContext, pairFst_pair,
    pairSnd_pair, CoerciveCoordinatePathSource.leaf]

lemma height_prepared (p : List Bool) : CoercivePairRouting.height (preparedContext p) =
    CoerciveCoordinatePathSource.stage (pairFst p) (Nat.fromBitsLE (pairSnd p)) := by
  simp only [CoercivePairRouting.height, bits_prepared]
  simp only [preparedContext, pairSnd_pair, CoerciveCoordinatePathSource.stage, CoerciveCoordinatePathSource.depth]

lemma pair_fields (p : List Bool) :
    let F := CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf
    let q := preparedContext p
    F.leftOrder q = (F.left q).natDegree ∧ F.rightOrder q = (F.right q).natDegree ∧
      SymbolicPairRecoveryBits.Family.coordinate F (decide (CoercivePairRouting.isRight q)) q =
        CoerciveCoordinatePathSource.inner (pairFst p) (Nat.fromBitsLE (pairSnd p)) := by
  let bits := pairFst (pairFst p)
  let h := CoerciveCoordinatePathSource.stage (pairFst p) (Nat.fromBitsLE (pairSnd p))
  let j := CoerciveCoordinatePathSource.leaf (pairFst p)
  let i := j / 2 ^ (h + 1)
  have hh : h + 1 ≤ CoerciveTableCorrectness.height bits :=
    CoerciveCoordinatePathSource.stage_lt (pairFst p) (Nat.fromBitsLE (pairSnd p))
  have hj : j < 2 ^ CoerciveTableCorrectness.height bits := by
    have hl := Nat.min_le_right (Nat.fromBitsLE (pairSnd (pairFst p))) (dimension bits)
    exact (hl.trans (Nat.le_succ _)).trans_lt (Nat.lt_size_self (dimension bits + 1))
  have hi : i < 2 ^ (CoerciveTableCorrectness.height bits - (h + 1)) := BalancedSubtreeLocality.ancestor_lt _ _ _ hh hj
  have hp : CoercivePairRouting.parent (preparedContext p) =
      BalancedParameterContext.packet (tablePrepare bits) (h + 1) i := by
    simp only [CoercivePairRouting.parent, CoercivePairRouting.parentIndex, table_prepared,
      leaf_prepared, height_prepared, bits, h, j, i]
  have spec := CoerciveTableCorrectness.pair_spec bits h i hh hi
  have fields := spec.fields CoercivePairRouting.parent (preparedContext p) hp
    (decide (CoercivePairRouting.isRight (preparedContext p)))
  refine ⟨fields.1, fields.2.1, fields.2.2.trans ?_⟩
  change SymbolicFixedTable.pairCoordinate _ _ _ _ =
    SymbolicFixedTable.leafStep (fun k => SymbolicScaledSquarefree.polynomial ((family bits).padded k))
      (family bits).directions j h
  simp only [SymbolicFixedTable.leafStep, BalancedLeafPath.ancestor, CoercivePairRouting.isRight,
    leaf_prepared, height_prepared]
  rfl

/-- The total supplied-table coordinate agrees with the actual source path
on the literally computed integer-prepared table. -/
lemma coordinate_eq (p : List Bool) :
    SymbolicPairRecoveryBits.Family.coordinate (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf)
      (decide (CoercivePairRouting.isRight (preparedContext p))) (preparedContext p) =
        CoerciveCoordinatePathSource.inner (pairFst p) (Nat.fromBitsLE (pairSnd p)) := (pair_fields p).2.2

/-- Native preparation retains the incoming coefficient degree and modulus. -/
noncomputable def prepareQuery (q : List Bool) : List Bool :=
  pair (pair (preparedContext (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

theorem prepareQueryEvaluator : SpaceFunction prepareQuery := by
  have h := preparedContextEvaluator.computable
  constructor
  unfold prepareQuery
  fun_prop

lemma numerator_from_prepared
    (N : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun p =>
      SymbolicPairRecoveryBits.Family.numerator (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf)
        (decide (CoercivePairRouting.isRight p)) p))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (SymbolicCoordinatePathBits.indexedNumerator CoerciveCoordinatePathSource.source)) := by
  refine (prepareQueryEvaluator.chain N).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, prepareQuery,
    pairFst_pair, pairSnd_pair]
  have h := congrArg SymbolicBalancedCoordinate.Coordinate.numerator (coordinate_eq (pairFst (pairFst q)))
  change SymbolicPairRecoveryBits.Family.numerator (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf) _ _ = _ at h
  rw [h]
  rfl

lemma denominator_from_prepared
    (D : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (SymbolicPairRecoveryBits.Family.denominator (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf)))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (SymbolicCoordinatePathBits.indexedDenominator CoerciveCoordinatePathSource.source)) := by
  refine (prepareQueryEvaluator.chain D).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, prepareQuery,
    pairFst_pair, pairSnd_pair]
  have h := congrArg SymbolicBalancedCoordinate.Coordinate.denominator (coordinate_eq (pairFst (pairFst q)))
  change SymbolicPairRecoveryBits.Family.denominator (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf) _ = _ at h
  rw [h]
  rfl

/-- The original syntax, formal leaf, uniform table node, pair recovery, and
literal integer table preparation all contribute their native space cost. -/
theorem numeratorEvaluator :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (SymbolicCoordinatePathBits.indexedNumerator CoerciveCoordinatePathSource.source)) :=
  numerator_from_prepared (CoercivePairRouting.numeratorEvaluator CoerciveFormalLeafReader.leaf
    CoerciveFormalLeafReader.bound CoerciveFormalLeafReader.leaf_inner_degree
    CoerciveFormalLeafReader.bound_binary CoerciveNodeCoefficient.evaluator)

theorem denominatorEvaluator :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (SymbolicCoordinatePathBits.indexedDenominator CoerciveCoordinatePathSource.source)) :=
  denominator_from_prepared (CoercivePairRouting.denominatorEvaluator CoerciveFormalLeafReader.leaf
    CoerciveFormalLeafReader.bound CoerciveFormalLeafReader.leaf_inner_degree
    CoerciveFormalLeafReader.bound_binary CoerciveNodeCoefficient.evaluator)

/-- Actual coordinate readers, with no supplied reader or metadata hypotheses. -/
noncomputable def readers : CoerciveCoordinateEncoding.Readers :=
  CoerciveCoordinatePathSource.readers numeratorEvaluator denominatorEvaluator

end LeanCanny.ETR.CoerciveCoordinatePairReaders
