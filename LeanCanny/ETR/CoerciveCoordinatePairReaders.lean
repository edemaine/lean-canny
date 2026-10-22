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
  have T := tablePrepareEvaluator.precompose (fun p => pairFst (pairFst p))
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have L := SpaceFunction.ofFP (fun p => pairSnd (pairFst p)) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have S := SpaceFunction.ofFP pairSnd pairSnd_mem_FP
  exact (T.pairOutputs L).pairOutputs S

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

lemma ancestor_lt (N h j : ℕ) (hh : h ≤ N) (hj : j < 2 ^ N) : j / 2 ^ h < 2 ^ (N - h) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).mpr
  calc
    j < 2 ^ N := hj
    _ = 2 ^ (N - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]

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
  have hi : i < 2 ^ (CoerciveTableCorrectness.height bits - (h + 1)) := ancestor_lt _ _ _ hh hj
  have hp : CoercivePairRouting.parent (preparedContext p) =
      BalancedParameterContext.packet (tablePrepare bits) (h + 1) i := by
    simp only [CoercivePairRouting.parent, CoercivePairRouting.parentIndex, table_prepared,
      leaf_prepared, height_prepared, bits, h, j, i]
  have hpow : 2 ^ (CoerciveTableCorrectness.height bits - h) =
      2 ^ (CoerciveTableCorrectness.height bits - (h + 1)) * 2 := by
    rw [← pow_succ]
    apply congrArg (fun n : ℕ => 2 ^ n)
    omega
  have hil : 2 * i < 2 ^ (CoerciveTableCorrectness.height bits - h) := by rw [hpow]; omega
  have hir : 2 * i + 1 < 2 ^ (CoerciveTableCorrectness.height bits - h) := by rw [hpow]; omega
  have hl := CoerciveTableCorrectness.tree_eq_reference bits h (2 * i) (by omega) hil
  have hr := CoerciveTableCorrectness.tree_eq_reference bits h (2 * i + 1) (by omega) hir
  have hs := CoerciveTableCorrectness.table_consistent_subtree bits (h + 1) i hh hi
  have hdl := hs.2.2.1.trans (CoerciveTableCorrectness.reference_node_degree bits h (2 * i) (by omega))
  have hdr := hs.2.2.2.1.trans (CoerciveTableCorrectness.reference_node_degree bits h (2 * i + 1) (by omega))
  have hd := CoerciveTableCorrectness.table_direction_reference bits h i hh hi
  have hleft : (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).left (preparedContext p) =
      SymbolicFixedTable.node (fun k => SymbolicScaledSquarefree.polynomial ((family bits).padded k))
        (family bits).directions h (2 * i) := by
    simp only [CoercivePairRouting.pairFamily, hp, BalancedParameterContext.child_packet,
      Bool.false_eq_true, ite_false, Nat.add_zero, SymbolicFixedTablePolynomialTree.node_packet]
    exact hl
  have hright : (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).right (preparedContext p) =
      SymbolicFixedTable.node (fun k => SymbolicScaledSquarefree.polynomial ((family bits).padded k))
        (family bits).directions h (2 * i + 1) := by
    simp only [CoercivePairRouting.pairFamily, hp, BalancedParameterContext.child_packet,
      ite_true, SymbolicFixedTablePolynomialTree.node_packet]
    exact hr
  have hml : (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).leftOrder (preparedContext p) =
      ((CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).left (preparedContext p)).natDegree := by
    calc
      _ = BalancedMetadataTable.order (BalancedParameterContext.packet (tablePrepare bits) h (2 * i)) := by
        simp only [CoercivePairRouting.pairFamily, hp, BalancedParameterContext.child_packet,
          Bool.false_eq_true, ite_false, Nat.add_zero]
      _ = _ := hdl
      _ = _ := congrArg Polynomial.natDegree hleft.symm
  have hmr : (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).rightOrder (preparedContext p) =
      ((CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).right (preparedContext p)).natDegree := by
    calc
      _ = BalancedMetadataTable.order (BalancedParameterContext.packet (tablePrepare bits) h (2 * i + 1)) := by
        simp only [CoercivePairRouting.pairFamily, hp, BalancedParameterContext.child_packet, ite_true]
      _ = _ := hdr
      _ = _ := congrArg Polynomial.natDegree hright.symm
  refine ⟨hml, hmr, ?_⟩
  rw [SymbolicPairRecoveryBits.Family.coordinate_eq
    (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf) (preparedContext p)
    (decide (CoercivePairRouting.isRight (preparedContext p))) hml hmr, hleft, hright]
  have hdir : (CoercivePairRouting.pairFamily CoerciveFormalLeafReader.leaf).direction (preparedContext p) =
      (family bits).directions h i := by simpa only [CoercivePairRouting.pairFamily, hp] using hd
  rw [hdir]
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
  have C := preparedContextEvaluator.precompose (fun q => pairFst (pairFst q))
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have M := SpaceFunction.ofFP (fun q => pairSnd (pairFst q)) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have D := SpaceFunction.ofFP pairSnd pairSnd_mem_FP
  exact (C.pairOutputs M).pairOutputs D

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
