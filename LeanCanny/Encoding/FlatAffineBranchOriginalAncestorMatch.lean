/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineBranchParentChoice
public import LeanCanny.Encoding.FlatAffineBranchAncestorMatch

/-! # Native branch filtering compares exact original ancestor tuples

Decoding the computed complete word through the odd-power equivalence
recovers every original ancestor coordinate, including its multipliers.
Native word comparison therefore decides equality of these original tuples.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchOriginalAncestorMatch
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineEndpointBranchLabels (source)
open FlatAffineJointPrefixChoice (original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchPrefixChoice.value FlatAffineBranchChoice.value
  FlatAffineJointPrefixChoice.value FlatAffineEndpointBranchLabels.language

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  FlatAffineBranchAncestorMatch.language (next F) C (FlatAffineLastHeightRow.row F h)

theorem decider {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceDecider (language F C h) :=
  FlatAffineBranchAncestorMatch.decider (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C
    (FlatAffineLastHeightRow.row F h) (FlatAffineLastHeightRow.row_unary hF h hh)

theorem mem_PSPACE {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : language F C h ∈ PSPACE :=
  (decider hF C h hh).mem_PSPACE

theorem packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h))
    (hv : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original) (source q) v) :
    pair q v ∈ language F C h ↔ FlatAffineBranchParentChoice.parent F C h q hq =
      FlatAffineBranchParentChoice.decode F (FlatAffineLastHeightRow.parentCone F C) (source q) v hv := by
  simp only [language, FlatAffineBranchAncestorMatch.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hq, true_and]
  change FlatAffineBranchParentChoice.value F C h q = v ↔ _
  constructor
  · intro he
    subst v
    rfl
  · intro he
    exact FlatAffineBranchParentChoice.decode_injective F (FlatAffineLastHeightRow.parentCone F C) (source q)
      (FlatAffineBranchParentChoice.value F C h q) v (FlatAffineBranchParentChoice.value_valid F C h q hq) hv he

theorem tuple_packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h))
    (hv : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original) (source q) v) :
    pair q v ∈ language F C h ↔
      FlatAffineShiftedSlice.ancestorPoint F (original (source q)) (FlatAffineBranchParentChoice.current F C h q) =
        (FlatAffineBranchParentChoice.decode F (FlatAffineLastHeightRow.parentCone F C) (source q) v hv).val := by
  constructor
  · intro he
    exact (FlatAffineBranchParentChoice.parent_val F C h q hq).symm.trans
      (congrArg Subtype.val ((packet F C h q v hq hv).mp he))
  · intro he
    exact (packet F C h q v hq hv).mpr
      (Subtype.ext ((FlatAffineBranchParentChoice.parent_val F C h q hq).trans he))

end LeanCanny.Encoding.FlatAffineBranchOriginalAncestorMatch
