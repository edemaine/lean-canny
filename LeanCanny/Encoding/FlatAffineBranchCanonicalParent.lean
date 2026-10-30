/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextRebase
public import LeanCanny.Encoding.FlatAffineBranchParentChoice

/-! # Canonical original-context ancestor labels for native branch descriptors

Branch witnesses first give a complete ancestor in the joint frame's
composed sampler. Explicit native re-encoding then produces a valid word
in the original parent sampler. Its original ancestor tuple is unchanged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchCanonicalParent
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineEndpointBranchLabels (source)
open FlatAffineJointPrefixChoice (original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchParentChoice.value SquareSampleContextRebase.value
  FlatAffineBranchPrefixChoice.value FlatAffineBranchChoice.value

def prepare (z : List Bool) : List Bool := pair (source (pairFst z)) (pairSnd z)
theorem prepare_FP : prepare ∈ FP := by polytime [prepare, source]

noncomputable def parentRecord (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  pair (source q) (FlatAffineBranchParentChoice.value F C h q)

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : List Bool → List Bool :=
  SquareSampleContextRebase.value (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original ∘
    parentRecord F C h

theorem evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceFunction (value F C h) := by
  have E := (FlatAffineBranchParentChoice.evaluator hF C h hh).withInput.postcompose prepare prepare_FP
  have HE : SpaceFunction (parentRecord F C h) := E.congr (funext fun q => by
    simp only [Function.comp_apply, prepare, parentRecord, pairFst_pair, pairSnd_pair])
  exact HE.chain (SquareSampleContextRebase.evaluator
    (FlatAffinePowerSampleInput.access hF (FlatAffineLastHeightRow.parentCone F C)) FlatAffineJointPrefixChoice.original_FP)

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    FlatAffineCompleteVertices.Valid F (FlatAffineLastHeightRow.parentCone F C) (original (source q)) (value F C h q) :=
  SquareSampleContextRebase.value_valid _ (FlatAffinePowerSampleInput.complete F (FlatAffineLastHeightRow.parentCone F C))
    original (source q) _ (FlatAffineBranchParentChoice.value_valid F C h q hq)

theorem value_parent (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    FlatAffineCompleteVertices.vertexEquiv F (FlatAffineLastHeightRow.parentCone F C) (original (source q))
      ⟨value F C h q, value_valid F C h q hq⟩ = FlatAffineBranchParentChoice.parent F C h q hq := by
  have HP := SquareSampleContextRebase.value_point _
    (FlatAffinePowerSampleInput.complete F (FlatAffineLastHeightRow.parentCone F C))
    original (source q) _ (FlatAffineBranchParentChoice.value_valid F C h q hq)
  apply congrArg (FlatAffinePowerSampleInput.originalRootsEquiv F (original (source q)))
  exact Subtype.ext HP

theorem value_point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineLastHeightRow.parentCone F C) (original (source q))
      ⟨value F C h q, value_valid F C h q hq⟩).val =
      FlatAffineShiftedSlice.ancestorPoint F (original (source q)) (FlatAffineBranchParentChoice.current F C h q) :=
  (congrArg Subtype.val (value_parent F C h q hq)).trans (FlatAffineBranchParentChoice.parent_val F C h q hq)

end LeanCanny.Encoding.FlatAffineBranchCanonicalParent
