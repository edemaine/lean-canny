import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphDepthCompleteness
import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociationGeometry
import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredGeometry
import LeanCanny.Encoding.FormulaSignSlotRadialProviderOriginalBudget
import LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitnessNative

open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.Geometry
open LeanCanny.Connectivity
open FormulaSignSlotRadialProviderGraph
set_option backward.isDefEq.respectTransparency false

example (c : List Bool) (k : ℕ) (hk : k≤FormulaSignSlotRadialProviderMarkedGeometry.number c+3) :
    DepthComplete c k := depth_complete c k hk

example (c a b : List Bool) (ha : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hb : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hca : FormulaSignSlotRadialProviderAtomic.provider a=c) (hcb : FormulaSignSlotRadialProviderAtomic.provider b=c)
    (hda : FormulaSignSlotRadialProviderAtomic.depth a=0) (hdb : FormulaSignSlotRadialProviderAtomic.depth b=0) :
    RawReachable c a b ↔ JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c)
      (pointAt c a ha hca) (pointAt c b hb hcb) := depth_zero_raw_reachable_iff_joined c a b ha hb hca hcb hda hdb

example (c a b : List Bool) (H : RawReachable c a b) :
    JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c)
      (pointAt c a H.1 H.2.2.1) (pointAt c b H.2.1 H.2.2.2.1) := raw_reachable_joined c a b H

example : FormulaSignSlotRadialProviderAssociation.language∈PSPACE := FormulaSignSlotRadialProviderAssociation.mem_PSPACE
example : FormulaSignSlotRadialProviderAnchoredAssociation.language∈PSPACE := FormulaSignSlotRadialProviderAnchoredAssociation.mem_PSPACE
example : FormulaSignSlotRadialProviderMarkedAnchor.language∈PSPACE := FormulaSignSlotRadialProviderMarkedAnchor.mem_PSPACE
example : FormulaSignSlotRadialProviderJointWitness.language∈PSPACE := FormulaSignSlotRadialProviderJointWitness.mem_PSPACE

example (c old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hc : FormulaSignSlotRadialProviderAtomic.provider old=c) (h0 : FormulaSignSlotRadialProviderAtomic.depth old=0)
    (HPath : JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c)
      (pointAt c old hv hc) (preludeAt c old hv hc)) :
    ∃q,FormulaSignSlotRadialProviderAtomic.Valid q ∧
      RawReachable c old q ∧q∈FormulaSignSlotRadialProviderMarkedAnchor.language := by
  obtain ⟨q,hq,_,_,HRaw,HMarked,_⟩ := FormulaSignSlotRadialProviderProperAppend.exists_reachable_marked_anchor_of_source_path
    c old hv hc h0 HPath
  exact ⟨q,hq,HRaw,HMarked⟩

#check FormulaSignSlotRadialProviderProperEdgeConstruct.exists_proper_pair
#check FormulaSignSlotRadialProviderAssociation.language_joined_iff
#check FormulaSignSlotRadialProviderFirstSeed.exists_at_occurrence
#check FormulaSignSlotRadialProviderOriginalBudget.component_hit_bounded_providers
#check FormulaSignSlotRadialProviderAnchoredGeometry.language_joined_preludes
#check FormulaSignSlotRadialProviderAnchoredGeometry.language_iff_joined_preludes_of_attachments
#check FormulaSignSlotRadialProviderJointWitness.language_iff
#check FormulaSignSlotRadialProviderJointWitness.of_seed_pairs

#print axioms depth_complete_step
#print axioms depth_complete
#print axioms depth_zero_raw_reachable_iff_joined
#print axioms proper_joined
#print axioms path_joined
#print axioms raw_reachable_joined
#print axioms PointReachable.joined
#print axioms PointReachable.symm
#print axioms FormulaSignSlotRadialProviderProperEdgeConstruct.exists_proper_pair
#print axioms FormulaSignSlotRadialProviderProperLocalFrame.local_joined
#print axioms FormulaSignSlotRadialProviderProperMidSignature.proper_midpoint_eq
#print axioms FormulaSignSlotRadialProviderAssociation.language_joined_iff
#print axioms FormulaSignSlotRadialProviderAssociation.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderFirstSeed.exists_at_occurrence
#print axioms FormulaSignSlotRadialProviderOriginalBudget.component_hit_bounded_providers
#print axioms FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_polynomial
#print axioms FormulaSignSlotRadialProviderProperAppend.exists_reachable_marked_anchor_of_source_path
#print axioms FormulaSignSlotRadialProviderMarkedAnchor.language_native_iff
#print axioms FormulaSignSlotRadialProviderMarkedAnchor.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderAnchoredAssociation.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderPreludePhaseGeometry.prelude_joined_same_provider
#print axioms FormulaSignSlotRadialProviderAnchoredGeometry.language_joined_preludes
#print axioms FormulaSignSlotRadialProviderAnchoredGeometry.language_iff_joined_preludes_of_attachments
#print axioms FormulaSignSlotRadialProviderJointWitness.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderJointWitness.of_seed_pairs
