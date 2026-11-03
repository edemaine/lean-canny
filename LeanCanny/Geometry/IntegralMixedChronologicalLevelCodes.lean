/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelLayout
public import LeanCanny.Geometry.IntegralMixedPointCompanionCodeReadback

/-! # Literal midpoint and endpoint blocks compile to the entire native level word -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap) (hk : d.labels.length<n+1)
  (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

noncomputable def NativePair.levelMidpointRows :=
  referencedMidpointRows R.result.atomic (IntegralMixedChronologicalSweepFrame.next d hk) R.result.left R.result.right
noncomputable def NativePair.levelMidpointData :=
  referencedMidpointData R.result.atomic (IntegralMixedChronologicalSweepFrame.next d hk) R.result.left R.result.right
    g g (R.result.free_after_pair _ g hg) (R.result.free_after_pair _ g hg)
noncomputable def NativePair.levelEndpointRows (side : Bool) :=
  referencedEndpointRows (R.result.capturedFrame_atomic (R.orderedFree hk).length)
    (IntegralMixedChronologicalSweepFrame.next d hk) (R.result.endpointIndex (R.orderedFree hk).length side)
noncomputable def NativePair.levelEndpointData (side : Bool) :=
  originalPointData (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (fun _=>false) (R.levelEndpointRows hk side) g g
    (R.result.free_after_pair _ g hg) (R.result.free_after_pair _ g hg)
noncomputable def NativePair.levelMidpointCodes :=
  IntegralMixedPointCompanion.codes (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk))
    (shiftRows (R.levelMidpointRows hk) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk)
noncomputable def NativePair.levelChildCodes (side : Bool) :=
  IntegralMixedPointCompanion.codes (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (fun _=>false) (shiftRows (R.levelEndpointRows hk side) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk)
noncomputable def NativePair.levelCodes (side : Bool) :=
  R.levelChildCodes hk g hg side++[(R.levelEndpointData hk g hg side).code]++
    R.levelMidpointCodes hk g hg++[(R.levelMidpointData hk g hg).code]++R.result.codes

theorem NativePair.midpoint_point_code (j : Free (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)) :
    (originalPointData (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
      (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (R.levelMidpointRows hk)
      g j.val (R.result.free_after_pair _ g hg) j.property).code=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1)
        (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1) g.val j.val.val :=by
  have HK : R.afterDescriptor.labels.length<n+1:=by rw [NativePair.afterDescriptor,retainMany_length];exact hk
  have HC:=midpoint_code_of_eq R.afterDescriptor HK R.result.frame R.result.atomic R.frame
    (IntegralMixedChronologicalSweepFrame.next d hk) (Fin.ext (retainMany_length d _).symm)
    R.result.left R.result.right R.leftLabel R.rightLabel R.leftLabel_reference R.rightLabel_reference
    g j.val (R.result.free_after_pair _ g hg) j.property
  simpa only [NativePair.afterDescriptor,retainMany_labels,NativePair.leftLabel,NativePair.rightLabel,
    referencedMidpointData,NativePair.levelMidpointRows] using HC

theorem NativePair.endpoint_point_code (side : Bool)
    (j : Free (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)) :
    (originalPointData (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
      (R.levelEndpointRows hk side) g j.val (R.result.free_after_pair _ g hg) j.property).code=
      IntegralMixedChronologicalEndpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1) g.val j.val.val :=by
  let q:=(R.orderedFree hk).length
  have HK : (R.capturedDescriptor q).labels.length<n+1:=by rw [R.capturedDescriptor_length];exact hk
  have HC:=endpoint_code_of_eq (R.capturedDescriptor q) HK (R.result.capturedFrame q)
    (R.result.capturedFrame_atomic q) (R.capturedFrame_eq q)
    (IntegralMixedChronologicalSweepFrame.next d hk) (Fin.ext (R.capturedDescriptor_length q).symm)
    (R.result.endpointIndex q side) (R.chosenLabel q side) (R.chosenLabel_reference q side)
    g j.val (R.result.free_after_pair _ g hg) j.property
  simpa only [R.capturedDescriptor_labels,NativePair.chosenLabel,NativePair.levelEndpointRows,q,
    PairResult.capturedFrame,capturedBaseFrame,IntegralMixedPointCompanion.frame,originalFrame,retained] using HC

theorem NativePair.levelMidpointData_code :
    (R.levelMidpointData hk g hg).code=IntegralMixedChronologicalMidpointCode.code n
      (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1)
      (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1) g.val g.val :=
  R.midpoint_point_code hk g hg ⟨g,R.result.free_after_pair _ g hg⟩

theorem NativePair.levelEndpointData_code (side : Bool) :
    (R.levelEndpointData hk g hg side).code=IntegralMixedChronologicalEndpointCode.code n
      (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1) g.val g.val :=
  R.endpoint_point_code hk g hg side ⟨g,R.result.free_after_pair _ g hg⟩

theorem NativePair.levelMidpointCodes_native :
    (R.levelMidpointCodes hk g hg).reverse=IntegralMixedChronologicalMidpointCompanionCode.codes n
      (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1)
      (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1) g.val :=by
  unfold NativePair.levelMidpointCodes
  rw [codes_shift]
  have HC:=ordered_codes _ _ (R.levelMidpointRows hk) ⟨g,R.result.free_after_pair _ g hg⟩
    (R.orderedFree hk) d.labels.length (R.orderedFree_length hk) (R.orderedFree_get hk)
    (fun j=>IntegralMixedChronologicalMidpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1) (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1) g.val j)
    (R.midpoint_point_code hk g hg)
  simpa only [IntegralMixedChronologicalMidpointCompanionCode.codes,IntegralMixedChronologicalFrameCode.labels_count] using HC

theorem NativePair.levelChildCodes_native (side : Bool) :
    (R.levelChildCodes hk g hg side).reverse=IntegralMixedChronologicalCompanionCode.codes n
      (IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d)
        (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1)) g.val :=by
  unfold NativePair.levelChildCodes
  rw [codes_shift]
  have HC:=ordered_codes _ _ (R.levelEndpointRows hk side) ⟨g,R.result.free_after_pair _ g hg⟩
    (R.orderedFree hk) d.labels.length (R.orderedFree_length hk) (R.orderedFree_get hk)
    (fun j=>IntegralMixedChronologicalEndpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1) g.val j)
    (R.endpoint_point_code hk g hg side)
  simpa only [IntegralMixedChronologicalCompanionCode.codes,IntegralMixedChronologicalEndpointCode.append_count,
    IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalEndpointCode.code] using HC

def NativePair.levelPacket (side : Bool) :=IntegralMixedRoadmapLevel.packet
  (IntegralMixedChronologicalFrameCode.labels d) R.leftSpec R.rightSpec side []

theorem NativePair.levelCodes_compiled (HG : g.val=d.labels.length+1) (side : Bool) :
    (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.codes n (R.levelPacket side) :=by
  unfold NativePair.levelCodes
  rw [List.reverse_append,List.reverse_append,List.reverse_append,List.reverse_append,
    R.levelChildCodes_native,R.levelEndpointData_code,R.levelMidpointCodes_native,R.levelMidpointData_code,R.codes]
  simp only [List.reverse_singleton]
  unfold IntegralMixedRoadmapLevel.codes IntegralMixedRoadmapLevel.midpointAnchor IntegralMixedRoadmapLevel.childAnchor
    IntegralMixedRoadmapLevel.childLabels IntegralMixedRoadmapLevel.chosen IntegralMixedRoadmapLevel.producer
    IntegralMixedRoadmapLevel.g IntegralMixedRoadmapLevel.k IntegralMixedRoadmapLevel.labels
    IntegralMixedRoadmapLevel.left IntegralMixedRoadmapLevel.right IntegralMixedRoadmapLevel.sideWord
    NativePair.levelPacket IntegralMixedRoadmapLevel.packet
  simp only [pairFst_pair,pairSnd_pair,IntegralMixedChronologicalFrameCode.labels_count,HG,List.append_assoc]
  cases side <;> rfl

theorem NativePair.levelWord_compiled (HG : g.val=d.labels.length+1) (side : Bool) :
    WordList.encode (R.levelCodes hk g hg side).reverse=
      IntegralMixedRoadmapLevel.compiled n (R.levelPacket side) :=
  congrArg WordList.encode (R.levelCodes_compiled hk g hg HG side)

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
