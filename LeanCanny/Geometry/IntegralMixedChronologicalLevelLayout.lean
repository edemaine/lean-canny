/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalAtomicFrameReadback
public import LeanCanny.Geometry.IntegralMixedMatchedOptionalAnchorCaptures
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelCode

/-! # The actual optional pair determines every retained endpoint and child label -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem retainMany_length (d : Descriptor n m) (q : ℕ) : (retainMany d q).labels.length=d.labels.length :=by
  have HE:=congrArg WordListRecords.count (retainMany_labels d q)
  simpa only [IntegralMixedChronologicalFrameCode.labels_count] using HE

noncomputable def NativePair.afterDescriptor (R : NativePair x d z φ values left right hn hcap) :=
  retainMany d R.result.commands.length

def NativePair.leftLabel (R : NativePair x d z φ values left right hn hcap) : Fin (m+R.result.commands.length):=
  ⟨IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1,by
    have HP:=IntegralMixedRoadmapEndpointSyntax.producer_lt R.left_good le_rfl
    have HC:=R.native_count
    omega⟩
def NativePair.rightLabel (R : NativePair x d z φ values left right hn hcap) : Fin (m+R.result.commands.length):=
  ⟨IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1,by
    have HP:=IntegralMixedRoadmapEndpointSyntax.producer_lt R.right_good (by omega)
    have HC:=R.native_count
    omega⟩

theorem NativePair.leftLabel_reference (R : NativePair x d z φ values left right hn hcap) :
    R.result.left=IntegralMixedChronologicalMidpoint.reference R.leftLabel :=Fin.ext R.left_reference
theorem NativePair.rightLabel_reference (R : NativePair x d z φ values left right hn hcap) :
    R.result.right=IntegralMixedChronologicalMidpoint.reference R.rightLabel :=Fin.ext R.right_reference

noncomputable def NativePair.capturedDescriptor (R : NativePair x d z φ values left right hn hcap) (q : ℕ) :=
  retainMany R.afterDescriptor.retain q

theorem NativePair.capturedDescriptor_length (R : NativePair x d z φ values left right hn hcap) (q : ℕ) :
    (R.capturedDescriptor q).labels.length=d.labels.length :=by
  rw [NativePair.capturedDescriptor,retainMany_length,Descriptor.retain_length]
  exact retainMany_length d _

theorem NativePair.capturedDescriptor_labels (R : NativePair x d z φ values left right hn hcap) (q : ℕ) :
    IntegralMixedChronologicalFrameCode.labels (R.capturedDescriptor q)=IntegralMixedChronologicalFrameCode.labels d :=by
  rw [NativePair.capturedDescriptor,retainMany_labels,IntegralMixedRoadmapEndpointSyntax.labels_retain]
  exact retainMany_labels d _

theorem NativePair.capturedFrame_eq (R : NativePair x d z φ values left right hn hcap) (q : ℕ) :
    R.result.capturedFrame q=(R.capturedDescriptor q).frame :=by
  have HE : retained R.result.frame=R.afterDescriptor.retain.frame:=
    (congrArg retained R.frame).trans R.afterDescriptor.frame_retain.symm
  exact captured_frame R.afterDescriptor.retain (retained R.result.frame) R.result.atomic.retained HE q

def NativePair.chosenLabel (R : NativePair x d z φ values left right hn hcap) (q : ℕ) (side : Bool) :
    Fin (m+R.result.commands.length+1+q):=
  ⟨IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1,by
    have HH:=(if side then R.rightLabel else R.leftLabel).isLt
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,NativePair.leftLabel,NativePair.rightLabel] at HH ⊢ <;> omega⟩

theorem NativePair.chosenLabel_reference (R : NativePair x d z φ values left right hn hcap) (q : ℕ) (side : Bool) :
    R.result.endpointIndex q side=IntegralMixedChronologicalMidpoint.reference (R.chosenLabel q side) :=by
  apply Fin.ext
  rw [R.result.endpointIndex_val]
  have HI:=R.reference side
  have HP:=(if side then R.rightLabel else R.leftLabel).isLt
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at HI HP ⊢
  all_goals change _=(m+R.result.commands.length+1+q)-1-_
  all_goals dsimp only [NativePair.chosenLabel,NativePair.leftLabel,NativePair.rightLabel] at *
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at *
  all_goals omega

noncomputable def NativePair.childFrameDescriptor (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) (q : ℕ) (side : Bool) :=
  (R.capturedDescriptor q).freeze (R.chosenLabel q side)
    (by rw [R.capturedDescriptor_length];exact hk)

theorem NativePair.childFrameDescriptor_labels (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) (q : ℕ) (side : Bool) :
    IntegralMixedChronologicalFrameCode.labels (R.childFrameDescriptor hk q side)=
      IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d)
        (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1) :=by
  rw [NativePair.childFrameDescriptor,←IntegralMixedChronologicalEndpointCode.append_actual,
    R.capturedDescriptor_labels]
  rfl

theorem NativePair.endpointFrame_eq (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) (q : ℕ) (side : Bool) :
    R.result.endpointFrame (IntegralMixedChronologicalSweepFrame.next d hk) q side=
      (R.childFrameDescriptor hk q side).frame :=by
  exact endpoint_frame_of_eq (R.capturedDescriptor q) (by rw [R.capturedDescriptor_length];exact hk)
    (R.result.capturedFrame q) (R.result.capturedFrame_atomic q) (R.capturedFrame_eq q)
    (IntegralMixedChronologicalSweepFrame.next d hk) (Fin.ext (R.capturedDescriptor_length q).symm)
    (R.result.endpointIndex q side) (R.chosenLabel q side) (R.chosenLabel_reference q side)

noncomputable def NativePair.orderedFree (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) : List (Free (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)) :=
  List.ofFn (fun i : Fin (n+1-(d.labels.length+1))=>
    ⟨⟨d.labels.length+1+i.val,by have :=i.isLt;omega⟩,by
      rw [R.result.frozen,Finset.mem_insert,d.frozen_mem,Fin.ext_iff]
      change ¬(d.labels.length+1+i.val=d.labels.length ∨ d.labels.length+1+i.val<d.labels.length)
      omega⟩)

theorem NativePair.orderedFree_length (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) : (R.orderedFree hk).length=n+1-(d.labels.length+1) :=List.length_ofFn

theorem NativePair.orderedFree_get (R : NativePair x d z φ values left right hn hcap)
    (hk : d.labels.length<n+1) (i : Fin (R.orderedFree hk).length) :
    ((R.orderedFree hk).get i).val.val=d.labels.length+1+i.val :=by
  simp only [NativePair.orderedFree,List.get_eq_getElem,List.getElem_ofFn]

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
