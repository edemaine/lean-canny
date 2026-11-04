/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendMidSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapProperOriginalGuards
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendAcceptance
/-! # The constructed endpoint fields give actual original order guards -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

theorem order_bounds_of_valid (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd :0<IntegralMixedRoadmapAtomic.depth q):
    IntegralMixedRoadmapProper.OrderBounds hn ht ha hR0 q:=by
  have HM:=IntegralMixedRoadmapProper.checked_midpoint_good
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv) hd
  have HA:=(IntegralMixedRoadmapCheckedProperMetadata.midpoint_anchor hn ht ha hR0 q
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv) hd).1
  have HBound:=HA.1
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] at HBound
  have HE :IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q=
      (IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data).birth
        ((BK).key (IntegralMixedRoadmapAtomic.context q)):=by
    unfold IntegralMixedRoadmapProper.fullCount IntegralMixedPhysicalFieldEquality.count
    rfl
  have HBirth:=HBound.trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth
    (BK).parameters (BK).plan (BK).data ((BK).key (IntegralMixedRoadmapAtomic.context q))).symm
  have HB :IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q<IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q:=
    HBirth.trans_eq HE.symm
  exact ⟨HM.2.1.trans HB,HM.2.2.1.trans HB⟩

private theorem original_field_at_context (q ctx w :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hw :SquareSampleCompleteVertices.Valid SAMP ctx w)
    (hc :IntegralMixedRoadmapAtomic.context q=ctx) (he :IntegralMixedRoadmapAtomic.word q=w) (i :ℕ):
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) ctx w hw i:=by
  subst ctx
  subst w
  rfl

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapLocalFrame.field IntegralMixedPhysicalFieldEquality.point

theorem WordReceipt.original_endpoint_fields {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word)):
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV
      (IntegralMixedRoadmapProper.producer false (packet D old R.leftSpec R.rightSpec side W.word))=left.value V ∧
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV
      (IntegralMixedRoadmapProper.producer true (packet D old R.leftSpec R.rightSpec side W.word))=right.value V:=by
  have HC :IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side W.word)=pair r []:=by
    simp only [IntegralMixedRoadmapAtomic.context,IntegralMixedRoadmapAtomic.root,
      candidate_packet,payload_packet,preparedRoot]
  have H:=W.endpoint_fields hn ht ha hR0 old hv hd left right R side pMID pChild N
  exact ⟨(original_field_at_context hn ht ha hR0 _ _ _ hV W.valid HC (word_packet _ _ _ _ _ _) _).trans H.1,
    (original_field_at_context hn ht ha hR0 _ _ _ hV W.valid HC (word_packet _ _ _ _ _ _) _).trans H.2⟩

theorem WordReceipt.original_order {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hab :left.value V<right.value V):
    IntegralMixedRoadmapProper.order hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word)=
      InfinitesimalSign.encode 1:=by
  have HDepth :0<IntegralMixedRoadmapAtomic.depth (packet D old R.leftSpec R.rightSpec side W.word):=by
    rw [depth_packet]
    omega
  apply (IntegralMixedRoadmapLocalFrame.order_iff_original_fields hn ht ha hR0 _ hV
    (order_bounds_of_valid hn ht ha hR0 _ hV HDepth)).mpr
  have H:=W.original_endpoint_fields hn ht ha hR0 old hv hd left right R side N hV
  rw [H.1,H.2]
  exact hab

/-- Every old chronological field is read on the new word, then identified
with the original accepted node by literal raw-column retention. -/
theorem WordReceipt.original_old_fields {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (b :ℕ) (hb :b<beginBirth hn ht ha hR0 old):
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV b=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv b:=by
  have HC :IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side W.word)=pair r []:=by
    simp only [IntegralMixedRoadmapAtomic.context,IntegralMixedRoadmapAtomic.root,
      candidate_packet,payload_packet,preparedRoot]
  have HP:=past_fields hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
    (endpoints_good hn ht ha hR0 old hv hd left right R) W.word W.valid
    (W.old_raw hn ht ha hR0 old hv hd left right R side hOld) b hb
  have HE :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedMarkedPrefixFieldReadback.context (IntegralMixedRoadmapAtomic.root old))
      (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) b=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv b:=by
    unfold IntegralMixedRoadmapLocalFrame.field
    rfl
  exact (original_field_at_context hn ht ha hR0 _ _ _ hV W.valid HC (word_packet _ _ _ _ _ _) b).trans
    (HP.trans HE)

/-- The actual coarse frozen numerical values are exactly those of the
canonical geometric parent, including the original chronological labels. -/
theorem WordReceipt.original_frozen_values {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (i :Fin (d).labels.length):
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV
      (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen old) i.val))=V ((d).reference i):=by
  have HL:=IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
  rw [IntegralMixedRoadmapRetainedAppend.parent_labels hn ht ha hR0 old hv hd e he] at HL
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  have HFit :Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen old) i.val)<
      beginBirth hn ht ha hR0 old:=by
    rw [HL]
    exact ((d).labels.get i).isLt.trans_eq HP
  have HF:=W.original_old_fields hn ht ha hR0 old hv hd left right R side hV hOld _ HFit
  have HV:=IntegralMixedRoadmapRetainedAppend.parent_frozen_value hn ht ha hR0 old hv hd e he i
  unfold IntegralMixedRoadmapAtomic.levels at HV
  have HE :IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv
      (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen old) i.val))=V ((d).reference i):=by
    unfold IntegralMixedRoadmapLocalFrame.field
    exact HV.symm
  exact HF.trans HE

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
