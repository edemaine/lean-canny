/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLevelFields
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignatureBounds
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointWordCutGuard
/-! # Shared pre-child scalar fields of two sampled proper append sides -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right)
noncomputable local instance properAppendMidSignatureIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "K"=>List.length (R.orderedFree hk)
local notation "oldCount"=>List.length oldCs+List.length R.result.commands
local notation "js"=>R.orderedFree hk
local notation "rootL"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec false
local notation "rootR"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec true
open IntegralMixedChronologicalLevelScalarValues

private theorem shared_finish (side :Bool) :
    finishBirth hn ht ha hR0 old hv hd left right R side=oldCount+1+K+1+K:=by
  unfold finishBirth
  rw [R.levelCodes_length]
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  omega

private theorem levelValues_before_child {dim base :ℕ} {frozen :Finset (Fin (dim+1))}
    (pm pl pr :Fin (dim+1)→ℝ) (v :Fin base→ℝ)
    (coord :Fin (dim+1)) (sels :List (IntegralMixedPointCompanion.Free frozen))
    (i :Fin (base+1+sels.length+1+sels.length)) (hi : sels.length + 1 ≤ (i : ℕ)) :
    levelValues pm pl v coord sels i=levelValues pm pr v coord sels i:=by
  let j :Fin (base+1+sels.length):=⟨i.val-sels.length-1,by have :=i.isLt;omega⟩
  have HE :i.val=sels.length+(1+j.val):=by dsimp only [j];omega
  have H (p :Fin (dim+1)→ℝ) :levelValues pm p v coord sels i=
      IntegralMixedPointCompanion.values pm (Fin.cons (pm coord) v) sels j:=by
    unfold levelValues
    have HH:=IntegralMixedPointCompanion.values_old p
      (Fin.cons (p coord) (IntegralMixedPointCompanion.values pm (Fin.cons (pm coord) v) sels))
      sels (⟨1+j.val,by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1))
    have HI :i=(⟨sels.length+(1+j.val),by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1+sels.length)):=Fin.ext HE
    rw [HI]
    apply HH.trans
    have HJ :(⟨1+j.val,by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1))=j.succ:=Fin.ext (by simp only [Fin.val_succ];omega)
    rw [HJ]
    rfl
  exact (H pl).trans (H pr).symm

/-- Both sides retain every pre-child scalar, including both endpoint values
and every midpoint capture. Their child points need not be equal. -/
theorem WordReceipt.before_child_fields
    {uL uR :ℕ→ℝ} {p0L :Fin ((P).ambient rootL+1)→ℝ}
    {p0R :Fin ((P).ambient rootR+1)→ℝ}
    (WL :WordReceipt hn ht ha hR0 old hv hd left right R false uL p0L)
    (WR :WordReceipt hn ht ha hR0 old hv hd left right R true uR p0R)
    (pMID pChildL pChildR :Fin ((P).ambient c+1)→ℝ)
    (NL :PhysicalReadback hn ht ha hR0 old hv hd left right R false uL pMID pChildL)
    (NR :PhysicalReadback hn ht ha hR0 old hv hd left right R true uR pMID pChildR)
    (b :ℕ) (hb :b<oldCount+1+K) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair rootL []) WL.word WL.valid b=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair rootR []) WR.word WR.valid b:=by
  have HL:=physical_bank_values hn ht ha hR0 old hv hd left right R false uL pMID pChildL NL
  have HR:=physical_bank_values hn ht ha hR0 old hv hd left right R true uR pMID pChildR NR
  let idx :Fin (oldCount+1+K+1+K):=⟨oldCount+1+K+1+K-1-b,by omega⟩
  have HIL:=WordReceipt.level_field hn ht ha hR0 old hv hd left right R false WL pMID pChildL HL idx
  have HIR:=WordReceipt.level_field hn ht ha hR0 old hv hd left right R true WR pMID pChildR HR idx
  have HE :oldCount+1+K+1+K-1-idx.val=b:=by dsimp only [idx];omega
  rw [shared_finish hn ht ha hR0 old hv hd left right R false,HE] at HIL
  rw [shared_finish hn ht ha hR0 old hv hd left right R true,HE] at HIR
  exact HIL.trans ((levelValues_before_child pMID pChildL pChildR R.result.nextValues g js idx
    (by dsimp only [idx];omega)).trans HIR.symm)

private theorem packet_mid_clock (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.midBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=oldCount:=by
  have HC :IntegralMixedRoadmapProper.midBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapProper.midBirth
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side []))
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side []))
        (packet D old R.leftSpec R.rightSpec side []):=by
    simp only [dimension_packet,initial_packet,IntegralMixedRoadmapProper.midBirth,
      IntegralMixedRoadmapProper.baseBirth,IntegralMixedRoadmapProper.levelIndex,depth_packet,payload_packet]
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  exact HC.trans ((midpoint_birth hn ht ha hR0 old hv hd left right R side).trans
    (congrArg (fun b=>b+R.result.commands.length) HP.symm))

theorem coarse_labels_packet (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.labels (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapAtomic.frozen old:=by
  simp only [IntegralMixedRoadmapProper.labels,IntegralMixedRoadmapProper.levelIndex,depth_packet,
    Nat.add_sub_cancel,payload_packet,payload]
  exact IntegralMixedRoadmapChain.append_frozen_before D (IntegralMixedRoadmapAtomic.payload old)
    R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
    (IntegralMixedRoadmapAtomic.depth old) (by unfold IntegralMixedRoadmapAtomic.depth;exact le_rfl)

theorem endpoint_producer_packet (side rightSide :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.producer rightSide (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapEndpointSyntax.field (if rightSide then R.rightSpec else R.leftSpec) 1:=by
  have HE:=IntegralMixedRoadmapChain.append_entry_last D (IntegralMixedRoadmapAtomic.payload old)
    R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
  cases rightSide <;> simp only [IntegralMixedRoadmapProper.producer,
    IntegralMixedRoadmapProper.levelIndex,depth_packet,Nat.add_sub_cancel,payload_packet,payload,IntegralMixedRoadmapAtomic.depth,
    Bool.false_eq_true,ite_false,ite_true,IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,
    HE,IntegralMixedRoadmapChain.levelEntry,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]

private theorem packet_signature (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedChronologicalPointSignatureCode.code D (oldCount+1)
        (IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedRoadmapAtomic.frozen old)
          (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1))++
        pair (BinaryNatCode.encode (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1)) []:=by
  unfold IntegralMixedRoadmapProperMidSignature.ownSignature IntegralMixedRoadmapProperMidSignature.signature
    IntegralMixedRoadmapProperMidSignature.extendedLabels IntegralMixedRoadmapProper.midFirst
  rw [packet_mid_clock hn ht ha hR0 old hv hd left right R side w,
    coarse_labels_packet hn ht ha hR0 old hv hd left right R side w,
    endpoint_producer_packet hn ht ha hR0 old hv hd left right R side false w,
    endpoint_producer_packet hn ht ha hR0 old hv hd left right R side true w,dimension_packet]
  simp only [Bool.false_eq_true,ite_false,ite_true]

/-- The midpoint signature bytes retain both endpoints and ignore the chosen
child side and the independently sampled full word. -/
theorem midpoint_signature_eq (wL wR :List Bool) :
    IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0
      (packet D old R.leftSpec R.rightSpec false wL)=
    IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0
      (packet D old R.leftSpec R.rightSpec true wR):=
  (packet_signature hn ht ha hR0 old hv hd left right R false wL).trans
    (packet_signature hn ht ha hR0 old hv hd left right R true wR).symm

private theorem packet_child_clock (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=oldCount+1+K:=by
  have HC :IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapAtomic.anchor
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side []))
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side []))
        (packet D old R.leftSpec R.rightSpec side []):=by
    simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.anchor,
      IntegralMixedRoadmapAtomic.endBirth,
      IntegralMixedRoadmapAtomic.free,depth_packet,payload_packet]
  exact HC.trans ((child_anchor hn ht ha hR0 old hv hd left right R side).trans
    (congrArg (fun b=>b+1+K) (packet_mid_clock hn ht ha hR0 old hv hd left right R side [])))

/-- The sampled endpoint producers carry the chosen endpoint values, for
either child side, including retained and fresh endpoint cases. -/
theorem WordReceipt.endpoint_fields (side :Bool)
    {u :ℕ→ℝ} {p0 :Fin ((P).ambient (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side)+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (pair (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side) []) W.word W.valid
      (IntegralMixedRoadmapProper.producer false (packet D old R.leftSpec R.rightSpec side W.word))=
        left.value (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he) ∧
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (pair (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side) []) W.word W.valid
      (IntegralMixedRoadmapProper.producer true (packet D old R.leftSpec R.rightSpec side W.word))=
        right.value (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he):=by
  have HV:=physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  have HL:=WordReceipt.endpoint_field_at hn ht ha hR0 old hv hd left right R side W pMID pChild HV R.result.left
  have HR:=WordReceipt.endpoint_field_at hn ht ha hR0 old hv hd left right R side W pMID pChild HV R.result.right
  have BL:=R.leftLabel.isLt
  have BR:=R.rightLabel.isLt
  change IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1<oldCount at BL
  change IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1<oldCount at BR
  have EL :beginBirth hn ht ha hR0 old+R.result.commands.length-1-R.result.left.val=
      IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1:=by
    have HE:=R.left_reference
    omega
  have ER :beginBirth hn ht ha hR0 old+R.result.commands.length-1-R.result.right.val=
      IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1:=by
    have HE:=R.right_reference
    omega
  rw [EL] at HL
  rw [ER] at HR
  rw [endpoint_producer_packet hn ht ha hR0 old hv hd left right R side false W.word,
    endpoint_producer_packet hn ht ha hR0 old hv hd left right R side true W.word]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  exact ⟨HL.trans R.result.left_value,HR.trans R.result.right_value⟩

private theorem midpoint_packet_context (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side w)=
      pair (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side) []:=by
  simp only [IntegralMixedRoadmapAtomic.context,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet]

/-- Independent full words for the same pair and midpoint pass the actual
native signature comparison, including both endpoint fields. -/
theorem WordReceipt.midpoint_signature
    {uL uR :ℕ→ℝ} {p0L :Fin ((P).ambient rootL+1)→ℝ}
    {p0R :Fin ((P).ambient rootR+1)→ℝ}
    (WL :WordReceipt hn ht ha hR0 old hv hd left right R false uL p0L)
    (WR :WordReceipt hn ht ha hR0 old hv hd left right R true uR p0R)
    (pMID pChildL pChildR :Fin ((P).ambient c+1)→ℝ)
    (NL :PhysicalReadback hn ht ha hR0 old hv hd left right R false uL pMID pChildL)
    (NR :PhysicalReadback hn ht ha hR0 old hv hd left right R true uR pMID pChildR)
    (hvL :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec false WL.word))
    (hvR :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec true WR.word)) :
    pair (packet D old R.leftSpec R.rightSpec false WL.word)
      (packet D old R.leftSpec R.rightSpec true WR.word)∈
        IntegralMixedRoadmapProperMidSignature.language hn ht ha hR0:=by
  let qL:=packet D old R.leftSpec R.rightSpec false WL.word
  let qR:=packet D old R.leftSpec R.rightSpec true WR.word
  have HD :IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 qL=
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 qR:=by
    rw [dimension_packet,dimension_packet]
  have HL :0<IntegralMixedRoadmapAtomic.depth qL:=by rw [depth_packet];omega
  have HR :0<IntegralMixedRoadmapAtomic.depth qR:=by rw [depth_packet];omega
  have HC :IntegralMixedRoadmapProperMidSignature.Compatible hn ht ha hR0 (pair qL qR):=by
    simp only [IntegralMixedRoadmapProperMidSignature.Compatible,
      IntegralMixedRoadmapProperMidSignature.left,IntegralMixedRoadmapProperMidSignature.right,
      pairFst_pair,pairSnd_pair]
    exact ⟨HD,by rw [depth_packet,depth_packet],HL⟩
  have HVL:=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 qL hvL
  have HVR:=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 qR hvR
  have HB :∀i<WordListRecords.count (IntegralMixedRoadmapProperMidSignature.table hn ht ha hR0 (pair qL qR)),
      IntegralMixedPhysicalFieldEqualityList.label false
        (WordList.get (IntegralMixedRoadmapProperMidSignature.table hn ht ha hR0 (pair qL qR)) i)<
          IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context qL) ∧
      IntegralMixedPhysicalFieldEqualityList.label true
        (WordList.get (IntegralMixedRoadmapProperMidSignature.table hn ht ha hR0 (pair qL qR)) i)<
          IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context qR):=by
    intro i hi
    have HI :i<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 qL+2:=by
      rwa [IntegralMixedRoadmapProperMidSignature.table_pair_count] at hi
    rw [IntegralMixedRoadmapProperMidSignature.table_pair_lookup hn ht ha hR0 qL qR ⟨i,HI⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    exact ⟨IntegralMixedRoadmapProperMidSignature.signature_bounded_full hn ht ha hR0 qL hvL HL i HI,
      IntegralMixedRoadmapProperMidSignature.signature_bounded_full hn ht ha hR0 qR hvR HR i (by omega)⟩
  have HE :IntegralMixedRoadmapProperMidSignature.query hn ht ha hR0 (pair qL qR)∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
    unfold IntegralMixedRoadmapProperMidSignature.query
    simp only [IntegralMixedRoadmapProperMidSignature.left,IntegralMixedRoadmapProperMidSignature.right,
      pairFst_pair,pairSnd_pair]
    apply (IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0)
      _ _ _ _ _ HVL HVR HB).mpr
    intro i hi
    have HI :i<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 qL+2:=by
      rwa [IntegralMixedRoadmapProperMidSignature.table_pair_count] at hi
    rw [IntegralMixedRoadmapProperMidSignature.table_pair_lookup hn ht ha hR0 qL qR ⟨i,HI⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    have HS :IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0 qL=
        IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0 qR:=
      midpoint_signature_eq hn ht ha hR0 old hv hd left right R WL.word WR.word
    rw [←HS]
    let b:=Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperMidSignature.ownSignature hn ht ha hR0 qL) i)
    have BB:=IntegralMixedRoadmapProperMidSignature.signature_bounded_before_child hn ht ha hR0 qL hvL HL i HI
    rw [packet_child_clock hn ht ha hR0 old hv hd left right R false WL.word] at BB
    have HH:=WordReceipt.before_child_fields hn ht ha hR0 old hv hd left right R WL WR
      pMID pChildL pChildR NL NR b BB
    simpa only [qL,qR,b,midpoint_packet_context,word_packet] using HH
  exact ⟨HC,HE⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
