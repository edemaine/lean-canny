/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPadding
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNoCut
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedFieldReadback
/-! # Scalar fields of a fresh retained-append word from its actual bank values -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial commands)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem command_room (A :Parameters) (D :IntegralMixedFramedHistoryFamilyBits.Plan A) (key :List Bool) :
    (commands A D key).length≤A.cap (pairFst key)+1+1:=by
  rw [commands,paddedPast_length]
  exact (min_le_right _ _).trans (Nat.le_succ _)

private def BankJoint (K :IntegralFramedBankQuery.Bank) (c w :List Bool) (u :ℕ→ℝ) :Prop:=
  ∀hv :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w,
  ∀i :Fin (IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c)),
    IntegralFramedPhysicalSquare.joint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hv i=u i.val

private theorem bank_observation (K :IntegralFramedBankQuery.Bank) (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (u :ℕ→ℝ) (HJ :BankJoint K c w u)
    (i :Fin ((IntegralMixedFramedHistoryFamilyBits.family K.parameters K.plan K.data).birth (K.key c))) :
    IntegralFramedPhysicalSquare.point K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hw i=
    (IntegralMixedFramedRunObservation.ofCommands (initial K.parameters K.plan (pairFst (K.key c)))
      (commands K.parameters K.plan (K.key c)) (command_room K.parameters K.plan (K.key c))).point u i.val:=
  IntegralFramedPhysicalSquare.point_of_joint_natural K.parameters K.plan K.data K.nodes K.factor K.seed
    K.bounds K.key K.positive c w hw u (HJ hw) i

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family preparedRoot parentCommands parentValues
  midpointSelections childSelections localInstructions localObservation seedTailCount
  IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralFramedPhysicalSquare.point
  IntegralMixedPhysicalFieldEquality.point

noncomputable def FieldJoint (old :List Bool) (e :ℕ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old e) w) (u :ℕ→ℝ) :Prop:=
  ∀i :Fin (IntegralFramedPhysicalSquare.count (BP).parameters (BP).plan ((BP).key (CTX old e))),
    IntegralFramedPhysicalSquare.joint (BP).parameters (BP).plan (BP).data (BP).nodes (BP).factor (BP).seed
      (BP).bounds (BP).key (BP).positive (CTX old e) w
        (IntegralMixedRoadmapSeedResampling.seed_valid_to_parent hn ht ha hR0 _ _ hw) i=u i.val

private theorem field_joint_native (old :List Bool) (e :ℕ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old e) w) (u :ℕ→ℝ)
    (HJ :FieldJoint hn ht ha hR0 old e w hw u) :BankJoint B (CTX old e) w u:=by
  have HE :B=BP:=by unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank;rfl
  have HP :BankJoint BP (CTX old e) w u:=by intro hvalid;exact HJ
  exact (congrArg (fun K=>BankJoint K (CTX old e) w u) HE).mpr HP

structure FieldValues (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (e :ℕ) (he :e<beginBirth hn ht ha hR0 old)
    (p p0 :Fin ((P).ambient (ROOT old e)+1)→ℝ) (z u :ℕ→ℝ) :Prop where
  local_values :∀i :Fin ((parentCommands hn ht ha hR0 old hv hd e he).length+
      (midpointSelections hn ht ha hR0 old hv hd e he).length+(childSelections hn ht ha hR0 old hv hd e he).length),
    (localObservation hn ht ha hR0 old hv hd e he).point z i.val=
      IntegralMixedPointCompanion.values p
        (IntegralMixedPointCompanion.values p (parentValues hn ht ha hR0 old hv hd e he)
          (midpointSelections hn ht ha hR0 old hv hd e he)) (childSelections hn ht ha hR0 old hv hd e he) i
  full_values :∀i :Fin ((localInstructions hn ht ha hR0 old hv hd e he).length+
      (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (ROOT old e)) (seedTailCount hn ht ha hR0 old e)).length),
    (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 (ROOT old e)).point u i.val=
      IntegralMixedPointCompanion.values p0
        (fun j=>(localObservation hn ht ha hR0 old hv hd e he).point z j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (ROOT old e)) (seedTailCount hn ht ha hR0 old e)) i

theorem field_observation (old :List Bool) (e :ℕ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old e) w) (u :ℕ→ℝ)
    (HJ :FieldJoint hn ht ha hR0 old e w hw u) (b :ℕ) (hb :b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old e) w hw b=
      (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 (ROOT old e)).point u
        (fullBirth hn ht ha hR0 old e-1-b) :=by
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX old e)=
      fullBirth hn ht ha hR0 old e:=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,fullBirth]
  have HP:=prefix_length hn ht ha hR0 old e
  have HI :fullBirth hn ht ha hR0 old e-1-b<
      (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth ((B).key (CTX old e)):=by
    change _<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX old e)
    rw [HC];omega
  have HX:=bank_observation B (CTX old e) w hw u (field_joint_native hn ht ha hR0 old e w hw u HJ) ⟨_,HI⟩
  have HT:=IntegralMixedMarkedPrefixFieldReadback.terminal_bank_data hn ht ha hR0 (ROOT old e)
  have HY:=HX.trans (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>
    O.point u (fullBirth hn ht ha hR0 old e-1-b)) HT)
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) (CTX old e) w hw b
    (by rw [HP];exact hb)
  simp only [HP] at HF
  exact HF.trans HY

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
