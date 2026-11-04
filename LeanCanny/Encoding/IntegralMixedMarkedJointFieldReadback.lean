/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendWord
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # Actual chronological fields of a fixed full-word joint tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedJointFieldReadback
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
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralFramedPhysicalSquare.point
  IntegralMixedPhysicalFieldEquality.point

noncomputable def Joint (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (pair root []) w) (u :ℕ→ℝ) :Prop:=
  ∀i :Fin (IntegralFramedPhysicalSquare.count (BP).parameters (BP).plan ((BP).key (pair root []))),
    IntegralFramedPhysicalSquare.joint (BP).parameters (BP).plan (BP).data (BP).nodes (BP).factor (BP).seed
      (BP).bounds (BP).key (BP).positive (pair root []) w
        (IntegralMixedRoadmapProperAppend.proper_valid_to_parent hn ht ha hR0 _ _ hw) i=u i.val

private theorem joint_native (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (pair root []) w) (u :ℕ→ℝ)
    (HJ :Joint hn ht ha hR0 root w hw u) :BankJoint B (pair root []) w u:=by
  have HE :B=BP:=by unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank;rfl
  have HP :BankJoint BP (pair root []) w u:=by intro hvalid;exact HJ
  exact (congrArg (fun K=>BankJoint K (pair root []) w u) HE).mpr HP

theorem field_observation (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (pair root []) w) (u :ℕ→ℝ)
    (HJ :Joint hn ht ha hR0 root w hw u) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair root []) w hw b=
      (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).point u
        (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-1-b) :=by
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (pair root [])=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq,pairFst_pair]
  have HP :IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (pair root []))=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    have HE :B=BP:=by unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank;rfl
    rw [HE]
    exact IntegralMixedMarkedReservedParent.full_prefix hn ht ha hR0 root
  have HI :IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-1-b<
      (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth ((B).key (pair root [])):=by
    change _<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (pair root [])
    rw [HC];omega
  have HX:=bank_observation B (pair root []) w hw u (joint_native hn ht ha hR0 root w hw u HJ) ⟨_,HI⟩
  have HT:=IntegralMixedMarkedPrefixFieldReadback.terminal_bank_data hn ht ha hR0 root
  have HY:=HX.trans (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>
    O.point u (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-1-b)) HT)
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) (pair root []) w hw b
    (by rw [HP];exact hb)
  simp only [HP] at HF
  exact HF.trans HY

end LeanCanny.Encoding.IntegralMixedMarkedJointFieldReadback
