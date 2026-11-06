/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendLocalReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendColumns
/-! # The complete own tuple retains both prescribed local physical blocks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_column_lt (a span blocks off i : ℕ) (h : off<blocks) (hi : i<span) :
    a+span*off+i<a+span*blocks := by
  have H : off+1≤blocks := by omega
  have HM := Nat.mul_le_mul_left span H
  have HI : a+span*off+i<a+span*(off+1) := by rw [Nat.mul_succ];omega
  exact HI.trans_le (Nat.add_le_add_left HM a)

private theorem candidate_from_joint (B : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (u : ℕ→ℝ) (HJ : ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val)
    (i : Fin ((IntegralFramedPhysicalBankTerm.input B).count c)) :
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val i=u i.val := HJ i

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor levelProgram levelObservation
variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.local_arity (W : WordReceipt old hv hd e he p) :
    arity (levelProgram old hv hd e he W.pair false)=arity (parentCommands old hv hd e he)+
      (2*(RP).ambient (preparedRoot old e)+4)*
        (2+2*(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length) := by
  have H := W.pair.level_physical_arity
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
    (parentCommands old hv hd e he) (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) false
  simpa only [levelProgram,pair_commands_nil old hv hd e he W.pair,List.map_nil,List.nil_append] using H

theorem WordReceipt.receipt_local_powered (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : (parentCommands old hv hd e he).length≤b)
    (hb1 : b<(parentCommands old hv hd e he).length+2+
      2*(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)
    (i : Fin ((RP).ambient (preparedRoot old e)+1)) :
    W.tuple (arity (parentCommands old hv hd e he)+(2*(RP).ambient (preparedRoot old e)+4)*
      (b-(parentCommands old hv hd e he).length)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b=p i := by
  have HC : arity (parentCommands old hv hd e he)+(2*(RP).ambient (preparedRoot old e)+4)*
      (b-(parentCommands old hv hd e he).length)+i.val<arity (levelProgram old hv hd e he W.pair false) := by
    rw [W.local_arity]
    apply critical_column_lt
    · omega
    · have HI := i.isLt
      omega
  rw [W.full.2.1 _ HC]
  exact W.local_powered b hb0 hb1 i

theorem native_dimension (old : List Bool) (e : ℕ) :
    (B).parameters.ambient (pairFst ((B).key (C (preparedRoot old e))))=(P).ambient (preparedRoot old e) :=
  congrArg (B).parameters.ambient (FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old e))

noncomputable def nativePoint (old : List Bool) (e : ℕ)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) :
    Fin ((B).parameters.ambient (pairFst ((B).key (C (preparedRoot old e))))+1)→ℝ :=
  fun i=>p (Fin.cast (congrArg (·+1) (native_dimension old e)) i)

private theorem physical_power (old : List Bool) (e b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) (C (preparedRoot old e))=
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b := by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
  rfl

private theorem native_column_lt (old : List Bool) (e b : ℕ)
    (hb : FormulaSignSlotRadialProviderAtomic.Active (C (preparedRoot old e)) b)
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (C (preparedRoot old e))))+1)) :
    prefixArity (B).parameters T (pair ((B).key (C (preparedRoot old e))) (List.replicate b true))+i.val<
      FormulaSignSlotRadialProviderAtomic.input.count (C (preparedRoot old e)) := by
  have H := IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T (B).key (fun _=>i.val)
    (fun _=>b) (C (preparedRoot old e))
    (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ hb) i.isLt
  have HC := IntegralFramedPhysicalCompanionPoint.count_eq B T
    FormulaSignSlotRadialProviderAtomic.bank_represents (C (preparedRoot old e)) []
  have HE : IntegralMixedFramedCriticalGuardBits.count (B).parameters T (B).key (C (preparedRoot old e))=
      FormulaSignSlotRadialProviderAtomic.input.count (C (preparedRoot old e)) := by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HC
  exact H.trans_eq HE

theorem WordReceipt.local_geometric_point (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b<finishBirth old e) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C (preparedRoot old e)) W.word W.valid b=
      nativePoint old e p := by
  have HA := active_after_begin old hv hd e he b hb0 (hb1.trans_le (finish_le_full old hv hd e he))
  have HBegin : (parentCommands old hv hd e he).length=N old+start old :=
    (parent_length old hv hd e he).trans (begin_eq old)
  have HK := W.pair.orderedFree_length (parent_descriptor_fit old hv hd e he)
  have HD : (RP).ambient (preparedRoot old e)=dimension old := prepared_dimension old e
  have HF := parent_descriptor_length old hv hd e he
  have HFree : (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=dimension old-depth old := by omega
  have HEnd : finishBirth old e=(parentCommands old hv hd e he).length+2+
      2*(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length := by
    have HX := finish_eq old e
    have HB := parent_length old hv hd e he
    omega
  funext i
  let j := Fin.cast (congrArg (·+1) (native_dimension old e)) i
  have HB := W.receipt_local_powered b (by omega) (by omega) j
  have HCol := native_column_lt old e b HA i
  have HValue := candidate_from_joint B (C (preparedRoot old e)) W.word W.valid W.tuple W.joint
    ⟨_,HCol⟩
  have HE : prefixArity (B).parameters T (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))+i.val=
      arity (parentCommands old hv hd e he)+(2*(RP).ambient (preparedRoot old e)+4)*
        (b-(parentCommands old hv hd e he).length)+j.val := by
    have HP : prefixArity (B).parameters T
        (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))=
        arity (parentCommands old hv hd e he)+(2*dimension old+4)*(b-(N old+start old)) :=
      prefix_arity_after_begin old hv hd e he b hb0 (hb1.le.trans (finish_le_full old hv hd e he))
    rw [HP,HBegin,HD]
    simp only [j,Fin.val_cast]
  unfold FormulaSignSlotRadialProviderAtomic.geometricPoint IntegralFramedPhysicalCompanionPoint.geometricPoint
    IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left HCol,HValue,physical_power]
  change W.tuple (prefixArity (B).parameters T
    (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b=p j
  rw [HE]
  exact HB

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
