/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPhysical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendScalarReadback
/-! # The fresh own word retains the genuine padding point in every tail block -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem padding_candidate_from_joint (B : IntegralFramedBankQuery.Bank) (c w : List Bool)
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

private theorem padding_physical_power (old : List Bool) (e b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) (C (preparedRoot old e))=
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b := by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
  rfl

private theorem padding_native_column_lt (old : List Bool) (e b : ℕ)
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

theorem WordReceipt.padding_geometric_point (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : finishBirth old e≤b) (hb1 : b<fullBirth old e) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C (preparedRoot old e)) W.word W.valid b=
      nativePoint old e W.paddingPoint := by
  have HF0 := finish_eq old e
  have HBegin := begin_eq old
  have HBF : N old+start old≤finishBirth old e := by omega
  have HA := active_after_begin old hv hd e he b (HBF.trans hb0) hb1
  have HL := local_program_length old hv hd e he W.pair
  have HF := padded_program_length old hv hd e he W.pair
  have HD : (RP).ambient (preparedRoot old e)=dimension old := prepared_dimension old e
  have HK := W.pair.orderedFree_length (parent_descriptor_fit old hv hd e he)
  have HDesc := parent_descriptor_length old hv hd e he
  have HFree : (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=dimension old-depth old := by omega
  have HBase : arity (levelProgram old hv hd e he W.pair false)=arity (parentCommands old hv hd e he)+
      (2*dimension old+4)*(finishBirth old e-(N old+start old)) := by
    simp only [W.local_arity,HFree,HD]
    have HC : finishBirth old e-(N old+start old)=2+2*(dimension old-depth old) := by omega
    rw [HC]
  let js := IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)
  let j : Fin js.length := ⟨js.length-1-(b-finishBirth old e),by
    change fullBirth old e=(levelProgram old hv hd e he W.pair false).length+js.length at HF
    omega⟩
  have HJ : js.length-1-j.val=b-finishBirth old e := by
    dsimp only [j]
    change fullBirth old e=(levelProgram old hv hd e he W.pair false).length+js.length at HF
    omega
  funext i
  let k := Fin.cast (congrArg (·+1) (native_dimension old e)) i
  have HB := W.full.2.2.1 j k
  change W.tuple (arity (levelProgram old hv hd e he W.pair false)+
    (2*(P).ambient (preparedRoot old e)+4)*(js.length-1-j.val)+k.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) ((levelProgram old hv hd e he W.pair false).length+(js.length-1-j.val))=
    W.paddingPoint k at HB
  rw [HJ,HL,Nat.add_sub_of_le hb0] at HB
  have HCol := padding_native_column_lt old e b HA i
  have HValue := padding_candidate_from_joint B (C (preparedRoot old e)) W.word W.valid W.tuple W.joint ⟨_,HCol⟩
  have HColumn : prefixArity (B).parameters T (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))+i.val=
      arity (levelProgram old hv hd e he W.pair false)+(2*(P).ambient (preparedRoot old e)+4)*
        (b-finishBirth old e)+k.val := by
    have HP : prefixArity (B).parameters T
        (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))=
        arity (parentCommands old hv hd e he)+(2*dimension old+4)*(b-(N old+start old)) :=
      prefix_arity_after_begin old hv hd e he b (HBF.trans hb0) hb1.le
    have HD' : (P).ambient (preparedRoot old e)=dimension old := prepared_dimension old e
    have HS : b-(N old+start old)=(finishBirth old e-(N old+start old))+(b-finishBirth old e) := by omega
    simp only [HP,HBase,k,Fin.val_cast,HD']
    rw [HS,Nat.mul_add]
    omega
  unfold FormulaSignSlotRadialProviderAtomic.geometricPoint IntegralFramedPhysicalCompanionPoint.geometricPoint
    IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left HCol,HValue,padding_physical_power]
  change W.tuple (prefixArity (B).parameters T
    (LeanCanny.pair ((B).key (C (preparedRoot old e))) (List.replicate b true))+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b=W.paddingPoint k
  rw [HColumn]
  exact HB

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
