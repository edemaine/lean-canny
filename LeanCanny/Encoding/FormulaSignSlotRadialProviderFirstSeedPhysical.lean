/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedFields
/-! # Every own seed physical block is the one prescribed critical point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem padded_suffix {n bwidth : ℕ} (fallback : Instruction n bwidth)
    (cs ds : List (Instruction n bwidth)) : paddedPast fallback (cs++ds) ds.length=ds := by
  rw [paddedPast_valid _ _ _ (by simp only [List.length_append];omega)]
  unfold past
  rw [List.reverse_append]
  have HT : (ds.reverse++cs.reverse).take ds.length=ds.reverse := by
    simpa only [List.length_reverse] using (@List.take_left _ ds.reverse cs.reverse)
  rw [HT,List.reverse_reverse]

private theorem suffix_of_eq {n bwidth : ℕ} (fallback : Instruction n bwidth)
    (all cs ds : List (Instruction n bwidth)) (N : ℕ) (hc : all=cs++ds) (hn : N=ds.length) :
    paddedPast fallback all N=ds := by cases hc;cases hn;exact padded_suffix _ _ _

private theorem candidate_from_joint (BB : IntegralFramedBankQuery.Bank) (cc w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) cc w)
    (u : ℕ→ℝ) (HJ : ∀i : Fin (IntegralFramedPhysicalSquare.count BB.parameters BB.plan (BB.key cc)),
      IntegralFramedPhysicalSquare.joint BB.parameters BB.plan BB.data BB.nodes BB.factor BB.seed BB.bounds
        BB.key BB.positive cc w hw i=u i.val)
    (i : Fin ((IntegralFramedPhysicalBankTerm.input BB).count cc)) :
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input BB) cc w hw).val i=u i.val := HJ i

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "BP" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "BD" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source prefixArity UniformIntegralPowerSchedule.physical
  commands older selections IntegralFramedPhysicalCompanionPoint.geometricPoint IntegralFramedPhysicalCompanionPoint.block

theorem older_arity (c : List Bool) : arity (older c)=FormulaSignSlotRadialProviderRecordPlan.count (root c) := by
  have HE := prefixArity_packet BP BD (B).data T FormulaSignSlotRadialProviderAtomic.bank_represents
    ((B).key (seedContext c)) (FormulaSignSlotRadialProviderRecordPlan.count (root c))
  have HK : pairFst ((B).key (seedContext c))=root c := seed_key_root c
  rw [HK] at HE
  have HC : ((BD).rules (root c))=
      (commands c).map (IntegralMixedFramedFixedContinuation.wrap (FormulaSignSlotRadialProviderRecordPlan.spatial (root c))
        (IntegralMixedStaticRecordPrefix.cap (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)) (sourceCap c)))++older c :=
    full_commands c
  have HS := suffix_of_eq (defaultInstruction BP BD (root c)) ((BD).rules (root c))
    ((commands c).map (IntegralMixedFramedFixedContinuation.wrap (FormulaSignSlotRadialProviderRecordPlan.spatial (root c))
      (IntegralMixedStaticRecordPrefix.cap (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)) (sourceCap c))))
    (older c) (FormulaSignSlotRadialProviderRecordPlan.count (root c)) HC (older_length c).symm
  have HA := congrArg arity HS
  have HN := prefix_arity c 0 (Nat.zero_le _)
  simp only [Nat.add_zero,Nat.mul_zero] at HN
  exact (HE.trans HA).symm.trans HN

theorem native_dimension (c : List Bool) :
    (B).parameters.ambient (pairFst ((B).key (seedContext c)))=(P).ambient (root c) :=
  congrArg (B).parameters.ambient (seed_key_root c)

noncomputable def nativePoint (c : List Bool) (p : Fin ((P).ambient (root c)+1)→ℝ) :
    Fin ((B).parameters.ambient (pairFst ((B).key (seedContext c)))+1)→ℝ :=
  fun i=>p (Fin.cast (congrArg (·+1) (native_dimension c)) i)

private theorem column_lt (c : List Bool) (a : ℕ)
    (ha : a<IntegralMixedCausalRecordPlanBits.count (root c))
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (seedContext c)))+1)) :
    prefixArity (B).parameters T (pair ((B).key (seedContext c))
      (List.replicate (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) true))+i.val<
        FormulaSignSlotRadialProviderAtomic.input.count (seedContext c) := by
  have HActive := critical_active c a ha
  have HL := IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T (B).key (fun _=>i.val)
    (fun _=>FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) (seedContext c)
    (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ HActive) i.isLt
  have HCount := IntegralFramedPhysicalCompanionPoint.count_eq B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (seedContext c) []
  have HC : IntegralMixedFramedCriticalGuardBits.count (B).parameters T (B).key (seedContext c)=
      FormulaSignSlotRadialProviderAtomic.input.count (seedContext c) := by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HCount
  exact HL.trans_eq HC

private theorem physical_power (c : List Bool) (a : ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key
      (fun _=>FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) (seedContext c)=
      UniformIntegralPowerSchedule.physical ((P).cap (root c)+1) (2^(P).width (root c))
        (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) := by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  have HK : pairFst ((B).key (seedContext c))=root c := seed_key_root c
  rw [HK]
  rfl

theorem WordReceipt.geometric_point {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (a : ℕ) (ha : a<IntegralMixedCausalRecordPlanBits.count (root c)) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (seedContext c) W.word W.valid
      (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a)=nativePoint c p := by
  funext i
  have HS := selections_count c
  let k : Fin (selections c).length := ⟨(selections c).length-1-a,by omega⟩
  let j : Fin ((P).ambient (root c)+1) := Fin.cast (congrArg (·+1) (native_dimension c)) i
  have HE : (selections c).length-1-k.val=a := by dsimp only [k];omega
  have HB := W.blocks k j
  rw [HE,older_arity,older_length] at HB
  have HP := prefix_arity c a ha.le
  rw [←ambient_root] at HP
  have HC := column_lt c a ha i
  unfold FormulaSignSlotRadialProviderAtomic.geometricPoint IntegralFramedPhysicalCompanionPoint.geometricPoint
    IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left HC]
  have HVal := candidate_from_joint B (seedContext c) W.word W.valid W.tuple W.joint
    ⟨prefixArity (B).parameters T (pair ((B).key (seedContext c))
      (List.replicate (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) true))+i.val,HC⟩
  have HF : W.tuple (prefixArity (B).parameters T (pair ((B).key (seedContext c))
        (List.replicate (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) true))+i.val)^
      IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key
        (fun _=>FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) (seedContext c)=nativePoint c p i := by
    have HP' : prefixArity (B).parameters T (pair ((B).key (seedContext c))
        (List.replicate (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) true))=
          FormulaSignSlotRadialProviderRecordPlan.count (root c)+(2*(P).ambient (root c)+4)*a := HP
    rw [HP',physical_power]
    exact HB
  exact (congrArg (fun z : ℝ=>z^IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key
    (fun _=>FormulaSignSlotRadialProviderRecordPlan.count (root c)+a) (seedContext c)) HVal).trans HF

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
