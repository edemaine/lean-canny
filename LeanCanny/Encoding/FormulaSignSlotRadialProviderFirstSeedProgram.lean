/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedLayout
public import LeanCanny.Encoding.IntegralMixedSourceIntegerStaticRecords
public import LeanCanny.Geometry.IntegralMixedChronologicalSeedProgram
public import LeanCanny.Geometry.IntegralMixedPointCompanionDecoded
/-! # The literal provider seed bytes compile to the same point-capture program -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem compile_full {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (Q : SpatialSource n) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (N C : ℕ) (p : ℕ→Polynomial ℤ) (hp : ∀i,p i≠0) (hd : ∀i,(p i).natDegree≤2^B)
    (w : ℕ→List Bool)
    (room : (IntegralMixedStaticRecordPrefix.records Q hn hcap N C p hp hd w).length≤S+1)
    (fallback : Instruction n B) (codes : List (List Bool)) (hC : C=codes.length)
    (hw : ∀i,i<codes.length→w i=(codes.reverse[i]?).getD [])
    (cs : List (IntegralMixedFullHistoryScript.Command Q B))
    (hc : (IntegralMixedCausalPlanBits.commands x
      (IntegralMixedStaticRecordContinuation.prefixRecords Q hn hcap N C p hp hd w 0)
      (by rw [IntegralMixedStaticRecordContinuation.prefixRecords_length _ _ _ _ _ _ _ _ _ 0 (Nat.zero_le _)];
          rw [IntegralMixedStaticRecordPrefix.records_length] at room;omega)).length+cs.length≤S+1)
    (HD : IntegralMixedOptionalEndpoints.Decodes
      (IntegralMixedStaticRecordContinuation.prefixStart Q hn hcap N C p hp hd w x room 0 (Nat.zero_le _)) hn hcap cs hc codes) :
    IntegralMixedCausalPlanBits.commands x (IntegralMixedStaticRecordPrefix.records Q hn hcap N C p hp hd w) room=
      cs.map (IntegralMixedFramedFixedContinuation.wrap Q (IntegralMixedStaticRecordPrefix.cap Q hcap))++
      IntegralMixedCausalPlanBits.commands x
        (IntegralMixedStaticRecordContinuation.prefixRecords Q hn hcap N C p hp hd w 0)
        (by rw [IntegralMixedStaticRecordContinuation.prefixRecords_length _ _ _ _ _ _ _ _ _ 0 (Nat.zero_le _)];
            rw [IntegralMixedStaticRecordPrefix.records_length] at room;omega) := by
  have H := IntegralMixedStaticRecordContinuation.prefix_commands Q hn hcap N C p hp hd w x room fallback 0 codes
    (by omega) (by intro i hi; simpa only [Nat.zero_add] using hw i hi) cs hc HD
  have HL : (IntegralMixedCausalPlanBits.commands x
      (IntegralMixedStaticRecordPrefix.records Q hn hcap N C p hp hd w) room).length=N+codes.length := by
    rw [IntegralMixedCausalPlanBits.commands_length,IntegralMixedStaticRecordPrefix.records_length,hC]
    omega
  simpa only [Nat.add_zero,←HL,paddedPast_full] using H

private theorem generic_seed_decodes {n S B m : ℕ} {V : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State V S B m ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) V.degree≤2^B) (t : ℕ)
    (room : m+(IntegralMixedPointCompanion.commands (P:=V) (B:=B)
      (IntegralMixedChronologicalSeedProgram.descriptor n m).frame.frozen (fun _=>false)
      (fun i=>.single ((IntegralMixedChronologicalSeedProgram.descriptor n m).atom i))
      (IntegralMixedChronologicalSeedProgram.zero n m) (IntegralMixedChronologicalSeedProgram.selections n m t)).length≤S+1) :
    IntegralMixedOptionalEndpoints.Decodes x hn hcap
      (IntegralMixedPointCompanion.commands (IntegralMixedChronologicalSeedProgram.descriptor n m).frame.frozen (fun _=>false)
        (fun i=>.single ((IntegralMixedChronologicalSeedProgram.descriptor n m).atom i))
        (IntegralMixedChronologicalSeedProgram.zero n m) (IntegralMixedChronologicalSeedProgram.selections n m t)) room
      (IntegralMixedPointCompanion.codes (IntegralMixedChronologicalSeedProgram.descriptor n m).frame.frozen (fun _=>false)
        (fun i=>.single ((IntegralMixedChronologicalSeedProgram.descriptor n m).atom i))
        (IntegralMixedChronologicalSeedProgram.zero n m) (IntegralMixedChronologicalSeedProgram.selections n m t)) := by
  have HOlder : m≤S+1 := (Nat.le_add_right _ _).trans room
  have H := IntegralMixedPointCompanion.decodes_append x
    (IntegralMixedChronologicalSeedProgram.descriptor n m).frame.frozen (fun _=>false)
    (fun i=>.single ((IntegralMixedChronologicalSeedProgram.descriptor n m).atom i))
    (IntegralMixedChronologicalSeedProgram.zero n m) hn hcap [] HOlder [] rfl (Nat.add_zero _).symm
    (IntegralMixedChronologicalSeedProgram.selections n m t)
    (by simpa only [List.append_nil] using room)
  simpa only [List.append_nil] using H

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.plan
local notation "Q" r => FormulaSignSlotRadialProviderRecordPlan.spatial r

theorem sourceCap (c : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient (root c)+1) (Q (root c)).degree≤2^(P).width (root c) := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
  exact FormulaSignSlotRadialProviderRecordPlan.spatial_cap (root c)
noncomputable def records (c : List Bool) := IntegralMixedSourceIntegerRecordAppend.staticRecords P
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.positive
  FormulaSignSlotRadialProviderRecordPlan.spatial_degree FormulaSignSlotRadialProviderRecordPlan.spatial_cap
  FormulaSignSlotRadialProviderRecordPlan.count FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.source_nonzero FormulaSignSlotRadialProviderRecordPlan.source_degree_cap (root c)

theorem records_length (c : List Bool) : (records c).length=IntegralMixedCausalRecordPlanBits.count (root c)+
    FormulaSignSlotRadialProviderRecordPlan.count (root c) :=
  IntegralMixedSourceIntegerRecordAppend.staticRecords_length _ _ _ _ _ _ _ _ _ _
theorem records_room (c : List Bool) : (records c).length≤(P).cap (root c)+1+1 := by
  rw [records_length]
  have H := FormulaSignSlotRadialProviderRecordPlan.room (root c)
  omega

noncomputable def olderRecords (c : List Bool) := IntegralMixedStaticRecordContinuation.prefixRecords
  (Q (root c)) (FormulaSignSlotRadialProviderRecordPlan.positive (root c)) (sourceCap c)
  (FormulaSignSlotRadialProviderRecordPlan.count (root c)) (IntegralMixedCausalRecordPlanBits.count (root c))
  (fun i=>FormulaSignSlotRadialProviderRecordPlan.source.polynomial (pair (root c) (BinaryNatCode.encode i)))
  (fun _=>FormulaSignSlotRadialProviderRecordPlan.source_nonzero _)
  (fun i=>(FormulaSignSlotRadialProviderRecordPlan.source.degree_bound _).trans
    (FormulaSignSlotRadialProviderRecordPlan.source_degree_cap (root c) i))
  (IntegralMixedCausalRecordPlanBits.code (root c)) 0

theorem olderRecords_length (c : List Bool) : (olderRecords c).length=FormulaSignSlotRadialProviderRecordPlan.count (root c) := by
  exact (IntegralMixedStaticRecordContinuation.prefixRecords_length _ _ _ _ _ _ _ _ _ 0 (Nat.zero_le _)).trans (Nat.add_zero _)
theorem olderRecords_room (c : List Bool) : (olderRecords c).length≤(P).cap (root c)+1+1 := by
  rw [olderRecords_length]
  have H := FormulaSignSlotRadialProviderRecordPlan.room (root c)
  omega
noncomputable def older (c : List Bool) := IntegralMixedCausalPlanBits.commands (initial P D (root c))
  (olderRecords c) (olderRecords_room c)
theorem older_length (c : List Bool) : (older c).length=FormulaSignSlotRadialProviderRecordPlan.count (root c) :=
  (IntegralMixedCausalPlanBits.commands_length _ _ _).trans (olderRecords_length c)
noncomputable def state (c : List Bool) := IntegralMixedCausalUnitContinuation.start (initial P D (root c))
  (Q (root c)) (sourceCap c) (olderRecords c) (olderRecords_room c)
noncomputable def descriptor (c : List Bool) := IntegralMixedChronologicalSeedProgram.descriptor
  ((P).ambient (root c)) (older c).length
noncomputable def objective (c : List Bool) := IntegralMixedChronologicalSeedProgram.zero
  ((P).ambient (root c)) (older c).length
noncomputable def selections (c : List Bool) := IntegralMixedChronologicalSeedProgram.selections
  ((P).ambient (root c)) (older c).length (tail c)
noncomputable def commands (c : List Bool) :
    List (IntegralMixedFullHistoryScript.Command (Q (root c)) ((P).width (root c))) := IntegralMixedPointCompanion.commands
  (descriptor c).frame.frozen (fun _=>false) (fun i=>.single ((descriptor c).atom i)) (objective c) (selections c)
noncomputable def codes (c : List Bool) := IntegralMixedPointCompanion.codes
  (descriptor c).frame.frozen (fun _=>false) (fun i=>.single ((descriptor c).atom i)) (objective c) (selections c)

theorem commands_length (c : List Bool) : (commands c).length=(selections c).length :=
  IntegralMixedPointCompanion.commands_length _ _ _ _ _
theorem codes_length (c : List Bool) : (codes c).length=(selections c).length :=
  IntegralMixedPointCompanion.codes_length _ _ _ _ _
theorem codes_exact (c : List Bool) : (codes c).reverse=
    IntegralMixedRoadmapChain.seedCodes (dim c)++List.replicate (tail c) (IntegralMixedRoadmapChain.seedCode (dim c)) :=
  (IntegralMixedChronologicalSeedProgram.codes_exact ((P).ambient (root c)) (older c).length (tail c)).trans
    (congrArg (fun d=>IntegralMixedRoadmapChain.seedCodes d++List.replicate (tail c) (IntegralMixedRoadmapChain.seedCode d))
      (ambient_root c))
theorem records_codes (c : List Bool) : IntegralMixedCausalRecordPlanBits.records (root c)=WordList.encode (codes c).reverse :=
  (raw_exact c).trans (congrArg WordList.encode (codes_exact c).symm)
theorem codes_count (c : List Bool) : (codes c).length=IntegralMixedCausalRecordPlanBits.count (root c) := by
  rw [IntegralMixedCausalRecordPlanBits.count,records_codes,WordListRecords.count_encode,List.length_reverse]
theorem commands_count (c : List Bool) : (commands c).length=IntegralMixedCausalRecordPlanBits.count (root c) :=
  (commands_length c).trans ((codes_length c).symm.trans (codes_count c))
theorem program_room (c : List Bool) : (older c).length+(commands c).length≤(P).cap (root c)+1+1 := by
  rw [older_length,commands_count]
  have H := FormulaSignSlotRadialProviderRecordPlan.room (root c)
  omega

noncomputable local instance providerFirstSeedOlderFintype (c : List Bool) :
    Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (older c)) :=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) (older c)

theorem decodes (c : List Bool) : @IntegralMixedOptionalEndpoints.Decodes
    ((P).ambient (root c)) ((P).cap (root c)+1) ((P).width (root c)) (older c).length (Q (root c))
    (IntegralMixedFramedHistoryScript.Index (Fin 0) (older c))
    (IntegralMixedFramedHistoryScript.indexFintype (Fin 0) (older c)) (state c)
    (FormulaSignSlotRadialProviderRecordPlan.positive (root c)) (sourceCap c)
    (commands c) (program_room c) (codes c) := by
  exact generic_seed_decodes (state c) (FormulaSignSlotRadialProviderRecordPlan.positive (root c))
    (sourceCap c) (tail c) (program_room c)

theorem full_commands (c : List Bool) : (D).rules (root c)=
    (commands c).map (IntegralMixedFramedFixedContinuation.wrap (Q (root c))
      (IntegralMixedStaticRecordPrefix.cap (Q (root c)) (sourceCap c)))++older c := by
  have HR := IntegralMixedSourceIntegerRecordAppend.rules_static P FormulaSignSlotRadialProviderRecordPlan.spatial
    FormulaSignSlotRadialProviderRecordPlan.positive FormulaSignSlotRadialProviderRecordPlan.spatial_degree
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room (root c)
  have HC := compile_full (initial P D (root c)) (Q (root c))
    (FormulaSignSlotRadialProviderRecordPlan.positive (root c)) (sourceCap c)
    (FormulaSignSlotRadialProviderRecordPlan.count (root c)) (IntegralMixedCausalRecordPlanBits.count (root c))
    (fun i=>FormulaSignSlotRadialProviderRecordPlan.source.polynomial (pair (root c) (BinaryNatCode.encode i)))
    (fun _=>FormulaSignSlotRadialProviderRecordPlan.source_nonzero _)
    (fun i=>(FormulaSignSlotRadialProviderRecordPlan.source.degree_bound _).trans
      (FormulaSignSlotRadialProviderRecordPlan.source_degree_cap (root c) i))
    (IntegralMixedCausalRecordPlanBits.code (root c)) (records_room c) (defaultInstruction P D (root c))
    (codes c) (codes_count c).symm (by
      intro i hi
      simp only [IntegralMixedCausalRecordPlanBits.code,records_codes,WordList.get_encode])
    (commands c) (program_room c) (decodes c)
  exact HR.trans HC

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
