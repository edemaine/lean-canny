/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedProgram
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrelude
/-! # The seed starts at the actual full-record integer realization -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem source_suffix (P : Parameters) (Q : (r : List Bool)→SpatialSource (P.ambient r))
    (hn : ∀r,0<P.ambient r) (hd : ∀r,(Q r).degree=P.degree r)
    (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
    (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
    (hT : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
    (hroom : ∀r,IntegralMixedCausalRecordPlanBits.count r+N r+2≤P.cap r+1) (r : List Bool) :
    ((IntegralMixedSourceIntegerRecordAppend.plan P (fun r _=>Q r) hn (fun r _=>hd r) hcap N T hz hT hroom).rules r).drop
      (IntegralMixedCausalRecordPlanBits.count r)=
      (IntegralMixedSourceIntegerRecordAppend.preludePlan P (fun r _=>Q r) (fun r _=>hd r) hcap N T hz hT hroom).rules r := by
  have H := IntegralMixedSourceIntegerPrelude.extended_suffix P Q hd hcap T N hz hT
    (IntegralMixedSourceIntegerRecordAppend.later P (fun r _=>Q r) hn (fun r _=>hd r) hcap N)
    (fun r=>by rw [IntegralMixedSourceIntegerRecordAppend.later_length]; exact hroom r) r
  rw [IntegralMixedSourceIntegerRecordAppend.later_length] at H
  exact H

private theorem realizes_congr {n S B : ℕ} {V : SpatialSource n}
    (x y : State V S B 0 (Fin 0)) (hxy : x=y) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds)
    (v : ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes (run x cs hc) v→
      IntegralMixedIntegerRealization.Realizes (run y ds hd) v := by
  cases hxy
  cases he
  exact id

private theorem realizes_start {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (Q : SpatialSource n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (rs : List (IntegralMixedCausalRecordBits.Record n B)) (hr : rs.length≤S+1) (v : ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes
      (run x (IntegralMixedCausalPlanBits.commands x rs hr) (by rw [IntegralMixedCausalPlanBits.commands_length];exact hr)) v→
    IntegralMixedIntegerRealization.Realizes (IntegralMixedCausalUnitContinuation.start x Q hcap rs hr) v := id

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.plan
local notation "I" => FormulaSignSlotRadialProviderRecordPlan.recordPrelude
local notation "Q" r => FormulaSignSlotRadialProviderRecordPlan.spatial r

theorem older_eq_prelude (c : List Bool) : older c=(I).rules (root c) := by
  have HS := source_suffix P FormulaSignSlotRadialProviderRecordPlan.spatial
    FormulaSignSlotRadialProviderRecordPlan.positive FormulaSignSlotRadialProviderRecordPlan.spatial_degree
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room (root c)
  have HH : ((D).rules (root c)).drop (IntegralMixedCausalRecordPlanBits.count (root c))=older c := by
    rw [full_commands]
    simpa only [List.length_map,commands_count] using
      (@List.drop_left (Instruction ((P).ambient (root c)) ((P).width (root c)))
        ((commands c).map (IntegralMixedFramedFixedContinuation.wrap (Q (root c))
          (IntegralMixedStaticRecordPrefix.cap (Q (root c)) (sourceCap c)))) (older c))
  exact HH.symm.trans HS

theorem state_realizes (c : List Bool) (v : ℕ→ℝ)
    (hv : ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
        (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes (state c)
      (fun j=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j)) := by
  have H := FormulaSignSlotRadialProviderRecordPlan.prelude_realizes (root c) v (by
    intro i hi
    rw [root_provider]
    exact hv i hi)
  have HC : ((I).rules (root c)).length≤(P).cap (root c)+1+1 := by
    rw [FormulaSignSlotRadialProviderRecordPlan.recordPrelude_length]
    have HH := FormulaSignSlotRadialProviderRecordPlan.room (root c)
    omega
  have HD : (older c).length≤(P).cap (root c)+1+1 := by
    rw [older_length]
    have HH := FormulaSignSlotRadialProviderRecordPlan.room (root c)
    omega
  have HH := realizes_congr (initial P I (root c)) (initial P D (root c))
    (FormulaSignSlotRadialProviderRecordPlan.record_prelude_initial (root c)).symm
    ((I).rules (root c)) (older c) HC HD (older_eq_prelude c).symm
    (fun j=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j)) H
  exact realizes_start (initial P D (root c)) (Q (root c)) (sourceCap c) (olderRecords c)
    (olderRecords_room c) _ HH

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
