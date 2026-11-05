/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordSerializer
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordControls
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
/-! # Canonical original raw prefixes in the actual marked record plan -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordActual
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

def codes (ctx:List Bool) (k:ℕ):List (List Bool):=
  ((List.range k).map (IntegralMixedCausalRecordPlanBits.code ctx)).reverse

theorem codes_length (ctx:List Bool) (k:ℕ):(codes ctx k).length=k:=by
  simp only [codes,List.length_reverse,List.length_map,List.length_range]

theorem codes_succ (ctx:List Bool) (k:ℕ):
    codes ctx (k+1)=IntegralMixedCausalRecordPlanBits.code ctx k::codes ctx k:=by
  simp only [codes,List.range_succ,List.map_append,List.map_singleton,List.reverse_append,
    List.reverse_singleton,List.singleton_append]

noncomputable def rawRecord (ctx:List Bool) (radius:List Bool→ℕ) (b:ℕ):
    Record (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx):=
  IntegralMixedSourceIntegerRecordAppend.step (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t radius root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8) ctx b

theorem rawRecord_eq (ctx:List Bool) (radius:List Bool→ℕ) (b:ℕ):
    rawRecord hn ht ha ctx radius b=
      CoefficientMarkedRecordSerializer.record hn ht ha ctx radius
        ((CoefficientMarkedPreludeActual.indices n ctx).length+b) (IntegralMixedCausalRecordPlanBits.code ctx b):=by
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

noncomputable def integerRecords (ctx:List Bool) (radius:List Bool→ℕ):
    List (Record (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx)):=
  CoefficientMarkedRecordSerializer.prelude hn ht ha ctx radius

noncomputable def prefixRecords (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ):
    List (Record (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx)):=
  ((List.range k).map (rawRecord hn ht ha ctx radius)).reverse ++
    integerRecords hn ht ha ctx radius

theorem records_eq (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ):
    CoefficientMarkedRecordSerializer.records hn ht ha ctx radius (codes ctx k)=prefixRecords hn ht ha ctx radius k:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [codes_succ,CoefficientMarkedRecordSerializer.records,ih]
    simp only [prefixRecords,List.range_succ,List.map_append,List.map_singleton,List.reverse_append,
      List.reverse_singleton,List.cons_append,List.nil_append]
    rw [rawRecord_eq,codes_length]

noncomputable def full (ctx:List Bool) (radius:List Bool→ℕ):=
  prefixRecords hn ht ha ctx radius (IntegralMixedCausalRecordPlanBits.count ctx)

theorem records_prefix (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    (full hn ht ha ctx radius).drop (IntegralMixedCausalRecordPlanBits.count ctx-k)=
      CoefficientMarkedRecordSerializer.records hn ht ha ctx radius (codes ctx k):=by
  rw [records_eq]
  unfold full prefixRecords
  rw [List.drop_append,List.length_reverse,List.length_map,List.length_range,
    Nat.sub_eq_zero_of_le (Nat.sub_le _ _),List.drop_zero,List.drop_reverse]
  simp only [List.length_map,List.length_range]
  rw [Nat.sub_sub_self hk,←List.map_take,List.take_range,min_eq_left hk]


theorem full_length (ctx:List Bool) (radius:List Bool→ℕ):
    (full hn ht ha ctx radius).length=(CoefficientMarkedPreludeActual.indices n ctx).length+
      IntegralMixedCausalRecordPlanBits.count ctx:=by
  change (prefixRecords hn ht ha ctx radius _).length=_
  rw [←records_eq, CoefficientMarkedRecordSerializer.records_length,codes_length]

noncomputable def horizon (ctx:List Bool):ℕ:=
  (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1

theorem prefix_room (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    (CoefficientMarkedPreludeActual.indices n ctx).length+(codes ctx k).length≤horizon hn ht ha ctx+1:=by
  rw [CoefficientMarkedPreludeActual.indices_length,codes_length]
  have H:=IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  unfold horizon
  omega

private theorem commands_congr {a S B:ℕ} {Q:SpatialSource a}
    (x:State Q S B 0 (Fin 0)) (cs ds:List (Record a B)) (he:cs=ds)
    (hc:cs.length≤S+1) (hd:ds.length≤S+1):
    IntegralMixedCausalPlanBits.commands x cs hc=IntegralMixedCausalPlanBits.commands x ds hd:=by
  cases he
  rfl

theorem plan_rules (ctx:List Bool) (radius:List Bool→ℕ):
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx=
      CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius (horizon hn ht ha ctx)
        (codes ctx (IntegralMixedCausalRecordPlanBits.count ctx)) (prefix_room hn ht ha ctx _ le_rfl):=by
  change IntegralMixedCausalPlanBits.commands
    (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius (horizon hn ht ha ctx))
    (full hn ht ha ctx radius) _ = _
  exact commands_congr _ _ _ (records_eq hn ht ha ctx radius _).symm _ _

theorem commands_prefix (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx).drop
      (IntegralMixedCausalRecordPlanBits.count ctx-k)=
      CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius (horizon hn ht ha ctx)
        (codes ctx k) (prefix_room hn ht ha ctx k hk):=by
  rw [plan_rules]
  unfold CoefficientMarkedRecordSerializer.commands
  rw [IntegralMixedSourceIntegerPrelude.causal_commands_drop]
  apply commands_congr
  exact (congrArg (List.drop (IntegralMixedCausalRecordPlanBits.count ctx-k))
    (records_eq hn ht ha ctx radius _)).trans (records_prefix hn ht ha ctx radius k hk)


theorem plan_length (ctx:List Bool) (radius:List Bool→ℕ):
    ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx).length=
      (CoefficientMarkedPreludeActual.indices n ctx).length+IntegralMixedCausalRecordPlanBits.count ctx:=by
  rw [plan_rules,CoefficientMarkedRecordSerializer.commands_length,codes_length]

private theorem past_eq_drop {α B:ℕ} (cs:List (Instruction α B)) (birth:ℕ):
    IntegralMixedFramedHistoryScript.past cs birth=cs.drop (cs.length-birth):=by
  rw [IntegralMixedFramedHistoryScript.past,List.take_reverse,List.reverse_reverse]

theorem padded_prefix (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction
        (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx)
      ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx)
      ((CoefficientMarkedPreludeActual.indices n ctx).length+k)=
      CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius (horizon hn ht ha ctx)
        (codes ctx k) (prefix_room hn ht ha ctx k hk):=by
  have HL:=plan_length hn ht ha ctx radius
  have HB:(CoefficientMarkedPreludeActual.indices n ctx).length+k≤
      ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx).length:=by omega
  rw [IntegralMixedFramedHistoryScript.paddedPast_valid _ _ _ HB,past_eq_drop,HL]
  have HE:(CoefficientMarkedPreludeActual.indices n ctx).length+
      IntegralMixedCausalRecordPlanBits.count ctx-((CoefficientMarkedPreludeActual.indices n ctx).length+k)=
      IntegralMixedCausalRecordPlanBits.count ctx-k:=by omega
  rw [HE]
  exact commands_prefix hn ht ha ctx radius k hk

theorem birth_room (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    (CoefficientMarkedPreludeActual.indices n ctx).length+k≤
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1:=by
  rw [CoefficientMarkedPreludeActual.indices_length]
  have H:=IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  omega

private theorem commands_at_congr (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (root root':List Bool) (birth birth':ℕ)
    (hr:root'=root) (hb:birth'=birth):
    HEq (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root') (D.rules root') birth')
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth):=by
  cases hr
  cases hb
  rfl

theorem family_commands (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    HEq (IntegralMixedFramedHistoryFamilyBits.commands
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius)
      (IntegralMixedFramedHistoryFamilyBits.keyAt ctx ((CoefficientMarkedPreludeActual.indices n ctx).length+k) aux))
      (CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius (horizon hn ht ha ctx)
        (codes ctx k) (prefix_room hn ht ha ctx k hk)):=by
  exact (commands_at_congr (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx _ _ _
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ (birth_room hn ht ha ctx k hk))).trans
      (heq_of_eq (padded_prefix hn ht ha ctx radius k hk))


private theorem run_reframe_congr {a S B p:ℕ} {Q:SpatialSource a}
    (x:State Q S B 0 (Fin 0)) (cs ds:List (Instruction a B)) (he:cs=ds)
    (hc:cs.length≤S+1) (hd:ds.length≤S+1) (P:SpatialSource p)
    (hP:PurePowerReductionBounds.dimension (p+1) P.degree≤2^B):
    HEq (reframe (run x cs hc) P hP) (reframe (run x ds hd) P hP):=by
  cases he
  rfl

theorem native_runAt (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    HEq (CoefficientMarkedRecordNative.run hn ht ha ctx radius (horizon hn ht ha ctx)
      (codes ctx k) (prefix_room hn ht ha ctx k hk))
      (reframe (IntegralMixedFramedFamilyRunView.runAt
        (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx
        ((CoefficientMarkedPreludeActual.indices n ctx).length+k) (birth_room hn ht ha ctx k hk))
        (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius)
        (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius (horizon hn ht ha ctx)).critical_cap):=by
  refine (CoefficientMarkedRecordSerializer.run_framed hn ht ha ctx radius (horizon hn ht ha ctx)
    (codes ctx k) (prefix_room hn ht ha ctx k hk)).trans ?_
  exact run_reframe_congr
    (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius (horizon hn ht ha ctx)) _ _
    (padded_prefix hn ht ha ctx radius k hk).symm _ _ _ _

private theorem reframe_source_heq {a S B m:ℕ} {P Q:SpatialSource a} {I:Type}
    (x:State P S B m I) (he:P=Q)
    (hq:PurePowerReductionBounds.dimension (a+1) Q.degree≤2^B):
    HEq x (reframe x Q hq):=by
  cases he
  exact (heq_of_eq (reframe_same x)).symm

private theorem static_runAt_congr (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (root root':List Bool) (birth birth':ℕ)
    (hr:root'=root) (hb:birth'=birth) (hc:birth≤P.cap root+1) (hc':birth'≤P.cap root'+1):
    HEq (reframe (IntegralMixedFramedFamilyRunView.runAt P D root' birth' hc')
      (D.initialSource root') (IntegralMixedFramedHistoryFamilyBits.initial P D root').critical_cap)
      (reframe (IntegralMixedFramedFamilyRunView.runAt P D root birth hc)
        (D.initialSource root) (IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap):=by
  cases hr
  cases hb
  rfl

private theorem static_state_at (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (hs:∀key,(IntegralMixedFramedHistoryFamilyBits.instruction P D key).source=D.initialSource (pairFst key))
    (root:List Bool) (birth:ℕ) (aux:List Bool) (hb:birth≤P.cap root+1):
    HEq ((IntegralMixedFramedHistoryFamilyBits.family P D H).state
      (IntegralMixedFramedHistoryFamilyBits.keyAt root birth aux))
      (reframe (IntegralMixedFramedFamilyRunView.runAt P D root birth hb)
        (D.initialSource root) (IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap):=by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root birth aux
  have H1:=reframe_source_heq ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
    (hs key) (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key)).critical_cap
  have H2:=IntegralMixedFramedFamilyRunView.family_reframe P D H key
    (D.initialSource (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key)).critical_cap
  have HR:pairFst key=root:=IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _
  have HB:IntegralMixedFramedHistoryFamilyBits.prefixLength P key=birth:=
    IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root birth aux hb
  have HC:IntegralMixedFramedHistoryFamilyBits.prefixLength P key≤P.cap (pairFst key)+1:=min_le_right _ _
  have H3:HEq (reframe (IntegralMixedFramedFamilyRunView.familyRun P D key)
      (D.initialSource (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key)).critical_cap)
      (reframe (IntegralMixedFramedFamilyRunView.runAt P D root birth hb)
        (D.initialSource root) (IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap):=by
    change HEq (reframe (IntegralMixedFramedFamilyRunView.runAt P D (pairFst key)
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) HC) _ _) _
    exact static_runAt_congr P D root _ birth _ HR HB hb HC

  exact H1.trans ((heq_of_eq H2).trans H3)

theorem native_family (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    HEq (CoefficientMarkedRecordNative.run hn ht ha ctx radius (horizon hn ht ha ctx)
      (codes ctx k) (prefix_room hn ht ha ctx k hk))
      ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius)
        (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha radius)).state
        (IntegralMixedFramedHistoryFamilyBits.keyAt ctx ((CoefficientMarkedPreludeActual.indices n ctx).length+k) aux)):=by
  exact (native_runAt hn ht ha ctx radius k hk).trans
    (static_state_at (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha radius)
      (IntegralMixedAuxiliaryMarkedRecordPlan.instruction_source hn ht ha radius)
      ctx _ aux (birth_room hn ht ha ctx k hk)).symm

end LeanCanny.Encoding.CoefficientMarkedRecordActual
