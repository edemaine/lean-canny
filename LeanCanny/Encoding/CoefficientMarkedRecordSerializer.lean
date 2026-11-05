/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordNative
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalPrelude
/-! # Literal causal serialization of the constructed native marked run -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordSerializer
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def prelude (ctx:List Bool) (radius:List Bool→ℕ):=
  IntegralMixedSourceIntegerPrelude.records (IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius)
    (fun root=>(CoefficientMarkedPreludePrefix.initial hn ht ha root radius 0).critical_cap)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha radius) ctx

theorem prelude_length (ctx:List Bool) (radius:List Bool→ℕ):
    (prelude hn ht ha ctx radius).length=(CoefficientMarkedPreludeActual.indices n ctx).length:=by
  rw [prelude,IntegralMixedSourceIntegerPrelude.records_length]
  exact (CoefficientMarkedPreludeActual.indices_length (n:=n) ctx).symm

noncomputable def record (ctx:List Bool) (radius:List Bool→ℕ) (birth:ℕ) (code:List Bool):=
  IntegralMixedCausalUnitRecordBits.record (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius)
    (by change 0<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3;omega)
    birth code (CoefficientMarkedRecordNative.source_cap hn ht ha ctx radius)

noncomputable def records (ctx:List Bool) (radius:List Bool→ℕ):List (List Bool)→
    List (Record (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx))
  | []=>prelude hn ht ha ctx radius
  | code::cs=>record hn ht ha ctx radius ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length) code::
      records ctx radius cs

theorem records_length (ctx:List Bool) (radius:List Bool→ℕ) (cs:List (List Bool)):
    (records hn ht ha ctx radius cs).length=(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length:=by
  induction cs with
  | nil=>exact prelude_length hn ht ha ctx radius
  | cons code cs ih=>simp only [records,List.length_cons,ih];omega

noncomputable def commands (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ) (cs:List (List Bool))
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1):=
  IntegralMixedCausalPlanBits.commands (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
    (records hn ht ha ctx radius cs) (by rw [records_length];exact h)

theorem commands_length (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ) (cs:List (List Bool))
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1):
    (commands hn ht ha ctx radius S cs h).length=(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length:=
  (IntegralMixedCausalPlanBits.commands_length _ _ _).trans (records_length hn ht ha ctx radius cs)

theorem commands_nil (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ)
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+([]:List (List Bool)).length≤S+1):
    commands hn ht ha ctx radius S [] h=
      CoefficientMarkedPreludePrefix.commands hn ht ha ctx radius (CoefficientMarkedPreludeActual.indices n ctx):=by
  have H:=IntegralMixedSourceIntegerPrelude.records_commands
    (IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius)
    (fun root=>(CoefficientMarkedPreludePrefix.initial hn ht ha root radius 0).critical_cap)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha radius) ctx
    (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
    (by rw [IntegralMixedSourceIntegerPrelude.records_length,←CoefficientMarkedPreludeActual.indices_length];exact h)
  exact H.trans (CoefficientMarkedPreludeActual.commands_eq hn ht ha ctx radius).symm

private theorem index_step {S m:ℕ} {ι:Type} (ctx:List Bool) (radius:List Bool→ℕ)
    {P:SpatialSource (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)}
    (x:State P S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (birth:ℕ) (code:List Bool):
    (if IntegralMixedUnitRecordCode.critical code then
      (ι⊕FlatAffineCriticalStage.Variables (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1))⊕Unit else ι⊕Unit)=
      IntegralMixedFullHistoryScript.NextIndex ι
        (instantiate x (record hn ht ha ctx radius birth code)).command:=by
  by_cases hc:IntegralMixedUnitRecordCode.critical code=true
  · simp only [record,instantiate,IntegralMixedCausalUnitRecordBits.record,hc,ite_true,Template.command,
      IntegralMixedFullHistoryScript.NextIndex]
  · simp only [record,instantiate,IntegralMixedCausalUnitRecordBits.record,hc,Bool.false_eq_true,ite_false,Template.command,
      IntegralMixedFullHistoryScript.NextIndex]

theorem commands_cons (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ) (code:List Bool) (cs:List (List Bool))
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+(code::cs).length≤S+1):
    commands hn ht ha ctx radius S (code::cs) h=
      instantiate (IntegralMixedFramedHistoryScript.run (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
        (commands hn ht ha ctx radius S cs (by simp only [List.length_cons] at h;omega))
        (by rw [commands_length];simp only [List.length_cons] at h;omega))
        (record hn ht ha ctx radius ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length) code)::
      commands hn ht ha ctx radius S cs (by simp only [List.length_cons] at h;omega):=by
  exact IntegralMixedCausalPlanBits.commands_cons _ _ _ _

theorem index_eq (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ) (cs:List (List Bool))
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1):
    CoefficientMarkedRecordPrefix.Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx)) cs=
    IntegralMixedFramedHistoryScript.Index (Fin 0) (commands hn ht ha ctx radius S cs h):=by
  induction cs with
  | nil=>
    rw [commands_nil]
    exact CoefficientMarkedPreludePrefix.index_eq hn ht ha ctx radius _
  | cons code cs ih=>
    have ht0:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1:=by
      simp only [List.length_cons] at h;omega
    let tail:=commands hn ht ha ctx radius S cs ht0
    let x:=IntegralMixedFramedHistoryScript.run (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
      tail (by rw [commands_length];exact ht0)
    have HT:=congrArg (fun I:Type=>if IntegralMixedUnitRecordCode.critical code then
      (I⊕FlatAffineCriticalStage.Variables (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1))⊕Unit
      else I⊕Unit) (ih ht0)
    have HS:=index_step hn ht ha ctx radius x ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length) code
    rw [commands_cons hn ht ha ctx radius S code cs h]
    change (if IntegralMixedUnitRecordCode.critical code then
      (CoefficientMarkedRecordPrefix.Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
        (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx)) cs⊕
          FlatAffineCriticalStage.Variables (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1))⊕Unit
      else CoefficientMarkedRecordPrefix.Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
        (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx)) cs⊕Unit)=
      IntegralMixedFullHistoryScript.NextIndex (IntegralMixedFramedHistoryScript.Index (Fin 0) tail)
        (instantiate x (record hn ht ha ctx radius
          ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length) code)).command
    exact HT.trans HS

private theorem common_eq {a S B m k:ℕ} {P:SpatialSource a} {ι κ:Type}
    (x:State P S B m ι) (y:State P S B k κ) (hm:m=k) (hi:ι=κ) (hxy:HEq x y):
    commonDenominator x=commonDenominator y:=by
  cases hm
  cases hi
  exact congrArg (fun z=>commonDenominator z) (eq_of_heq hxy)

private theorem command_congr {a S T B m k:ℕ} {P Q:SpatialSource a} {ι κ:Type}
    (x:State P S B m ι) (y:State Q T B k κ) (r:Record a B)
    (h:commonDenominator x=commonDenominator y):
    (instantiate x r).command=(instantiate y r).command:=by
  have H (p q:ℤ) (hp:p≠0) (hq:q≠0) (he:p=q):r.template.command p hp=r.template.command q hq:=by
    cases he
    rfl
  exact H _ _ _ _ h

private theorem run_list_congr {a S B:ℕ} {P Q:SpatialSource a}
    (x:State P S B 0 (Fin 0)) (cs ds:List (IntegralMixedFramedHistoryScript.Instruction a B))
    (he:cs=ds) (hc:cs.length≤S+1) (hd:ds.length≤S+1)
    (cap:PurePowerReductionBounds.dimension (a+1) Q.degree≤2^B):
    HEq (reframe (IntegralMixedFramedHistoryScript.run x cs hc) Q cap)
      (reframe (IntegralMixedFramedHistoryScript.run x ds hd) Q cap):=by
  cases he
  rfl

private theorem run_cons_step {a S B:ℕ} {P:SpatialSource a}
    (x:State P S B 0 (Fin 0)) (c:IntegralMixedFramedHistoryScript.Instruction a B)
    (cs:List (IntegralMixedFramedHistoryScript.Instruction a B)) (h:(c::cs).length≤S+1):
    HEq (reframe (IntegralMixedFramedHistoryScript.run x (c::cs) h) c.source c.source_cap)
      (IntegralMixedFullHistoryScript.step
        (reframe (IntegralMixedFramedHistoryScript.run x cs (by simp only [List.length_cons] at h;omega))
          c.source c.source_cap) (by simp only [List.length_cons] at h;omega) c.command):=
  heq_of_eq (reframe_same _)

private theorem serializer_step_heq {a S B m:ℕ} {P:SpatialSource a} {ι:Type} [Fintype ι]
    (x:State P S B m ι) (hm:m≤S) {c d:IntegralMixedFullHistoryScript.Command P B} (h:c=d):
    HEq (IntegralMixedFullHistoryScript.step x hm c) (IntegralMixedFullHistoryScript.step x hm d):=by
  cases h
  rfl

/-- Exact execution of the original causal records, including their current-Q insertion. -/
theorem run_framed (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ) (cs:List (List Bool))
    (h:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1):
    HEq (CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs h)
      (reframe (IntegralMixedFramedHistoryScript.run (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
        (commands hn ht ha ctx radius S cs h) (by rw [commands_length];exact h))
        (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius)
        (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S).critical_cap):=by
  induction cs with
  | nil=>
    have HA:=CoefficientMarkedPreludePrefix.nativeRun_framed hn ht ha ctx radius S
      (CoefficientMarkedPreludeActual.indices n ctx) (by simpa only [List.length_nil,Nat.add_zero] using h)
    have HB:=run_list_congr (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S)
      (CoefficientMarkedPreludePrefix.commands hn ht ha ctx radius (CoefficientMarkedPreludeActual.indices n ctx))
      (commands hn ht ha ctx radius S [] h) (commands_nil hn ht ha ctx radius S h).symm
      (by rw [CoefficientMarkedPreludePrefix.commands_length];exact h)
      (by rw [commands_length];exact h) (CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S).critical_cap
    exact HA.trans HB
  | cons code cs ih=>
    have ht0:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1:=by
      simp only [List.length_cons] at h;omega
    have hm:(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S:=by
      simp only [List.length_cons] at h;omega
    let tail:=commands hn ht ha ctx radius S cs ht0
    let initial:=CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius S
    let old:=IntegralMixedFramedHistoryScript.run initial tail (by rw [commands_length];exact ht0)
    let x:=CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs ht0
    let y:=reframe old (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius) initial.critical_cap
    let r:=record hn ht ha ctx radius ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length) code
    have HM:=common_eq x y (commands_length hn ht ha ctx radius S cs ht0).symm
      (index_eq hn ht ha ctx radius S cs ht0) (ih ht0)
    change commonDenominator x=commonDenominator (reframe old _ _) at HM
    rw [reframe_denominator] at HM
    have HC:=command_congr x old r HM
    have HC0:(CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x code).command=(instantiate old r).command:=HC
    have HX:=IntegralMixedFramedStateTransport.step_reframe_heq x y
      (commands_length hn ht ha ctx radius S cs ht0).symm (index_eq hn ht ha ctx radius S cs ht0) (ih ht0)
      hm (by rw [commands_length];exact hm)
      (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x code).command
      (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius) initial.critical_cap
    have HN:=CoefficientMarkedRecordNative.next_command hn ht ha ctx radius x hm code
    have HY:=serializer_step_heq y (by rw [commands_length];exact hm) HC0
    have Hcons:(instantiate old r::tail).length≤S+1:=by
      rw [List.length_cons,commands_length]
      omega
    have HC1:=run_cons_step initial (instantiate old r) tail Hcons
    have HL:=run_list_congr initial (commands hn ht ha ctx radius S (code::cs) h)
      (instantiate old r::tail) (commands_cons hn ht ha ctx radius S code cs h)
      (by rw [commands_length];exact h) Hcons initial.critical_cap
    change HEq (CoefficientMarkedRecordNative.next hn ht ha ctx radius x hm code) _
    exact HN.trans ((heq_of_eq (reframe_same _)).symm.trans (HX.trans
      ((heq_of_eq (reframe_same _)).trans (HY.trans (HC1.symm.trans HL.symm)))))

end LeanCanny.Encoding.CoefficientMarkedRecordSerializer
