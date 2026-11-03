/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalPrefixes
public import LeanCanny.Geometry.IntegralMixedAtomicFrameRecord
/-! # The appended original critical record is the literal creating command -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalCommand
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def criticalOf {n B : ℕ} (c : Instruction n B) : Option (CriticalRule n) :=
  match c.command with | .critical r=>some r | _=>none
private noncomputable def recordCritical {n B : ℕ} (r : Record n B) : Option (CriticalRule n) :=
  match r.template with | .critical c=>some c | _=>none

private theorem commands_critical {n S B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (IntegralMixedCausalPlanBits.commands x rs h).map criticalOf=rs.map recordCritical :=by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    rw [IntegralMixedCausalPlanBits.commands_cons,List.map_cons,List.map_cons,ih]
    congr 1
    cases r with | mk source hc templ=>cases templ <;> rfl

private theorem critical_of_eq {n B : ℕ} (c : Instruction n B) (r : CriticalRule n)
    (h : criticalOf c=some r) : c.command=.critical r :=by
  cases hc : c.command <;> simp_all [criticalOf]

section Generic
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)

private theorem records_lookup (root : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count root) :
    let base:=IntegralMixedSourceIntegerPrelude.plan P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
      (IntegralMixedSourceIntegerPrelude.prelude_room P N (IntegralMixedSourceIntegerRecordAppend.later P S hn hd hcap N)
        (fun root=>by rw [IntegralMixedSourceIntegerRecordAppend.later_length]; exact hroom root))
    let rs:=IntegralMixedSourceIntegerRecordAppend.later P S hn hd hcap N root++
      IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0)
        (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P base root).critical_cap) T N hz hT root
    rs.reverse[N root+b]?=some (IntegralMixedSourceIntegerRecordAppend.step P S hn hd hcap N root b) :=by
  dsimp only
  rw [List.reverse_append,List.getElem?_append_right (by
    rw [List.length_reverse,IntegralMixedSourceIntegerPrelude.records_length];omega)]
  simp only [List.length_reverse,IntegralMixedSourceIntegerPrelude.records_length,Nat.add_sub_cancel_left,
    IntegralMixedSourceIntegerRecordAppend.later,List.reverse_reverse,List.getElem?_map,
    List.getElem?_range hb,Option.map_some]

theorem instruction_critical (root : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count root)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code root b)=true) :
    (IntegralMixedFramedRootPullback.instructionAt P
      (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom) root (N root+b)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical (P.ambient root) (N root+b)
        (IntegralMixedCausalRecordPlanBits.code root b)) :=by
  let later:=IntegralMixedSourceIntegerRecordAppend.later P S hn hd hcap N
  let room : ∀root,(later root).length+N root+2≤P.cap root+1:=fun root=>by
    rw [IntegralMixedSourceIntegerRecordAppend.later_length]
    exact hroom root
  let base:=IntegralMixedSourceIntegerPrelude.plan P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (IntegralMixedSourceIntegerPrelude.prelude_room P N later room)
  let rs:=later root++IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0)
    (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P base root).critical_cap) T N hz hT root
  have hrs : rs.length≤P.cap root+1+1 :=by
    dsimp only [rs]
    rw [List.length_append,IntegralMixedSourceIntegerPrelude.records_length]
    have HH:=room root
    omega
  have HM:=commands_critical (IntegralMixedFramedHistoryFamilyBits.initial P base root) rs hrs
  have HE:=congrArg (fun l=>l.reverse[N root+b]?) HM
  rw [←List.map_reverse,←List.map_reverse,List.getElem?_map,List.getElem?_map,
    records_lookup P S hn hd hcap N T hz hT hroom root b hb] at HE
  have HS : recordCritical (IntegralMixedSourceIntegerRecordAppend.step P S hn hd hcap N root b)=
      some (IntegralMixedCausalUnitRecordBits.physical (P.ambient root) (N root+b)
        (IntegralMixedCausalRecordPlanBits.code root b)) :=by
    simp only [IntegralMixedSourceIntegerRecordAppend.step,IntegralMixedCausalUnitRecordBits.record,hc,ite_true,recordCritical]
  rw [Option.map_some,HS] at HE
  have HI : ∃c,chronological (IntegralMixedCausalPlanBits.commands
      (IntegralMixedFramedHistoryFamilyBits.initial P base root) rs hrs) (N root+b)=some c ∧
      criticalOf c=some (IntegralMixedCausalUnitRecordBits.physical (P.ambient root) (N root+b)
        (IntegralMixedCausalRecordPlanBits.code root b)) :=by
    unfold chronological
    cases he : (IntegralMixedCausalPlanBits.commands (IntegralMixedFramedHistoryFamilyBits.initial P base root) rs hrs).reverse[N root+b]? with
    | none=>simp only [he,Option.map_none] at HE
            cases HE
    | some c=>exact ⟨c,rfl,by simpa only [he,Option.map_some,Option.some.injEq] using HE⟩
  obtain ⟨c,Hc,Hcrit⟩:=HI
  apply critical_of_eq
  change criticalOf ((chronological (IntegralMixedCausalPlanBits.commands
    (IntegralMixedFramedHistoryFamilyBits.initial P base root) rs hrs) (N root+b)).getD _)=_
  rw [Hc,Option.getD_some]
  exact Hcrit
end Generic
section Concrete
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCriticalQuery (root lastCode)
open IntegralMixedPhysicalCriticalPrefixes (birth)

private theorem marked_critical (root : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count root)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code root b)=true) :
    (IntegralMixedFramedRootPullback.instructionAt (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) root
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8+b)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical
        ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).ambient root)
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8+b)
        (IntegralMixedCausalRecordPlanBits.code root b)) :=
  instruction_critical (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (fun c=>IntegralMixedAuxiliaryMarkedIntegerSource.number n c+8) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha)
    root b hb hc

private theorem outer_critical (root : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count root)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code root b)=true) :
    (IntegralMixedFramedRootPullback.instructionAt (IntegralMixedAuxiliaryOuterRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.plan hn ht ha R) root
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n root+10+b)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical
        ((IntegralMixedAuxiliaryOuterRecordPlan.parameters hn ht ha).ambient root)
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n root+10+b)
        (IntegralMixedCausalRecordPlanBits.code root b)) :=
  instruction_critical (IntegralMixedAuxiliaryOuterRecordPlan.parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (IntegralMixedAuxiliaryOuterRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (IntegralMixedAuxiliaryOuterRecordPlan.spatial_cap hn ht ha)
    (fun c=>IntegralMixedAuxiliaryMarkedIntegerSource.number n c+10) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryOuterRecordPlan.source_degree_cap hn ht ha R) (IntegralMixedAuxiliaryOuterRecordPlan.room hn ht ha)
    root b hb hc

private theorem planned_instructionAt (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (root : List Bool) (b : ℕ) :
    IntegralMixedFramedRootPullback.instructionAt (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) root b=
      IntegralMixedFramedRootPullback.instructionAt P D root b :=rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  IntegralMixedAuxiliaryOuterRecordPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedAuxiliaryOuterRecordPlan.parameters IntegralMixedAuxiliaryOuterRecordPlan.plan

theorem command (outer : Bool) (q : List Bool)
    (hp : 0<IntegralMixedCausalRecordPlanBits.count (root q))
    (hc : IntegralMixedUnitRecordCode.critical (lastCode q)=true) :
    (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (root q) (birth n outer false q)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical
        ((bank hn ht ha hR outer).parameters.ambient (root q)) (birth n outer false q) (lastCode q)) :=by
  have hb : IntegralMixedCausalRecordPlanBits.count (root q)-1<IntegralMixedCausalRecordPlanBits.count (root q) :=by omega
  cases outer
  · have HE:=marked_critical hn ht ha (R:=R) (root q) _ hb hc
    have HB : IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8+
        (IntegralMixedCausalRecordPlanBits.count (root q)-1)=birth n false false q :=by
      simp only [IntegralMixedPhysicalCriticalPrefixes.birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,Bool.false_eq_true,ite_false]
      omega
    rw [HB] at HE
    have HM : bank hn ht ha hR false=IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR :=by
      unfold IntegralMixedPhysicalMarkedPlan.bank
      exact ite_eq_right Bool.false_ne_true
    rw [HM]
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.bank
    change (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR) (root q) (birth n false false q)).command=_
    rw [planned_instructionAt]
    exact HE
  · have HE:=outer_critical hn ht ha (R:=R) (root q) _ hb hc
    have HB : IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+10+
        (IntegralMixedCausalRecordPlanBits.count (root q)-1)=birth n true false q :=by
      simp only [IntegralMixedPhysicalCriticalPrefixes.birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,Bool.false_eq_true,ite_false,ite_true]
      omega
    rw [HB] at HE
    have HM : bank hn ht ha hR true=IntegralMixedAuxiliaryOuterRecordPlan.bank hn ht ha hR :=by
      unfold IntegralMixedPhysicalMarkedPlan.bank
      exact ite_eq_left rfl
    rw [HM]
    unfold IntegralMixedAuxiliaryOuterRecordPlan.bank
    change (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedPlan hn ht ha hR) (root q) (birth n true false q)).command=_
    rw [planned_instructionAt]
    exact HE
theorem command_data (outer : Bool) (q : List Bool)
    (hp : 0<IntegralMixedCausalRecordPlanBits.count (root q))
    (d : IntegralMixedCriticalRecordConstructor.Data
      ((bank hn ht ha hR outer).parameters.ambient (root q)) (birth n outer false q))
    (hd : lastCode q=d.code) :
    (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (root q) (birth n outer false q)).command=.critical d.rule :=by
  have hc : IntegralMixedUnitRecordCode.critical (lastCode q)=true :=by
    simp only [hd,IntegralMixedUnitRecordCode.critical,IntegralMixedCriticalRecordConstructor.field_0,
      List.getElem?_cons_zero,Option.getD_some]
  have HE:=command hn ht ha hR outer q hp hc
  simpa only [hd,IntegralMixedCriticalRecordConstructor.rule_decode] using HE

theorem packet_command (outer : Bool) (q : List Bool)
    (d : IntegralMixedCriticalRecordConstructor.Data
      ((bank hn ht ha hR outer).parameters.ambient (root q)) (birth n outer false q))
    (ctx w : List Bool) (a b : ℕ) (he : d.coordinate.val=d.objective.val)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx d.code w a b) :
    (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (root q) (birth n outer false q)).command=.critical d.rule :=by
  have HD : lastCode q=d.code :=(congrArg lastCode hq).trans
    ((IntegralMixedPhysicalCriticalQuery.lastCode_packet ctx d.code w a b).trans
      (IntegralMixedPhysicalCriticalQuery.normalize_data d he))
  have HP:= (IntegralMixedPhysicalCriticalQuery.critical_packet ctx d.code w a b).1
  have HC:=congrArg (fun z=>0<IntegralMixedCausalRecordPlanBits.count (root z)) hq
  exact command_data hn ht ha hR outer q (HC.mpr HP) d HD

theorem point_command (outer : Bool) (q : List Bool)
    {F : IntegralMixedFrozenFrame.Frame ((bank hn ht ha hR outer).parameters.ambient (root q))}
    (HA : IntegralMixedFrozenFrame.AtomicRows F (birth n outer false q))
    (h : Fin ((bank hn ht ha hR outer).parameters.ambient (root q)+1)) (hh : h∉F.frozen)
    (ctx w : List Bool) (a b : ℕ)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx (HA.pointData h h hh hh).code w a b) :
    (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (root q) (birth n outer false q)).command=
      .critical (HA.pointData h h hh hh).rule :=
  packet_command hn ht ha hR outer q (HA.pointData h h hh hh) ctx w a b rfl hq

end Concrete
end LeanCanny.Encoding.IntegralMixedPhysicalCriticalCommand
