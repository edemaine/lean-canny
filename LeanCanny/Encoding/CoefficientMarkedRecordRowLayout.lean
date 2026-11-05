/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLayoutCongruence
public import LeanCanny.Encoding.IntegralFramedPhysicalSquare
/-! # Radius-independent literal physical layout of the actual marked prefixes -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRowLayout
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

attribute [local irreducible] CoefficientMarkedRecordSerializer.prelude
  CoefficientMarkedRecordSerializer.records CoefficientMarkedRecordSerializer.record
  CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

private theorem integer_records_tags (P:IntegralCriticalHistoryTask.Parameters)
    (Q:∀root,SpatialSource (P.ambient root))
    (hq:∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S:IntegerPolynomialRootQueriesBits.Source) (N:List Bool→ℕ) (hz:∀q,S.polynomial q≠0)
    (hd:∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root) (root:List Bool):
    (IntegralMixedSourceIntegerPrelude.records P Q hq S N hz hd root).map recordCritical=
      List.replicate (N root) false:=by
  simp only [IntegralMixedSourceIntegerPrelude.records,List.map_ofFn]
  change List.ofFn (fun _:Fin (N root)=>false)=_
  exact List.ofFn_const _ _

private theorem unit_record_tag {a B:ℕ} (P:SpatialSource a) (hp:0<a) (birth:ℕ) (code:List Bool)
    (hP:IntegralMixedExceptionalBounds.auxiliaryCap (a+1) P.degree≤2^B):
    recordCritical (IntegralMixedCausalUnitRecordBits.record P hp birth code hP)=
      IntegralMixedUnitRecordCode.critical code:=by
  unfold IntegralMixedCausalUnitRecordBits.record
  cases IntegralMixedUnitRecordCode.critical code <;> rfl

private theorem prelude_flags (ctx:List Bool) (R:List Bool→ℕ):
    (CoefficientMarkedRecordSerializer.prelude hn ht ha ctx R).map recordCritical=
      List.replicate (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) false:=by
  unfold CoefficientMarkedRecordSerializer.prelude
  exact integer_records_tags _ _ _ _ _ _ _ _

private theorem prelude_tags (ctx:List Bool) (R U:List Bool→ℕ):
    (CoefficientMarkedRecordSerializer.prelude hn ht ha ctx R).map recordCritical=
      (CoefficientMarkedRecordSerializer.prelude hn ht ha ctx U).map recordCritical:=by
  exact (prelude_flags hn ht ha ctx R).trans (prelude_flags hn ht ha ctx U).symm

private theorem record_tags (ctx:List Bool) (R U:List Bool→ℕ) (cs:List (List Bool)):
    (CoefficientMarkedRecordSerializer.records hn ht ha ctx R cs).map recordCritical=
      (CoefficientMarkedRecordSerializer.records hn ht ha ctx U cs).map recordCritical:=by
  induction cs with
  | nil=>simpa only [CoefficientMarkedRecordSerializer.records] using prelude_tags hn ht ha ctx R U
  | cons code cs ih=>
    simp only [CoefficientMarkedRecordSerializer.records,List.map_cons]
    apply congrArg₂ List.cons _ ih
    unfold CoefficientMarkedRecordSerializer.record
    exact (unit_record_tag _ _ _ _ _).trans (unit_record_tag _ _ _ _ _).symm

noncomputable def commands (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):=
  CoefficientMarkedRecordSerializer.commands hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)

theorem tags_eq (ctx:List Bool) (R U:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    tags (commands hn ht ha ctx R k hk)=tags (commands hn ht ha ctx U k hk):=by
  unfold commands CoefficientMarkedRecordSerializer.commands
  rw [commands_tags,commands_tags]
  exact record_tags hn ht ha ctx R U (CoefficientMarkedRecordActual.codes ctx k)

abbrev index (ctx:List Bool) (k:ℕ):Type:=
  CoefficientMarkedRecordPrefix.Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
    (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx))
    (CoefficientMarkedRecordActual.codes ctx k)

noncomputable def castLayout (I:Type) (L:Layout) (h:I=L.index):Layout:=
  ⟨I,L.count,(Equiv.cast h).trans L.enumeration⟩

private theorem castLayout_eq (I:Type) (L:Layout) (h:I=L.index):castLayout I L h=L:=by
  cases h
  rfl

noncomputable def fixed (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):Layout:=
  castLayout (index (n:=n) ctx k) (layout (commands hn ht ha ctx (fun _=>0) k hk))
    (CoefficientMarkedRecordSerializer.index_eq hn ht ha ctx (fun _=>0)
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
      (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk))

theorem commands_layout (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    layout (commands hn ht ha ctx R k hk)=fixed hn ht ha ctx k hk:=
  (layout_eq _ _ (tags_eq hn ht ha ctx R (fun _=>0) k hk)).trans (castLayout_eq _ _ _).symm

attribute [local irreducible] commands fixed IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedFramedHistoryFamilyBits.commands

def key (ctx:List Bool) (k:ℕ) (aux:List Bool):List Bool:=
  IntegralMixedFramedHistoryFamilyBits.keyAt ctx ((CoefficientMarkedPreludeActual.indices n ctx).length+k) aux

theorem key_root (ctx:List Bool) (k:ℕ) (aux:List Bool):pairFst (key (n:=n) ctx k aux)=ctx:=
  IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

private theorem layout_of_heq {a b B C:ℕ} (cs:List (Instruction a B)) (ds:List (Instruction b C))
    (ha:a=b) (hb:B=C) (hs:HEq cs ds):layout cs=layout ds:=by
  cases ha
  cases hb
  cases eq_of_heq hs
  rfl

theorem family_layout (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    layout (IntegralMixedFramedHistoryFamilyBits.commands
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (key (n:=n) ctx k aux))=
      fixed hn ht ha ctx k hk:=by
  have Hn:(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).ambient
      (pairFst (key (n:=n) ctx k aux))=IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3:=
    congrArg (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+3) (key_root (n:=n) ctx k aux)
  have HB:(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width
      (pairFst (key (n:=n) ctx k aux))=CoefficientMarkedIntegerBirth.width hn ht ha ctx:=
    congrArg (fun root=>CoefficientMarkedIntegerBirth.width hn ht ha root) (key_root (n:=n) ctx k aux)
  have HC:=commands_layout hn ht ha ctx R k hk
  unfold commands at HC
  exact (layout_of_heq _ _ Hn HB (CoefficientMarkedRecordActual.family_commands hn ht ha ctx R k hk aux)).trans HC

theorem count_eq (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (key (n:=n) ctx k aux)=
      (fixed hn ht ha ctx k hk).count:=by
  change IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (key (n:=n) ctx k aux))=_
  exact congrArg Layout.count (family_layout hn ht ha ctx R k hk aux)

end LeanCanny.Encoding.CoefficientMarkedRecordRowLayout
