/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightQuery
/-! # Actual old common-cleared entries are native scalar phase2 replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Active (P : Parameters) (q : List Bool) : Prop := sourceBirth P q<P.cap (root q)
theorem active_FP (P : Parameters) (a : Access P) : FPPred (Active P) :=
  (BinaryFn.ofUnary (sourceBirth_unary P a)).lt (BinaryFn.ofUnary (a.cap.comp root_FP))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Active P q then residueBits (IntegralMixedFramedOldHeightBankBits.sourceEntry P D H
    (key q) (retainedIndex P q) (rowIndex P q) (colIndex P q) : ZMod (callerModulus q)) else []

theorem query_birth (P : Parameters) (q : List Bool) : birth P (query P q)=sourceBirth P q := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  apply RankedHistoryTask.birth_pack
  simpa only [parent,RankedHistoryTask.root,pairFst_pair] using sourceBirth_bound P q

theorem query_phase (P : Parameters) (q : List Bool) : phase (query P q)=2 := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ (by decide)

theorem query_routine (P : Parameters) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (query P q)=0 := by
  rw [IntegralMixedRoutineTaskBits.routine,query_get]
  change min (min 0 (numericCap P (root q))) 6=0
  exact min_eq_left (by simp)

theorem query_context (P : Parameters) (q : List Bool) : get P .slot15 (query P q)=2 := by
  rw [query_get]
  change min 2 (numericCap P (root q))=2
  exact min_eq_left ((by decide : 2≤6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))

theorem query_modulus (P : Parameters) (q : List Bool) (hm : callerModulus q≤numericCap P (root q)) :
    modulus P (query P q)=callerModulus q := by
  unfold modulus
  rw [query_field P q hm]
  change (if callerModulus q=0 then 1 else callerModulus q)=callerModulus q
  rw [ite_eq_right (by unfold callerModulus IntegralMixedFramedCompanionQueryBits.callerModulus; omega)]

theorem query_valid (P : Parameters) (q : List Bool) (hb : Active P q) : IntegralMixedVirtualCaps.valid P (query P q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_root,query_birth]
  exact hb

theorem query_saved_root (P : Parameters) (q : List Bool) : pairFst (IntegralMixedVirtualTaskBits.saved P (query P q))=pairFst (key q) := by
  rw [IntegralMixedFullHistoryFamilyBits.saved_root,query_root]
  rfl

theorem query_saved_birth (P : Parameters) (q : List Bool) :
    prefixLength P (IntegralMixedVirtualTaskBits.saved P (query P q))=prefixLength P (key q) := by
  rw [IntegralMixedFramedProducerActualBits.framed_saved_prefix,query_birth]
  rfl

attribute [local irreducible] IntegralMixedFramedOldHeightBankBits.sourceEntry query

theorem model_query (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedNativeBits.Controls P D H) (q : List Bool) (hb : Active P q)
    (hm : callerModulus q≤numericCap P (root q)) :
    (IntegralMixedFramedNativeBits.machine P a D H c).model (query P q)=value P D H q := by
  have HV := query_valid P q hb
  have HR := query_routine P q
  have HC : 1≤get P .slot15 (query P q) ∧ get P .slot15 (query P q)≤4 := by rw [query_context]; omega
  have HP : isPhase .clearedHeight (query P q) := query_phase P q
  have HN := IntegralMixedFramedNativeBits.model_component P a D H c 0 (query P q) HR
  have HS := IntegralMixedFramedFullScalarBits.model_phase P a D H c.scalar .clearedHeight (query P q) HV HR HC (by decide) HP
  simp only [IntegralMixedFramedNativeBits.component] at HN
  rw [HN,HS]
  change IntegralMixedFramedOldHeightBits.value P D H (query P q)=_
  rw [value,ite_eq_left hb,IntegralMixedFramedOldHeightBankBits.value_source,query_modulus P q hm,
    query_field P q hm .sourceIndex,query_field P q hm .row,query_field P q hm .col]
  simp only [field]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
  rw [IntegralMixedFramedOldHeightBankBits.sourceEntry_root,
    IntegralMixedFramedOldHeightBankBits.sourceEntry_root,query_saved_root,query_saved_birth]

end LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
