/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
/-! # Current-point comparison between two compatible endpoint providers

This comparison is separate from either fixed-provider graph. It compares
current point signatures and permits different initial marked coordinates.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def radius (q : List Bool) :=
  FormulaSignSlotRadialExternalPrelude.radius (FormulaSignSlotRadialProviderAtomic.provider q)
theorem radius_binary : BinaryFn radius :=
  FormulaSignSlotRadialExternalPrelude.radius_binary.comp FormulaSignSlotRadialProviderAtomic.provider_FP

def SameOriginal (z : List Bool) :=
  FormulaSignSlotRadialProviderAtomic.original (pairFst z)=
    FormulaSignSlotRadialProviderAtomic.original (pairSnd z)
noncomputable def SameRadius (z : List Bool) := radius (pairFst z)=radius (pairSnd z)
noncomputable def Compatible (z : List Bool) := SameOriginal z∧SameRadius z

theorem sameOriginal_FP : FPPred SameOriginal := Brackets.stringEq_fppred
  (mem_FP_comp (f:=pairFst) (g:=FormulaSignSlotRadialProviderAtomic.original) pairFst_mem_FP FormulaSignSlotRadialProviderAtomic.original_FP)
  (mem_FP_comp (f:=pairSnd) (g:=FormulaSignSlotRadialProviderAtomic.original) pairSnd_mem_FP FormulaSignSlotRadialProviderAtomic.original_FP)
theorem sameRadius_FP : FPPred SameRadius := by
  have HL : BinaryFn (fun z=>radius (pairFst z)):=radius_binary.comp pairFst_mem_FP
  have HR : BinaryFn (fun z=>radius (pairSnd z)):=radius_binary.comp pairSnd_mem_FP
  apply (Brackets.stringEq_fppred HL.bits_mem_FP HR.bits_mem_FP).of_iff
  intro z
  exact BinaryNatCode.encode_injective.eq_iff

theorem compatible_FP : FPPred Compatible:=sameOriginal_FP.and sameRadius_FP

theorem dimension_eq (a b : List Bool) (hc : SameOriginal (pair a b)) :
    FormulaSignSlotRadialProviderAtomic.dimension a=FormulaSignSlotRadialProviderAtomic.dimension b := by
  rw [FormulaSignSlotRadialProviderIdentity.dimension_eq,FormulaSignSlotRadialProviderIdentity.dimension_eq]
  exact congrArg (fun c : List Bool=>LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension c+3)
    (by simpa only [SameOriginal,pairFst_pair,pairSnd_pair] using hc)

noncomputable def language : Language := {z |Compatible z∧
  FormulaSignSlotRadialProviderAtomic.Valid (pairFst z)∧
  FormulaSignSlotRadialProviderAtomic.Valid (pairSnd z)∧
  FormulaSignSlotRadialProviderIdentity.query z∈FormulaSignSlotRadialProviderFieldEqualityList.language}

theorem decider : SpaceDecider language := by
  have EC:=SpaceFunction.ofFP _ compatible_FP.flag_mem_FP
  have EL:=FormulaSignSlotRadialProviderAtomic.evaluator.precompose pairFst pairFst_mem_FP
  have ER:=FormulaSignSlotRadialProviderAtomic.evaluator.precompose pairSnd pairSnd_mem_FP
  have EM:=(FormulaSignSlotRadialProviderFieldEqualityList.decider.precompose _
    FormulaSignSlotRadialProviderIdentity.query_FP).flagEvaluator
  apply (EC.andFlags (EL.andFlags (ER.andFlags EM))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,Function.comp_apply,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

theorem language_iff (a b : List Bool) (ha : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hb : FormulaSignSlotRadialProviderAtomic.Valid b) (hc : Compatible (pair a b)) :
    pair a b∈language ↔ HEq (FormulaSignSlotRadialProviderIdentity.point a ha)
      (FormulaSignSlotRadialProviderIdentity.point b hb) := by
  simpa only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,hc,ha,hb,true_and] using
    FormulaSignSlotRadialProviderIdentity.query_iff a b ha hb (dimension_eq a b hc.1)

private theorem cast_function_heq {a b : ℕ} (h : a=b) (p : Fin a→ℝ) :
    HEq (fun i : Fin b=>p (Fin.cast h.symm i)) p := by
  cases h
  rfl

theorem point_native_heq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    HEq (FormulaSignSlotRadialProviderIdentity.point q hv)
      (FormulaSignSlotRadialProviderAtomic.point q hv) := by
  unfold FormulaSignSlotRadialProviderIdentity.point
  exact cast_function_heq (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q))
    (FormulaSignSlotRadialProviderAtomic.point q hv)

theorem language_native_iff (a b : List Bool) (ha : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hb : FormulaSignSlotRadialProviderAtomic.Valid b) (hc : Compatible (pair a b)) :
    pair a b∈language ↔ HEq (FormulaSignSlotRadialProviderAtomic.point a ha)
      (FormulaSignSlotRadialProviderAtomic.point b hb) := by
  rw [language_iff a b ha hb hc]
  constructor
  · intro h
    exact (point_native_heq a ha).symm.trans (h.trans (point_native_heq b hb))
  · intro h
    exact (point_native_heq a ha).trans (h.trans (point_native_heq b hb).symm)

theorem compatible_oldOf (provider payloadL wordL payloadR wordR : List Bool) :
    Compatible (pair
      (FormulaSignSlotRadialProviderAtomic.packet (FormulaSignSlotRadialProviderPair.oldOf provider) payloadL wordL)
      (FormulaSignSlotRadialProviderAtomic.packet provider payloadR wordR)) := by
  constructor
  · simpa only [SameOriginal,pairFst_pair,pairSnd_pair,FormulaSignSlotRadialProviderAtomic.original,
      FormulaSignSlotRadialProviderAtomic.provider_packet,FormulaSignSlotRadialProviderIntegerPlan.original] using
      FormulaSignSlotRadialProviderPair.original_oldOf provider
  · simpa only [SameRadius,radius,pairFst_pair,pairSnd_pair,
      FormulaSignSlotRadialProviderAtomic.provider_packet] using
      FormulaSignSlotRadialProviderPair.radius_oldOf provider

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint
