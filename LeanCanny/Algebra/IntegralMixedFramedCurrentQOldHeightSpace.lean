/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightSpace
public import LeanCanny.Algebra.IntegralMixedFramedClearedMatrixSpace
/-! # Current-Q controls evaluate actual old cleared matrices at every modulus

This reuses the literal old-height packet and its source pullback, while the
current-Q scalar dispatcher supplies phase2. No legacy slope Primitive or
interpreted matrix evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedOldHeightBankBits.sourceEntry query

theorem model_query_currentQ (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (q : List Bool) (hb : Active P q)
    (hm : callerModulus q≤numericCap P (root q)) :
    (IntegralMixedFramedCurrentQNativeBits.machine P a D H c).model (query P q)=value P D H q := by
  have HV := query_valid P q hb
  have HR := query_routine P q
  have HC : 1≤get P .slot15 (query P q) ∧ get P .slot15 (query P q)≤4 := by rw [query_context]; omega
  have HP : isPhase .clearedHeight (query P q) := query_phase P q
  have HN := IntegralMixedFramedCurrentQNativeBits.model_component P a D H c 0 (query P q) HR
  have HS := IntegralMixedFramedCurrentQScalarBits.model_phase P a D H c.scalar .clearedHeight (query P q) HV HR HC (by decide) HP
  simp only [IntegralMixedFramedCurrentQNativeBits.component] at HN
  rw [HN,HS]
  change IntegralMixedFramedOldHeightBits.value P D H (query P q)=_
  rw [value,ite_eq_left hb,IntegralMixedFramedOldHeightBankBits.value_source,query_modulus P q hm,
    query_field P q hm .sourceIndex,query_field P q hm .row,query_field P q hm .col]
  simp only [field]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
  rw [IntegralMixedFramedOldHeightBankBits.sourceEntry_root,
    IntegralMixedFramedOldHeightBankBits.sourceEntry_root,query_saved_root,query_saved_birth]


theorem currentQ_query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedCurrentQNativeBits.machine (lifted P) (lifted_access P a) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) c).model
      (query (lifted P) (packet q))=value P D H q := by
  have HB := (packet_active P q).mpr hq
  have HM : callerModulus (packet q)≤numericCap (lifted P) (root (packet q)) := by
    simpa only [callerModulus,source,packet,pairFst_pair,root,key,lifted,IntegralMixedFramedCompanionQueryBits.root] using
      IntegralMixedFramedModulusPacket.packet_modulus_le P (pairFst q)
  exact (model_query_currentQ (lifted P) (lifted_access P a) (liftedPlan P D) _ c (packet q) HB HM).trans
    (value_pullback P D H q)

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) c) :
    SpaceFunction (value P D H) := by
  have EM:=IntegralMixedFramedCurrentQNativeBits.model_space (lifted P) (lifted_access P a) (liftedPlan P D) _ c hb
  have HQ: (query (lifted P)∘packet)∈FP := mem_FP_comp packet_FP (query_FP (lifted P) (lifted_access P a))
  have EE := (EM.precompose _ HQ).withInput.postcompose (finish P) (finish_FP P a)
  exact EE.congr (funext fun q=>by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact currentQ_query_value P a D H c q hq
    · exact (ite_eq_right hq : value P D H q=[]).symm)

end LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits

namespace LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) c) :
    SpaceFunction (value P D H) :=
  ((IntegralMixedFramedOldHeightQueryBits.currentQ_evaluator P a D H c hb).precompose (request P D H)
    (request_FP P a D H)).congr (funext fun q=>
      finite_value P D H (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q)
        (index q) (row P D H q) (col P D H q))

end LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
