/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Algebra.IntegralMixedFramedCompanionControlsSpace
/-! # Arbitrary-modulus companion access from the charged current-Q backend

The existing modulus-augmented root, literal lifted plan and source pullback
are reused exactly. Producer semantics give the source matrix entry directly;
no legacy full-slope Primitive or evaluated bank reader is constructed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access Active finish finish_FP controlsQuery)
open scoped Classical

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew) : controlsQuery P D∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (IntegralMixedFramedCompanionQueryBits.query_FP (lifted P) (lifted_access P a) (liftedPlan P D) Hnew
      c.producer.tables c.producer.native c.producer.represents)

theorem model_query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (q : List Bool)
    (hb : IntegralMixedFramedCompanionQueryBits.sourceBirth P q<P.cap (IntegralMixedFramedCompanionQueryBits.root q))
    (hm : IntegralMixedFramedCompanionQueryBits.callerModulus q≤numericCap P (IntegralMixedFramedCompanionQueryBits.root q)) :
    (IntegralMixedFramedCurrentQNativeBits.machine P a D H c).model (IntegralMixedFramedCompanionQueryBits.query P D q)=
      PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HA := IntegralMixedFramedCurrentQNativeBits.producer_actual P a D H c _ (fun _ _ => rfl)
  rw [HA.companion _ (IntegralMixedFramedCompanionQueryBits.query_valid P D q hb)
    (IntegralMixedFramedCompanionQueryBits.query_routine P D q)
    (IntegralMixedFramedCompanionQueryBits.query_context_le P D q) (IntegralMixedFramedCompanionQueryBits.query_phase P D q)]
  rw [IntegralMixedFramedProducerActualBits.companion_actual P D H _
    (IntegralMixedFramedCompanionQueryBits.query_actual_context P D q) (IntegralMixedFramedCompanionQueryBits.query_actual_coordinate P D q)]
  exact IntegralMixedFramedCompanionQueryBits.query_source_value P D H q hb hm

theorem query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedCurrentQNativeBits.machine (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c).model
      (controlsQuery P D q)=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HR := IntegralMixedFramedModulusPacket.packet_representable P q hq
  exact (model_query_value (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c
    (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2).trans
      (IntegralMixedFramedModulusPacket.source_value P D H Hnew q)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)) := by
  have EM := IntegralMixedFramedCurrentQNativeBits.model_space (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c hb
  have EA := EM.precompose (controlsQuery P D) (query_FP P a D Hnew c)
  have ED := IntegralMixedFramedCompanionDefaultBits.evaluator P a D H
  have EE := ((EA.pairOutputs ED).withInput.postcompose (finish P) (finish_FP P a))
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact query_value P a D H Hnew c q hq
    · exact IntegralMixedFramedCompanionDefaultBits.value_source P D H q (by unfold Active at hq; omega))
end LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionBits
