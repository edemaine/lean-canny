/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionUniformSpace

/-! # Arbitrary-modulus companions from general native framed controls

The modulus-augmented root retains every original source and bank. General
charged controls and verified bounds supply its arithmetic, without requiring
the specialized unit-selector syntax or a supplied matrix evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable def controlsQuery (P : Parameters) (D : Plan P) (q : List Bool) : List Bool :=
  IntegralMixedFramedCompanionQueryBits.query (lifted P) (liftedPlan P D) (IntegralMixedFramedModulusPacket.packet q)

theorem controlsQuery_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedNativeBits.Controls (lifted P) (liftedPlan P D) Hnew) : controlsQuery P D∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (IntegralMixedFramedCompanionQueryBits.query_FP (lifted P) (lifted_access P a) (liftedPlan P D) Hnew
      c.producer.tables c.producer.native c.producer.represents)

theorem controls_query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedNativeBits.machine (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c).model
      (controlsQuery P D q)=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HR:=IntegralMixedFramedModulusPacket.packet_representable P q hq
  exact (IntegralMixedFramedCompanionQueryBits.model_query_value (lifted P) (lifted_access P a)
    (liftedPlan P D) Hnew c (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2).trans
      (IntegralMixedFramedModulusPacket.source_value P D H Hnew q)

theorem controls_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)) := by
  have EM:=IntegralMixedFramedNativeBits.model_space (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c hb
  have EA:=EM.precompose (controlsQuery P D) (controlsQuery_FP P a D Hnew c)
  have ED:=IntegralMixedFramedCompanionDefaultBits.evaluator P a D H
  have EE:=((EA.pairOutputs ED).withInput.postcompose (finish P) (finish_FP P a))
  exact EE.congr (funext fun q=>by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact controls_query_value P a D H Hnew c q hq
    · exact IntegralMixedFramedCompanionDefaultBits.value_source P D H q (by unfold Active at hq; omega))
end LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
