/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
public import LeanCanny.Algebra.IntegralMixedFramedLeadingSpace

/-! # Actual creating leading residues from the native current-Q machine

The producer's integer backend may be a streamed polynomial Source; no
integer term word is required. The complete caller-modulus pullback is charged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access Active finish finish_FP)
open scoped Classical

theorem model_query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D H)
    (q : List Bool)
    (hb : IntegralMixedFramedCompanionQueryBits.sourceBirth P q<P.cap (IntegralMixedFramedCompanionQueryBits.root q))
    (hm : IntegralMixedFramedCompanionQueryBits.callerModulus q≤numericCap P (IntegralMixedFramedCompanionQueryBits.root q)) :
    (IntegralMixedFramedCurrentQNativeBits.machine P a D H c).model (IntegralMixedFramedLeadingBits.query P D q)=
      IntegralMixedFramedLeadingBits.value P D H q := by
  have HA:=IntegralMixedFramedCurrentQNativeBits.producer_actual P a D H c _ (fun _ _=>rfl)
  have HX : get P .slot15 (IntegralMixedFramedLeadingBits.query P D q)≤4 := by
    rw [IntegralMixedFramedLeadingBits.query_get]
    exact IntegralMixedFramedCompanionQueryBits.query_context_le P D q
  have HC : get P .slot15 (IntegralMixedFramedLeadingBits.query P D q)=
      (IntegralMixedFramedHistoryFamilyBits.instruction P D
        (IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedLeadingBits.query P D q))).command.context := by
    rw [IntegralMixedFramedLeadingBits.query_get,IntegralMixedFramedLeadingBits.query_saved]
    exact IntegralMixedFramedCompanionQueryBits.query_actual_context P D q
  rw [HA.leading _ (IntegralMixedFramedLeadingBits.query_valid P D q hb)
    (IntegralMixedFramedLeadingBits.query_routine P D q) HX (IntegralMixedFramedLeadingBits.query_phase P D q),
    IntegralMixedFramedProducerActualBits.leading_actual P D H _ HC,IntegralMixedFramedLeadingBits.query_modulus P D q hm]
  unfold IntegralMixedFramedLeadingBits.value
  apply congrArg (fun z : ℤ=>residueBits (z : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
  rw [IntegralMixedFramedLeadingBits.query_saved]
  exact IntegralMixedFramedLeadingBits.leading_congr P D H _ _
    (IntegralMixedFramedCompanionQueryBits.query_saved_root P D q)
    (IntegralMixedFramedCompanionQueryBits.query_saved_birth P D q)

noncomputable def query (P : Parameters) (D : Plan P) (q : List Bool) :=
  IntegralMixedFramedLeadingBits.query (lifted P) (liftedPlan P D) (IntegralMixedFramedModulusPacket.packet q)

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew) : query P D∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (IntegralMixedFramedLeadingBits.query_FP (lifted P) (lifted_access P a) (liftedPlan P D) Hnew
      c.producer.tables c.producer.native c.producer.represents)

theorem query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedCurrentQNativeBits.machine (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c).model
      (query P D q)=IntegralMixedFramedLeadingBits.value P D H q := by
  have HR:=IntegralMixedFramedModulusPacket.packet_representable P q hq
  exact (model_query_value (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c
    (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2).trans
      (IntegralMixedFramedLeadingBits.lifted_value P D H Hnew q)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c) :
    SpaceFunction (IntegralMixedFramedLeadingBits.value P D H) := by
  have EM:=IntegralMixedFramedCurrentQNativeBits.model_space (lifted P) (lifted_access P a) (liftedPlan P D) Hnew c hb
  have EA:=EM.precompose (query P D) (query_FP P a D Hnew c)
  have ED:=SpaceFunction.ofFP _ IntegralMixedFramedLeadingBits.defaultValue_FP
  have EE:=((EA.pairOutputs ED).withInput.postcompose (finish P) (finish_FP P a))
  exact EE.congr (funext fun q=>by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact query_value P a D H Hnew c q hq
    · exact IntegralMixedFramedLeadingBits.default_value P D H q (by unfold Active at hq; omega))

end LeanCanny.Algebra.IntegralMixedFramedCurrentQLeadingBits
