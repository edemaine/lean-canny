/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanned
/-! # Honest caller-modulus lifting followed by current-Q budget planning

The original root, source and saved creator are retained. This charges native
controls and verified original bounds, without legacy integer-word syntax.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionPlannedBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access Active finish finish_FP)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData planned_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev parameters (P : Parameters) (L F C : List Bool → ℕ) := planned (lifted P) L F C
noncomputable abbrev plan (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) := plannedPlan (lifted P) (liftedPlan P D) L F C
noncomputable abbrev data (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D)) (L F C : List Bool → ℕ) :=
  plannedData (lifted P) (liftedPlan P D) H L F C

noncomputable def query (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (q : List Bool) :=
  IntegralMixedFramedCompanionQueryBits.query (parameters P L F C) (plan P D L F C) (IntegralMixedFramedModulusPacket.packet q)

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C)) :
    query P D L F C∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (IntegralMixedFramedCompanionQueryBits.query_FP (parameters P L F C)
      (planned_access (lifted P) (lifted_access P a) hL hF hC) (plan P D L F C) (data P D H L F C)
      c.producer.tables c.producer.native c.producer.represents)

theorem query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D Hnew L F C))
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedCurrentQNativeBits.machine (parameters P L F C)
      (planned_access (lifted P) (lifted_access P a) hL hF hC) (plan P D L F C) (data P D Hnew L F C) c).model
      (query P D L F C q)=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HB := (IntegralMixedFramedModulusPacket.packet_representable P q hq).1
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (IntegralMixedFramedModulusPacket.packet q)≤
      (lifted P).modulusBound (IntegralMixedFramedCompanionQueryBits.root (IntegralMixedFramedModulusPacket.packet q)) := by
    rw [IntegralMixedFramedModulusPacket.packet_root,IntegralMixedFramedModulusPacket.packet_modulus]
    simpa only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,
      IntegralMixedFramedModulusPacket.extra,pairSnd_pair,IntegralMixedFramedCompanionQueryBits.callerModulus] using
      (le_max_right (P.modulusBound (IntegralMixedFramedCompanionQueryBits.root q))
        (IntegralMixedFramedCompanionQueryBits.callerModulus q))
  have HR := IntegralMixedFramedCompanionBits.representable_planned (lifted P) L F C _ HB HM
  have HE := IntegralMixedFramedCurrentQCompanionBits.model_query_value (parameters P L F C)
    (planned_access (lifted P) (lifted_access P a) hL hF hC) (plan P D L F C) (data P D Hnew L F C) c
    (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2
  exact HE.trans ((IntegralMixedFramedCompanionBits.value_planned _ _ Hnew _ _ _ _).trans
    (IntegralMixedFramedModulusPacket.source_value P D H Hnew q))

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D Hnew L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D Hnew L F C) c) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)) := by
  have EM := IntegralMixedFramedCurrentQNativeBits.model_space (parameters P L F C)
    (planned_access (lifted P) (lifted_access P a) hL hF hC) (plan P D L F C) (data P D Hnew L F C) c hb
  have EA := EM.precompose (query P D L F C) (query_FP P a D Hnew L F C hL hF hC c)
  have ED := IntegralMixedFramedCompanionDefaultBits.evaluator P a D H
  have EE := ((EA.pairOutputs ED).withInput.postcompose (finish P) (finish_FP P a))
  exact EE.congr (funext fun q=>by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact query_value P a D H Hnew L F C hL hF hC c q hq
    · exact IntegralMixedFramedCompanionDefaultBits.value_source P D H q (by unfold Active at hq; omega))

end LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionPlannedBits
