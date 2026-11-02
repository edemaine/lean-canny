/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedModulusPacket
public import LeanCanny.Algebra.IntegralMixedFramedCompanionPlanning
public import LeanCanny.Algebra.IntegralMixedFramedCompanionDefault
public import LeanCanny.Algebra.IntegralMixedFramedNativePlanned
public import LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
/-! # Total actual creating-companion readback at arbitrary moduli

An honest projected-root plan carries the caller modulus in an additional
original field. Complete native arithmetic evaluates active births; literal
default-X companions evaluate all remaining prefixes. The theorem charges
only original syntax and its source/script bounds, never a matrix evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionQueryBits (root sourceBirth)
open scoped Classical

abbrev lifted (P : Parameters) := IntegralMixedFramedRootPullback.parameters P pairFst IntegralMixedFramedModulusPacket.extra
noncomputable abbrev liftedPlan (P : Parameters) (D : Plan P) :=
  IntegralMixedFramedRootPullback.plan P D pairFst IntegralMixedFramedModulusPacket.extra
theorem lifted_access (P : Parameters) (a : Access P) : Access (lifted P) :=
  IntegralMixedFramedRootPullback.access P a pairFst pairFst_mem_FP _ IntegralMixedFramedModulusPacket.extra_binary

def Active (P : Parameters) (q : List Bool) : Prop := sourceBirth P q<P.cap (root q)
theorem active_FP (P : Parameters) (a : Access P) : FPPred (Active P) :=
  (BinaryFn.ofUnary (IntegralMixedFramedCompanionQueryBits.sourceBirth_unary P a)).lt
    ((BinaryFn.ofUnary a.cap).comp IntegralMixedFramedCompanionQueryBits.root_FP)

noncomputable def finish (P : Parameters) (z : List Bool) : List Bool :=
  if Active P (pairFst z) then pairFst (pairSnd z) else pairSnd (pairSnd z)
theorem finish_FP (P : Parameters) (a : Access P) : finish P∈FP :=
  ((active_FP P a).comp pairFst_mem_FP).ite_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def query (P : Parameters) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) (q : List Bool) : List Bool :=
  IntegralMixedFramedCompanionQueryBits.query
    (IntegralMixedFramedNormalizationBits.planned (lifted P) s.nodes s.factor s.seed)
    (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (IntegralMixedFramedModulusPacket.packet q)

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) : query P D Hnew s∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (IntegralMixedFramedCompanionQueryBits.query_FP _
      (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a) s.nodes_native s.factor_native s.seed_native)
      (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
      (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) Hnew s.nodes s.factor s.seed)
      s.unit.tables s.unit.native ⟨s.unit.represents.commands,s.unit.represents.fallback⟩)

theorem query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew)
    (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedNativeBits.plannedMachine (lifted P) (lifted_access P a) (liftedPlan P D) Hnew s).model
      (query P D Hnew s q)=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HB := (IntegralMixedFramedModulusPacket.packet_representable P q hq).1
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (IntegralMixedFramedModulusPacket.packet q)≤
      (lifted P).modulusBound (root (IntegralMixedFramedModulusPacket.packet q)) := by
    rw [IntegralMixedFramedModulusPacket.packet_root,IntegralMixedFramedModulusPacket.packet_modulus]
    simpa only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,
      IntegralMixedFramedModulusPacket.extra,pairSnd_pair,IntegralMixedFramedCompanionQueryBits.callerModulus] using
      (le_max_right (P.modulusBound (root q)) (IntegralMixedFramedCompanionQueryBits.callerModulus q))
  have HR := IntegralMixedFramedCompanionBits.representable_planned (lifted P) s.nodes s.factor s.seed _ HB HM
  have HE := IntegralMixedFramedCompanionQueryBits.model_query_value _
    (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a) s.nodes_native s.factor_native s.seed_native)
    (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) Hnew s.nodes s.factor s.seed)
    (IntegralMixedFramedNativeBits.plannedControls (lifted P) (lifted_access P a) (liftedPlan P D) Hnew s)
    (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2
  exact HE.trans ((IntegralMixedFramedCompanionBits.value_planned _ _ Hnew _ _ _ _).trans
    (IntegralMixedFramedModulusPacket.source_value P D H Hnew q))

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (hF : ∀ root, 1≤s.factor root) (hL : ∀ root, 1≤s.nodes root) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)) := by
  have EM := IntegralMixedFramedNativeBits.planned_model_space (lifted P) (lifted_access P a)
    (liftedPlan P D) Hnew s hs hF
    (IntegralMixedFramedUnitSourceBounds.fallback_bounds _ _ _ s.unit.writer s.unit.snapshot s.nodes s.seed hL)
  have EA := EM.precompose (query P D Hnew s) (query_FP P a D Hnew s)
  have ED := IntegralMixedFramedCompanionDefaultBits.evaluator P a D H
  have EE := ((EA.pairOutputs ED).withInput.postcompose (finish P) (finish_FP P a))
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact query_value P a D H Hnew s q hq
    · exact IntegralMixedFramedCompanionDefaultBits.value_source P D H q (by unfold Active at hq; omega))

theorem source_arity_unary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (IntegralMixedFramedCompanionBits.source P D H).arity :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq
    (fun key => (IntegralMixedFramedCompanionBits.source_arity P D H key).symm)

theorem source_width_unary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (IntegralMixedFramedCompanionBits.source P D H).width :=
  a.width.comp pairFst_mem_FP

end LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
