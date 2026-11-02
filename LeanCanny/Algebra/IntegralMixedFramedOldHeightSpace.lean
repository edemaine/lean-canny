/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightPacket
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackSyntax
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackBounds
/-! # Original syntax evaluates actual common-cleared old-bank matrices

Caller moduli enter an extra original-root field. The verified native phase2
model supplies each active old prefix; no matrix or interpreted-cell evaluator
is an input premise. Inactive birth packets have an explicit zero extension.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def uniformQuery (P : Parameters) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) :=
  query (IntegralMixedFramedNormalizationBits.planned (lifted P) s.nodes s.factor s.seed) ∘ packet

theorem uniformQuery_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) : uniformQuery P D Hnew s∈FP :=
  mem_FP_comp packet_FP (query_FP _ (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a)
    s.nodes_native s.factor_native s.seed_native))

theorem uniformQuery_value (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
    (q : List Bool) (hb : Active P q) :
    (IntegralMixedFramedNativeBits.plannedMachine (lifted P) (lifted_access P a) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) s).model
        (uniformQuery P D _ s q)=value P D H q := by
  have HB := (packet_active P q).mpr hb
  have HM : callerModulus (packet q)≤(lifted P).modulusBound (root (packet q)) := by
    rw [packet_modulus,packet_root]
    simpa only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,
      IntegralMixedFramedModulusPacket.extra,pairSnd_pair,callerModulus,IntegralMixedFramedCompanionQueryBits.callerModulus] using
        (le_max_right (P.modulusBound (root q)) (callerModulus q))
  have HR := IntegralMixedFramedCompanionBits.representable_planned (lifted P) s.nodes s.factor s.seed (source (packet q)) HB HM
  have HE := model_query _
    (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a) s.nodes_native s.factor_native s.seed_native)
    (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) s.nodes s.factor s.seed)
    (IntegralMixedFramedNativeBits.plannedControls (lifted P) (lifted_access P a) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) s)
    (packet q) HR.1 HR.2
  exact HE.trans ((value_planned _ _ _ _ _ _ _).trans (value_pullback P D H q))

noncomputable def finish (P : Parameters) (z : List Bool) := if Active P (pairFst z) then pairSnd z else []
theorem finish_FP (P : Parameters) (a : Access P) : finish P∈FP :=
  ((active_FP P a).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

theorem lifted_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
    (hs : IntegralMixedFramedStepHeight.FamilyInputs (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) := by
  have EM := IntegralMixedFramedNativeBits.planned_model_space _ (lifted_access P a) _ _ s hs hF
    (IntegralMixedFramedUnitSourceBounds.fallback_bounds _ _ _ s.unit.writer s.unit.snapshot s.nodes s.seed hL)
  have EE := (EM.precompose (uniformQuery P D _ s) (uniformQuery_FP P a D _ s)).withInput.postcompose (finish P) (finish_FP P a)
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hb
    · exact uniformQuery_value P a D H s q hb
    · exact (ite_eq_right hb : value P D H q=[]).symm)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) :=
  lifted_evaluator P a D H
    (IntegralMixedFramedRootPullback.pullSyntax P D H s pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.familyInputs P D pairFst IntegralMixedFramedModulusPacket.extra s.nodes s.factor s.seed hs)
    (fun root => hF (pairFst root)) (fun root => hL (pairFst root))

end LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
