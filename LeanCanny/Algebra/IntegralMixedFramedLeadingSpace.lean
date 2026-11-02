/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedLeadingQuery
/-! # Actual creating leading residues from original syntax alone

An extra original root field carries the exact caller modulus. The complete
planned controller supplies active producers; default-X producers supply one.
No leading, denominator or interpreted arithmetic evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedFramedCompanionQueryBits (root sourceBirth callerModulus)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access Active)
open scoped Classical

def defaultValue (q : List Bool) := ArithmeticBits.one (BinaryNat.succ (PaddedIntegralGeneratorSource.modulus q))
theorem defaultValue_FP : defaultValue∈FP := by
  have HS : (fun q => BinaryNat.succ (PaddedIntegralGeneratorSource.modulus q))∈FP :=
    mem_FP_comp (f := PaddedIntegralGeneratorSource.modulus) (g := BinaryNat.succ)
      PaddedIntegralGeneratorSource.modulus_FP BinaryNat.succ_mem_FP
  exact mem_FP_comp (f := fun q => BinaryNat.succ (PaddedIntegralGeneratorSource.modulus q))
    (g := ArithmeticBits.one) HS ArithmeticBits.one_mem_FP
theorem default_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hb : P.cap (root q)≤sourceBirth P q) : defaultValue q=value P D H q := by
  unfold value
  rw [leading_default P D H _ hb]
  have HI : ((1 : ℤ) : ZMod (callerModulus q))=1 := Int.cast_one
  rw [HI]
  simpa only [defaultValue,BinaryNat.succ_eq_bits,callerModulus,BinaryNatCode.encode] using
    ArithmeticBits.one_residueBits (callerModulus q)

theorem lifted_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D)) (q : List Bool) :
    value (lifted P) (liftedPlan P D) Hnew (IntegralMixedFramedModulusPacket.packet q)=value P D H q := by
  unfold value
  rw [IntegralMixedFramedModulusPacket.packet_modulus,pullback_leading P D H]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
  apply leading_congr
  · simp only [IntegralMixedFramedRootPullback.key,IntegralMixedFramedModulusPacket.packet,
      IntegralMixedFramedModulusPacket.originalKey,PaddedIntegralGeneratorSource.base,pairFst_pair,root]
  · simp only [prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,IntegralMixedFramedRootPullback.key,
      IntegralMixedFramedModulusPacket.packet,IntegralMixedFramedModulusPacket.originalKey,PaddedIntegralGeneratorSource.base,
      pairFst_pair,pairSnd_pair,root]

noncomputable def uniformQuery (P : Parameters) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) (q : List Bool) : List Bool :=
  query (IntegralMixedFramedNormalizationBits.planned (lifted P) s.nodes s.factor s.seed)
    (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (IntegralMixedFramedModulusPacket.packet q)

theorem uniformQuery_FP (P : Parameters) (a : Access P) (D : Plan P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) : uniformQuery P D Hnew s∈FP :=
  mem_FP_comp IntegralMixedFramedModulusPacket.packet_FP
    (query_FP _ (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a) s.nodes_native s.factor_native s.seed_native)
      (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
      (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) Hnew s.nodes s.factor s.seed)
      s.unit.tables s.unit.native ⟨s.unit.represents.commands,s.unit.represents.fallback⟩)

theorem uniformQuery_value (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew) (q : List Bool) (hq : Active P q) :
    (IntegralMixedFramedNativeBits.plannedMachine (lifted P) (lifted_access P a) (liftedPlan P D) Hnew s).model
      (uniformQuery P D Hnew s q)=value P D H q := by
  have HB := (IntegralMixedFramedModulusPacket.packet_representable P q hq).1
  have HM : callerModulus (IntegralMixedFramedModulusPacket.packet q)≤(lifted P).modulusBound (root (IntegralMixedFramedModulusPacket.packet q)) := by
    rw [IntegralMixedFramedModulusPacket.packet_root,IntegralMixedFramedModulusPacket.packet_modulus]
    simpa only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,
      IntegralMixedFramedModulusPacket.extra,pairSnd_pair,callerModulus] using
      (le_max_right (P.modulusBound (root q)) (callerModulus q))
  have HR := IntegralMixedFramedCompanionBits.representable_planned (lifted P) s.nodes s.factor s.seed _ HB HM
  have HE := model_query _
    (IntegralMixedFramedNormalizationBits.planned_access _ (lifted_access P a) s.nodes_native s.factor_native s.seed_native)
    (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) Hnew s.nodes s.factor s.seed)
    (IntegralMixedFramedNativeBits.plannedControls (lifted P) (lifted_access P a) (liftedPlan P D) Hnew s)
    (IntegralMixedFramedModulusPacket.packet q) HR.1 HR.2
  have HP : value (IntegralMixedFramedNormalizationBits.planned (lifted P) s.nodes s.factor s.seed)
      (IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
      (IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) Hnew s.nodes s.factor s.seed)
      (IntegralMixedFramedModulusPacket.packet q)=value (lifted P) (liftedPlan P D) Hnew (IntegralMixedFramedModulusPacket.packet q) := rfl
  exact HE.trans (HP.trans (lifted_value P D H Hnew q))

theorem lifted_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted P) (liftedPlan P D) Hnew)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs (lifted P) (liftedPlan P D) s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) := by
  have EM := IntegralMixedFramedNativeBits.planned_model_space _ (lifted_access P a) _ Hnew s hs hF
    (IntegralMixedFramedUnitSourceBounds.fallback_bounds _ _ _ s.unit.writer s.unit.snapshot s.nodes s.seed hL)
  have EA := EM.precompose (uniformQuery P D Hnew s) (uniformQuery_FP P a D Hnew s)
  have ED := SpaceFunction.ofFP _ defaultValue_FP
  have EE := ((EA.pairOutputs ED).withInput.postcompose (IntegralMixedFramedCompanionUniformBits.finish P)
    (IntegralMixedFramedCompanionUniformBits.finish_FP P a))
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,IntegralMixedFramedCompanionUniformBits.finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact uniformQuery_value P a D H Hnew s q hq
    · exact default_value P D H q (by unfold Active at hq; omega))

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) :=
  lifted_evaluator P a D H (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.pullSyntax P D H s pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.familyInputs P D pairFst IntegralMixedFramedModulusPacket.extra s.nodes s.factor s.seed hs)
    (fun root => hF (pairFst root)) (fun root => hL (pairFst root))

end LeanCanny.Algebra.IntegralMixedFramedLeadingBits
