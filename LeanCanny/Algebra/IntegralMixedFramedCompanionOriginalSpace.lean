/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionUniformSpace
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackSyntax
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackBounds
/-! # Original syntax supplies the total creating-companion evaluator

The copied-root syntax and its native headers are constructed internally.
The result evaluates the literal actual framed source at every caller
modulus and basis packet, including terminal prefixes and malformed keys.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem original_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1≤s.factor root) (hL : ∀ root, 1≤s.nodes root) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)) :=
  evaluator P a D H
    (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.pullSyntax P D H s pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.familyInputs P D pairFst IntegralMixedFramedModulusPacket.extra
      s.nodes s.factor s.seed hs)
    (fun root => hF (pairFst root)) (fun root => hL (pairFst root))

end LeanCanny.Algebra.IntegralMixedFramedCompanionUniformBits
