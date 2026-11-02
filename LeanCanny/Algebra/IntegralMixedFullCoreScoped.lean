/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCoreCurrent
public import LeanCanny.Algebra.IntegralMixedFullAlgebraCanonical
public import LeanCanny.Algebra.IntegralMixedFullProducerScoped
/-! # Joint arithmetic closes against the context-restricted normalization interface -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem correct_scoped (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalScalarReplyBits.Matches P (IntegralMixedFullCriticalDispatcherBits.physicalFamily P D) (fun q => residueBits (x q)))
    (hv : IntegralMixedVirtualContextScalarReplyBits.Matches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · apply node_correct
    · exact IntegralMixedFullCriticalDispatcherBits.correct P a D h.critical x (critical_matches P a D h _ hm) hp hv
    · exact IntegralMixedFullCriticalDispatcherBits.selected P a D h.critical
  · rcases List.mem_cons.mp hb with rfl | hb
    · apply node_correct
      · exact IntegralMixedFullProducerDispatcherBits.correct_scoped P a D h.producer x (producer_matches P a D h _ hm)
          (IntegralMixedFullCriticalDispatcherBits.physical_matches P a D h.critical _ (critical_matches P a D h _ hm)) hp hn
      · exact IntegralMixedFullProducerDispatcherBits.selected P a D h.producer
    · cases hb

end LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits

namespace LeanCanny.Algebra.IntegralMixedFullCoreBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem correct_scoped (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedFullScalarBits.correct_of_matches P a D h.scalar _ (producer_matches P a D h _ hm) (scalar_matches P a D h _ hm)
    · intro q _
      exact IntegralMixedFullScalarBits.machine_selected P a D h.scalar q
  · exact IntegralMixedFullAlgebraSpaceBits.correct P a D h.algebra x (algebra_matches P a D h _ hm)
      (IntegralMixedFullScalarBits.physical_matches P a D h.scalar _ (scalar_matches P a D h _ hm))
      (IntegralMixedFullScalarBits.virtual_matches P a D h.scalar _ (scalar_matches P a D h _ hm)) hn

end LeanCanny.Algebra.IntegralMixedFullCoreBits
