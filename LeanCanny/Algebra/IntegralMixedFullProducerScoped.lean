/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionScopedDispatcher
public import LeanCanny.Algebra.IntegralMixedFullProducerValues
/-! # Full producers require normalized replies only in virtual creating contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem correct_scoped (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalComponentBits.Matches P (IntegralMixedPhysicalCompanionBits.fullFamily P D) (fun q => residueBits (x q)))
    (hs : IntegralMixedPhysicalScalarReplyBits.Matches P (IntegralMixedPhysicalCompanionBits.fullFamily P D) (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply guarded_correct
    · exact IntegralMixedIntegerProducerDispatcherBits.correct_of_matches P a D h.integer h.cells x (integer_matches P a D h _ hm)
    · exact IntegralMixedIntegerProducerDispatcherBits.machine_selected P a D h.integer h.cells
  · apply choose_correct
    · apply guarded_correct
      · exact IntegralMixedPhysicalCompanionDispatcherBits.correct_of_matches P a _ h.physical
          (IntegralMixedFullPhysicalBits.geometry P (IntegralMixedFullHistoryFamilyBits.physicalData P D)) x hp hs
          (physical_matches P a D h _ hm)
      · exact IntegralMixedPhysicalCompanionDispatcherBits.machine_selected P a _ h.physical
    · apply choose_correct
      · apply guarded_correct
        · exact IntegralMixedNormalizedCompanionDispatcherBits.correct_of_matches_scoped P a _
            (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree
            (IntegralMixedFullHistoryFamilyBits.geometry P D) x hn (cut_matches P a D h _ hm)
        · exact IntegralMixedNormalizedCompanionDispatcherBits.machine_selected P a _
            (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree
      · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
