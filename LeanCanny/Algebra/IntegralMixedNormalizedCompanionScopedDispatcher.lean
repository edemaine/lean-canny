/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionScoped
/-! # Current creating-cut dispatch uses only scoped normalized replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open IntegralMixedCutSource IntegralMixedNormalizedCompanionBits
theorem correct_scoped (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : ScopedNormalizationMatches P F (fun q => residueBits (x q)))
    (hl : LeadingMatches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact leading_correct_scoped P a F hd g x hm
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact companion_correct_scoped P a F h hd g x hm hl
    · cases hb

theorem correct_of_matches_scoped (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hn : ScopedNormalizationMatches P F (fun q => residueBits (x q)))
    (hm : Matches P a F h hd (fun q => residueBits (x q))) :
    Correct (machine P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_scoped P a F h hd g x hn (leading_matches P a F h hd _ hm)

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
