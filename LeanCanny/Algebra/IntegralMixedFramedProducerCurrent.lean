/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerDispatcher
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionCurrent
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionScopedDispatcher
/-! # Actual producer components share their current dispatcher replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 → answer q = (machine P a D H h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedPhysicalCompanionDispatcherBits.Matches P a (physicalFamily P D H) (physicalInput P a D H h) answer := by
  intro q hv hr hx
  exact (hm q hv hr).trans (model_physical P a D H h q hv hr hx)

theorem cut_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedNormalizedCompanionDispatcherBits.Matches P a (virtualFamily P D H)
      (virtualInput P a D H h) (degreeInput P a D H h) answer := by
  intro q hv hr hl hu
  exact (hm q hv hr).trans (model_cut P a D H h q hv hr hl hu)

theorem guarded_correct (P : Parameters) (a : Access P) (lo hi : ℕ) (M : Machine)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hm : Correct M answer frame) (hs : ∀ q, M.selected q = true) :
    Correct (guarded P a lo hi M) answer frame :=
  withGuard_correct M _ _ answer frame hm (fun q _ => hs q)

theorem correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D H h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalComponentBits.Matches P (physicalFamily P D H) (fun q => residueBits (x q)))
    (hs : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D H) (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (virtualFamily P D H) (fun q => residueBits (x q))) :
    Correct (machine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply guarded_correct
    · exact IntegralMixedIntegerFamilyBits.correct P a (virtualFamily P D H) (virtualInput P a D H h) (IntegralMixedFramedIntegerBits.polynomial P D) h.integer (fun q => residueBits (x q))
    · exact IntegralMixedIntegerFamilyBits.machine_selected P a (virtualFamily P D H) (virtualInput P a D H h) (IntegralMixedFramedIntegerBits.polynomial P D) h.integer
  · apply choose_correct
    · apply guarded_correct
      · exact IntegralMixedPhysicalCompanionDispatcherBits.correct_of_matches P a _ (physicalInput P a D H h)
          (IntegralMixedFramedPhysicalBits.geometry P D H) x hp hs
          (physical_matches P a D H h _ hm)
      · exact IntegralMixedPhysicalCompanionDispatcherBits.machine_selected P a _ (physicalInput P a D H h)
    · apply choose_correct
      · apply guarded_correct
        · exact IntegralMixedNormalizedCompanionDispatcherBits.correct_of_matches_scoped P a _
            (virtualInput P a D H h) (degreeInput P a D H h)
            (IntegralMixedFramedHistoryFamilyBits.geometry P D H) x hn (cut_matches P a D H h _ hm)
        · exact IntegralMixedNormalizedCompanionDispatcherBits.machine_selected P a _
            (virtualInput P a D H h) (degreeInput P a D H h)
      · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedFramedProducerBits
