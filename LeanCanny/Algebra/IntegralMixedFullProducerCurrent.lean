/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullProducerDispatcher
/-! # Actual producer components share their current dispatcher replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 → answer q = (machine P a D h).model q

theorem integer_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedIntegerProducerDispatcherBits.Matches P a D h.integer h.cells answer := by
  intro q hv hr hx
  exact (hm q hv hr).trans (model_integer P a D h q hv hr hx)

theorem physical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedPhysicalCompanionDispatcherBits.Matches P a (IntegralMixedPhysicalCompanionBits.fullFamily P D) h.physical answer := by
  intro q hv hr hx
  exact (hm q hv hr).trans (model_physical P a D h q hv hr hx)

theorem cut_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedNormalizedCompanionDispatcherBits.Matches P a (IntegralMixedFullHistoryFamilyBits.family P D)
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree answer := by
  intro q hv hr hl hu
  exact (hm q hv hr).trans (model_cut P a D h q hv hr hl hu)

theorem guarded_correct (P : Parameters) (a : Access P) (lo hi : ℕ) (M : Machine)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hm : Correct M answer frame) (hs : ∀ q, M.selected q = true) :
    Correct (guarded P a lo hi M) answer frame :=
  withGuard_correct M _ _ answer frame hm (fun q _ => hs q)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalComponentBits.Matches P (IntegralMixedPhysicalCompanionBits.fullFamily P D) (fun q => residueBits (x q)))
    (hs : IntegralMixedPhysicalScalarReplyBits.Matches P (IntegralMixedPhysicalCompanionBits.fullFamily P D) (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.NormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
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
        · exact IntegralMixedNormalizedCompanionDispatcherBits.correct_of_matches P a _
            (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree
            (IntegralMixedFullHistoryFamilyBits.geometry P D) x hn (cut_matches P a D h _ hm)
        · exact IntegralMixedNormalizedCompanionDispatcherBits.machine_selected P a _
            (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree
      · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
