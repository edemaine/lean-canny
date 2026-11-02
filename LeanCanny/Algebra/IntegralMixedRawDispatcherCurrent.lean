/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawDispatcherValue
public import LeanCanny.Algebra.IntegralMixedNormalizationScopedCurrent
/-! # Raw-factor and coefficient replies close against one literal current model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 4 → answer q = (machine P a F h k hd).model q

theorem valueFactor_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool)
    (hm : Matches P a F h k hd answer) (q : List Bool) (hq : IntegralMixedValueFactorScopedBits.Selected P F q) :
    answer q = IntegralMixedValueFactorValue.value P F q :=
  (hm q hq.1.1 hq.1.2.1).trans (model_valueFactor P a F h k hd q hq)

theorem squarefreeFactor_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool)
    (hm : Matches P a F h k hd answer) : IntegralMixedSquarefreeCoefficientNative.FactorMatches P F answer := by
  intro q hq
  exact (hm q hq.1 hq.2.1).trans (model_squarefreeFactor P a F h k hd q hq)

theorem raw_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool)
    (hm : Matches P a F h k hd answer) : IntegralMixedNormalizationScopedBits.RawMatches P F answer := by
  intro q hv hr hp hx
  exact (hm q hv hr).trans (model_raw P a F h k hd q hv hr hp hx)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a F h k hd (fun q => residueBits (x q)))
    (critical : IntegralMixedVirtualContextComponentBits.Matches P F (fun q => residueBits (x q)))
    (gram : IntegralMixedGramScopedBits.Matches P F (fun q => residueBits (x q)))
    (psc : IntegralMixedPscContextUpperModel.Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h k hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · exact IntegralMixedPreparedCoordinateNative.correct P a F h k hd g _ critical
  · apply choose_correct
    · exact IntegralMixedPreparedSquarefreeNative.correct P a F h k hd g _ (squarefreeFactor_matches P a F h k hd _ hm)
    · apply choose_correct
      · exact IntegralMixedPreparedValueNative.correct_scoped P a F h k hd g _ (valueFactor_matches P a F h k hd _ hm)
      · apply choose_correct
        · exact IntegralMixedValueFactorScopedBits.correct_of_matches P a F h g _ gram
        · apply choose_correct
          · exact IntegralMixedSquarefreeFactorBits.correct_of_matches P a F h g x critical psc
          · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedRawDispatcherBits
