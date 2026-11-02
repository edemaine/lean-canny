/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorNative
public import LeanCanny.Algebra.IntegralMixedPscContextUpperCorrect
/-! # Squarefree products close against current same-context arithmetic replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedSquarefreeFactorTasks
open scoped Classical

theorem top_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) :
    IntegralMixedVirtualContextBits.selected P .criticalCoefficient (top P F q) = true := by
  apply decide_eq_true
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P (topCol P) .critical .criticalCoefficient .coefficient _ q,
    IntegralMixedValueFieldQuery.query_phase P (topCol P) .critical .criticalCoefficient .coefficient _ q, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [top_root, top_birth]
    exact hs.1
  · simpa only [IntegralMixedVirtualContextBits.context, top_get P F g, reduceCtorEq,
      or_false, ite_false] using hs.2.2.2.1

theorem determinant_domain (P : Parameters) (F : Family) (q : List Bool) (hs : Selected P F q) :
    IntegralMixedPscContextUpperBits.Domain P F (determinant P q) := by
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P id .pscDeterminant .factorPower .target _ q, ?_, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [determinant_root, determinant_birth]
    exact hs.1
  · simpa only [IntegralMixedVirtualContextBits.context, determinant_get, reduceCtorEq, ite_false] using hs.2.2.2.1
  · rw [IntegralMixedPscContextUpperBits.degree_transport P F q _ (determinant_saved P q)]
    simpa only [determinant_get, reduceCtorEq, ite_false] using hs.2.2.2.2.1

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool)
    (critical : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (psc : IntegralMixedPscContextUpperModel.Matches P F answer) (q : List Bool) (hs : Selected P F q) :
    RepliesAt P F answer q := by
  constructor
  · have H := critical .criticalCoefficient (top P F q) (by decide) (top_selected P F g q hs)
    change answer (top P F q) = (IntegralMixedVirtualTaskBits.source P F).value (top P F q) at H
    exact H
  · have HP : phase (determinant P q) = 4 :=
      IntegralMixedValueFieldQuery.query_phase P id .pscDeterminant .factorPower .target _ q
    have H := psc _ (determinant_domain P F q hs) (Or.inr (Or.inr (Or.inr (Or.inr HP))))
    rw [HP] at H
    exact H

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (critical : IntegralMixedVirtualContextComponentBits.Matches P F (fun q => residueBits (x q)))
    (psc : IntegralMixedPscContextUpperModel.Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g x (fun q hs => replies_of_matches P F g _ critical psc q hs)

end LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
