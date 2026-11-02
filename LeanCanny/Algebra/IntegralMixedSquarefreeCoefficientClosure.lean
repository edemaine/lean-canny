/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientNative
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorNative
/-! # The coefficient kernel closes against the actual value-factor branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedSquarefreeCoefficientTasks
open scoped Classical

abbrev FactorMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedSquarefreeFactorBits.Selected P F q → answer q = IntegralMixedSquarefreeFactorBits.value P F q

theorem child_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) (hl : Labels P F q) :
    IntegralMixedSquarefreeFactorBits.Selected P F (query P F q) := by
  refine ⟨IntegralMixedValueRowInternalReplies.valid_transport P q _ hs.1 (query_root P F q) (query_birth P F q),
    IntegralMixedValueFieldQuery.query_routine P (first P F) .rawFactor .relativePower .col (packedCol P F) q,
    IntegralMixedValueFieldQuery.query_phase P (first P F) .rawFactor .relativePower .col (packedCol P F) q,
    ?_, ?_, ?_, ?_⟩
  · simpa only [IntegralMixedVirtualContextBits.context, query_get P F g q hs.1 hl,
      reduceCtorEq, ite_false] using hs.2.2.2.1
  · change get P .slot8 (query P F q) < IntegralMixedCoordinateSquarefree.coordinateDegree
      (F.spatial (IntegralMixedVirtualTaskBits.saved P (query P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (query P F q)))
    rw [query_saved]
    have Hchoice := hs.2.2.2.2
    change get P .slot8 q < IntegralMixedCoordinateSquarefree.coordinateDegree
      (F.spatial (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q)) at Hchoice
    simpa only [query_get P F g q hs.1 hl, reduceCtorEq, ite_false] using Hchoice
  · change get P .row (query P F q) <
      count (F.birth (IntegralMixedVirtualTaskBits.saved P (query P F q)) + 1)
        (F.width (IntegralMixedVirtualTaskBits.saved P (query P F q)))
    rw [query_saved]
    simpa only [query_get P F g q hs.1 hl, reduceCtorEq, ite_false, ite_true, packedRow, scalar] using
      pack_lt _ _ _ _ hl.1 hl.2.2
  · change get P .col (query P F q) <
      count (F.birth (IntegralMixedVirtualTaskBits.saved P (query P F q)) + 1)
        (F.width (IntegralMixedVirtualTaskBits.saved P (query P F q)))
    rw [query_saved]
    simpa only [query_get P F g q hs.1 hl, reduceCtorEq, ite_false, ite_true, packedCol, scalar, Nat.zero_add] using
      pack_lt _ _ _ 0 hl.2.1 (Nat.two_pow_pos _)

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : FactorMatches P F answer) (q : List Bool) (hs : Selected P F q) :
    RepliesAt P F answer q := fun hl => own _ (child_selected P F g q hs hl)

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : FactorMatches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer (fun q hs => replies_of_matches P F g answer own q hs)

end LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientNative
