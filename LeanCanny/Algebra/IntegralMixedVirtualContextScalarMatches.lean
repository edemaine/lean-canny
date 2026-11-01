/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalar
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyMatching
/-! # Virtual scalar machines use only current original-leading and denominator leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem replies_of_matches (P : Parameters) (F : Family) (k : Kind)
    (answer : List Bool → List Bool) (hm : IntegralMixedVirtualContextScalarReplyBits.Matches P F answer)
    (q : List Bool) (hq : selected P k q = true) : RepliesAt P F answer q := by
  have H := (selected_iff P k q).mp hq
  exact ⟨(IntegralMixedVirtualContextScalarReplyBits.query_match P F answer hm .originalCoefficient q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) H.1 H.2.2.2).trans
      (IntegralMixedVirtualContextScalarReplyBits.leading_child P F q),
    (IntegralMixedVirtualContextScalarReplyBits.query_match P F answer hm .derivativeCoefficient q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) H.1 H.2.2.2).trans
      (IntegralMixedVirtualDenominatorBits.scalar_child P F q)⟩

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind)
    (answer : List Bool → List Bool) (hm : IntegralMixedVirtualContextScalarReplyBits.Matches P F answer) :
    Correct (machine P a F h k) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h k answer (replies_of_matches P F k answer hm)

end LeanCanny.Algebra.IntegralMixedVirtualContextScalarBits
namespace LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case originalCoefficient => exact ⟨_, rfl⟩
  case derivativeCoefficient => exact ⟨_, rfl⟩
  case monomialFactor => exact ⟨_, rfl⟩
  case factorPower => exact IntegralMixedVirtualCanonicalBits.height_canonical P F q
  all_goals exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyBits
