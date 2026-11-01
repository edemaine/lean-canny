/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeScalar
/-! # Physical scalar machines use only current original-leading and denominator leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem replies_of_matches (P : Parameters) (F : Family) (k : Kind)
    (answer : List Bool → List Bool) (hm : IntegralMixedPhysicalScalarReplyBits.Matches P F answer)
    (q : List Bool) (hq : selected P k q = true) : RepliesAt P F answer q := by
  have H := (selected_iff P k q).mp hq
  exact ⟨(IntegralMixedPhysicalScalarReplyBits.query_match P F answer hm .originalCoefficient q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) H.1 H.2.2.2).trans
      (IntegralMixedPhysicalScalarReplyBits.leading_child P F q),
    (IntegralMixedPhysicalScalarReplyBits.query_match P F answer hm .derivativeCoefficient q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) H.1 H.2.2.2).trans
      (IntegralMixedPhysicalDenominatorBits.scalar_child P F q)⟩

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind)
    (answer : List Bool → List Bool) (hm : IntegralMixedPhysicalScalarReplyBits.Matches P F answer) :
    Correct (machine P a F h k) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h k answer (replies_of_matches P F k answer hm)

end LeanCanny.Algebra.IntegralMixedPhysicalNativeScalarBits
namespace LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case originalCoefficient => exact ⟨_, rfl⟩
  case derivativeCoefficient => exact ⟨_, rfl⟩
  case monomialFactor => exact ⟨_, rfl⟩
  case factorPower => exact IntegralMixedPhysicalCanonicalBits.height_canonical P F q
  all_goals exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyBits
