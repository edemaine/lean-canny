/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualScaleRequests
public import LeanCanny.Algebra.IntegralMixedVirtualDenominatorValue
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFrozenConstant
/-! # Concrete scalar routine zero, phase five, for a * Q^D -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalScaleBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

def query (P : Parameters) := IntegralMixedRoutineTaskBits.query P (birth P) .scalar .productEntry

theorem query_FP (P : Parameters) (a : Access P) : query P ∈ FP :=
  IntegralMixedScalarQueryBits.scalarQuery_FP P a .productEntry

noncomputable def value (P : Parameters) (F : Family) :=
  IntegralMixedVirtualScaleRequestBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen

noncomputable def program (P : Parameters) (F : Family) :=
  IntegralMixedVirtualScaleRequestBits.program (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen
    (IntegralMixedScalarQueryBits.originalLeading P) (IntegralMixedScalarQueryBits.commonDenominator P)

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralMixedVirtualScaleRequestBits.certificates _ (IntegralMixedVirtualTaskBits.access P a F h).toEuler.toGradient.toFrozen _ _
    (IntegralMixedScalarQueryBits.scalarQuery_FP P a .originalCoefficient)
    (IntegralMixedScalarQueryBits.scalarQuery_FP P a .derivativeCoefficient)

theorem value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool)
    (ha : reply (IntegralMixedScalarQueryBits.originalLeading P q) = IntegralMixedVirtualNativeLowerBits.originalLeadingValue P F q)
    (hq : reply (IntegralMixedScalarQueryBits.commonDenominator P q) = IntegralMixedVirtualDenominatorBits.value P F q) :
    (program P F).value reply q = value P F q :=
  IntegralMixedVirtualScaleRequestBits.value_at _ (IntegralMixedVirtualTaskBits.access P a F h).toEuler.toGradient.toFrozen _ _ reply q
    (ha.trans ((IntegralMixedVirtualTaskBits.access P a F h).leading_eq q).symm)
    (hq.trans ((IntegralMixedVirtualTaskBits.access P a F h).denominator_eq q).symm)

theorem requests_frame (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 0) (hp : phase q = 5)
    (hc : (program P F).controller.Requests reply (fun _ => 2) q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  rcases (IntegralMixedVirtualScaleRequestBits.requests_iff _ _ _ reply q c).mp hc with rfl | rfl
  · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .originalCoefficient q hr (by rw [hp]; decide)
  · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .derivativeCoefficient q hr (by rw [hp]; decide)

theorem value_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := ⟨_, rfl⟩
end LeanCanny.Algebra.IntegralMixedOriginalScaleBits
