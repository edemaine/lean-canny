/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalContextLeaves
public import LeanCanny.Algebra.IntegralMixedPhysicalGuardedLeaves
/-! # Current physical low replies follow actual earlier component matches

Only selected valid original, derivative, and height children are matched.
The remaining callbacks name the literal physical denominator and height
at scalar routine queries. No child evaluator or source equality is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits IntegralMixedPhysicalNativeLowerBits
set_option backward.isDefEq.respectTransparency false

structure Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  original : ∀ q, IntegralMixedPhysicalContextBits.selected P .originalCoefficient q = true → reply q = original P F q
  derivative : ∀ q, IntegralMixedPhysicalContextBits.selected P .derivativeCoefficient q = true → reply q = IntegralMixedPhysicalCoefficientBits.derivative P F q
  height : ∀ q, IntegralMixedPhysicalContextBits.selected P .clearedHeight q = true → reply q = IntegralMixedPhysicalNativeLowerBits.height P F q

structure Callbacks (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  denominator : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → get P .slot15 q = 1 →
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) =
      IntegralMixedPhysicalDenominatorBits.value P F (IntegralMixedScalarQueryBits.commonDenominator P q)
  height : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → get P .slot15 q = 1 →
    reply (IntegralMixedScalarQueryBits.virtualHeight P q) =
      IntegralMixedPhysicalNativeLowerBits.height P F (IntegralMixedScalarQueryBits.virtualHeight P q)

theorem current_selected (P : Parameters) (p : Phase) (q c : List Bool)
    (hroot : RankedHistoryTask.root c = RankedHistoryTask.root q) (hbirth : birth P c = birth P q)
    (hroutine : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (hcontext : get P .slot15 c = get P .slot15 q)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : get P .slot15 q = 1) (hc : isPhase p c) :
    IntegralMixedPhysicalContextBits.selected P p c = true := by
  apply (IntegralMixedPhysicalContextBits.selected_iff P p c).mpr
  refine ⟨?_, hcontext.trans hx⟩
  apply (selectedValid_iff P p c).mpr
  constructor
  · change birth P c < P.cap (RankedHistoryTask.root c)
    rw [hroot, hbirth]
    exact hv
  · exact ⟨hroutine.trans hr, hc⟩

theorem matrix_selected (P : Parameters) (p : Phase) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hx : get P .slot15 (pairFst z) = 1) :
    IntegralMixedPhysicalContextBits.selected P p (IntegralCriticalFlatMatrixQuery.writer P p z) = true :=
  current_selected P p _ _ (IntegralCriticalFlatMatrixQuery.writer_root P p z)
    (IntegralCriticalFlatMatrixQuery.writer_birth P p z) (IntegralMixedMatrixFrames.matrix_routine P p z)
    (by rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl) hv hr hx
    (IntegralCriticalFlatMatrixQuery.writer_phase P p z)

theorem factor_selected (P : Parameters) (p : Phase) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hx : get P .slot15 (pairFst z) = 1) :
    IntegralMixedPhysicalContextBits.selected P p (IntegralCriticalFlatFactorQuery.writer P p z) = true := by
  apply current_selected P p _ _ (IntegralCriticalFlatFactorQuery.writer_root P p z)
    (IntegralCriticalFlatFactorQuery.writer_birth P p z) _
    (IntegralCriticalFlatFactorQuery.writer_other P p z .slot15 (by decide) (by decide) (by decide)) hv hr hx
    (IntegralCriticalFlatFactorQuery.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatFactorQuery.writer_other P p z .slot14 (by decide) (by decide) (by decide)]

theorem coefficient (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (z : List Bool) (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hctx : get P .slot15 (pairFst z) = 1) :
    reply (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) =
      IntegralMixedPhysicalMonomialLeafBits.coefficient P F (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) := by
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  split_ifs with hx
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl
    unfold IntegralMixedPhysicalMonomialLeafBits.coefficient
    rw [HE, ite_eq_left hx]
    exact hm.derivative _ (matrix_selected P .derivativeCoefficient z hv hr hctx)
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl
    unfold IntegralMixedPhysicalMonomialLeafBits.coefficient
    rw [HE, ite_eq_right hx]
    exact hm.original _ (matrix_selected P .originalCoefficient z hv hr hctx)

theorem monomial_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (hc : Callbacks P F reply) (q : List Bool)
    (hq : IntegralMixedPhysicalContextBits.selected P .monomialFactor q = true) : MonomialRepliesAt P F reply q := by
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .monomialFactor q).mp hq).2
  have HQ := (selectedValid_iff P .monomialFactor q).mp (IntegralMixedPhysicalContextBits.selected_raw P .monomialFactor q hq)
  refine ⟨?_, ?_, ?_⟩
  · intro _
    apply coefficient P F reply hm
    · rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]; exact HQ.1
    · rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]; exact HQ.2.1
    · rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]; exact HX
  · intro _
    apply hm.height
    apply factor_selected P .clearedHeight
    · rw [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent]; exact HQ.1
    · rw [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent]; exact HQ.2.1
    · rw [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent]; exact HX
  · intro _
    exact hc.denominator q HQ.1 HQ.2.1 HX

theorem monomial_correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (hc : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.monomialMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.monomial_correct P a F h g reply (monomial_replies P F reply hm hc)

theorem height_correct_of_callbacks (P : Parameters) (a : Access P) (F : Family) (reply : List Bool → List Bool)
    (hc : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.heightMachine P a F) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.height_correct P a F reply (fun q hq =>
    let HQ := (selectedValid_iff P .clearedHeight q).mp (IntegralMixedPhysicalContextBits.selected_raw P .clearedHeight q hq)
    hc.height q HQ.1 HQ.2.1 ((IntegralMixedPhysicalContextBits.selected_iff P .clearedHeight q).mp hq).2)

theorem derivative_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .derivativeCoefficient q = true) :
    DerivativeRepliesAt P F reply q := by
  intro _
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .derivativeCoefficient q).mp hq
  have HQ := (selectedValid_iff P .derivativeCoefficient q).mp HX.1
  let z := IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)
  have HO : IntegralDerivativeBits.original z = q :=
    (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans
      (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
  apply hm.original
  apply current_selected P .originalCoefficient q _
  · simpa only [HO] using IntegralCriticalFlatDerivativeQuery.writer_root P z
  · simpa only [HO] using IntegralCriticalFlatDerivativeQuery.writer_birth P z
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatDerivativeQuery.writer_other P z .slot14 (by decide) (by decide) (by decide), HO]
  · simpa only [HO] using IntegralCriticalFlatDerivativeQuery.writer_other P z .slot15 (by decide) (by decide) (by decide)
  · exact HQ.1
  · exact HQ.2.1
  · exact HX.2
  · exact IntegralCriticalFlatDerivativeQuery.writer_phase P z

theorem derivative_correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.derivative_correct P a F h g reply (derivative_replies P F reply hm)
end LeanCanny.Algebra.IntegralMixedPhysicalContextReplyBits
