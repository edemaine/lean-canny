/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
/-! # Current virtual low replies follow actual earlier component matches

Only selected valid original, derivative, and height children are matched.
The remaining callbacks name the literal virtual denominator and height
at scalar routine queries. No child evaluator or source equality is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualNativeLowerBits
set_option backward.isDefEq.respectTransparency false

structure Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  original : ∀ q, IntegralMixedVirtualContextBits.selected P .originalCoefficient q = true → reply q = original P F q
  derivative : ∀ q, IntegralMixedVirtualContextBits.selected P .derivativeCoefficient q = true → reply q = IntegralMixedVirtualCoefficientBits.derivative P F q
  height : ∀ q, IntegralMixedVirtualContextBits.selected P .clearedHeight q = true → reply q = IntegralMixedVirtualNativeLowerBits.height P F q

structure Callbacks (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  denominator : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → IntegralMixedVirtualContextBits.context P q →
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) =
      IntegralMixedVirtualDenominatorBits.value P F (IntegralMixedScalarQueryBits.commonDenominator P q)
  height : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → IntegralMixedVirtualContextBits.context P q →
    reply (IntegralMixedScalarQueryBits.virtualHeight P q) =
      IntegralMixedVirtualNativeLowerBits.height P F (IntegralMixedScalarQueryBits.virtualHeight P q)

theorem current_selected (P : Parameters) (p : Phase) (q c : List Bool)
    (hroot : RankedHistoryTask.root c = RankedHistoryTask.root q) (hbirth : birth P c = birth P q)
    (hroutine : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (hcontext : get P .slot15 c = get P .slot15 q)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : IntegralMixedVirtualContextBits.context P q) (hc : isPhase p c) :
    IntegralMixedVirtualContextBits.selected P p c = true := by
  apply (IntegralMixedVirtualContextBits.selected_iff P p c).mpr
  refine ⟨?_, by simpa only [IntegralMixedVirtualContextBits.context, hcontext] using hx⟩
  apply (selectedValid_iff P p c).mpr
  constructor
  · change birth P c < P.cap (RankedHistoryTask.root c)
    rw [hroot, hbirth]
    exact hv
  · exact ⟨hroutine.trans hr, hc⟩

theorem matrix_selected (P : Parameters) (p : Phase) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    IntegralMixedVirtualContextBits.selected P p (IntegralCriticalFlatMatrixQuery.writer P p z) = true :=
  current_selected P p _ _ (IntegralCriticalFlatMatrixQuery.writer_root P p z)
    (IntegralCriticalFlatMatrixQuery.writer_birth P p z) (IntegralMixedMatrixFrames.matrix_routine P p z)
    (by rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl) hv hr hx
    (IntegralCriticalFlatMatrixQuery.writer_phase P p z)

theorem factor_selected (P : Parameters) (p : Phase) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    IntegralMixedVirtualContextBits.selected P p (IntegralCriticalFlatFactorQuery.writer P p z) = true := by
  apply current_selected P p _ _ (IntegralCriticalFlatFactorQuery.writer_root P p z)
    (IntegralCriticalFlatFactorQuery.writer_birth P p z) _
    (IntegralCriticalFlatFactorQuery.writer_other P p z .slot15 (by decide) (by decide) (by decide)) hv hr hx
    (IntegralCriticalFlatFactorQuery.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatFactorQuery.writer_other P p z .slot14 (by decide) (by decide) (by decide)]

theorem coefficient (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (z : List Bool) (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) (hctx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    reply (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) =
      IntegralMixedVirtualMonomialLeafBits.coefficient P F (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) := by
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  split_ifs with hx
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl
    unfold IntegralMixedVirtualMonomialLeafBits.coefficient
    rw [HE, ite_eq_left hx]
    exact hm.derivative _ (matrix_selected P .derivativeCoefficient z hv hr hctx)
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]; rfl
    unfold IntegralMixedVirtualMonomialLeafBits.coefficient
    rw [HE, ite_eq_right hx]
    exact hm.original _ (matrix_selected P .originalCoefficient z hv hr hctx)

theorem monomial_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (hc : Callbacks P F reply) (q : List Bool)
    (hq : IntegralMixedVirtualContextBits.selected P .monomialFactor q = true) : MonomialRepliesAt P F reply q := by
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .monomialFactor q).mp hq).2
  have HQ := (selectedValid_iff P .monomialFactor q).mp (IntegralMixedVirtualContextBits.selected_raw P .monomialFactor q hq)
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
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (hc : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.monomialMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.monomial_correct P a F h g reply (monomial_replies P F reply hm hc)

theorem height_correct_of_callbacks (P : Parameters) (a : Access P) (F : Family) (reply : List Bool → List Bool)
    (hc : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.heightMachine P a F) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.height_correct P a F reply (fun q hq =>
    let HQ := (selectedValid_iff P .clearedHeight q).mp (IntegralMixedVirtualContextBits.selected_raw P .clearedHeight q hq)
    hc.height q HQ.1 HQ.2.1 ((IntegralMixedVirtualContextBits.selected_iff P .clearedHeight q).mp hq).2)

theorem derivative_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .derivativeCoefficient q = true) :
    DerivativeRepliesAt P F reply q := by
  intro _
  have HX := (IntegralMixedVirtualContextBits.selected_iff P .derivativeCoefficient q).mp hq
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
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.derivative_correct P a F h g reply (derivative_replies P F reply hm)
end LeanCanny.Algebra.IntegralMixedVirtualContextReplyBits
