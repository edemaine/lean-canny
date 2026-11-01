/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLowerModelView
/-! # One semantic component match supplies concrete lower-controller replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLowerReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualNativeLowerBits
open IntegralMixedVirtualLowerModelBits
set_option backward.isDefEq.respectTransparency false

def Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 16 → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 →
    isPhase p q → reply q = component P F p q

structure Callbacks (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  leading : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 →
    reply (IntegralMixedScalarQueryBits.originalLeading P q) = originalLeadingValue P F q
  denominator : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 →
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) =
      IntegralMixedVirtualDenominatorBits.value P F (IntegralMixedScalarQueryBits.commonDenominator P q)
  height : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 →
    reply (IntegralMixedScalarQueryBits.virtualHeight P q) = height P F (IntegralMixedScalarQueryBits.virtualHeight P q)

theorem context (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (q c : List Bool)
    (hroot : RankedHistoryTask.root c = RankedHistoryTask.root q) (hbirth : birth P c = birth P q)
    (hroutine : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hc : isPhase p c) :
    reply c = component P F p c := by
  apply hm p c hp
  · change birth P c < P.cap (RankedHistoryTask.root c)
    rw [hroot, hbirth]
    exact hv
  · exact hroutine.trans hr
  · exact hc

theorem matrix (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatMatrixQuery.writer P p z) = component P F p (IntegralCriticalFlatMatrixQuery.writer P p z) :=
  context P F reply hm p hp _ _ (IntegralCriticalFlatMatrixQuery.writer_root P p z)
    (IntegralCriticalFlatMatrixQuery.writer_birth P p z) (IntegralMixedMatrixFrames.matrix_routine P p z) hv hr
    (IntegralCriticalFlatMatrixQuery.writer_phase P p z)

theorem factor (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatFactorQuery.writer P p z) = component P F p (IntegralCriticalFlatFactorQuery.writer P p z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatFactorQuery.writer_root P p z)
    (IntegralCriticalFlatFactorQuery.writer_birth P p z) _ hv hr (IntegralCriticalFlatFactorQuery.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatFactorQuery.writer_other P p z .slot14 (by decide) (by decide) (by decide)]

theorem grid (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatGridBits.writer P p z) = component P F p (IntegralCriticalFlatGridBits.writer P p z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatGridBits.writer_root P p z)
    (IntegralCriticalFlatGridBits.writer_birth P p z) _ hv hr (IntegralCriticalFlatGridBits.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatGridBits.writer_other P p z .slot14 (by decide)]

theorem next (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) :
    reply (IntegralCriticalFlatEulerBits.next P p q) = component P F p (IntegralCriticalFlatEulerBits.next P p q) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatEulerBits.next_root P p q)
    (IntegralCriticalFlatEulerBits.next_birth P p q) _ hv hr (IntegralCriticalFlatEulerBits.next_phase P p q)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerBits.next_get]

theorem coordinate (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatCoordinateQuery.writer P p z) = component P F p (IntegralCriticalFlatCoordinateQuery.writer P p z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatCoordinateQuery.writer_root P p z)
    (IntegralCriticalFlatCoordinateQuery.writer_birth P p z) _ hv hr (IntegralCriticalFlatCoordinateQuery.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatCoordinateQuery.writer_other P p z .slot14 (by decide)]

theorem spatial (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (x : ℕ) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatEulerRowsBits.spatial P p x z) = component P F p (IntegralCriticalFlatEulerRowsBits.spatial P p x z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatEulerRowsBits.spatial_root P p x z)
    (IntegralCriticalFlatEulerRowsBits.spatial_birth P p x z) _ hv hr (IntegralCriticalFlatEulerRowsBits.spatial_phase P p x z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerRowsBits.spatial_other P p x z .slot14 (by decide) (by decide) (by decide)]

theorem derivative (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (z : List Bool) (hv : IntegralMixedVirtualCaps.valid P (IntegralDerivativeBits.original z))
    (hr : IntegralMixedRoutineTaskBits.routine P (IntegralDerivativeBits.original z) = 1) :
    reply (IntegralCriticalFlatDerivativeQuery.writer P z) = component P F .originalCoefficient (IntegralCriticalFlatDerivativeQuery.writer P z) := by
  apply context P F reply hm .originalCoefficient (by decide) _ _ (IntegralCriticalFlatDerivativeQuery.writer_root P z)
    (IntegralCriticalFlatDerivativeQuery.writer_birth P z) _ hv hr (IntegralCriticalFlatDerivativeQuery.writer_phase P z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatDerivativeQuery.writer_other P z .slot14 (by decide) (by decide) (by decide)]


theorem coefficient (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (z : List Bool) (hv : IntegralMixedVirtualCaps.valid P (pairFst z))
    (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1) :
    reply (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) =
      IntegralMixedVirtualMonomialLeafBits.coefficient P F (IntegralCriticalFlatGenericMonomialBits.coefficientTask P z) := by
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  split_ifs with hx
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]
      rfl
    unfold IntegralMixedVirtualMonomialLeafBits.coefficient
    rw [HE, ite_eq_left hx]
    exact matrix P F reply hm .derivativeCoefficient (by decide) z hv hr
  · have HE : get P .expression (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient z) = get P .expression (pairFst z) := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]
      rfl
    unfold IntegralMixedVirtualMonomialLeafBits.coefficient
    rw [HE, ite_eq_right hx]
    exact matrix P F reply hm .originalCoefficient (by decide) z hv hr

theorem replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (hm : Matches P F reply) (hs : Callbacks P F reply) : IntegralMixedVirtualLowerDispatcherBits.Replies P F reply := by
  constructor
  · intro q hq _
    have HQ := (selectedValid_iff P .derivativeCoefficient q).mp hq
    let z := IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)
    have HO : IntegralDerivativeBits.original z = q :=
      (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans
        (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
    exact derivative P F reply hm z (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
  · intro q hq
    have HQ := (selectedValid_iff P .monomialFactor q).mp hq
    refine ⟨?_, ?_, ?_⟩
    · intro _
      have HO : pairFst (IntegralMonomialTermBits.coefficientQuery (monomialInput P F q)) = q :=
        IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent P (monomialSource P F) q
      exact coefficient P F reply hm _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
    · intro _
      have HO : pairFst (IntegralMonomialTermBits.heightQuery (monomialInput P F q)) = q :=
        IntegralCriticalFlatGenericMonomialBits.heightQuery_parent P (monomialSource P F) q
      exact factor P F reply hm .clearedHeight (by decide) _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
    · intro _
      exact hs.denominator q HQ.1 HQ.2.1
  · intro q hq r t
    have HQ := (selectedValid_iff P .factorPower q).mp hq
    exact matrix P F reply hm .monomialFactor (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq _
    have HQ := (selectedValid_iff P .productEntry q).mp hq
    have HO : pairFst (MatrixProductBits.factorQuery (productEntryFamily P F) (productEntryInput P F q)) = q := by
      simp only [MatrixProductBits.factorQuery, productEntryInput, IntegralCriticalFlatGenericProductEntryBits.input, pairFst_pair]
    change reply (IntegralCriticalFlatFactorQuery.writer P .factorPower _) = _
    exact factor P F reply hm .factorPower (by decide) _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
  · intro q hq r t
    have HQ := (selectedValid_iff P .productPower q).mp hq
    exact matrix P F reply hm .productEntry (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq _
    have HQ := (selectedValid_iff P .originalGridTerm q).mp hq
    change reply (IntegralCriticalFlatGridBits.writer P .productPower (gridTermInput P q)) = _
    exact grid P F reply hm .productPower (by decide) _ (by rw [IntegralCriticalFlatGridBits.termInput_parent]; exact HQ.1)
      (by rw [IntegralCriticalFlatGridBits.termInput_parent]; exact HQ.2.1)
  · intro q hq k _
    have HQ := (selectedValid_iff P .clearedGridSum q).mp hq
    exact grid P F reply hm .originalGridTerm (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq _ r t
    have HQ := (selectedValid_iff P .frozenPowerTerm q).mp hq
    exact matrix P F reply hm .clearedHeight (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq i _
    have HQ := (selectedValid_iff P .frozenPowerSum q).mp hq
    exact coordinate P F reply hm .frozenPowerTerm (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq _
    have HQ := (selectedValid_iff P .frozenConstant q).mp hq
    exact ⟨hs.leading q HQ.1 HQ.2.1, next P F reply hm .frozenPowerSum (by decide) q HQ.1 HQ.2.1⟩
  · intro q hq
    have HQ := (selectedValid_iff P .frozenLower q).mp hq
    refine ⟨?_, next P F reply hm .frozenConstant (by decide) q HQ.1 HQ.2.1⟩
    unfold IntegralCriticalFlatFrozenLowerBits.clearedTask
    exact spatial P F reply hm .clearedGridSum (by decide) 0 _
      (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1)
  · intro q hq _
    have HQ := (selectedValid_iff P .coordinateGradientProduct q).mp hq
    have HO : pairFst (coordinateQuery P F q) = q := IntegralCriticalFlatEulerRowsBits.productGradientQuery_parent P (source P F) q
    change reply (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (coordinateQuery P F q)) = _
    exact spatial P F reply hm .clearedGridSum (by decide) 1 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
  · intro q hq i _
    have HQ := (selectedValid_iff P .eulerSum q).mp hq
    unfold IntegralCriticalFlatEulerRowsBits.sumTask
    have HO : pairFst (IntegralEulerBits.termQuery (source P F) (pair q (BinaryNatCode.encode i))) = q := by
      simp only [IntegralEulerBits.termQuery, pairFst_pair]
    exact spatial P F reply hm .coordinateGradientProduct (by decide) 0 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
  · intro q hq
    have HQ := (selectedValid_iff P .eulerObjective q).mp hq
    exact ⟨next P F reply hm .frozenLower (by decide) q HQ.1 HQ.2.1,
      next P F reply hm .eulerSum (by decide) q HQ.1 HQ.2.1⟩
  · intro q hq
    have HQ := (selectedValid_iff P .eulerLower q).mp hq
    refine ⟨fun _ => next P F reply hm .eulerObjective (by decide) q HQ.1 HQ.2.1, ?_⟩
    intro _
    have HO : pairFst (gradientQuery P F q) = q := pairFst_pair _ _
    exact spatial P F reply hm .clearedGridSum (by decide) 1 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1)
  · intro q hq
    have HQ := (selectedValid_iff P .clearedHeight q).mp hq
    exact hs.height q HQ.1 HQ.2.1


theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : IntegralMixedVirtualLowerDispatcherBits.Primitive P F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) (hs : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualLowerDispatcherBits.machine P a F h ha)
      reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualLowerDispatcherBits.correct P a F h ha g reply (replies P F reply hm hs)
end LeanCanny.Algebra.IntegralMixedVirtualLowerReplyBits
