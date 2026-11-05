/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedShiftDegreeCeiling
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow
/-! # Actual eta-shifted certified heads retain affine radius mass -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData factor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem shift_rebudget (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C L' F' C' : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hs' : IntegralMixedFramedStepHeight.FamilyInputs P D L' F' C')
    (parent terminal : List Bool → List Bool) (d e center : List Bool → ℕ) (negative : Bool) :
    IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negative =
      IntegralMixedFramedTerminalTarskiHeadBits.head P D H L' F' C' hs' parent terminal d e center negative := by
  funext q
  unfold IntegralMixedFramedTerminalTarskiHeadBits.head
    IntegralMixedFramedTerminalParameterShiftBits.endpointFamily IntegralMixedFramedWindowQuery.family
  apply Polynomial.ext
  intro y
  simp only [RationalMonomialBivariateShift.coefficient]
  unfold RationalMonomialBivariateShift.coefficientMap RationalMonomialParameterShift.sourceDegree
    RationalMonomialParameterShift.numerator RationalMonomialParameterShift.parameterNumerator
    RationalMonomialParameterShift.base FixedWidthMonomialBits.polynomial IntegralMixedFramedBankScalars.scalars
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def shiftAllowance (roots : List Bool) :=
  IntegralMixedFramedShiftDegreeCeiling.shiftCeiling
    ((parameters hn ht ha).cap (pairFst roots)+1) ((parameters hn ht ha).width (pairFst roots))
    ((parameters hn ht ha).cap (pairSnd roots)+1)

theorem shiftAllowance_binary : BinaryFn (shiftAllowance hn ht ha) :=
  IntegralMixedFramedShiftDegreeCeiling.shiftCeiling_binary
    (((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp pairFst_mem_FP)
    (((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.comp pairSnd_mem_FP).add (UnaryFn.const 1))

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

private theorem native_coordinate_head_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      parent terminal d (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha hR) parent) q).coeff y) ≤
      2^(rawSlope hn ht ha (RankedHistoryTask.root (parent q))*R (RankedHistoryTask.root (parent q))+
        nativeHeadOffset hn ht ha (RankedHistoryTask.root (parent q))) := by
  have HM := certified_head_coefficient_mass hn ht ha hR parent terminal d
    (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha hR) parent) q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HP : 0 < 2^(parameters hn ht ha).width (RankedHistoryTask.root (parent q)) := pow_pos (by decide) _
  simp only [headOffset, IntegralMixedVirtualTaskBits.saved, pairFst_pair, nativeHeadOffset,
    IntegralMixedSelectedCoordinateHead.fullParameter]
  change _ + (_ + ((2^(parameters hn ht ha).width (RankedHistoryTask.root (parent q))-1)+1).size) ≤ _
  rw [Nat.sub_add_cancel HP, Nat.size_pow]

noncomputable def shiftedHead {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d center : List Bool → ℕ) (negative : Bool) (q : List Bool) :
    Polynomial (MvPolynomial (Fin ((IntegralMixedFramedBankSnapshotBits.atKey
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (terminal q)).count+1)) ℤ) :=
  IntegralMixedFramedTerminalTarskiHeadBits.head
    (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
    (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR) parent terminal d
    (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha hR) parent) center negative q

theorem certified_shifted_head_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d center : List Bool → ℕ) (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((shiftedHead hn ht ha hR parent terminal d center negative q).coeff y) ≤
      2^(rawSlope hn ht ha (RankedHistoryTask.root (parent q))*R (RankedHistoryTask.root (parent q))+
        nativeHeadOffset hn ht ha (RankedHistoryTask.root (parent q))+
        2*shiftAllowance hn ht ha (pair (RankedHistoryTask.root (parent q)) (pairFst (terminal q)))*
          (coordinateSlope hn ht ha (pairFst (terminal q))*R (pairFst (terminal q))+
            coordinateOffset hn ht ha (pairFst (terminal q))+1)) := by
  let P := certifiedParameters hn ht ha hR
  let D := certifiedPlan hn ht ha hR
  let H := certifiedData hn ht ha hR
  let e := IntegralMixedSelectedCoordinateHead.fullParameter P parent
  let hA := certified_affine_inputs hn ht ha hR
  let endpoint := IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) hA terminal center
  rw [shiftedHead, shift_rebudget _ _ _ _ _ _ (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) _ hA]
  have HM := RationalMonomialBivariateShift.coefficient_mass endpoint negative
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e)
    (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e)
    (fun c yy i => IntegralMixedFramedTerminalCoordinateHeadBits.source_fit P D H parent terminal d e (fun _ => yy) c i)
    _ q y (native_coordinate_head_mass hn ht ha hR parent terminal d q y)
  have HD := IntegralMixedFramedShiftDegreeCeiling.source_degree_bound P D H parent terminal
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) hA center q
  have HC := certified_coordinate_mass_affine hn ht ha hR (terminal q)
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HCap : P.cap = (parameters hn ht ha).cap := rfl
  have HWidth : P.width = (parameters hn ht ha).width := rfl
  rw [HCap, HWidth] at HD
  have HD' : RationalMonomialParameterShift.sourceDegree endpoint
      (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e) q ≤
      shiftAllowance hn ht ha (pair (RankedHistoryTask.root (parent q)) (pairFst (terminal q))) := by
    simpa only [shiftAllowance, pairFst_pair, pairSnd_pair] using HD
  have HC' : endpoint.scalars.mass q ≤ coordinateSlope hn ht ha (pairFst (terminal q))*R (pairFst (terminal q))+
      coordinateOffset hn ht ha (pairFst (terminal q)) := HC
  have HP := Nat.mul_le_mul HD' (Nat.add_le_add_right HC' 1)
  simpa only [Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_left 2 HP)
    (rawSlope hn ht ha (RankedHistoryTask.root (parent q))*R (RankedHistoryTask.root (parent q))+
      nativeHeadOffset hn ht ha (RankedHistoryTask.root (parent q)))

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
