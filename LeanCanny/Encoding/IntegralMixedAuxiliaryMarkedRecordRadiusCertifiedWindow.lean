/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedHeight
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth

/-! # Actual certified epsilon windows ignore the mass certificate

Only the proof budget is replaced. The certified plan, parser, key, retained
numerators, denominators, and physical power schedule remain literal.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
  (parameters plan data factor certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem window_rebudget (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C L' F' C' : List Bool → ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (h' : IntegralMixedFramedStepHeight.FamilyInputs P D L' F' C')
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (negative : Bool) (q : List Bool) :
    IntegralMixedFramedWindowQuery.polynomial P D H L F C h terminal selected negative q =
      IntegralMixedFramedWindowQuery.polynomial P D H L' F' C' h' terminal selected negative q := by
  unfold IntegralMixedFramedWindowQuery.polynomial RationalMonomialWindowQuery.query
    RationalMonomialWindowQuery.body RationalMonomialWindowQuery.epsilon RationalMonomialWindowQuery.raw
    IntegralMixedFramedWindowQuery.family IntegralMixedFramedBankScalars.scalars
  rfl

private theorem query_rebudget (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C L' F' C' : List Bool → ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (h' : IntegralMixedFramedStepHeight.FamilyInputs P D L' F' C')
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (power : List Bool → Fin 3)
    (negative : Bool) (q : List Bool) :
    IntegralMixedFramedZeroTarskiBits.query P D H L F C h terminal selected power negative q =
      IntegralMixedFramedZeroTarskiBits.query P D H L' F' C' h' terminal selected power negative q := by
  have HE : IntegralMixedFramedWindowQuery.polynomial P D H L F C h terminal selected negative =
      IntegralMixedFramedWindowQuery.polynomial P D H L' F' C' h' terminal selected negative :=
    funext (window_rebudget P D H L F C L' F' C' h h' terminal selected negative)
  unfold IntegralMixedFramedZeroTarskiBits.query IntegralMixedFramedZeroTarskiBits.baseQuery
  rw [HE]

private theorem coordinate_planning (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L0 F0 C0 L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedBankTermBits.coordinateMass (IntegralMixedFramedNormalizationBits.planned P L0 F0 C0)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L0 F0 C0)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L0 F0 C0) L F C key =
        IntegralMixedFramedBankTermBits.coordinateMass P D H L F C key := by
  simp only [IntegralMixedFramedBankTermBits.coordinateMass,
    IntegralMixedFramedBankSnapshotBits.count_prefix]
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed
  IntegralMixedFramedHistoryFamilyBits.family

theorem certified_coordinate_mass_affine {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralMixedFramedBankTermBits.coordinateMass (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key ≤
        coordinateSlope hn ht ha (pairFst key) * R (pairFst key) + coordinateOffset hn ht ha (pairFst key) := by
  rw [coordinate_planning]
  exact coordinate_mass_affine hn ht ha R key

theorem certified_window_coefficient_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedWindowQuery.polynomial (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR) terminal selected negative q).coeff y) ≤
      2 ^ ((2 * coordinateSlope hn ht ha (pairFst (terminal q))) * R (pairFst (terminal q)) +
        (2 * coordinateOffset hn ht ha (pairFst (terminal q)) + 1)) := by
  rw [window_rebudget _ _ _ _ _ _ (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) _
    (certified_affine_inputs hn ht ha hR)]
  have HM := IntegralMixedFramedWindowQuery.coefficient_mass (certifiedParameters hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (certified_affine_inputs hn ht ha hR) terminal selected negative q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC := certified_coordinate_mass_affine hn ht ha hR (terminal q)
  nlinarith only [HC]

theorem certified_powered_window_coefficient_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (power : List Bool → Fin 3)
    (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedZeroTarskiBits.query (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR) terminal selected power negative q).coeff y) ≤
      2 ^ ((4 * coordinateSlope hn ht ha (pairFst (terminal q))) * R (pairFst (terminal q)) +
        (4 * coordinateOffset hn ht ha (pairFst (terminal q)) + 4)) := by
  rw [query_rebudget _ _ _ _ _ _ (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) _
    (certified_affine_inputs hn ht ha hR)]
  have HM := IntegralMixedFramedZeroTarskiBits.query_coefficient_mass (certifiedParameters hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (certified_affine_inputs hn ht ha hR) terminal selected power negative q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC := certified_coordinate_mass_affine hn ht ha hR (terminal q)
  unfold IntegralMixedFramedZeroTarskiBits.queryHeight
  nlinarith only [HC]

noncomputable def nativeHeadOffset (root : List Bool) :=
  rawOffset hn ht ha root + ((parameters hn ht ha).cap root + 1) * (parameters hn ht ha).width root +
    ((parameters hn ht ha).width root + 1)

theorem nativeHeadOffset_binary : BinaryFn (nativeHeadOffset hn ht ha) :=
  ((rawOffset_binary hn ht ha).add
    ((BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))).mul
      (BinaryFn.ofUnary (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width))).add
    (BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.add (UnaryFn.const 1)))

theorem certified_native_head_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedZeroTarskiBits.head
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      parent terminal d (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha hR) parent) q).coeff y) ≤
      2 ^ (rawSlope hn ht ha (RankedHistoryTask.root (parent q)) * R (RankedHistoryTask.root (parent q)) +
        nativeHeadOffset hn ht ha (RankedHistoryTask.root (parent q))) := by
  have HM := (FixedWidthBivariateZeroLiftBits.mass _ _ q y).trans
    (certified_head_coefficient_mass hn ht ha hR parent terminal d
      (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha hR) parent) q y)
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HP : 0 < 2 ^ (parameters hn ht ha).width (RankedHistoryTask.root (parent q)) := pow_pos (by decide) _
  simp only [headOffset, IntegralMixedVirtualTaskBits.saved, pairFst_pair, nativeHeadOffset,
    IntegralMixedSelectedCoordinateHead.fullParameter]
  change _ + (_ + ((2 ^ (parameters hn ht ha).width (RankedHistoryTask.root (parent q)) - 1) + 1).size) ≤ _
  rw [Nat.sub_add_cancel HP, Nat.size_pow]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
