/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiMass

/-! # Affine radius mass of actual retained-coordinate epsilon windows

The terminal and selected-coordinate readers are fixed across radius. Epsilon
is retained, and powers zero, one, and two use the actual native query.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def coordinateSlope (root : List Bool) :=
  ((parameters hn ht ha).cap root + 1) * bankSlope hn ht ha root
noncomputable def coordinateOffset (root : List Bool) :=
  ((parameters hn ht ha).cap root + 1) * bankOffset hn ht ha root

theorem coordinateSlope_binary : BinaryFn (coordinateSlope hn ht ha) :=
  (BinaryFn.ofUnary ((access hn ht ha).cap.add (UnaryFn.const 1))).mul (bankSlope_binary hn ht ha)

theorem coordinateOffset_binary : BinaryFn (coordinateOffset hn ht ha) :=
  (BinaryFn.ofUnary ((access hn ht ha).cap.add (UnaryFn.const 1))).mul (bankOffset_binary hn ht ha)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedFramedHistoryFamilyBits.family

private theorem coordinate_mass_le (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedBankTermBits.coordinateMass P D H L F C key ≤
      (P.cap (pairFst key) + 1) * IntegralMixedFramedStepHeight.familyHeight P L F C key := by
  have HB : (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key ≤ P.cap (pairFst key) + 1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact min_le_right _ _
  exact Nat.mul_le_mul_right _ HB

theorem coordinate_mass_affine (R : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedBankTermBits.coordinateMass (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key ≤
        coordinateSlope hn ht ha (pairFst key) * R (pairFst key) + coordinateOffset hn ht ha (pairFst key) := by
  apply (coordinate_mass_le (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key).trans
  exact (Nat.mul_le_mul_left _ (familyHeight_le hn ht ha R key)).trans_eq (by
    unfold coordinateSlope coordinateOffset
    ring)

theorem window_coefficient_mass (R : List Bool → ℕ) (terminal : List Bool → List Bool)
    (selected : List Bool → ℕ) (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedWindowQuery.polynomial (parameters hn ht ha) (plan hn ht ha R)
      (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
      terminal selected negative q).coeff y) ≤
      2 ^ ((2 * coordinateSlope hn ht ha (pairFst (terminal q))) * R (pairFst (terminal q)) +
        (2 * coordinateOffset hn ht ha (pairFst (terminal q)) + 1)) := by
  have HM := IntegralMixedFramedWindowQuery.coefficient_mass (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
    terminal selected negative q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC := coordinate_mass_affine hn ht ha R (terminal q)
  nlinarith only [HC]

theorem powered_window_coefficient_mass (R : List Bool → ℕ) (terminal : List Bool → List Bool)
    (selected : List Bool → ℕ) (power : List Bool → Fin 3) (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedZeroTarskiBits.query (parameters hn ht ha) (plan hn ht ha R)
      (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
      terminal selected power negative q).coeff y) ≤
      2 ^ ((4 * coordinateSlope hn ht ha (pairFst (terminal q))) * R (pairFst (terminal q)) +
        (4 * coordinateOffset hn ht ha (pairFst (terminal q)) + 4)) := by
  have HM := IntegralMixedFramedZeroTarskiBits.query_coefficient_mass (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
    terminal selected power negative q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC := coordinate_mass_affine hn ht ha R (terminal q)
  unfold IntegralMixedFramedZeroTarskiBits.queryHeight
  nlinarith only [HC]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
