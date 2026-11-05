/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight
public import LeanCanny.Algebra.IntegralMixedFramedFullRowMassControls

/-! # Actual full physical sampler rows have affine radius coefficient height -/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem physical_seed_affine (n S B W D L F A C : ℕ) :
    IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F (A * (C + 1)) +
        C * IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F A =
      IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F A +
        C * IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F (A * 2) := by
  unfold IntegralMixedPhysicalRowBudget.criticalExponent PhysicalCriticalMassBudget.exponent
    PhysicalCriticalMassBudget.sourceExponent IntegralMixedPhysicalRowBudget.sourceC
    IntegralMixedPhysicalRowBudget.normalExponent IntegralMixedPhysicalRowBudget.heightExponent
    IntegralMixedPhysicalRowBudget.bankG
  ring

private theorem exponent_seed_bound (n S B W D L F A C : ℕ) :
    IntegralMixedPhysicalRowBudget.exponent n S B W D L F (A * (C + 1)) ≤
      IntegralMixedPhysicalRowBudget.exponent n S B W D L F (A * 2) * C +
        IntegralMixedPhysicalRowBudget.exponent n S B W D L F A := by
  apply max_le
  · have H := physical_seed_affine n S B W D L F A C
    calc
      _ ≤ IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F A +
          C * IntegralMixedPhysicalRowBudget.criticalExponent n S B W D L F (A * 2) :=
        (Nat.le_add_right _ _).trans_eq H
      _ ≤ IntegralMixedPhysicalRowBudget.exponent n S B W D L F A +
          C * IntegralMixedPhysicalRowBudget.exponent n S B W D L F (A * 2) :=
        Nat.add_le_add (Nat.le_max_left _ _) (Nat.mul_le_mul_left C (Nat.le_max_left _ _))
      _ = _ := by ring
  · have H : PaddedIntegralParameterExtension.rowMassHeight S B (A * (C + 1)) +
          C * PaddedIntegralParameterExtension.rowMassHeight S B A =
        PaddedIntegralParameterExtension.rowMassHeight S B A +
          C * PaddedIntegralParameterExtension.rowMassHeight S B (A * 2) := by
      unfold PaddedIntegralParameterExtension.rowMassHeight
      ring
    calc
      _ ≤ PaddedIntegralParameterExtension.rowMassHeight S B A +
          C * PaddedIntegralParameterExtension.rowMassHeight S B (A * 2) :=
        (Nat.le_add_right _ _).trans_eq H
      _ ≤ IntegralMixedPhysicalRowBudget.exponent n S B W D L F A +
          C * IntegralMixedPhysicalRowBudget.exponent n S B W D L F (A * 2) :=
        Nat.add_le_add (Nat.le_max_right _ _) (Nat.mul_le_mul_left C (Nat.le_max_right _ _))
      _ = _ := by ring

private theorem familyMass_seed_bound (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    IntegralMixedPhysicalRowBudget.familyMass P L F C root ≤
      IntegralMixedPhysicalRowBudget.familyMass P L F (fun _ => 1) root * C root +
        IntegralMixedPhysicalRowBudget.familyMass P L F (fun _ => 0) root := by
  simpa only [IntegralMixedPhysicalRowBudget.familyMass, height, Nat.one_add, Nat.zero_add, Nat.mul_one] using
    exponent_seed_bound (P.ambient root) (P.cap root + 1) (P.width root) (P.sourceWidth root)
      (P.degree root) (L root) (F root)
      (growth (P.ambient root) (P.cap root + 1) (P.width root) (P.sourceWidth root)
        (P.degree root) (L root) (F root) ^ (P.cap root + 2)) (C root)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def rowSeedZero :=
  IntegralMixedPhysicalRowBudget.familyMass (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (fun _ => 0)

noncomputable def rowSeedOne :=
  IntegralMixedPhysicalRowBudget.familyMass (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (fun _ => 1)

noncomputable def rowSlope (root : List Bool) := rowSeedOne hn ht ha root * seedSlope hn ht ha root
noncomputable def rowOffset (root : List Bool) := rowSeedOne hn ht ha root * seedOffset hn ht ha root + rowSeedZero hn ht ha root

theorem rowSlope_binary : BinaryFn (rowSlope hn ht ha) :=
  (IntegralMixedPhysicalRowBudget.familyMass_binary (parameters hn ht ha) (access hn ht ha)
    (BinaryFn.const 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha) (BinaryFn.const 1)).mul
      (seedSlope_binary hn ht ha)

theorem rowOffset_binary : BinaryFn (rowOffset hn ht ha) :=
  ((IntegralMixedPhysicalRowBudget.familyMass_binary (parameters hn ht ha) (access hn ht ha)
    (BinaryFn.const 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha) (BinaryFn.const 1)).mul
      (seedOffset_binary hn ht ha)).add
    (IntegralMixedPhysicalRowBudget.familyMass_binary (parameters hn ht ha) (access hn ht ha)
      (BinaryFn.const 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha) (BinaryFn.const 0))

theorem row_ceiling_le (R : List Bool → ℕ) (root : List Bool) :
    IntegralMixedPhysicalRowBudget.familyMass (parameters hn ht ha) (fun _ => 3) (factor hn ht ha)
      (seed hn ht ha R) root ≤ rowSlope hn ht ha root * R root + rowOffset hn ht ha root := by
  apply (familyMass_seed_bound (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) root).trans_eq
  unfold rowSlope rowOffset rowSeedZero rowSeedOne seed
  ring

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data

theorem full_row_mass (R : List Bool → ℕ) (key : List Bool) (i : (actualFamily hn ht ha R).physical key) :
    MvMass.mass (((actualFamily hn ht ha R).state key).sampler.rows i) ≤
      2 ^ (rowSlope hn ht ha (pairFst key) * R (pairFst key) + rowOffset hn ht ha (pairFst key)) :=
  (IntegralMixedPhysicalRowBudget.family_mass (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R) key i).trans
      (Nat.pow_le_pow_right (by decide) (row_ceiling_le hn ht ha R (pairFst key)))

theorem full_row_coefficient_bound (R : List Bool → ℕ) (key : List Bool)
    (i : (actualFamily hn ht ha R).physical key) (e : (actualFamily hn ht ha R).physical key →₀ ℕ) :
    ((((actualFamily hn ht ha R).state key).sampler.rows i).coeff e).natAbs ≤
      2 ^ (rowSlope hn ht ha (pairFst key) * R (pairFst key) + rowOffset hn ht ha (pairFst key)) :=
  (MvMass.coeff_le _ _).trans (full_row_mass hn ht ha R key i)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
