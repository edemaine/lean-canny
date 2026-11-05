/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSample
public import LeanCanny.Encoding.FormulaSignSlotRadialMarkedCenterField
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
/-! # The actual joint word supplies the same retained center to every family -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "HN" => FormulaSignSlotRadialJointLayout.dimension_unary
local notation "HT" => FormulaSignSlotRadialJointCore.equation_FP
local notation "HA" => FormulaSignSlotRadialJointCore.scope
local notation "HR" => IntegralMixedOriginalRegularSource.radius_binary radius_binary
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank HN HT HA HR false
local notation "T" => IntegralMixedPhysicalMarkedPlan.tables HN HT HA HR false
local notation "H" => IntegralMixedPhysicalMarkedPlan.represents HN HT HA HR false
attribute [local irreducible] radius FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedPhysicalFieldEquality.point IntegralMixedRoadmapMarkedPrelude.value

private theorem original_lt_count (c : List Bool) : FormulaSignSlotRadialJointLayout.dimension (headerContext c) <
    IntegralMixedPhysicalFieldEquality.count HN HT HA HR c := by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  change FormulaSignSlotRadialJointLayout.dimension (headerContext c) <
    FormulaSignSlotRadialJointLayout.dimension (headerContext c) + 8 + _
  omega

theorem center_reference (p : List Bool) (i : Fin (FormulaSignSlotRadialJointLayout.centerCount (header p))) :
    Nat.fromBitsLE (WordList.get (centerRefs (context p)) i.val) = FormulaSignSlotRadialJointLayout.column 0 i.val := by
  unfold centerRefs
  rw [header_context]
  exact FormulaSignSlotRadialJointLayout.centerRefs_lookup _ i

theorem center_reference_fit (p : List Bool) (i : Fin (FormulaSignSlotRadialJointLayout.centerCount (header p))) :
    Nat.fromBitsLE (WordList.get (centerRefs (context p)) i.val) <
      IntegralMixedPhysicalFieldEquality.count HN HT HA HR (context p) := by
  rw [center_reference]
  have HI := FormulaSignSlotRadialJointLayout.centerVariable_lt (header p) i
  have HC := original_lt_count (context p)
  rw [header_context] at HC
  unfold FormulaSignSlotRadialJointLayout.centerVariable FormulaSignSlotRadialJointLayout.column at HI
  unfold FormulaSignSlotRadialJointLayout.column
  omega

noncomputable def retainedCenter (p : List Bool) (hv : Valid p)
    (i : Fin (FormulaSignSlotRadialJointLayout.centerCount (header p))) : ℝ :=
  FormulaSignSlotRadialBankCenterTest.center B T H centerRefs (context p) (word p) (full_valid p hv) i.val

theorem retained_center (p : List Bool) (hv : Valid p)
    (i : Fin (FormulaSignSlotRadialJointLayout.centerCount (header p))) :
    retainedCenter p hv i = FormulaSignSlotRadialJointGeometry.center (header p) (values p hv) i := by
  have HE := FormulaSignSlotRadialMarkedCenterField.center_field HN HT HA HR centerRefs
    (context p) (word p) (full_valid p hv) i.val (center_reference_fit p i)
  rw [center_reference] at HE
  have HP := IntegralMixedPhysicalMarkedContext.point_eq HN HT HA HR
    (context p) (IntegralMixedRoadmapAtomic.context (node p)) (word p) (by
      simp only [context, IntegralMixedRoadmapAtomic.context, pairFst_pair])
    (full_valid p hv) (IntegralMixedRoadmapAtomic.full_valid HN HT HA radius_binary (node p) hv)
    (FormulaSignSlotRadialJointLayout.column 0 i.val)
  unfold retainedCenter FormulaSignSlotRadialJointGeometry.center values IntegralMixedRoadmapMarkedPrelude.value
  exact HE.trans HP

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
