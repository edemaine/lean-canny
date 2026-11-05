/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordNative
public import LeanCanny.Algebra.IntegralMixedStaticRecordLookup
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
/-! # Actual provider creating commands follow their literal checked bytes -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
noncomputable def polynomial (root : List Bool) (i : ℕ) :=
  FormulaSignSlotRadialProviderRecordPlan.source.polynomial (pair root (BinaryNatCode.encode i))
theorem polynomial_nonzero (root : List Bool) (i : ℕ) : polynomial root i≠0 :=
  FormulaSignSlotRadialProviderRecordPlan.source_nonzero _
theorem polynomial_degree (root : List Bool) (i : ℕ) : (polynomial root i).natDegree≤2^(P).width root :=
  (FormulaSignSlotRadialProviderRecordPlan.source.degree_bound _).trans
    (FormulaSignSlotRadialProviderRecordPlan.source_degree_cap root i)
theorem actual_spatial_cap (root : List Bool) : IntegralMixedExceptionalBounds.auxiliaryCap
    ((P).ambient root+1) (FormulaSignSlotRadialProviderRecordPlan.spatial root).degree≤2^(P).width root := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
  exact FormulaSignSlotRadialProviderRecordPlan.spatial_cap root
noncomputable def records (root : List Bool) := IntegralMixedStaticRecordPrefix.records
  (FormulaSignSlotRadialProviderRecordPlan.spatial root) (FormulaSignSlotRadialProviderRecordPlan.positive root)
  (actual_spatial_cap root) (FormulaSignSlotRadialProviderRecordPlan.count root)
  (IntegralMixedCausalRecordPlanBits.count root) (polynomial root) (polynomial_nonzero root)
  (polynomial_degree root) (IntegralMixedCausalRecordPlanBits.code root)
theorem records_length (root : List Bool) : (records root).length=
    IntegralMixedCausalRecordPlanBits.count root+FormulaSignSlotRadialProviderRecordPlan.count root :=
  IntegralMixedStaticRecordPrefix.records_length _ _ _ _ _ _ _ _ _
theorem room (root : List Bool) : (records root).length≤(P).cap root+2 := by
  rw [records_length root]
  have H := FormulaSignSlotRadialProviderRecordPlan.room root
  change _≤FormulaSignSlotRadialProviderRecordPlan.parameters.cap root+2
  omega
theorem rules (root : List Bool) : (D).rules root=
    IntegralMixedCausalPlanBits.commands (initial P D root) (records root) (room root) := rfl

theorem critical (root :List Bool) (i :ℕ) (hi :i<IntegralMixedCausalRecordPlanBits.count root)
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient root) (FormulaSignSlotRadialProviderRecordPlan.count root+i) labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code root i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient root) labels g j) :
    (IntegralMixedFramedRootPullback.instructionAt P D root (FormulaSignSlotRadialProviderRecordPlan.count root+i)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient root) (FormulaSignSlotRadialProviderRecordPlan.count root+i) labels g j hg).rule :=by
  have HR :IntegralMixedCausalRecordPlanBits.count root+(FormulaSignSlotRadialProviderRecordPlan.count root)≤(P).cap root+1+1 :=by
    have HH:=room root
    rw [records_length root] at HH
    exact HH
  unfold IntegralMixedFramedRootPullback.instructionAt
  rw [rules root]
  unfold records
  exact IntegralMixedStaticRecordLookup.critical_receipt
    (FormulaSignSlotRadialProviderRecordPlan.spatial root)
    (FormulaSignSlotRadialProviderRecordPlan.positive root)
    (actual_spatial_cap root)
    (FormulaSignSlotRadialProviderRecordPlan.count root) (IntegralMixedCausalRecordPlanBits.count root)
    (polynomial root)
    (polynomial_nonzero root)
    (polynomial_degree root)
    (IntegralMixedCausalRecordPlanBits.code root) (initial P D root) HR (defaultInstruction P D root)
    i hi labels g j hg hw

theorem critical_at (root :List Bool) (i birth :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count root) (hb :birth=FormulaSignSlotRadialProviderRecordPlan.count root+i)
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient root) birth labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code root i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient root) labels g j) :
    (IntegralMixedFramedRootPullback.instructionAt P D root birth).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient root) birth labels g j hg).rule :=by
  subst birth
  exact critical root i hi labels g j hg hw

theorem source_at (root :List Bool) (i birth :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count root) (hb :birth=FormulaSignSlotRadialProviderRecordPlan.count root+i) :
    (IntegralMixedFramedRootPullback.instructionAt P D root birth).source=
      FormulaSignSlotRadialProviderRecordPlan.spatial root :=by
  subst birth
  have HR :IntegralMixedCausalRecordPlanBits.count root+(FormulaSignSlotRadialProviderRecordPlan.count root)≤(P).cap root+1+1:=by
    have HH:=room root
    rw [records_length root] at HH
    exact HH
  unfold IntegralMixedFramedRootPullback.instructionAt
  rw [rules root]
  unfold records
  exact IntegralMixedStaticRecordLookup.source_receipt
    (FormulaSignSlotRadialProviderRecordPlan.spatial root)
    (FormulaSignSlotRadialProviderRecordPlan.positive root)
    (actual_spatial_cap root)
    (FormulaSignSlotRadialProviderRecordPlan.count root) (IntegralMixedCausalRecordPlanBits.count root)
    (polynomial root)
    (polynomial_nonzero root)
    (polynomial_degree root)
    (IntegralMixedCausalRecordPlanBits.code root) (initial P D root) HR (defaultInstruction P D root) i hi
end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
