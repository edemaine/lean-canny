/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSample
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalQuery
/-! # Actual source-aware parent and child prefixes of one reserved critical root

The provider bytes stay literal when the normalized critical record is
appended. Both own samplers use this one root, cap, width, and schedule.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalPrefixes
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalCriticalQuery (root)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A" => FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables

theorem provider_prepare (ctx code : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext
      (IntegralMixedPhysicalCriticalQuery.prepare (pair ctx code))=
      FormulaSignSlotRadialProviderRecordPlan.providerContext ctx :=
  IntegralMixedPhysicalCriticalQuery.prepare_candidate ctx code

private theorem spatial_heq {ι : Type} {m : ι→ℕ} (Q : ∀i,IntegralMixedHistory.SpatialSource (m i))
    (a b : ι) (h : a=b) : HEq (Q a) (Q b) := by
  cases h
  rfl

theorem spatial_prepare (ctx code : List Bool) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial
      (IntegralMixedPhysicalCriticalQuery.prepare (pair ctx code)))
      (FormulaSignSlotRadialProviderRecordPlan.spatial ctx) := by
  unfold FormulaSignSlotRadialProviderRecordPlan.spatial
  exact spatial_heq FormulaSignSlotRadialProviderIntegerPlan.spatial _ _ (provider_prepare ctx code)

noncomputable def birth (child : Bool) (q : List Bool) :=
  FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)-(if child then 0 else 1)
theorem birth_unary (child : Bool) : UnaryFn (birth child) :=
  (FormulaSignSlotRadialProviderRecordPlan.fullCount_unary.comp pairFst_mem_FP).sub
    (UnaryFn.const (if child then 0 else 1))
theorem birth_pos (child : Bool) (q : List Bool) : 0<birth child q := by
  change 0<FormulaSignSlotRadialProviderIntegerPlan.number
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root q))+8+
      IntegralMixedCausalRecordPlanBits.count (root q)-(if child then 0 else 1)
  cases child <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> omega
theorem birth_le (child : Bool) (q : List Bool) : birth child q≤(B).parameters.cap (root q)+1 := by
  change FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)-(if child then 0 else 1)≤
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)+2+1
  omega
theorem below_cap (child : Bool) (q : List Bool) : birth child q<(B).parameters.cap (root q) := by
  change FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)-(if child then 0 else 1)<
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)+2
  omega

noncomputable def key (child : Bool) (q : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (root q) (birth child q) q
theorem key_FP (child : Bool) : key child∈FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (BinaryFn.ofUnary (birth_unary child)).bits_mem_FP id_mem_FP)
theorem key_birth (child : Bool) (q : List Bool) :
    (family (B).parameters (B).plan (B).data).birth (key child q)=birth child q :=
  (IntegralMixedFramedHistoryFamilyBits.family_birth _ _ _ _).trans
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ (birth_le child q))
theorem positive (child : Bool) (q : List Bool) :
    0<(family (B).parameters (B).plan (B).data).birth (key child q) := by
  rw [key_birth]
  exact birth_pos child q

noncomputable abbrev input (child : Bool) := IntegralFramedPhysicalSquare.input
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds (key child) (positive child)
theorem row_evaluator (child : Bool) : SpaceFunction (SquareSampleInput.rowCoefficient (input child)) :=
  IntegralFramedPhysicalSquare.native_row_evaluator (B).parameters (A).parameters (B).plan (B).data
    T FormulaSignSlotRadialProviderRecordPlan.tables_native FormulaSignSlotRadialProviderAtomic.bank_represents
    (B).nodes (B).factor (B).seed (B).bounds (key child) (key_FP child) (positive child)
    (A).liftedData (A).controls (A).bounds
theorem access (child : Bool) : (input child).Access :=
  IntegralFramedPhysicalSquare.native_access (B).parameters (A).parameters (B).plan (B).data
    T FormulaSignSlotRadialProviderRecordPlan.tables_native FormulaSignSlotRadialProviderAtomic.bank_represents
    (B).nodes (B).factor (B).seed (B).bounds (A).nodes (A).factor (A).seed
    (key child) (key_FP child) (positive child) (A).liftedData (A).controls (A).bounds

theorem consecutive (q : List Bool) : birth true q=birth false q+1 := by
  have H:=birth_pos false q
  simp only [birth,Bool.false_eq_true,ite_false,ite_true,Nat.sub_zero] at H ⊢
  omega
theorem same_root (q : List Bool) : pairFst (key false q)=pairFst (key true q) := by
  simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalPrefixes
