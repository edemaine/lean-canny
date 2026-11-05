/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicFrame
public import LeanCanny.Encoding.IntegralMixedMarkedRecordReceipt
public import LeanCanny.Geometry.IntegralMixedAtomicOccurrence
/-! # Actual source-aware atomic frozen-slice occurrences -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank

theorem last_capture_birth (q : List Bool) (hv : Valid q) :
    first (dimension q) (initial q) q+(free (dimension q) q-1)=ownBirth q := by
  have HD := depth_le q (valid_grammar q hv)
  have HF : 0<free (dimension q) q := by change 0<dimension q+1-depth q; omega
  have HE := latest_block_end q hv
  unfold ownBirth
  omega
theorem own_active (q : List Bool) (hv : Valid q) : Active (context q) (ownBirth q) := by
  have HD := depth_le q (valid_grammar q hv)
  have HF : 0<free (dimension q) q := by change 0<dimension q+1-depth q; omega
  obtain ⟨HB,_,_⟩ := companions q hv (free (dimension q) q-1) (by omega)
  simpa only [last_capture_birth q hv] using HB
theorem own_height_point (q : List Bool) (hv : Valid q) :
    geometricPoint (context q) (word q) (full_valid q hv) (ownBirth q)=point q hv := by
  have HD := depth_le q (valid_grammar q hv)
  have HF : 0<free (dimension q) q := by change 0<dimension q+1-depth q; omega
  obtain ⟨_,HE,_⟩ := companions q hv (free (dimension q) q-1) (by omega)
  simpa only [last_capture_birth q hv] using HE
theorem native_point_good (q : List Bool) (hv : Valid q) :
    IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key (context q))))
      (ownBirth q) (frozen q) (depth q) (depth q) := by
  rw [native_dimension]
  exact own_point_good q hv
theorem native_creating_command (q : List Bool) (hv : Valid q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q))) (ownBirth q)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key (context q))))
        (ownBirth q) (frozen q) (depth q) (depth q) (native_point_good q hv)).rule :=
  IntegralMixedStaticRecordLookup.critical_root_transport P D (root q) _ (context_root q).symm
    (ownBirth q) (frozen q) (depth q) (depth q) (own_point_good q hv) (native_point_good q hv)
    (own_creating_command q hv)

noncomputable def source (q : List Bool) :=
  (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q))) (ownBirth q)).source
theorem source_provider (q : List Bool) (hv : Valid q) : HEq (source q)
    (FormulaSignSlotRadialProviderIntegerPlan.spatial (provider q)) := by
  unfold source
  rw [context_root]
  exact (heq_of_eq (own_creating_source q hv)).trans (spatial_provider q)
noncomputable def levels (q : List Bool) (hv : Valid q) (i : ℕ) :=
  field q hv (Nat.fromBitsLE (WordList.get (frozen q) i))
section
attribute [local irreducible] source levels point field FormulaSignSlotRadialProviderRecordPlan.bank
theorem occurrence (q : List Bool) (hv : Valid q) :
    IntegralMixedAtomicOccurrence.Occurrence (source q) (depth q) (levels q hv) (point q hv) := by
  unfold source
  have H := IntegralFramedPhysicalCompanionPoint.frame_point_env B T bank_represents
    (context q) (word q) (full_valid q hv) (ownBirth q) (own_active q hv)
    (frozen q) (depth q) (depth q) (native_point_good q hv) (native_creating_command q hv)
  dsimp only at H
  have HP : IntegralFramedPhysicalCompanionPoint.geometricPoint B T
      (context q) (word q) (full_valid q hv) (ownBirth q)=point q hv := own_height_point q hv
  rw [HP] at H
  refine ⟨?_,H.1,?_,?_⟩
  · rw [native_dimension]
    exact depth_le q (valid_grammar q hv)
  · intro i hi
    have HI : i.val<WordListRecords.count (frozen q) := by rw [frozen_count]; exact hi
    simpa only [levels,field,bankField] using H.2.1 i.val HI
  · intro i hi hig
    exact H.2.2 i (by rw [frozen_count]; exact hi) hig
end

theorem native_capture_good (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key (context q))))
      (first (dimension q) (initial q) q+j) (frozen q) (depth q) (dimension q-j) := by
  rw [native_dimension]
  exact capture_good q hv j hj
theorem native_capture_command (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q)))
      (first (dimension q) (initial q) q+j)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key (context q))))
        (first (dimension q) (initial q) q+j) (frozen q) (depth q) (dimension q-j)
        (native_capture_good q hv j hj)).rule :=
  IntegralMixedStaticRecordLookup.critical_root_transport P D (root q) _ (context_root q).symm _ _ _ _
    (capture_good q hv j hj) (native_capture_good q hv j hj) (capture_creating_command q hv j hj)
theorem capture_selected (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    selected (context q) (first (dimension q) (initial q) q+j)=dimension q-j :=
  IntegralFramedPhysicalCompanionPoint.selected_of_frame B T bank_represents _ _ _ _ _
    (native_capture_good q hv j hj) (native_capture_command q hv j hj)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
