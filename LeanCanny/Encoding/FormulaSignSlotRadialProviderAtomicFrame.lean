/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicCaptureRecords
public import LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode
/-! # Every latest provider capture has its literal actual creating frame -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial

noncomputable def ownBirth (q : List Bool) := endBirth (dimension q) (initial q) q-1
theorem latest_block_end (q : List Bool) (hv : Valid q) :
    first (dimension q) (initial q) q+free (dimension q) q=endBirth (dimension q) (initial q) q :=
  IntegralMixedRoadmapAtomic.block_end _ _ q (depth_le q (valid_grammar q hv))
theorem capture_good (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    IntegralMixedChronologicalFrameCode.PointGood (dimension q)
      (first (dimension q) (initial q) q+j) (frozen q) (depth q) (dimension q-j) :=
  IntegralMixedRoadmapAtomic.capture_point_good (q:=q) (checked q (valid_grammar q hv)) j hj
theorem own_point_good (q : List Bool) (hv : Valid q) :
    IntegralMixedChronologicalFrameCode.PointGood (dimension q) (ownBirth q) (frozen q) (depth q) (depth q) := by
  have HD := depth_le q (valid_grammar q hv)
  have HF : 0<free (dimension q) q := by change 0<dimension q+1-depth q; omega
  have HG := capture_good q hv (free (dimension q) q-1) (by omega)
  have HB : first (dimension q) (initial q) q+(free (dimension q) q-1)=ownBirth q := by
    have HE := latest_block_end q hv
    unfold ownBirth
    omega
  have HJ : dimension q-(free (dimension q) q-1)=depth q := by
    change dimension q-(dimension q+1-depth q-1)=depth q
    omega
  simpa only [HB,HJ] using HG
theorem own_frame_good (q : List Bool) (hv : Valid q) :
    IntegralMixedChronologicalFrameCode.Good (dimension q) (ownBirth q) (frozen q) := (own_point_good q hv).1

theorem own_raw_fit (q : List Bool) (hv : Valid q) :
    IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q)-1<
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) := by
  have H := IntegralMixedRoadmapChain.rawStart_bound (dimension q) (payload q) (depth q)
    (by have HD := depth_le q (valid_grammar q hv); omega)
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega
theorem root_record_count (q : List Bool) (hv : Valid q) : IntegralMixedCausalRecordPlanBits.count (root q)=
    IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) := by
  unfold IntegralMixedCausalRecordPlanBits.count
  rw [root_records]
  exact raw_count q (valid_grammar q hv)
theorem root_record_code (q : List Bool) (i : ℕ) : IntegralMixedCausalRecordPlanBits.code (root q) i=
    WordList.get (IntegralMixedRoadmapChain.raw (payload q)) i := by
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [root_records]
theorem own_height_record (q : List Bool) (hv : Valid q) :
    IntegralMixedCausalRecordPlanBits.code (root q)
      (IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q)-1)=
      IntegralMixedChronologicalFrameCode.code (dimension q) (frozen q) (depth q) (depth q) := by
  rw [root_record_code]
  exact IntegralMixedRoadmapOwnHeightCode.checked_own_height_record (checked q (valid_grammar q hv)) (depth q) le_rfl
theorem own_birth_eq (q : List Bool) : ownBirth q=FormulaSignSlotRadialProviderRecordPlan.count (root q)+
    (IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q)-1) := by
  have H : 0<IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q) := by
    unfold IntegralMixedRoadmapChain.rawStart
    omega
  unfold ownBirth endBirth IntegralMixedRoadmapAtomic.endBirth
  change initial q+IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q)-1=
    initial q+(IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q)-1)
  omega
theorem own_creating_command (q : List Bool) (hv : Valid q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (root q) (ownBirth q)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData (dimension q) (ownBirth q)
        (frozen q) (depth q) (depth q) (own_point_good q hv)).rule :=
  FormulaSignSlotRadialProviderRecordReceipt.critical_at (root q) _ _
    (by rw [root_record_count q hv]; exact own_raw_fit q hv) (own_birth_eq q) _ _ _ (own_point_good q hv)
    (own_height_record q hv)
theorem own_creating_source (q : List Bool) (hv : Valid q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (root q) (ownBirth q)).source=
      FormulaSignSlotRadialProviderRecordPlan.spatial (root q) :=
  FormulaSignSlotRadialProviderRecordReceipt.source_at (root q) _ _
    (by rw [root_record_count q hv]; exact own_raw_fit q hv) (own_birth_eq q)

theorem first_ge_initial (q : List Bool) (hv : Valid q) : initial q<first (dimension q) (initial q) q := by
  have HE := latest_block_end q hv
  have H : dimension q+2≤IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q) := by
    unfold IntegralMixedRoadmapChain.rawStart
    omega
  change first (dimension q) (initial q) q+free (dimension q) q=
    initial q+IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q) at HE
  change first (dimension q) (initial q) q+(dimension q+1-depth q)=_ at HE
  omega
theorem capture_raw_fit (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    first (dimension q) (initial q) q-initial q+j<IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) := by
  have HF := first_ge_initial q hv
  have HE := latest_block_end q hv
  have H := IntegralMixedRoadmapChain.rawStart_bound (dimension q) (payload q) (depth q)
    (by have HD := depth_le q (valid_grammar q hv); omega)
  change _=initial q+IntegralMixedRoadmapChain.rawStart (dimension q) (payload q) (depth q) at HE
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega
theorem capture_creating_command (q : List Bool) (hv : Valid q) (j : ℕ) (hj : j<free (dimension q) q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (root q) (first (dimension q) (initial q) q+j)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData (dimension q)
        (first (dimension q) (initial q) q+j) (frozen q) (depth q) (dimension q-j) (capture_good q hv j hj)).rule := by
  have HW : IntegralMixedCausalRecordPlanBits.code (root q) (first (dimension q) (initial q) q-initial q+j)=
      IntegralMixedChronologicalFrameCode.code (dimension q) (frozen q) (depth q) (dimension q-j) := by
    rw [root_record_code]
    exact IntegralMixedRoadmapAtomic.latest_capture_record (q:=q) (checked q (valid_grammar q hv)) j hj
  exact FormulaSignSlotRadialProviderRecordReceipt.critical_at (root q) _ _
    (by rw [root_record_count q hv]; exact capture_raw_fit q hv j hj)
    (by change _=initial q+_; have H := first_ge_initial q hv; omega) _ _ _ (capture_good q hv j hj) HW

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
