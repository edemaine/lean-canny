/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceOrigin
public import LeanCanny.Encoding.IntegralFramedTraceCutSelectedParent
/-! # Native marked traces provide the uniquely selected geometric parent

The embedding at each actual cut is fixed by the suffix of one terminal
sample. This supplies the selected-factor input of frame continuation.
It does not assert that arbitrary decoded records form a geometric frame:
fresh frozen coordinates and the literal frame/rule agreement are still
required when assembling the recursive geometric trace.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "P" => certifiedParameters hn ht ha hR
local notation "D" => certifiedPlan hn ht ha hR
local notation "H" => certifiedData hn ht ha hR
local notation "L" => (fun _ : List Bool=>3)
local notation "F" => factor hn ht ha
local notation "C" => IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
local notation "HS" => certifiedInputs hn ht ha hR

/-- One valid terminal vertex determines the selected old embedding at
EVERY actual cut, along with its full factor root and exact stored degree. -/
theorem validated_selected_iff (q : List Bool) : q∈language hn ht ha hR ↔
    ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (pairFst q) (pairSnd q),
      ∀ j<fullCount n (pairFst q),
        IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j).command →
        ∃! φ,IntegralFramedTraceCutSelectedParent.At P D H L F C HS
          (pairFst q) (List.replicate j true) (pairSnd q) hv φ := by
  rw [validated_records_iff hn ht ha hR q]
  constructor
  · rintro ⟨hv,hAll⟩
    exact ⟨hv,fun j hj hc=>(IntegralFramedTraceCutSelectedParent.compatible_iff_existsUnique
      P D H L F C HS (pairFst q) (List.replicate j true) (pairSnd q) hv).mp (hAll j hj hc)⟩
  · rintro ⟨hv,hAll⟩
    exact ⟨hv,fun j hj hc=>(IntegralFramedTraceCutSelectedParent.compatible_iff_existsUnique
      P D H L F C HS (pairFst q) (List.replicate j true) (pairSnd q) hv).mpr (hAll j hj hc)⟩
end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
