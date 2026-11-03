/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
public import LeanCanny.Encoding.IntegralFramedTraceCutOriginalCount
/-! # Exact full-script-plus-default provenance of the marked cut sampler -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedFramedHistoryFamilyBits.family
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "P" => certifiedParameters hn ht ha hR
local notation "D" => certifiedPlan hn ht ha hR
local notation "H" => certifiedData hn ht ha hR

theorem length_eq (root : List Bool) :
    IntegralFramedTraceCutMetadata.length P D root=fullCount n root := by
  change ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R).rules root).length=fullCount n root
  have HE:=IntegralMixedSourceIntegerRecordAppend.script_length (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) root
  exact HE.trans (by unfold fullCount; omega)

noncomputable def terminalKey (root : List Bool) := IntegralFramedTraceCutMetadata.terminal P D root

theorem terminalKey_eq (root : List Bool) : terminalKey hn ht ha hR root=
    IntegralMixedFramedHistoryFamilyBits.keyAt root (fullCount n root+1) [] := by
  unfold terminalKey IntegralFramedTraceCutMetadata.terminal
  rw [length_eq]

theorem terminalKey_FP : terminalKey hn ht ha hR∈FP :=
  IntegralFramedTraceCutMetadata.terminal_FP P D H (certifiedControls hn ht ha hR).normalization

theorem count_eq (root : List Bool) : (input hn ht ha hR).count root=fullCount n root+1 := by
  exact (IntegralFramedTraceCutSource.input_count P D H (fun _=>3) (factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (certifiedInputs hn ht ha hR) root).trans
      (congrArg (fun k=>k+1) (length_eq hn ht ha hR root))

/-- The extra last birth is a default command, not an additional stored cut. -/
theorem terminal_not_cut (root : List Bool) :
    ¬IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D root (fullCount n root)).command := by
  intro hc
  have HL:=IntegralFramedTraceCutMetadata.cut_lt_length P D root (fullCount n root) hc
  rw [length_eq] at HL
  omega

/-- This range names the literal chronological original instructions. -/
theorem validated_records_iff (q : List Bool) : q∈language hn ht ha hR ↔
    ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (pairFst q) (pairSnd q),
      ∀ j<fullCount n (pairFst q),
        IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j).command →
        IntegralFramedTraceCutExact.Compatible P D H (fun _=>3) (factor hn ht ha)
          (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (certifiedInputs hn ht ha hR)
          (pairFst q) (List.replicate j true) (pairSnd q) hv := by
  simpa only [length_eq hn ht ha hR] using validated_iff hn ht ha hR q

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
