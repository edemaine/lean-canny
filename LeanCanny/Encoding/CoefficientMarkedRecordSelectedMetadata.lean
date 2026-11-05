/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
/-! # Actual selected cut headers are original-only at every key -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordSelectedMetadata
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedFramedHistoryFamilyBits IntegralMixedCommandHeaderBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem selected_cap (P Q : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool)
    (h : P.cap (pairFst key) = Q.cap (pairFst key)) :
    IntegralMixedHeaderTablesBits.selected P T key = IntegralMixedHeaderTablesBits.selected Q T key := by
  simp only [IntegralMixedHeaderTablesBits.selected, IntegralMixedHeaderTablesBits.producer,
    IntegralMixedHeaderTablesBits.fallback, IntegralMixedHeaderTablesBits.fallbackIndex,
    IntegralMixedFullHistoryFamilyBits.prefixLength, h]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem bank_cap {R : List Bool → ℕ} (hR : BinaryFn R) (root : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap root =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap root := rfl

/-- This includes degree, finite choice, coordinate, offset, objective and tag;
actual radius readers and their resource budgets need not be identified. -/
theorem selected_header {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralMixedCommandHeaderBits.selection
      (IntegralMixedFramedHistoryFamilyBits.selection (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).data key) =
      IntegralMixedHeaderTablesBits.selected (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) key := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  have hs := IntegralMixedFramedHeaderBits.selected_eq B.parameters B.plan B.data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) key
  have hc := selected_cap B.parameters (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) T key
    (bank_cap hn ht ha hR (pairFst key))
  have htable := CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR
  exact hs.symm.trans (hc.trans (congrArg
    (fun table => IntegralMixedHeaderTablesBits.selected (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) table key) htable))

theorem selected_radius_eq {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S) (key : List Bool) :
    IntegralMixedCommandHeaderBits.selection
      (IntegralMixedFramedHistoryFamilyBits.selection (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).data key) =
    IntegralMixedCommandHeaderBits.selection
      (IntegralMixedFramedHistoryFamilyBits.selection (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hS false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hS false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hS false).data key) :=
  (selected_header hn ht ha hR key).trans (selected_header hn ht ha hS key).symm

end LeanCanny.Encoding.CoefficientMarkedRecordSelectedMetadata
