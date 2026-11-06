/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCompanionScan
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
/-! # Companion grammar uses only original headers and creating births -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCompanionMetadata
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedPhysicalPointCompanionScan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem bank_key {R : List Bool → ℕ} (hR : BinaryFn R) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key = IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n := rfl

private theorem bank_cap {R : List Bool → ℕ} (hR : BinaryFn R) (root : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap root =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap root := rfl

private theorem active_cap (P Q : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool → List Bool) (stage : List Bool → ℕ)
    (z : List Bool) (hc : P.cap (pairFst (key z)) = Q.cap (pairFst (key z))) :
    IntegralMixedFramedCriticalGuardBits.Active P T key stage z ↔
      IntegralMixedFramedCriticalGuardBits.Active Q T key stage z := by
  simp only [IntegralMixedFramedCriticalGuardBits.Active, IntegralMixedFramedHistoryFamilyBits.prefixLength,
    IntegralMixedFullHistoryFamilyBits.prefixLength, hc]

theorem active_static {R : List Bool → ℕ} (hR : BinaryFn R) (z : List Bool) :
    IntegralMixedFramedCriticalGuardBits.Active
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key)
      IntegralFramedPhysicalCriticalGuardScan.stage z ↔
    IntegralMixedFramedCriticalGuardBits.Active
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n))
      IntegralFramedPhysicalCriticalGuardScan.stage z := by
  rw [CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR, bank_key hn ht ha hR]
  exact active_cap _ _ _ _ _ z (bank_cap hn ht ha hR _)

theorem grammar_packet_iff {R : List Bool → ℕ} (hR : BinaryFn R)
    (ctx w : List Bool) (a f k : ℕ) :
    Grammar hn ht ha hR false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k)) ↔
    IntegralMixedFramedCriticalGuardBits.Active
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n))
      IntegralFramedPhysicalCriticalGuardScan.stage
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (List.replicate a true)) ∧
    f + k ≤ IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  rw [Grammar, and_iff_right (descriptor_packet (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w a f k)]
  simp only [anchorQuery, anchor, first, number,
    descriptor, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [CoefficientMarkedRecordCriticalFullSemantics.full_length hn ht ha hR ctx,
    active_static hn ht ha hR]

theorem grammar_eq {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (ctx w w' : List Bool) (a f k : ℕ) :
    Grammar hn ht ha hR false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k)) ↔
    Grammar hn ht ha hS false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w') (descriptor a f k)) :=
  (grammar_packet_iff hn ht ha hR ctx w a f k).trans (grammar_packet_iff hn ht ha hS ctx w' a f k).symm

theorem dimension_eq {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (ctx w w' : List Bool) (a f k : ℕ) :
    dimension hn ht ha hR false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k)) =
    dimension hn ht ha hS false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w') (descriptor a f k)) := by
  simp only [dimension, pairFst_pair]
  rfl

theorem fullCount_le_cap (ctx : List Bool) :
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ≤
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx + 1 := by
  have hr := IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  omega

/-- All actual companion point queries lie in the original finite stage
box, including the anchor; no stage bound is supplied by the caller. -/
theorem stages_of_grammar {R : List Bool → ℕ} (hR : BinaryFn R)
    (ctx w : List Bool) (a f k : ℕ)
    (hg : Grammar hn ht ha hR false
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k))) :
    a ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx + 1 ∧
    ∀ j < k, f + j ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx + 1 := by
  have hanchor := hg.2.1.1
  simp only [anchorQuery, anchor, descriptor, IntegralFramedPhysicalCriticalGuardScan.stage,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair, pairSnd_pair, List.length_replicate] at hanchor
  rw [CoefficientMarkedRecordCriticalFullSemantics.full_length hn ht ha hR ctx] at hanchor
  have hfit := (grammar_packet_iff hn ht ha hR ctx w a f k).mp hg
  have hcap := fullCount_le_cap hn ht ha ctx
  exact ⟨hanchor.le.trans hcap, fun j hj => by omega⟩

end LeanCanny.Encoding.CoefficientMarkedRecordCompanionMetadata
