/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTest
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeFields
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutInstalled
/-! # Actual NoBad query metadata before allocating either own word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeMetadata
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def dimension (n : List Bool → ℕ) (q : List Bool) :=
  n (pairFst (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q))) + 3
def initial (n : List Bool → ℕ) (q : List Bool) := dimension n q + 5
def request (candidate raw labels left right hint word : List Bool) :=
  pair (IntegralMixedRoadmapBadProbePacket.packet candidate raw word labels left right) hint
def baseRoot (candidate raw : List Bool) := pair candidate (pair raw [])

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem ambient_base (root : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.ambient root =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).ambient root := rfl

private theorem width_base (root : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.width root =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width root := by
  simp only [IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,
    IntegralMixedFramedNormalizationBits.planned]

theorem dimension_model (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR q = dimension n q := by
  unfold IntegralMixedRoadmapBadProbeTest.dimension
  rw [ambient_base hn ht ha hR]
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapBadProbePacket.root (pairFst q)) + 3 = _
  unfold IntegralMixedAuxiliaryMarkedIntegerSource.number IntegralMixedAuxiliaryMarkedIntegerSource.original
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedRoadmapBadProbePacket.root dimension
  rw [pairFst_pair]

theorem initial_model (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR q = initial n q := by
  unfold IntegralMixedRoadmapBadProbeTest.initial initial
  rw [dimension_model hn ht ha hR]

theorem width_model (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.width hn ht ha hR q =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (IntegralMixedRoadmapBadProbePacket.root (pairFst q)) :=
  width_base hn ht ha hR _

theorem intervalContext_model (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR q =
      IntegralMixedRoadmapBadProbePacket.intervalContext (dimension n q) (initial n q) q := by
  unfold IntegralMixedRoadmapBadProbeTest.intervalContext
  rw [dimension_model hn ht ha hR, initial_model hn ht ha hR]

theorem fieldPacket_model (z : List Bool) :
    IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR z =
      IntegralMixedRoadmapBadProbeFields.packet (dimension n (pairFst z)) (initial n (pairFst z))
        (pairFst z) (pairSnd z) := by
  unfold IntegralMixedRoadmapBadProbeTest.fieldPacket IntegralMixedRoadmapBadProbeFields.packet
    IntegralMixedRoadmapBadProbeFields.leftContext IntegralMixedRoadmapBadProbeFields.rightContext
  rw [dimension_model hn ht ha hR, initial_model hn ht ha hR]

theorem dimension_eq {S : List Bool → ℕ} (hS : BinaryFn S) (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR q =
      IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hS q :=
  (dimension_model hn ht ha hR q).trans (dimension_model hn ht ha hS q).symm

theorem initial_eq {S : List Bool → ℕ} (hS : BinaryFn S) (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR q =
      IntegralMixedRoadmapBadProbeTest.initial hn ht ha hS q :=
  (initial_model hn ht ha hR q).trans (initial_model hn ht ha hS q).symm

theorem width_eq {S : List Bool → ℕ} (hS : BinaryFn S) (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.width hn ht ha hR q =
      IntegralMixedRoadmapBadProbeTest.width hn ht ha hS q :=
  (width_model hn ht ha hR q).trans (width_model hn ht ha hS q).symm

theorem intervalContext_eq {S : List Bool → ℕ} (hS : BinaryFn S) (q : List Bool) :
    IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR q =
      IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hS q :=
  (intervalContext_model hn ht ha hR q).trans (intervalContext_model hn ht ha hS q).symm

theorem fieldPacket_eq {S : List Bool → ℕ} (hS : BinaryFn S) (z : List Bool) :
    IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR z =
      IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hS z :=
  (fieldPacket_model hn ht ha hR z).trans (fieldPacket_model hn ht ha hS z).symm

theorem root_request (candidate raw labels left right hint word : List Bool) :
    IntegralMixedRoadmapBadProbePacket.root (pairFst (request candidate raw labels left right hint word)) = baseRoot candidate raw := by
  simp only [request, baseRoot, IntegralMixedRoadmapBadProbePacket.root, IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate, IntegralMixedRoadmapBadProbePacket.raw, pairFst_pair, pairSnd_pair]

private theorem request_dimension (candidate raw labels left right hint word : List Bool) :
    dimension n (request candidate raw labels left right hint word) = n (pairFst candidate) + 3 := by
  simp only [dimension, request, IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate, pairFst_pair]

private theorem prepared_words (d : ℕ) (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbePacket.preparedRoot d (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbePacket.preparedRoot d (request candidate raw labels left right hint v) := by
  simp only [request, IntegralMixedRoadmapBadProbePacket.preparedRoot, IntegralMixedRoadmapBadProbePacket.preparedRaw,
    IntegralMixedRoadmapBadProbePacket.prefixCodes, IntegralMixedRoadmapBadProbePacket.probe,
    IntegralMixedRoadmapBadProbePacket.field, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.candidate, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.labels, IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]

private theorem interval_words (d initial : ℕ) (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbePacket.intervalContext d initial (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbePacket.intervalContext d initial (request candidate raw labels left right hint v) := by
  unfold IntegralMixedRoadmapBadProbePacket.intervalContext
  rw [prepared_words d candidate raw labels left right hint w v]
  simp only [request, IntegralMixedRoadmapBadProbePacket.creating, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.producer,
    IntegralMixedRoadmapBadProbePacket.endpoints, IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]

theorem dimension_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hS (request candidate raw labels left right hint v) := by
  rw [dimension_model hn ht ha hR, dimension_model hn ht ha hS, request_dimension, request_dimension]

theorem initial_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbeTest.initial hn ht ha hS (request candidate raw labels left right hint v) := by
  unfold IntegralMixedRoadmapBadProbeTest.initial
  rw [dimension_request hn ht ha hR hS]

theorem width_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbeTest.width hn ht ha hS (request candidate raw labels left right hint v) := by
  rw [width_model hn ht ha hR, width_model hn ht ha hS, root_request, root_request]

theorem intervalContext_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hS (request candidate raw labels left right hint v) := by
  rw [intervalContext_model hn ht ha hR, intervalContext_model hn ht ha hS]
  unfold initial
  rw [request_dimension, request_dimension]
  exact interval_words _ _ candidate raw labels left right hint w v

theorem preparedRoot_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbePacket.preparedRoot
        (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (request candidate raw labels left right hint w))
        (request candidate raw labels left right hint w) =
      IntegralMixedRoadmapBadProbePacket.preparedRoot
        (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hS (request candidate raw labels left right hint v))
        (request candidate raw labels left right hint v) := by
  rw [dimension_request hn ht ha hR hS candidate raw labels left right hint w v]
  exact prepared_words _ candidate raw labels left right hint w v

theorem matchTable_request {S : List Bool → ℕ} (hS : BinaryFn S)
    (candidate raw labels left right hint w v : List Bool) :
    IntegralMixedRoadmapBadProbePacket.matchTable
        (IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (request candidate raw labels left right hint w))
        (pairFst (request candidate raw labels left right hint w)) =
      IntegralMixedRoadmapBadProbePacket.matchTable
        (IntegralMixedRoadmapBadProbeTest.initial hn ht ha hS (request candidate raw labels left right hint v))
        (pairFst (request candidate raw labels left right hint v)) := by
  rw [initial_request hn ht ha hR hS candidate raw labels left right hint w v]
  simp only [request, IntegralMixedRoadmapBadProbePacket.matchTable,
    IntegralMixedRoadmapBadProbePacket.creating, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]

/-- The OWN base and prepared words remain in their literal slots. Only the
contexts and match table ignore word bytes and the actual radius reader. -/
theorem fieldPacket_request (candidate raw labels left right hint word fresh : List Bool) :
    IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR
      (pair (request candidate raw labels left right hint word) fresh) =
      IntegralMixedPhysicalFieldEqualityList.packet (pair (baseRoot candidate raw) []) word
        (pair (IntegralMixedRoadmapBadProbePacket.preparedRoot (n (pairFst candidate) + 3)
          (request candidate raw labels left right hint [])) []) fresh
        (IntegralMixedRoadmapBadProbePacket.matchTable (n (pairFst candidate) + 3 + 5)
          (IntegralMixedRoadmapBadProbePacket.packet candidate raw [] labels left right)) := by
  rw [fieldPacket_model hn ht ha hR]
  simp only [pairFst_pair, pairSnd_pair]
  unfold IntegralMixedRoadmapBadProbeFields.packet IntegralMixedRoadmapBadProbeFields.leftContext
    IntegralMixedRoadmapBadProbeFields.rightContext initial
  rw [request_dimension, root_request, prepared_words _ candidate raw labels left right hint word []]
  simp only [request, IntegralMixedRoadmapBadProbePacket.word, IntegralMixedRoadmapBadProbePacket.matchTable,
    IntegralMixedRoadmapBadProbePacket.creating, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]

theorem prepared_count (q : List Bool) (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst q)) :
    IntegralMixedCausalRecordPlanBits.count
        (IntegralMixedRoadmapBadProbePacket.preparedRoot (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR q) q) =
      IntegralMixedRoadmapBadProbePacket.count (pairFst q) :=
  IntegralMixedRoadmapBadProbePacket.prepared_count _ q hc

private theorem prepared_birth (q : List Bool) (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst q)) :
    CoefficientMarkedRecordCutSource.birth (n := n) (IntegralMixedRoadmapBadProbePacket.preparedRoot (dimension n q) q)
      (IntegralMixedRoadmapBadProbePacket.count (pairFst q) - 1) =
      IntegralMixedRoadmapBadProbePacket.creating (initial n q) (pairFst q) := by
  rw [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedPreludeActual.indices_length,
    CoefficientMarkedRecordActual.codes_length]
  have hi : IntegralMixedAuxiliaryMarkedIntegerSource.number n
      (IntegralMixedRoadmapBadProbePacket.preparedRoot (dimension n q) q) + 8 = initial n q := by
    unfold IntegralMixedAuxiliaryMarkedIntegerSource.number IntegralMixedAuxiliaryMarkedIntegerSource.original
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate initial dimension
    rw [IntegralMixedRoadmapBadProbePacket.prepared_candidate]
  rw [hi]
  unfold IntegralMixedRoadmapBadProbePacket.creating
  omega

/-- The literal native interval context has exactly the installed raw-cut
clock and endpoint labels; source/root/degree semantics are not assumed. -/
theorem intervalContext_installed (q : List Bool) (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst q)) :
    IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR q =
      CoefficientMarkedRecordFullCutInstalled.context (n := n)
        (IntegralMixedRoadmapBadProbePacket.preparedRoot (dimension n q) q)
        (IntegralMixedRoadmapBadProbePacket.count (pairFst q) - 1)
        (IntegralMixedRoadmapBadProbePacket.creating (initial n q) (pairFst q) -
          IntegralMixedRoadmapBadProbePacket.producer false (pairFst q))
        (IntegralMixedRoadmapBadProbePacket.creating (initial n q) (pairFst q) -
          IntegralMixedRoadmapBadProbePacket.producer true (pairFst q)) := by
  rw [intervalContext_model hn ht ha hR]
  unfold IntegralMixedRoadmapBadProbePacket.intervalContext CoefficientMarkedRecordFullCutInstalled.context
  rw [prepared_birth q hc]

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeMetadata
