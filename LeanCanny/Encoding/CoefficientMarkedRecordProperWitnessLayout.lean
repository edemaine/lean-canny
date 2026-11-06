/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperGuardPackets
public import LeanCanny.Encoding.IntegralMixedRoadmapProperInputComposition
/-! # Literal coordinate-witness keys erase only the original sample word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessLayout
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapProperRow
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def request (z word : List Bool) := pair
  (IntegralMixedRoadmapAtomic.packet (IntegralMixedRoadmapAtomic.candidate (atomic z))
    (IntegralMixedRoadmapAtomic.payload (atomic z)) word) (pairSnd z)
def anchor (z : List Bool) := request z []
def leftContext (z : List Bool) := IntegralMixedRoadmapAtomic.context (atomic z)
noncomputable abbrev preparedContext (n : List Bool → ℕ) (mean : Bool) (z : List Bool) := pair (catalogRoot n mean z) []
def table (n : List Bool → ℕ) (z : List Bool) :=
  IntegralMixedRoadmapBadProbePacket.matchTable (catalogInitial n z) (oldPacket z)

theorem count_request (z word : List Bool) :
    IntegralMixedRoadmapBadProbePacket.count (oldPacket (request z word)) =
      IntegralMixedRoadmapBadProbePacket.count (oldPacket z) := by
  simp only [request, oldPacket, atomic, IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.payload, IntegralMixedRoadmapAtomic.candidate,
    IntegralMixedRoadmapAtomic.word, pairFst_pair, pairSnd_pair]

theorem syntax_request (n : List Bool → ℕ) (z word : List Bool) :
    rankRowSyntax n (request z word) ↔ rankRowSyntax n z := by
  simp only [rankRowSyntax, request, catalogDimension, catalogCreating, catalogInitial, labels, offset,
    coordinate, oldProducer, oldPacket, atomic, IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapProper.producer, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapProper.badPacket, IntegralMixedRoadmapBadProbePacket.creating,
    IntegralMixedRoadmapBadProbePacket.count, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

theorem catalogRoot_request (n : List Bool → ℕ) (mean : Bool) (z word : List Bool) :
    catalogRoot n mean (request z word) = catalogRoot n mean z := by
  simp only [catalogRoot, catalogCode, request, catalogDimension,
    labels, offset, coordinate, oldProducer, oldPacket, atomic, IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapProper.producer, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapProper.badPacket, IntegralMixedRoadmapBadProbePacket.prefixCodes,
    IntegralMixedRoadmapBadProbePacket.count, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

theorem leftContext_request (z word : List Bool) : leftContext (request z word) = leftContext z := by
  simp only [leftContext, request, atomic, IntegralMixedRoadmapAtomic.context,
    IntegralMixedRoadmapAtomic.root, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

theorem side_request (right : Bool) (z word : List Bool) :
    IntegralMixedRoadmapProperRowWitness.SideGood right (request z word) ↔
      IntegralMixedRoadmapProperRowWitness.SideGood right z := by
  simp only [IntegralMixedRoadmapProperRowWitness.SideGood, request, atomic,
    IntegralMixedRoadmapProper.levelIndex, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

theorem native_context (mean : Bool) (z word : List Bool) :
    context hn ht ha hR mean (request z word) = preparedContext n mean z := by
  unfold context preparedContext
  rw [root_catalog, catalogRoot_request]

theorem native_row_good (z word : List Bool) :
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR (request z word) ↔ rankRowSyntax n z := by
  rw [rank_row_good_iff, syntax_request]

theorem field_packet (mean : Bool) (z word ordinary centered code : List Bool) :
    IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR mean
      (IntegralMixedRoadmapProperRowWitness.packet (request z word) ordinary centered code) =
    IntegralMixedPhysicalFieldEqualityList.packet (leftContext z) word (preparedContext n mean z)
      (if mean then centered else ordinary) (table n z) := by
  unfold IntegralMixedRoadmapProperRowWitness.fieldMatch IntegralMixedRoadmapProperRowWitness.atomic
    IntegralMixedRoadmapProperRowWitness.key IntegralMixedRoadmapProperRowWitness.ownWord
    IntegralMixedRoadmapProperRowWitness.packet
  simp only [pairFst_pair, pairSnd_pair]
  rw [native_context hn ht ha hR]
  have HOld : IntegralMixedRoadmapAtomic.context (atomic (request z word)) = leftContext z :=
    leftContext_request z word
  rw [HOld]
  change IntegralMixedPhysicalFieldEqualityList.packet (leftContext z)
    (IntegralMixedRoadmapAtomic.word (atomic (request z word))) (preparedContext n mean z)
    (if mean then centered else ordinary)
    (IntegralMixedRoadmapBadProbePacket.matchTable (initial hn ht ha hR (request z word)) (oldPacket (request z word))) = _
  rw [initial_catalog]
  simp only [table, catalogInitial, request, oldPacket, atomic, IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.matchTable, IntegralMixedRoadmapBadProbePacket.creating,
    IntegralMixedRoadmapBadProbePacket.count, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload,
    IntegralMixedRoadmapAtomic.word, IntegralMixedRoadmapAtomic.original, pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessLayout
