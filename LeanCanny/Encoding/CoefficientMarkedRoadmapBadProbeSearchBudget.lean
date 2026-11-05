/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeExistence
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeHints
public import LeanCanny.Computation.WordResourceEnvelope
/-! # One original numeric cutoff for every bounded native NoBad hint -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def base (q word : List Bool) := IntegralMixedRoadmapBadProbePacket.packet
  (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)) (IntegralMixedRoadmapBadProbePacket.raw (pairFst q)) word
  (IntegralMixedRoadmapBadProbePacket.labels (pairFst q))
  (pairFst (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
  (pairSnd (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
def canonical (q : List Bool) := base q []

theorem canonical_FP : canonical ∈ FP := by
  polytime [canonical, base, IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.labels, IntegralMixedRoadmapBadProbePacket.endpoints]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def allowance (b : List Bool) := 2*b.length+
  IntegralMixedRoadmapBadProbeSearch.hintWidth hn ht ha (BinaryFn.const 0) b+2

theorem allowance_unary : UnaryFn (allowance hn ht ha) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add
    (IntegralMixedRoadmapBadProbeSearch.hintWidth_unary hn ht ha (BinaryFn.const 0))).add (UnaryFn.const 2)

/-- This envelope bounds the ALREADY proved concrete sign cutoff at every
short actual hint-packet input. It asserts no stability from FP complexity. -/
theorem exists_envelope : ∃ g : List Bool → ℕ, BinaryFn g ∧ ∀ b z,
    z.length ≤ allowance hn ht ha b →
      cutoff hn ht ha (IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha (BinaryFn.const 0) z) ≤ g b := by
  have HF : BinaryFn (fun z => cutoff hn ht ha
      (IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha (BinaryFn.const 0) z)) :=
    (cutoff_binary hn ht ha).comp (IntegralMixedRoadmapBadProbeSearch.hintPacket_FP hn ht ha (BinaryFn.const 0))
  exact HF.wordEnvelope (allowance_unary hn ht ha)

noncomputable def envelope : List Bool → ℕ := Classical.choose (exists_envelope hn ht ha)

theorem envelope_binary : BinaryFn (envelope hn ht ha) := (Classical.choose_spec (exists_envelope hn ht ha)).1

theorem envelope_bound (b z : List Bool) (hz : z.length ≤ allowance hn ht ha b) :
    cutoff hn ht ha (IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha (BinaryFn.const 0) z) ≤ envelope hn ht ha b :=
  (Classical.choose_spec (exists_envelope hn ht ha)).2 b z hz

noncomputable def searchCutoff (q : List Bool) := envelope hn ht ha (canonical q)+1

theorem searchCutoff_binary : BinaryFn (searchCutoff hn ht ha) := by
  have H : BinaryFn (fun q => envelope hn ht ha (canonical q)) := (envelope_binary hn ht ha).comp canonical_FP
  exact H.add (BinaryFn.const 1)

/-- Every literal bounded hint receives the same original ceiling. The base
packet has its sampled word removed before the resource envelope is taken. -/
theorem hint_cutoff_le (q bits : List Bool)
    (hlen : bits.length = IntegralMixedRoadmapBadProbeSearch.hintWidth hn ht ha (BinaryFn.const 0) (canonical q)) :
    cutoff hn ht ha (IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha (BinaryFn.const 0) (pair (canonical q) bits)) ≤
      searchCutoff hn ht ha q := by
  apply (envelope_bound hn ht ha (canonical q) (pair (canonical q) bits) ?_).trans (Nat.le_succ _)
  unfold allowance
  rw [pair_length, hlen]
  omega

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
