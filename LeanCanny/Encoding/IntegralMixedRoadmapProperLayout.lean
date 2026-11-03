/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicControls
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode

/-! # Literal latest-level midpoint and endpoint query layout

Chronological producers are retained even after the anchor and all capture
births. Midpoint coordinates are never represented by a producer alias.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def levelIndex (q : List Bool):=IntegralMixedRoadmapAtomic.depth q-1
def labels (q : List Bool):=IntegralMixedRoadmapChain.frozen (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
def level (n : ℕ) (q : List Bool):=IntegralMixedRoadmapChain.levelPacket n (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
def producer (right : Bool) (q : List Bool):=IntegralMixedRoadmapEndpointSyntax.field
  (if right then IntegralMixedRoadmapChain.right (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
    else IntegralMixedRoadmapChain.left (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)) 1
def baseBirth (n initial : ℕ) (q : List Bool):=IntegralMixedRoadmapChain.birth n initial
  (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
def midBirth (n initial : ℕ) (q : List Bool):=baseBirth n initial q+
  IntegralMixedRoadmapChain.freshCount (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
def midFirst (n initial : ℕ) (q : List Bool):=midBirth n initial q+1
def captureCount (n : ℕ) (q : List Bool):=n-levelIndex q
def midProducer (n initial : ℕ) (q : List Bool) (j : ℕ):=midFirst n initial q+(n-j)
def childProducer (n initial : ℕ) (q : List Bool) (j : ℕ):=IntegralMixedRoadmapAtomic.first n initial q+(n-j)
def chosen (q : List Bool):=IntegralMixedRoadmapChain.chosen (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
def midCompanions (n initial : ℕ) (q : List Bool):=pair (IntegralMixedRoadmapAtomic.sampleQuery q)
  (IntegralMixedPhysicalPointCompanionScan.descriptor (midBirth n initial q) (midFirst n initial q) (captureCount n q))
def badPacket (q : List Bool):=IntegralMixedRoadmapBadProbePacket.packet
  (IntegralMixedRoadmapAtomic.candidate q) (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q))
  (IntegralMixedRoadmapAtomic.word q) (labels q) (BinaryNatCode.encode (producer false q)) (BinaryNatCode.encode (producer true q))

theorem levelIndex_unary : UnaryFn levelIndex:=IntegralMixedRoadmapAtomic.depth_unary.sub (UnaryFn.const 1)
theorem labels_FP : labels∈FP:=IntegralMixedRoadmapChain.frozen_FP IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary
theorem level_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun q=>level (n q) q)∈FP:=
  IntegralMixedRoadmapChain.levelPacket_FP hn IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary
theorem producer_binary (right : Bool) : BinaryFn (producer right):=by
  cases right
  · exact IntegralMixedRoadmapEndpointSyntax.field_binary
      (IntegralMixedRoadmapChain.left_FP IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary) 1
  · exact IntegralMixedRoadmapEndpointSyntax.field_binary
      (IntegralMixedRoadmapChain.right_FP IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary) 1
theorem baseBirth_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>baseBirth (n q) (initial q) q):=
  hi.add (IntegralMixedRoadmapChain.rawStart_unary hn IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary)
theorem midBirth_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>midBirth (n q) (initial q) q):=
  (baseBirth_unary hn hi).add (IntegralMixedRoadmapChain.freshCount_unary IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary)
theorem midFirst_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>midFirst (n q) (initial q) q):=(midBirth_unary hn hi).add (UnaryFn.const 1)
theorem captureCount_unary {n : List Bool→ℕ} (hn : UnaryFn n) :UnaryFn (fun q=>captureCount (n q) q):=hn.sub levelIndex_unary
theorem midProducer_binary {n initial j : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hj : BinaryFn j) :
    BinaryFn (fun q=>midProducer (n q) (initial q) q (j q)):=
  (BinaryFn.ofUnary (midFirst_unary hn hi)).add ((BinaryFn.ofUnary hn).sub hj)
theorem childProducer_binary {n initial j : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hj : BinaryFn j) :
    BinaryFn (fun q=>childProducer (n q) (initial q) q (j q)):=
  (BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.first_unary hn hi)).add ((BinaryFn.ofUnary hn).sub hj)
theorem chosen_binary : BinaryFn chosen:=IntegralMixedRoadmapChain.chosen_binary
  IntegralMixedRoadmapAtomic.payload_FP levelIndex_unary
theorem midCompanions_FP {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    (fun q=>midCompanions (n q) (initial q) q)∈FP:=
  mem_FP_pair IntegralMixedRoadmapAtomic.sampleQuery_FP (mem_FP_pair (midBirth_unary hn hi).mem_FP
    (mem_FP_pair (midFirst_unary hn hi).mem_FP (captureCount_unary hn).mem_FP))
theorem badPacket_FP : badPacket∈FP:=by
  exact mem_FP_pair IntegralMixedRoadmapAtomic.candidate_FP
    (mem_FP_pair (mem_FP_comp (f:=IntegralMixedRoadmapAtomic.payload) (g:=IntegralMixedRoadmapChain.raw)
      IntegralMixedRoadmapAtomic.payload_FP IntegralMixedRoadmapChain.raw_FP)
      (mem_FP_pair IntegralMixedRoadmapAtomic.word_FP (mem_FP_pair labels_FP
        (mem_FP_pair (producer_binary false).bits_mem_FP (producer_binary true).bits_mem_FP))))

theorem labels_count (q : List Bool) : WordListRecords.count (labels q)=levelIndex q:=
  IntegralMixedRoadmapChain.frozen_count _ _
theorem badPacket_root (q : List Bool) : IntegralMixedRoadmapBadProbePacket.root (badPacket q)=IntegralMixedRoadmapAtomic.root q:=by
  simp only [badPacket,IntegralMixedRoadmapBadProbePacket.root,IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralMixedRoadmapProper
