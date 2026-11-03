/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
public import LeanCanny.Encoding.IntegralMixedChronologicalPointSignatureCode
/-! # One atomic vertex keeps its checked chain and one full word

No midpoint mode is encoded. The latest child anchor and companions end
at the meaningful-record prefix; padding and the reserved probe follow.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def packet (candidate payload word : List Bool):=pair candidate (pair payload word)
def candidate (q : List Bool):=pairFst q
def payload (q : List Bool):=pairFst (pairSnd q)
def word (q : List Bool):=pairSnd (pairSnd q)
def original (q : List Bool):=pairFst (candidate q)
def root (q : List Bool):=pair (candidate q) (pair (IntegralMixedRoadmapChain.raw (payload q)) [])
def context (q : List Bool):=pair (root q) []
def fullQuery (q : List Bool):=pair (root q) (word q)
def sampleQuery (q : List Bool):=pair (context q) (word q)
def depth (q : List Bool):=IntegralMixedRoadmapChain.depth (payload q)
def frozen (q : List Bool):=IntegralMixedRoadmapChain.frozen (payload q) (depth q)
def free (n : ℕ) (q : List Bool):=n+1-depth q
def endBirth (n initial : ℕ) (q : List Bool):=initial+IntegralMixedRoadmapChain.rawStart n (payload q) (depth q)
def anchor (n initial : ℕ) (q : List Bool):=endBirth n initial q-(free n q+1)
def first (n initial : ℕ) (q : List Bool):=anchor n initial q+1
def companionQuery (n initial : ℕ) (q : List Bool):=pair (sampleQuery q)
  (IntegralMixedPhysicalPointCompanionScan.descriptor (anchor n initial q) (first n initial q) (free n q))
def signature (n initial : ℕ) (q : List Bool):=
  IntegralMixedChronologicalPointSignatureCode.code n (first n initial q) (frozen q)

theorem candidate_FP :candidate∈FP:=pairFst_mem_FP
theorem payload_FP :payload∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem word_FP :word∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem original_FP :original∈FP:=mem_FP_comp candidate_FP pairFst_mem_FP
theorem root_FP :root∈FP:=mem_FP_pair candidate_FP
  (mem_FP_pair (mem_FP_comp (f:=payload) (g:=IntegralMixedRoadmapChain.raw) payload_FP
    IntegralMixedRoadmapChain.raw_FP) (constFn_mem_FP []))
theorem context_FP :context∈FP:=mem_FP_pair root_FP (constFn_mem_FP [])
theorem fullQuery_FP :fullQuery∈FP:=mem_FP_pair root_FP word_FP
theorem sampleQuery_FP :sampleQuery∈FP:=mem_FP_pair context_FP word_FP
theorem depth_unary :UnaryFn depth:=IntegralMixedRoadmapChain.depth_unary.comp payload_FP
theorem frozen_FP :frozen∈FP:=IntegralMixedRoadmapChain.frozen_FP payload_FP depth_unary
theorem free_unary {n : List Bool→ℕ} (hn :UnaryFn n) :UnaryFn (fun q=>free (n q) q):=
  (hn.add (UnaryFn.const 1)).sub depth_unary
theorem endBirth_unary {n initial : List Bool→ℕ} (hn :UnaryFn n) (hi :UnaryFn initial) :
    UnaryFn (fun q=>endBirth (n q) (initial q) q):=
  hi.add (IntegralMixedRoadmapChain.rawStart_unary hn payload_FP depth_unary)
theorem anchor_unary {n initial : List Bool→ℕ} (hn :UnaryFn n) (hi :UnaryFn initial) :
    UnaryFn (fun q=>anchor (n q) (initial q) q):=
  (endBirth_unary hn hi).sub ((free_unary hn).add (UnaryFn.const 1))
theorem first_unary {n initial : List Bool→ℕ} (hn :UnaryFn n) (hi :UnaryFn initial) :
    UnaryFn (fun q=>first (n q) (initial q) q):=(anchor_unary hn hi).add (UnaryFn.const 1)
theorem companionQuery_FP {n initial : List Bool→ℕ} (hn :UnaryFn n) (hi :UnaryFn initial) :
    (fun q=>companionQuery (n q) (initial q) q)∈FP:=
  mem_FP_pair sampleQuery_FP (mem_FP_pair (anchor_unary hn hi).mem_FP
    (mem_FP_pair (first_unary hn hi).mem_FP (free_unary hn).mem_FP))
theorem signature_FP {n initial : List Bool→ℕ} (hn :UnaryFn n) (hi :UnaryFn initial) :
    (fun q=>signature (n q) (initial q) q)∈FP:=
  IntegralMixedChronologicalPointSignatureCode.code_FP hn (BinaryFn.ofUnary (first_unary hn hi)) frozen_FP

theorem frozen_count (q :List Bool):WordListRecords.count (frozen q)=depth q :=
  IntegralMixedRoadmapChain.frozen_count _ _
theorem signature_count (n initial :ℕ) (q :List Bool):WordListRecords.count (signature n initial q)=n+1 :=
  IntegralMixedChronologicalPointSignatureCode.code_count _ _ _

theorem seed_anchor (n initial :ℕ) (q :List Bool) (hd :depth q=0) :anchor n initial q=initial :=by
  simp only [anchor,endBirth,free,hd,IntegralMixedRoadmapChain.rawStart,
    IntegralMixedRoadmapChain.prefixCount,Finset.sum_range_zero,Nat.add_zero,Nat.sub_zero]
  omega

theorem child_anchor (n initial :ℕ) (q :List Bool) (i :ℕ) (hd :depth q=i+1) (hi :i<n) :
    anchor n initial q=IntegralMixedRoadmapLevel.childBirth n
      (IntegralMixedRoadmapChain.birth n initial (payload q) i)
      (IntegralMixedRoadmapChain.levelPacket n (payload q) i) :=by
  have HE:=IntegralMixedRoadmapChain.level_end n initial (payload q) i
  have HG :IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n (payload q) i)=n-i :=by
    simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k]
    omega
  unfold anchor endBirth free
  rw [hd]
  change IntegralMixedRoadmapChain.birth n initial (payload q) (i+1)-(n+1-(i+1)+1)=_
  rw [←HE]
  unfold IntegralMixedRoadmapLevel.childBirth IntegralMixedRoadmapLevel.endBirth
  rw [HG]
  omega

theorem block_end (n initial :ℕ) (q :List Bool) (hd :depth q≤n) :
    first n initial q+free n q=endBirth n initial q :=by
  have HR :n+2≤IntegralMixedRoadmapChain.rawStart n (payload q) (depth q) :=by
    unfold IntegralMixedRoadmapChain.rawStart
    omega
  unfold first anchor free endBirth
  omega
end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
