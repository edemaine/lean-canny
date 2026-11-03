/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainCode
/-! # Native original-only whole-chain validation -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def LevelChecked (n B sourceCap initial : ℕ) (q : List Bool) (i : ℕ) : Prop :=
  entry q i=canonicalEntry q i ∧
  IntegralMixedRoadmapLevel.Checked n B sourceCap (birth n initial q i) (levelPacket n q i) ∧
  IntegralMixedRoadmapLevel.InRaw n (levelPacket n q i) (raw q) (rawStart n q i)

def Checked (n B sourceCap initial C : ℕ) (q : List Bool) : Prop :=
  depth q≤n ∧ B≤C ∧ sourceCap≤2^B ∧
  metadata q=IntegralMixedRoadmapLevel.rawSlice (metadata q) 0 (depth q) ∧
  (∀i<depth q,LevelChecked n B sourceCap initial q i) ∧
  raw q=compiled n q ∧ WordListRecords.count (raw q)=IntegralMixedRoadmapRecordChain.probedRecordBound n ∧
  (probe q).length≤IntegralMixedRoadmapRecordChain.codeBound n initial C ∧
  q=packet (metadata q) (raw q) (probe q)

theorem level_checked_iff (n B sourceCap initial : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.Checked n B sourceCap (birth n initial q i) (levelPacket n q i) ↔
    (IntegralMixedChronologicalFrameCode.Good n (birth n initial q i) (frozen q i) ∧ i+1<n+1 ∧
      IntegralMixedRoadmapEndpointSyntax.Good n B sourceCap (birth n initial q i) (birth n initial q i) (frozen q i) (left q i) ∧
      IntegralMixedRoadmapEndpointSyntax.Good n B sourceCap (birth n initial q i)
        (birth n initial q i+IntegralMixedRoadmapEndpointSyntax.fresh (left q i)) (frozen q i) (right q i) ∧sourceCap≤2^B) ∧
      IntegralMixedRoadmapLevel.rawSlice (raw q) (rawStart n q i) (blockCount n q i)=
        IntegralMixedRoadmapLevel.compiled n (template q i) :=by
  unfold IntegralMixedRoadmapLevel.Checked
  rw [level_compiled]
  by_cases hs :sideWord q i=[true]
  all_goals simp [IntegralMixedRoadmapLevel.Good,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.sideWord,IntegralMixedRoadmapLevel.side,
    IntegralMixedRoadmapLevel.slice,levelPacket,withSlice,IntegralMixedRoadmapLevel.packet,side,hs,frozen_count]

theorem level_inRaw_iff (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.InRaw n (levelPacket n q i) (raw q) (rawStart n q i) ↔
      rawStart n q i+blockCount n q i≤WordListRecords.count (raw q) :=by
  unfold IntegralMixedRoadmapLevel.InRaw
  rw [level_count]
  simp only [IntegralMixedRoadmapLevel.slice,
    levelPacket,withSlice,IntegralMixedRoadmapLevel.packet,pairSnd_pair,and_true]

theorem levelChecked_FP {n B sourceCap initial i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hB : UnaryFn B) (hc : BinaryFn sourceCap) (hm : BinaryFn initial)
    (hq : q∈FP) (hi : UnaryFn i) : FPPred (fun p=>LevelChecked (n p) (B p) (sourceCap p) (initial p) (q p) (i p)) :=by
  have HB:=birth_binary hn hm hq hi
  have HW:=frozen_FP hq hi
  have HL:=left_FP hq hi
  have HR:=right_FP hq hi
  have HLC:=IntegralMixedRoadmapEndpointSyntax.fresh_unary HL
  have Hframe:=IntegralMixedChronologicalFrameCode.good_FP hn HB HW
  have Hleft:=IntegralMixedRoadmapEndpointSyntax.good_FP hn hB hc HB HB HW HL
  have Hright:=IntegralMixedRoadmapEndpointSyntax.good_FP hn hB hc HB (HB.add (BinaryFn.ofUnary HLC)) HW HR
  have Hsource:=hc.le ((BinaryFn.const 2).powUnary hB)
  have Hraw:=mem_FP_comp (f:=q) (g:=raw) hq raw_FP
  have HS:=rawStart_unary hn hq hi
  have Hcount:=blockCount_unary hn hq hi
  have Hslice:=IntegralMixedRoadmapLevel.rawSlice_FP Hraw (BinaryFn.ofUnary HS) Hcount
  have Hcode:=compileAt_FP hn (template_FP hq hi)
  have Hspace:=((BinaryFn.ofUnary hi).add (BinaryFn.const 1)).lt ((BinaryFn.ofUnary hn).add (BinaryFn.const 1))
  have Hchecked:=((Hframe.and (Hspace.and (Hleft.and (Hright.and Hsource)))).and
    (Brackets.stringEq_fppred Hslice Hcode)).of_iff (fun p=>(level_checked_iff _ _ _ _ _ _).symm)
  have HinRaw:=((BinaryFn.ofUnary (HS.add Hcount)).le (BinaryFn.ofUnary (WordListRecords.count_unary.comp Hraw))).of_iff
    (fun p=>(level_inRaw_iff _ _ _).symm)
  exact (Brackets.stringEq_fppred (entry_FP hq hi) (canonicalEntry_FP hq hi)).and (Hchecked.and HinRaw)

theorem checkedAt_FP {n B sourceCap initial C : List Bool→ℕ} {payload : List Bool→List Bool}
    (hn : UnaryFn n) (hB : UnaryFn B) (hc : BinaryFn sourceCap) (hm : BinaryFn initial) (hC : UnaryFn C)
    (hp : payload∈FP) : FPPred (fun q=>Checked (n q) (B q) (sourceCap q) (initial q) (C q) (payload q)) :=by
  have HD:=depth_unary.comp hp
  have HM:=mem_FP_comp (f:=payload) (g:=metadata) hp metadata_FP
  have HR:=mem_FP_comp (f:=payload) (g:=raw) hp raw_FP
  have HP:=mem_FP_comp (f:=payload) (g:=probe) hp probe_FP
  have Hlevels0:=(levelChecked_FP (hn.comp pairFst_mem_FP) (hB.comp pairFst_mem_FP)
    (hc.comp pairFst_mem_FP) (hm.comp pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP hp) UnaryFn.index).forall_lt HD
  have Hlevels : FPPred (fun q=>∀i<depth (payload q),LevelChecked (n q) (B q) (sourceCap q) (initial q) (payload q) i):=
    Hlevels0.of_iff (fun q=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate])
  have Hmeta:=IntegralMixedRoadmapLevel.rawSlice_FP HM (BinaryFn.const 0) HD
  have Hbound:=IntegralMixedRoadmapRecordChain.codeBound_unary hn hm hC
  have Hreconstruct:=mem_FP_pair HM (mem_FP_pair HR HP)
  exact ((BinaryFn.ofUnary HD).le (BinaryFn.ofUnary hn)).and
    (((BinaryFn.ofUnary hB).le (BinaryFn.ofUnary hC)).and
    ((hc.le ((BinaryFn.const 2).powUnary hB)).and
    ((Brackets.stringEq_fppred HM Hmeta).and
    (Hlevels.and ((Brackets.stringEq_fppred HR (compiledAt_FP hn hp)).and
    ((FPPred.eq (WordListRecords.count_unary.comp HR) ((IntegralMixedRoadmapRecordChain.recordBound_unary hn).add (UnaryFn.const 1))).and
    ((FPPred.le (UnaryFn.length HP) Hbound).and (Brackets.stringEq_fppred hp Hreconstruct))))))))

theorem checked_FP {n B sourceCap initial C : List Bool→ℕ}
    (hn : UnaryFn n) (hB : UnaryFn B) (hc : BinaryFn sourceCap) (hm : BinaryFn initial) (hC : UnaryFn C) :
    FPPred (fun q=>Checked (n q) (B q) (sourceCap q) (initial q) (C q) q) :=
  checkedAt_FP hn hB hc hm hC id_mem_FP

theorem level_checked {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i<depth q) : IntegralMixedRoadmapLevel.Checked n B sourceCap (birth n initial q i) (levelPacket n q i) :=
  (h.2.2.2.2.1 i hi).2.1

attribute [local irreducible] IntegralMixedChronologicalEndpointCode.appendLabels frozen chosen rawStart blockCount

theorem level_frozen (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.childLabels (levelPacket n q i)=frozen q (i+1) :=by
  have HL : IntegralMixedRoadmapLevel.labels (levelPacket n q i)=frozen q i:=by
    simp only [levelPacket,withSlice,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.packet,pairFst_pair]
  have HC : IntegralMixedRoadmapLevel.chosen (levelPacket n q i)=chosen q i:=withSlice_chosen q i _
  simp only [IntegralMixedRoadmapLevel.childLabels,HL,HC,frozen_succ]

theorem level_end_bound {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i<depth q) :
    IntegralMixedRoadmapLevel.endBirth n (birth n initial q i) (levelPacket n q i)≤IntegralMixedRoadmapRecordChain.maxBirth n initial :=by
  rw [level_end]
  exact Nat.add_le_add_left (rawStart_bound n q (i+1) (by have HD:=h.1;omega)) initial

end LeanCanny.Encoding.IntegralMixedRoadmapChain
