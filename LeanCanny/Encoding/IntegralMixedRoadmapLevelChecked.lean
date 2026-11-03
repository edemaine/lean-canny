/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelCode
/-! # Native checking of one literal nonterminal roadmap level

Only original syntax and numerical producer/source bounds are checked.
Endpoint order, point equations, component membership and graph edges are
not inferred from this syntax recognizer.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLevel
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Good (n B sourceCap birth : ℕ) (q : List Bool) : Prop :=
  IntegralMixedChronologicalFrameCode.Good n birth (labels q) ∧ g q<n+1 ∧
  IntegralMixedRoadmapEndpointSyntax.Good n B sourceCap birth birth (labels q) (left q) ∧
  IntegralMixedRoadmapEndpointSyntax.Good n B sourceCap birth (birth+freshLeft q) (labels q) (right q) ∧
  (sideWord q=[] ∨ sideWord q=[true]) ∧ sourceCap≤2^B ∧
  q=packet (labels q) (left q) (right q) (side q) (slice q)

def Checked (n B sourceCap birth : ℕ) (q : List Bool) :=Good n B sourceCap birth q ∧ slice q=compiled n q
def InRaw (n : ℕ) (q raw : List Bool) (start : ℕ) : Prop :=
  start+emittedCount n q≤WordListRecords.count raw ∧ slice q=rawSlice raw start (emittedCount n q)

theorem reconstructed_FP : (fun q=>packet (labels q) (left q) (right q) (side q) (slice q))∈FP :=by
  have HS:=(Brackets.stringEq_fppred sideWord_FP (constFn_mem_FP [true])).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])
  simpa only [packet,side,decide_eq_true_eq] using
    mem_FP_pair labels_FP (mem_FP_pair left_FP (mem_FP_pair right_FP (mem_FP_pair HS slice_FP)))

theorem good_FP {n B sourceCap birth : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B)
    (hc : BinaryFn sourceCap) (hb : BinaryFn birth) :
    FPPred (fun q=>Good (n q) (B q) (sourceCap q) (birth q) q) :=by
  exact (IntegralMixedChronologicalFrameCode.good_FP hn hb labels_FP).and
    (((BinaryFn.ofUnary g_unary).lt ((BinaryFn.ofUnary hn).add (BinaryFn.const 1))).and
    ((IntegralMixedRoadmapEndpointSyntax.good_FP hn hB hc hb hb labels_FP left_FP).and
    ((IntegralMixedRoadmapEndpointSyntax.good_FP hn hB hc hb (hb.add (BinaryFn.ofUnary freshLeft_unary)) labels_FP right_FP).and
    (((Brackets.stringEq_fppred sideWord_FP (constFn_mem_FP [])).or
      (Brackets.stringEq_fppred sideWord_FP (constFn_mem_FP [true]))).and
    ((hc.le ((BinaryFn.const 2).powUnary hB)).and (Brackets.stringEq_fppred id_mem_FP reconstructed_FP))))))

theorem checked_FP {n B sourceCap birth : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B)
    (hc : BinaryFn sourceCap) (hb : BinaryFn birth) :
    FPPred (fun q=>Checked (n q) (B q) (sourceCap q) (birth q) q) :=
  (good_FP hn hB hc hb).and (Brackets.stringEq_fppred slice_FP (compiled_FP hn))

theorem inRaw_FP {n start : List Bool→ℕ} {raw : List Bool→List Bool}
    (hn : UnaryFn n) (hr : raw∈FP) (hs : BinaryFn start) :
    FPPred (fun q=>InRaw (n q) q (raw q) (start q)) :=
  ((hs.add (BinaryFn.ofUnary (emittedCount_unary hn))).le
    (BinaryFn.ofUnary (WordListRecords.count_unary.comp hr))).and
    (Brackets.stringEq_fppred slice_FP (rawSlice_FP hr hs (emittedCount_unary hn)))

theorem checked_raw_record {n B sourceCap birth start : ℕ} {q raw : List Bool}
    (h : Checked n B sourceCap birth q) (hr : InRaw n q raw start) (i : ℕ) (hi : i<emittedCount n q) :
    WordList.get (compiled n q) i=WordList.get raw (start+i) :=by
  rw [←h.2,hr.2,rawSlice,WordList.get_encode,List.getElem?_eq_getElem (by
    simpa only [List.length_map,List.length_range] using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem checked_packet (n B sourceCap birth : ℕ) (w l r : List Bool) (s : Bool)
    (h : Good n B sourceCap birth (packet w l r s [])) :
    Checked n B sourceCap birth (packet w l r s (compiled n (packet w l r s []))) :=by
  constructor
  · have HN : ([] : List Bool)≠[true]:=by decide
    cases s <;> simpa only [Good,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,
      pairFst_pair,pairSnd_pair,Bool.false_eq_true,decide_eq_true_eq,HN,ite_false,ite_true] using h
  · simp only [slice,packet,pairSnd_pair]
    exact compiled_packet n w l r s [] _

theorem freeCount_pos {n B sourceCap birth : ℕ} {q : List Bool} (h : Good n B sourceCap birth q) :
    0<freeCount n q :=by
  have H:=h.2.1
  unfold freeCount
  omega

theorem producer_left_lt {n B sourceCap birth : ℕ} {q : List Bool} (h : Good n B sourceCap birth q) :
    producer false q<afterEndpoints birth q :=by
  have H:=IntegralMixedRoadmapEndpointSyntax.producer_lt h.2.2.1 (Nat.le_refl birth)
  change IntegralMixedRoadmapEndpointSyntax.field (left q) 1<_
  unfold afterEndpoints freshLeft
  omega

theorem producer_right_lt {n B sourceCap birth : ℕ} {q : List Bool} (h : Good n B sourceCap birth q) :
    producer true q<afterEndpoints birth q :=by
  exact IntegralMixedRoadmapEndpointSyntax.producer_lt h.2.2.2.1 (Nat.le_add_right birth (freshLeft q))

theorem chosen_lt {n B sourceCap birth : ℕ} {q : List Bool} (h : Good n B sourceCap birth q) :
    chosen q<afterEndpoints birth q :=by
  unfold chosen
  split_ifs
  · exact producer_right_lt h
  · exact producer_left_lt h

theorem frame_mono {n a b : ℕ} {w : List Bool} (h : IntegralMixedChronologicalFrameCode.Good n a w)
    (hab : a≤b) : IntegralMixedChronologicalFrameCode.Good n b w :=
  ⟨h.1,fun i hi=>(h.2 i hi).trans_le hab⟩

theorem child_frame_good {n B sourceCap birth : ℕ} {q : List Bool} (h : Good n B sourceCap birth q) :
    IntegralMixedChronologicalFrameCode.Good n (childBirth n birth q) (childLabels q) :=by
  have HE:=chosen_lt h
  have HK:=h.2.1
  apply (IntegralMixedChronologicalEndpointCode.append_good_iff _ _ _ _).mpr
  refine ⟨frame_mono h.1 ?_,?_,?_⟩
  all_goals unfold childBirth afterEndpoints g k at *;omega

theorem midpoint_good {n B sourceCap birth current j : ℕ} {q : List Bool}
    (h : Good n B sourceCap birth q) (hm : afterEndpoints birth q≤current)
    (hj : g q≤j) (hjn : j<n+1) :
    IntegralMixedChronologicalMidpointCode.Good n current (labels q) (producer false q) (producer true q) (g q) j :=by
  have HL:=producer_left_lt h
  have HR:=producer_right_lt h
  have HG:=h.2.1
  refine ⟨frame_mono h.1 ?_,by omega,by omega,by rfl,HG,hj,hjn⟩
  unfold afterEndpoints at hm
  omega

theorem child_point_good {n B sourceCap birth current j : ℕ} {q : List Bool}
    (h : Good n B sourceCap birth q) (hm : childBirth n birth q≤current)
    (hj : g q≤j) (hjn : j<n+1) :
    IntegralMixedChronologicalEndpointCode.PointGood n current (labels q) (chosen q) (g q) j :=by
  have HC:=chosen_lt h
  have HG:=h.2.1
  refine ⟨⟨frame_mono h.1 ?_,?_,?_⟩,by rfl,HG,hj,hjn⟩
  all_goals unfold childBirth afterEndpoints g k at *;omega

theorem companion_coordinate {n : ℕ} {q : List Bool} {i : ℕ} (hi : i<freeCount n q) :
    g q≤n-i ∧ n-i<n+1 :=by
  unfold freeCount at hi
  omega

theorem checked_count {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q) :
    WordListRecords.count (slice q)=freshLeft q+freshRight q+2+2*freeCount n q :=by
  rw [h.2,compiled,WordListRecords.count_encode,codes_length]

theorem checked_codes {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q) :
    WordListRecords.decode (slice q)=codes n q :=by
  rw [h.2,compiled,WordListRecords.decode_encode]

theorem checked_child_frozen {n B sourceCap birth : ℕ} {q : List Bool} (_h : Checked n B sourceCap birth q) :
    WordListRecords.count (childLabels q)=WordListRecords.count (labels q)+1 :=child_labels_count q

theorem checked_endBirth {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q) :
    birth+WordListRecords.count (slice q)=endBirth n birth q :=by
  rw [checked_count h]
  unfold endBirth afterEndpoints
  omega

theorem reject_terminal {n B sourceCap birth : ℕ} {q : List Bool} (hk : n+1≤g q) :
    ¬Checked n B sourceCap birth q :=by
  intro h
  exact (Nat.not_lt.mpr hk) h.1.2.1

theorem checked_midpoint_anchor {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q) :
    IntegralMixedChronologicalMidpointCode.Good n (afterEndpoints birth q) (labels q)
      (producer false q) (producer true q) (g q) (g q) :=
  midpoint_good h.1 le_rfl le_rfl h.1.2.1

theorem checked_midpoint_companion {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q)
    (i : ℕ) (hi : i<freeCount n q) :
    IntegralMixedChronologicalMidpointCode.Good n (afterEndpoints birth q+1+i) (labels q)
      (producer false q) (producer true q) (g q) (n-i) :=by
  exact midpoint_good h.1 (by omega) (companion_coordinate hi).1 (companion_coordinate hi).2

theorem checked_child_anchor {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q) :
    IntegralMixedChronologicalEndpointCode.PointGood n (childBirth n birth q) (labels q) (chosen q) (g q) (g q) :=
  child_point_good h.1 le_rfl le_rfl h.1.2.1

theorem checked_child_companion {n B sourceCap birth : ℕ} {q : List Bool} (h : Checked n B sourceCap birth q)
    (i : ℕ) (hi : i<freeCount n q) :
    IntegralMixedChronologicalEndpointCode.PointGood n (childBirth n birth q+1+i) (labels q)
      (chosen q) (g q) (n-i) :=by
  exact child_point_good h.1 (by omega) (companion_coordinate hi).1 (companion_coordinate hi).2

end LeanCanny.Encoding.IntegralMixedRoadmapLevel
