/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEndpointSize
public import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
/-! # All checked history metadata fits an original fixed horizon

Canonical endpoint fields and entries rule out arbitrarily padded retained
labels. The bound covers the full payload, including its terminal probe.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapRecordChain
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def entryBudget (n initial C : ℕ):=(2*IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C+2)*3
def metadataBudget (n initial C : ℕ):=(2*entryBudget n initial C+2)*n
def payloadBudget (n initial C : ℕ):=2*metadataBudget n initial C+
  2*((2*codeBound n initial C+2)*probedRecordBound n)+codeBound n initial C+4

theorem entryBudget_unary {n initial C : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hC : UnaryFn C) :
    UnaryFn (fun q=>entryBudget (n q) (initial q) (C q)) :=
  (((UnaryFn.const 2).mul (IntegralMixedRoadmapEndpointSyntax.specBudget_unary hn
    (maxBirth_unary hn hi) hC)).add (UnaryFn.const 2)).mul (UnaryFn.const 3)

theorem metadataBudget_unary {n initial C : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hC : UnaryFn C) :
    UnaryFn (fun q=>metadataBudget (n q) (initial q) (C q)) :=
  (((UnaryFn.const 2).mul (entryBudget_unary hn hi hC)).add (UnaryFn.const 2)).mul hn

theorem payloadBudget_unary {n initial C : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hC : UnaryFn C) :
    UnaryFn (fun q=>payloadBudget (n q) (initial q) (C q)) :=by
  have HC:=codeBound_unary hn (BinaryFn.ofUnary hi) hC
  have HT:=(((UnaryFn.const 2).mul HC).add (UnaryFn.const 2)).mul ((recordBound_unary hn).add (UnaryFn.const 1))
  exact ((((UnaryFn.const 2).mul (metadataBudget_unary hn hi hC)).add ((UnaryFn.const 2).mul HT)).add HC).add
    (UnaryFn.const 4)

private theorem endpoint_bounds {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (i : ℕ) (hi : i<depth q) :
    (left q i).length≤IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C ∧
    (right q i).length≤IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C :=by
  have HL:=((level_checked_iff n B sourceCap initial q i).mp (level_checked hq i hi)).1
  have HB : birth n initial q i≤maxBirth n initial:=by
    have HH:=rawStart_bound n q i (by have :=hq.1;omega)
    unfold birth maxBirth
    omega
  have HR : birth n initial q i+IntegralMixedRoadmapEndpointSyntax.fresh (left q i)≤maxBirth n initial:=by
    have HH:=rawStart_bound n q (i+1) (by have :=hq.1;omega)
    rw [rawStart_succ] at HH
    unfold birth maxBirth blockCount freshCount at *
    omega
  have HS:=IntegralMixedRoadmapEndpointSyntax.good_length HL.2.2.1 HB HB hq.2.2.1 HL.1.1
  have HT:=IntegralMixedRoadmapEndpointSyntax.good_length HL.2.2.2.1 HB HR hq.2.2.1 HL.1.1
  have HM : IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) B≤
      IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C:=by
    unfold IntegralMixedRoadmapEndpointSyntax.specBudget
    have :=hq.2.1
    omega
  exact ⟨HS.trans HM,HT.trans HM⟩

theorem entry_length {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (i : ℕ) (hi : i<depth q) :
    (entry q i).length≤entryBudget n initial C :=by
  obtain ⟨HL,HR⟩:=endpoint_bounds hq i hi
  rw [(hq.2.2.2.2.1 i hi).1]
  have HS : (if side q i then ([true] : List Bool) else []).length≤
      IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C:=by
    unfold IntegralMixedRoadmapEndpointSyntax.specBudget
    cases side q i <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_nil,List.length_cons] <;> omega
  have HF : ∀w∈[left q i,right q i,if side q i then [true] else []],
      w.length≤IntegralMixedRoadmapEndpointSyntax.specBudget n (maxBirth n initial) C:=by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl
    · exact HL
    · exact HR
    · exact HS
  simpa only [canonicalEntry,entryBudget,List.length_cons,List.length_nil] using WordList.length_le _ _ HF

theorem metadata_length {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) : (metadata q).length≤metadataBudget n initial C :=by
  have HF : ∀w∈(List.range (depth q)).map (fun i=>WordList.get (metadata q) (0+i)),
      w.length≤entryBudget n initial C:=by
    intro w hw
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
    simpa only [Nat.zero_add,entry] using entry_length hq i (List.mem_range.mp hi)
  have HL:=WordList.length_le _ (entryBudget n initial C) HF
  rw [hq.2.2.2.1]
  change (WordList.encode _).length≤_
  apply HL.trans
  simp only [List.length_map,List.length_range]
  exact Nat.mul_le_mul_left _ hq.1

theorem payload_length {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) : q.length≤payloadBudget n initial C :=by
  have HM:=metadata_length hq
  have HR:=raw_length_le hq
  have HP:=hq.2.2.2.2.2.2.2.1
  have HE:=congrArg List.length hq.2.2.2.2.2.2.2.2
  simp only [packet,pair_length] at HE
  unfold payloadBudget
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapChain
