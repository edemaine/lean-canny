/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanHeaders
public import LeanCanny.Algebra.IntegralMixedCausalUnitHeader
public import LeanCanny.Encoding.IntegralMixedCausalUnitBody
public import LeanCanny.Encoding.WordListRecords
/-! # Literal original record tables instantiate the causal plan

Records are chronological words in the second root field. Source descriptors
are indexed by the complete original root and creating scalar birth. Missing
records use the original source0; no interpreted value enters a native writer.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def records (root : List Bool) := pairFst (pairSnd root)
def count (root : List Bool) := WordListRecords.count (records root)
def code (root : List Bool) (i : ℕ) := WordList.get (records root) i

theorem records_FP : records∈FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem count_unary : UnaryFn count := WordListRecords.count_unary.comp records_FP

def reader (z : List Bool) := code (pairFst z) (pairSnd z).length

theorem reader_FP : reader∈FP := by
  have H := mem_FP_comp (g:=WordList.reader) (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP records_FP) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq H (fun z => by simp only [Function.comp_apply,reader,code,WordList.reader,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀ root,0<P.ambient root)
  (hd : ∀ root b,(S root b).degree=P.degree root)
  (hcap : ∀ root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)

noncomputable def step (root : List Bool) (b : ℕ) : Record (P.ambient root) (P.width root) :=
  IntegralMixedCausalUnitRecordBits.record (S root b) (hn root) b (code root b)
    (by rw [hd]; exact hcap root)

noncomputable def originalRecords (root : List Bool) := ((List.range (count root)).map (step P S hn hd hcap root)).reverse

theorem originalRecords_length (root : List Bool) : (originalRecords P S hn hd hcap root).length=count root := by
  simp only [originalRecords,List.length_reverse,List.length_map,List.length_range]

theorem originalRecords_degree (root : List Bool) (r : Record (P.ambient root) (P.width root))
    (hr : r∈originalRecords P S hn hd hcap root) : r.source.degree=P.degree root := by
  rw [originalRecords,List.mem_reverse] at hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact hd root b

noncomputable def base (hroom : ∀ root,count root+2≤P.cap root+1) : Plan P where
  initialSource root := S root 0
  initial_degree root := hd root 0
  scalar_cap := hcap
  rules _ := []
  room root := by change 0+2≤P.cap root+1; have H := hroom root; omega

noncomputable def plan (hroom : ∀ root,count root+2≤P.cap root+1) : Plan P :=
  IntegralMixedCausalPlanBits.plan P (base P S hd hcap hroom) (originalRecords P S hn hd hcap)
    (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root)

noncomputable def data (hroom : ∀ root,count root+2≤P.cap root+1)
    (hW : ∀ root,(P.degree root).size≤P.sourceWidth root) : IntegralMixedFramedHistoryFamilyBits.Data P (plan P S hn hd hcap hroom) :=
  IntegralMixedCausalPlanBits.data P (base P S hd hcap hroom) (originalRecords P S hn hd hcap)
    (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root)
    hn (originalRecords_degree P S hn hd hcap) hW

def sourceIndex (key : List Bool) :=
  if prefixLength P key<count (pairFst key) then prefixLength P key else 0

theorem sourceIndex_unary (a : Access P) : UnaryFn (sourceIndex P) :=
  UnaryFn.ite ((BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).lt
    (BinaryFn.ofUnary (count_unary.comp pairFst_mem_FP)))
    (IntegralMixedFullHistoryFamilyBits.prefix_unary P a) (UnaryFn.const 0)

theorem selectedSource_eq (hroom : ∀ root,count root+2≤P.cap root+1) (key : List Bool) :
    IntegralMixedCausalPlanBits.selectedSource P (base P S hd hcap hroom)
      (originalRecords P S hn hd hcap) key=S (pairFst key) (sourceIndex P key) := by
  unfold IntegralMixedCausalPlanBits.selectedSource originalRecords sourceIndex
  rw [List.reverse_reverse,List.getElem?_map]
  split_ifs with hb
  · rw [List.getElem?_range hb]
    rfl
  · have HR : (List.range (count (pairFst key)))[prefixLength P key]?=none :=
      List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt hb)
    rw [HR]
    rfl

theorem instruction_source (hroom : ∀ root,count root+2≤P.cap root+1) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P S hn hd hcap hroom) key).source=
      S (pairFst key) (sourceIndex P key) :=
  (IntegralMixedCausalPlanBits.instruction_source P (base P S hd hcap hroom)
    (originalRecords P S hn hd hcap) (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root) key).trans
    (selectedSource_eq P S hn hd hcap hroom key)

end LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
