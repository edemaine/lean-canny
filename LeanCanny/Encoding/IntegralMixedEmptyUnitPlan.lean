/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitSource
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Encoding.WordListRecords
/-! # Canonical changing-source records with an empty initial bank

The root stores the original input first, followed by chronological records
and advice. Every actual record is critical or a relative limit cut. The
framed interpreter starts at its empty bank. Padded instructions use integer
X and source zero; this does not identify the terminal source with the final
advanced spatial frame.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open scoped Classical

def input (root : List Bool) := pairFst root
def records (root : List Bool) := pairFst (pairSnd root)
def count (root : List Bool) := WordListRecords.count (records root)
def code (root : List Bool) (i : ℕ) := WordList.get (records root) i

theorem input_FP : input∈FP := pairFst_mem_FP
theorem records_FP : records∈FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem count_unary : UnaryFn count := WordListRecords.count_unary.comp records_FP

def inRecords (P : Parameters) (key : List Bool) : Prop :=
  IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key)

theorem inRecords_FP (P : Parameters) (a : Access P) : FPPred (inRecords P) :=
  FPPred.lt (IntegralMixedFullHistoryFamilyBits.prefix_unary P a) (count_unary.comp pairFst_mem_FP)

noncomputable def selectedCode (P : Parameters) (key : List Bool) :=
  if inRecords P key then code (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) else []

theorem selectedCode_FP (P : Parameters) (a : Access P) : selectedCode P∈FP := by
  have HP := (BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).bits_mem_FP
  have HC := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP records_FP) HP) WordList.reader_FP
  exact mem_FP_of_eq ((inRecords_FP P a).ite_mem_FP HC (constFn_mem_FP [])) (fun key => by
    simp only [Function.comp_apply,selectedCode,code,WordList.reader,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits])

noncomputable def step (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (root : List Bool) (i : ℕ) : Instruction (P.ambient root) (P.width root) where
  source := source P O root i
  source_cap := (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root)≤
      IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root)
  command := IntegralMixedCanonicalUnitRuleBits.command (source P O root i) (hn root) i (code root i) (hcap root)

noncomputable def rules (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (root : List Bool) := ((List.range (count root)).map (step P O hn hcap root)).reverse

theorem rules_length (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (root : List Bool) : (rules P O hn hcap root).length=count root := by
  simp only [rules,List.length_reverse,List.length_map,List.length_range]

theorem rules_chronological (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (root : List Bool) (b : ℕ) : chronological (rules P O hn hcap root) b=
      if _hb : b<count root then some (step P O hn hcap root b) else none := by
  unfold chronological rules
  rw [List.reverse_reverse]
  by_cases hb : b<count root
  · rw [dite_eq_left hb]
    simp only [List.getElem?_map,List.getElem?_range hb,Option.map_some]
  · rw [dite_eq_right hb]
    exact List.getElem?_eq_none (by simpa only [List.length_map,List.length_range] using Nat.le_of_not_gt hb)

noncomputable def plan (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, count root+2≤P.cap root+1) : IntegralMixedFramedHistoryFamilyBits.Plan P where
  initialSource root := source P O root 0
  initial_degree _ := rfl
  scalar_cap := hcap
  rules := rules P O hn hcap
  room root := by rw [rules_length]; exact hroom root

noncomputable def writer (P : Parameters) (key : List Bool) :=
  IntegralMixedUnitRecordCode.body (P.ambient (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key)

theorem writer_FP (P : Parameters) (a : Access P) : writer P∈FP := by
  have HA : UnaryFn (fun key => P.ambient (pairFst key)) := a.ambient.comp pairFst_mem_FP
  have HB : UnaryFn (IntegralMixedFramedHistoryFamilyBits.prefixLength P) := IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HE := mem_FP_comp (mem_FP_pair (selectedCode_FP P a)
    (mem_FP_pair (HA.replicate_mem_FP true) (BinaryFn.ofUnary HB).bits_mem_FP)) IntegralMixedUnitRecordCode.writer_FP
  exact mem_FP_of_eq HE (fun key => by simp only [Function.comp_apply,IntegralMixedUnitRecordCode.writer_packet]; rfl)

end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
