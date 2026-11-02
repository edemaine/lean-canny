/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitSource
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerPrelude
public import LeanCanny.Encoding.WordListRecords
/-! # An actual initial bank followed by changing-source unit records

The root stores its original input first and a word-list of chronological
original records next. The retained bank is interpreted only by the existing
framed interpreter; the body decoder never inspects that interpreted bank.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def input (root : List Bool) := pairFst root
def records (root : List Bool) := pairFst (pairSnd root)
def count (root : List Bool) := WordListRecords.count (records root)
def code (root : List Bool) (i : ℕ) := WordList.get (records root) i

theorem input_FP : input ∈ FP := pairFst_mem_FP
theorem records_FP : records ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem count_unary : UnaryFn count := WordListRecords.count_unary.comp records_FP

def seedCount (F : Inputs) (root : List Bool) := FlatAffineExceptionalBankSource.births F (input root)
theorem seedCount_unary {F : Inputs} (hF : F.Access) : UnaryFn (seedCount F) :=
  (FlatAffineExceptionalBankSource.births_unary hF).comp input_FP

def inLater (P : Parameters) (F : Inputs) (key : List Bool) : Prop :=
  seedCount F (pairFst key) ≤ IntegralMixedFramedHistoryFamilyBits.prefixLength P key ∧
    IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key) < count (pairFst key)

noncomputable def selectedCode (P : Parameters) (F : Inputs) (key : List Bool) :=
  if inLater P F key then code (pairFst key)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)) else []

theorem selectedCode_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : selectedCode P F ∈ FP := by
  have HB : UnaryFn (fun key => seedCount F (pairFst key)) := (seedCount_unary hF).comp pairFst_mem_FP
  have HP : UnaryFn (IntegralMixedFramedHistoryFamilyBits.prefixLength P) := IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HN : UnaryFn (fun key => count (pairFst key)) := count_unary.comp pairFst_mem_FP
  have HI : BinaryFn (fun key => IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)) :=
    (BinaryFn.ofUnary HP).sub (BinaryFn.ofUnary HB)
  have HS : FPPred (inLater P F) := (FPPred.le HB HP).and (HI.lt (BinaryFn.ofUnary HN))
  have HC := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP records_FP) HI.bits_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq (HS.ite_mem_FP HC (constFn_mem_FP [])) (fun key => by
    simp only [Function.comp_apply, selectedCode, code, WordList.reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

noncomputable def step (P : Parameters) (O : Originals P) (F : Inputs)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (root : List Bool) (i : ℕ) : Instruction (P.ambient root) (P.width root) where
  source := source P O root (seedCount F root+i)
  source_cap := (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root) ≤
      IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root)
  command := IntegralMixedCanonicalUnitRuleBits.command (source P O root (seedCount F root+i))
    (hn root) (seedCount F root+i) (code root i) (hcap root)

noncomputable def later (P : Parameters) (O : Originals P) (F : Inputs)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (root : List Bool) := ((List.range (count root)).map (step P O F hn hcap root)).reverse

theorem later_length (P : Parameters) (O : Originals P) (F : Inputs)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (root : List Bool) : (later P O F hn hcap root).length=count root := by
  simp only [later, List.length_reverse, List.length_map, List.length_range]

theorem later_chronological (P : Parameters) (O : Originals P) (F : Inputs)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (root : List Bool) (b : ℕ) : chronological (later P O F hn hcap root) b =
      if _hb : b<count root then some (step P O F hn hcap root b) else none := by
  unfold chronological later
  rw [List.reverse_reverse]
  by_cases hb : b<count root
  · rw [dite_eq_left hb]
    simp only [List.getElem?_map, List.getElem?_range hb, Option.map_some]
  · rw [dite_eq_right hb]
    exact List.getElem?_eq_none (by simpa only [List.length_map, List.length_range] using Nat.le_of_not_gt hb)

noncomputable def plan (P : Parameters) (O : Originals P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root) ≤ P.width root)
    (hroom : ∀ root, count root+seedCount F root+2 ≤ P.cap root+1) : IntegralMixedFramedHistoryFamilyBits.Plan P :=
  let base := IntegralMixedCanonicalUnitSourceBits.seed P O hcap (fun root => by have H:=hroom root; omega)
  FlatAffineExceptionalFramedIntegerPrelude.plan P base F C h input (later P O F hn hcap) hW
    (fun root => by rw [later_length]; exact hroom root)

noncomputable def writer (P : Parameters) (F : Inputs) (key : List Bool) :=
  IntegralMixedUnitRecordCode.body (P.ambient (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key)

theorem writer_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : writer P F ∈ FP := by
  have HA : UnaryFn (fun key => P.ambient (pairFst key)) := a.ambient.comp pairFst_mem_FP
  have HB : UnaryFn (IntegralMixedFramedHistoryFamilyBits.prefixLength P) := IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HE := mem_FP_comp (mem_FP_pair (selectedCode_FP P a hF) (mem_FP_pair (HA.replicate_mem_FP true) (BinaryFn.ofUnary HB).bits_mem_FP))
    IntegralMixedUnitRecordCode.writer_FP
  exact mem_FP_of_eq HE (fun key => by simp only [Function.comp_apply, IntegralMixedUnitRecordCode.writer_packet]; rfl)
end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
