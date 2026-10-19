/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.SyntaxClassifierCorrect
public import LeanCanny.Encoding.FiniteTreeLanguage
public import Complexitylib.Classes.P.DecisionFn

/-!
# Polynomial-time recognition of the complete canonical ETR grammar

This checks syntax, including every integer payload, and makes no claim about
real satisfiability. The recognizers are executable finite-frame stack passes.
Their time certificates refer to Complexitylib's multitape `FP` and `P` classes.
-/

@[expose] public section

namespace LeanCanny.ETR.Grammar
open Complexity
open LeanCanny.Encoding
open SyntaxClassifier

/-- Check the outer brackets and inspect the classified root of the tree. -/
def recognizeWith (test : Info → Bool) (bits : List Bool) : Bool :=
  decide (Brackets.TreeCode bits) &&
    TreeFold.acceptState (fun f => test f.first) (TreeFold.run emptyFrame combine bits)

theorem recognizeWith_true_iff (test : Info → Bool) (bits : List Bool) :
    recognizeWith test bits = true ↔
      ∃ d : Data, bits = d.toBits ∧ test (classify d) = true := by
  simp only [recognizeWith, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hbrackets, htest⟩
    obtain ⟨d, rfl⟩ := (Brackets.treeCode_iff bits).mp hbrackets
    refine ⟨d, rfl, ?_⟩
    rw [TreeFold.run_toBits] at htest
    simpa only [TreeFold.acceptState, combine, prepend, ← classify_eq_fold] using htest
  · rintro ⟨d, rfl, htest⟩
    refine ⟨Brackets.treeCode_toBits d, ?_⟩
    rw [TreeFold.run_toBits]
    simpa only [TreeFold.acceptState, combine, prepend, ← classify_eq_fold] using htest

theorem recognizeWith_mem_FP (test : Info → Bool) :
    (fun bits => [recognizeWith test bits]) ∈ FP := by
  have hp := Brackets.treeCode_fppred.and
    (TreeFold.acceptRun_fppred emptyFrame combine (fun f => test f.first))
  have hflag := hp.flag_mem_FP
  refine mem_FP_of_eq hflag fun bits => ?_
  simp only [recognizeWith, Bool.decide_and, Bool.decide_eq_true]

def recognizeTerm : List Bool → Bool := recognizeWith Info.term

def recognizeFormula : List Bool → Bool := recognizeWith Info.formula

theorem recognizeTerm_true_iff (bits : List Bool) :
    recognizeTerm bits = true ↔ ∃ t : Term, bits = t.toData.toBits := by
  rw [recognizeTerm, recognizeWith_true_iff]
  constructor
  · rintro ⟨d, hd, ht⟩
    obtain ⟨t, he⟩ := (classify_correct d).term.mp ht
    exact ⟨t, hd.trans (congrArg Data.toBits he)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t.toData, ht, (classify_correct t.toData).term.mpr ⟨t, rfl⟩⟩

theorem recognizeFormula_true_iff (bits : List Bool) :
    recognizeFormula bits = true ↔ ∃ p : Formula, bits = p.encode := by
  rw [recognizeFormula, recognizeWith_true_iff]
  constructor
  · rintro ⟨d, hd, ht⟩
    obtain ⟨p, he⟩ := (classify_correct d).formula.mp ht
    exact ⟨p, hd.trans (congrArg Data.toBits he)⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.toData, hp, (classify_correct p.toData).formula.mpr ⟨p, rfl⟩⟩

theorem recognizeTerm_mem_FP : (fun bits => [recognizeTerm bits]) ∈ FP :=
  recognizeWith_mem_FP Info.term

theorem recognizeFormula_mem_FP : (fun bits => [recognizeFormula bits]) ∈ FP :=
  recognizeWith_mem_FP Info.formula

@[simp] theorem recognizeTerm_toBits (t : Term) : recognizeTerm t.toData.toBits = true :=
  (recognizeTerm_true_iff _).mpr ⟨t, rfl⟩

@[simp] theorem recognizeFormula_encode (p : Formula) : recognizeFormula p.encode = true :=
  (recognizeFormula_true_iff _).mpr ⟨p, rfl⟩

/-- The fast checker agrees with successful parsing by the original canonical decoder. -/
theorem recognizeFormula_iff_decode (bits : List Bool) :
    recognizeFormula bits = true ↔ ∃ p : Formula, Formula.decode bits = some p := by
  rw [recognizeFormula_true_iff]
  simp only [Formula.decode_eq_some_iff]

def termLanguage : Language := {bits | ∃ t : Term, bits = t.toData.toBits}

def formulaLanguage : Language := {bits | ∃ p : Formula, bits = p.encode}

theorem termLanguage_mem_P : termLanguage ∈ P :=
  mem_P_of_decisionFn_bool recognizeTerm_mem_FP (fun bits => (recognizeTerm_true_iff bits).symm)

theorem formulaLanguage_mem_P : formulaLanguage ∈ P :=
  mem_P_of_decisionFn_bool recognizeFormula_mem_FP (fun bits => (recognizeFormula_true_iff bits).symm)

end LeanCanny.ETR.Grammar
