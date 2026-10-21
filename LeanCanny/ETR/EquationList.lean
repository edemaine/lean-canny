/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.Grammar

/-!
# Polynomial-time recognition of lists of polynomial equations

An outer tree is an equation list exactly when the sum-of-squares writer produces
a well-formed polynomial term. This supplies an all-string input validator for
the final normalization stage, using the already certified term recognizer.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationList

open LeanCanny.Encoding
open Brackets
open SyntaxClassifier

def addSquareData (d acc : Data) : Data :=
  .l [Codec.unary 2, .l [Codec.unary 3, d, d], acc]

def accumulateData (xs : List Data) (acc : Data) : Data :=
  xs.foldl (fun a d => addSquareData d a) acc

@[simp] theorem accumulateData_cons (d : Data) (xs : List Data) (acc : Data) :
    accumulateData (d :: xs) acc = accumulateData xs (addSquareData d acc) := by
  simp only [accumulateData, List.foldl_cons]

def forestData (xs : List Data) : List Bool := (xs.map Data.toBits).flatten

theorem addSquareData_toBits (d acc : Data) :
    (addSquareData d acc).toBits = SumSquares.addSquareBits d.toBits acc.toBits := by
  simp only [addSquareData, SumSquares.addSquareBits, Codec.taggedTwo_toBits]

theorem forestData_length_ge (xs : List Data) : xs.length ≤ (forestData xs).length := by
  induction xs with
  | nil => simp [forestData]
  | cons d ds ih =>
      have hp : 0 < d.toBits.length := by simp
      simp only [forestData, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at *
      omega

theorem step_data_cons (d : Data) (xs : List Data) (acc : Data) :
    SumSquares.step (pair (forestData (d :: xs)) acc.toBits) =
      pair (forestData xs) (addSquareData d acc).toBits := by
  have hn : forestData (d :: xs) ≠ [] := by
    have hl := forestData_length_ge (d :: xs)
    intro he
    rw [he] at hl
    simp at hl
  rw [SumSquares.step, pairFst_pair, pairSnd_pair, ite_eq_right hn]
  simp only [forestData, List.map_cons, List.flatten_cons, firstNode_toBits_append,
    afterNode_toBits_append, addSquareData_toBits]

theorem iterate_data (xs : List Data) (acc : Data) (n : ℕ) (hn : xs.length ≤ n) :
    SumSquares.step^[n] (pair (forestData xs) acc.toBits) =
      pair [] (accumulateData xs acc).toBits := by
  induction xs generalizing acc n with
  | nil =>
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih (by simp)]
          simp [SumSquares.step, accumulateData]
  | cons d xs ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          rw [Function.iterate_succ_apply, step_data_cons]
          simpa only [accumulateData_cons] using
            ih (addSquareData d acc) n (by simp only [List.length_cons] at hn; omega)

theorem collapse_data (xs : List Data) :
    SumSquares.collapse (Data.l xs).toBits =
      (accumulateData xs (Term.const 0).toData).toBits := by
  rw [SumSquares.collapse, SumSquares.init, contents_toBits]
  change pairSnd (SumSquares.step^[(forestData xs).length]
    (pair (forestData xs) (Term.const 0).toData.toBits)) = _
  rw [iterate_data xs _ _ (forestData_length_ge xs), pairSnd_pair]

theorem binary_term_flag (tag : ℕ) (htag : tag = 2 ∨ tag = 3) (a b : Data) :
    (classify (Data.l [Codec.unary tag, a, b])).term = true ↔
      (classify a).term = true ∧ (classify b).term = true := by
  rw [classify, finish_summary]
  rcases htag with rfl | rfl <;>
    simp [direct, classify_tag_iff, Codec.unary]

theorem addSquareData_term_iff (d acc : Data) :
    (classify (addSquareData d acc)).term = true ↔
      (classify d).term = true ∧ (classify acc).term = true := by
  rw [addSquareData, binary_term_flag 2 (Or.inl rfl), binary_term_flag 3 (Or.inr rfl)]
  tauto

theorem accumulateData_term_iff (xs : List Data) (acc : Data) :
    (classify (accumulateData xs acc)).term = true ↔
      (∀ d ∈ xs, (classify d).term = true) ∧ (classify acc).term = true := by
  induction xs generalizing acc with
  | nil => simp [accumulateData]
  | cons d xs ih =>
      rw [accumulateData_cons, ih, addSquareData_term_iff, List.forall_mem_cons]
      tauto

theorem term_image_list (xs : List Data) :
    (∀ d ∈ xs, ∃ t : Term, d = t.toData) ↔ ∃ ts : List Term, xs = ts.map Term.toData := by
  constructor
  · intro h
    induction xs with
    | nil => exact ⟨[], rfl⟩
    | cons d ds ih =>
        obtain ⟨t, ht⟩ := h d (List.mem_cons_self ..)
        obtain ⟨ts, hts⟩ := ih (fun c hc => h c (List.mem_cons_of_mem d hc))
        exact ⟨t :: ts, by rw [ht, hts]; rfl⟩
  · rintro ⟨ts, rfl⟩
    intro d hd
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hd
    exact ⟨t, rfl⟩

def recognize (bits : List Bool) : Bool :=
  Brackets.recognize bits && Grammar.recognizeTerm (SumSquares.collapse bits)

theorem recognize_true_iff (bits : List Bool) :
    recognize bits = true ↔ ∃ ts : List Term, bits = SumSquares.listBits ts := by
  simp only [recognize, Bool.and_eq_true, Brackets.recognize_eq_true_iff]
  constructor
  · rintro ⟨⟨d, rfl⟩, ht⟩
    cases d with
    | l xs =>
        rw [collapse_data, Grammar.recognizeTerm_true_iff] at ht
        obtain ⟨t, he⟩ := ht
        have heq := Data.toBits_injective he
        have htyped : (classify (accumulateData xs (Term.const 0).toData)).term = true :=
          (classify_correct _).term.mpr ⟨t, heq⟩
        have hall := (accumulateData_term_iff xs _).mp htyped |>.1
        have hex : ∀ c ∈ xs, ∃ t : Term, c = t.toData := by
          intro c hc
          exact (classify_correct c).term.mp (hall c hc)
        obtain ⟨ts, rfl⟩ := (term_image_list xs).mp hex
        exact ⟨ts, rfl⟩
  · rintro ⟨ts, rfl⟩
    refine ⟨⟨Data.l (ts.map Term.toData), rfl⟩, ?_⟩
    rw [SumSquares.collapse_listBits]
    exact Grammar.recognizeTerm_toBits _

theorem recognize_mem_FP : (fun bits => [recognize bits]) ∈ FP := by
  have ht := mem_FP_comp SumSquares.collapse_mem_FP Grammar.recognizeTerm_mem_FP
  have hp := (FPPred.of_flag Brackets.recognize_mem_FP).and (FPPred.of_flag ht)
  refine mem_FP_of_eq hp.flag_mem_FP fun bits => ?_
  simp only [recognize, Bool.decide_and, Bool.decide_eq_true]

end LeanCanny.ETR.EquationList
