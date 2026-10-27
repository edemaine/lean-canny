/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellCover

/-! # Short native labels for the constructed real cells

Point cells precede gap cells in a consecutive binary numbering. The fixed
word width follows from the original indexed degree and count controls.
Validity checks the base root and computes the actual distinct-root count
natively. Every valid word labels exactly one cell; at valid base roots,
every cell has such a word.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellLabels
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover
open scoped Classical

private theorem word_value (w n : ℕ) (hn : n < 2 ^ w) : Nat.fromBitsLE (ImplicitGraph.word w n) = n := by
  have H := FixedWidthNatVector.decode_block 1 w (fun _ => n) 0 (by decide) hn
  simp only [Nat.zero_mul, List.drop_zero] at H
  change Nat.fromBitsLE ((ImplicitGraph.word w n).take w) = n at H
  simpa only [List.take_of_length_le (ImplicitGraph.length_word w n).le] using H

noncomputable def label (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : Index P Q u) : List Bool :=
  ImplicitGraph.word (labelWidth Q u) (Geometry.OrderedRealCells.code (roots P Q u) i)

theorem code_lt_width (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : Index P Q u) :
    Geometry.OrderedRealCells.code (roots P Q u) i < 2 ^ labelWidth Q u := by
  have H : Geometry.OrderedRealCells.code (roots P Q u) i < Fintype.card (Index P Q u) := by
    simpa only [Geometry.OrderedRealCells.card_index] using Geometry.OrderedRealCells.code_lt (roots P Q u) i
  exact H.trans (card_lt_pow_width P Q u)

theorem label_length (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : Index P Q u) :
    (label P Q u i).length = labelWidth Q u := ImplicitGraph.length_word _ _

theorem label_value (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : Index P Q u) :
    Nat.fromBitsLE (label P Q u i) = Geometry.OrderedRealCells.code (roots P Q u) i :=
  word_value _ _ (code_lt_width P Q u i)

theorem label_injective (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    Function.Injective (label P Q u) := by
  intro i j hij
  apply Geometry.OrderedRealCells.code_injective (roots P Q u)
  have H := congrArg Nat.fromBitsLE hij
  simpa only [label_value] using H

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) : Language := {q |
  pairFst q ∈ valid P ∧ (pairSnd q).length = labelWidth Q (pairFst q) ∧
    Nat.fromBitsLE (pairSnd q) < 2 * BoundedAlgebraicSliceRootProduct.count P Q (pairFst q) + 1}

noncomputable def accept (Q : BivariateQueryProductBits.Family) (z : List Bool) : Bool := decide
  (pairSnd (pairSnd z) = [true] ∧ (pairSnd (pairFst z)).length = labelWidth Q (pairFst (pairFst z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < 2 * Nat.fromBitsLE (pairFst (pairSnd z)) + 1)

theorem accept_FP {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) :
    (fun z => [accept Q z]) ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have he := FPPred.eq (UnaryFn.length hw)
    ((labelWidth_unary A).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  have hn := ((BinaryFn.const 2).mul (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))).add (BinaryFn.const 1)
  have hv := Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])
  exact (hv.and (he.and ((BinaryFn.fromBits hw).lt hn))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (language P Q) := by
  have N := (BoundedAlgebraicSliceRootProduct.count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have V := ((valid_decider h ha).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (N.pairOutputs V).withInput.decider (accept Q) (accept_FP A)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, List.cons.injEq, and_true, decide_eq_true_eq]

theorem label_valid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) (i : Index P Q u) :
    pair u (label P Q u i) ∈ language P Q := by
  change _ ∧ _ ∧ _
  rw [pairFst_pair, pairSnd_pair, label_length, label_value]
  refine ⟨hu, rfl, ?_⟩
  have H := Geometry.OrderedRealCells.code_lt (roots P Q u) i
  exact H

theorem exists_unique_label (P : Readers) (Q : BivariateQueryProductBits.Family) (u word : List Bool)
    (hw : pair u word ∈ language P Q) : ∃! i : Index P Q u, label P Q u i = word := by
  change _ ∧ _ ∧ _ at hw
  simp only [pairFst_pair, pairSnd_pair] at hw
  have hn : Nat.fromBitsLE word < 2 * (roots P Q u).card + 1 := hw.2.2
  let i := Geometry.OrderedRealCells.decode (roots P Q u) (Nat.fromBitsLE word) hn
  have hi : label P Q u i = word := by
    rw [label, Geometry.OrderedRealCells.code_decode, ← hw.2.1, ImplicitGraph.word_fromBitsLE]
  exact ⟨i, hi, fun j hj => label_injective P Q u (hj.trans hi.symm)⟩

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (u word : List Bool) (hu : u ∉ valid P) :
    pair u word ∉ language P Q := by
  intro H
  exact hu (by simpa only [pairFst_pair] using H.1)

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    language P Q ∈ PSPACE := (decider h A ha).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceCellLabels
