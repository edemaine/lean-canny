/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellSigns

/-! # Validated native sign tests for complete real cells

All queries validate the algebraic base, cell label, and factor index.
Accepted tags describe the factor's sign on the entire requested cell.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellSignLanguage
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover
open scoped Classical

def cellQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem cellQuery_FP : cellQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) : Language := {q |
  cellQuery q ∈ AlgebraicSliceCellLabels.language P Q ∧
    Nat.fromBitsLE (pairFst (pairSnd q)) < Q.count (pairFst (pairFst q)) ∧
      AlgebraicSliceCellSigns.value P Q q = InfinitesimalSign.encode s}

def accept (Q : BivariateQueryProductBits.Family) (s : SignType) (z : List Bool) : Bool := decide
  (pairSnd (pairSnd z) = [true] ∧
    Nat.fromBitsLE (pairFst (pairSnd (pairFst z))) < Q.count (pairFst (pairFst (pairFst z))) ∧
      pairFst (pairSnd z) = InfinitesimalSign.encode s)

theorem accept_FP {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) (s : SignType) :
    (fun z => [accept Q s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hn : BinaryFn (fun z => Q.count (pairFst (pairFst (pairFst z)))) := A.count_binary.comp hc
  have hv := Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])
  have hs := Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP (InfinitesimalSign.encode s))
  exact (hv.and ((hi.lt hn).and hs)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (language P Q s) := by
  have V := AlgebraicSliceCellSigns.evaluator h A ha
  have W := ((AlgebraicSliceCellLabels.decider h A ha).precompose cellQuery cellQuery_FP).flagEvaluator
  apply (V.pairOutputs W).withInput.decider (accept Q s) (accept_FP A s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (c : Index P Q u) (s : SignType) :
    pair u (pair (BinaryNatCode.encode i.val) (AlgebraicSliceCellLabels.label P Q u c)) ∈ language P Q s ↔
      AlgebraicSliceCellSignGeometry.sign P Q u i.val c = s := by
  change _ ∧ _ ∧ _ ↔ _
  have hb : Nat.fromBitsLE (BinaryNatCode.encode i.val) = i.val := Nat.fromBitsLE_bits _
  simp only [cellQuery, pairFst_pair, pairSnd_pair, hb, i.isLt,
    and_iff_right (AlgebraicSliceCellLabels.label_valid P Q u hu c), true_and, AlgebraicSliceCellSigns.value_packet]
  generalize AlgebraicSliceCellSignGeometry.sign P Q u i.val c = v
  cases v <;> cases s <;> decide

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (u i c : List Bool) (s : SignType) (hu : u ∉ valid P) :
    pair u (pair i c) ∉ language P Q s := by
  intro H
  exact AlgebraicSliceCellLabels.invalid_base P Q u c hu (by simpa only [cellQuery, pairFst_pair, pairSnd_pair] using H.1)

theorem invalid_factor (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) (s : SignType)
    (hi : Q.count (pairFst (pairFst q)) ≤ Nat.fromBitsLE (pairFst (pairSnd q))) :
    q ∉ language P Q s := fun H => (Nat.not_lt_of_ge hi) H.2.1

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    language P Q s ∈ PSPACE := (decider h A ha s).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceCellSignLanguage
