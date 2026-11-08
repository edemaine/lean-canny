/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceBooleanPSPACE

/-! # Native cell-label paths in Boolean-defined algebraic slices

Both endpoint widths and the algebraic base are validated. Native guarded
reachability in the constructed graph is exactly path connection in the
actual circuit-defined real solution set, including excluded root points.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceBooleanReachability
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover AlgebraicSliceBooleanAtoms AlgebraicSliceBooleanPSPACE
open Turing.MultiTapeTM
open scoped Classical

def leftWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def rightWord (q : List Bool) : List Bool := pairSnd (pairSnd q)

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : Language := {q |
  pairFst q ∈ valid P ∧ (leftWord q).length = labelWidth Q (pairFst q) ∧
    (rightWord q).length = labelWidth Q (pairFst q) ∧
      ImplicitGraph.Reachable (edge P Q S (pairFst q)) (vertex P Q S (pairFst q))
        (labelWidth Q (pairFst q)) (leftWord q) (rightWord q)}

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceDecider (language P Q S) := by
  have hp := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have he := (edge_computable h A ha S B).comp
    (.of_tidyPolyTime (((FP.computable pairFst_mem_FP).comp hp).prod hr))
  have hq := ComputableTidilyInPolyTime.fst encBits encBits
  have ht := ComputableTidilyInPolyTime.snd encBits encBits
  have hv := (vertex_computable h A ha S B).comp
    (.of_tidyPolyTime (((FP.computable pairFst_mem_FP).comp hq).prod ht))
  have hw : UnaryFn (fun q => labelWidth Q (pairFst q)) := (labelWidth_unary A).comp pairFst_mem_FP
  have hl : leftWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hd : rightWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hs := ImplicitGraph.word_computable hw (BinaryFn.fromBits hl)
  have ht' := ImplicitGraph.word_computable hw (BinaryFn.fromBits hd)
  have G := ImplicitGraph.reachable_computable (edge := fun q => edge P Q S (pairFst q))
    (valid := fun q => vertex P Q S (pairFst q)) he hv hw (.of_tidyPolyTime hs) (.of_tidyPolyTime ht')
    (fun _ => ImplicitGraph.length_word _ _) (fun _ => ImplicitGraph.length_word _ _)
  have HG := (FPPred.eq (UnaryFn.length hl) hw).and (FPPred.eq (UnaryFn.length hd) hw)
  have F : ComputableInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_tidyPolyTime (ComputableTidilyInPolyTime.const false)
  have D := (valid_decider h ha).precompose pairFst pairFst_mem_FP
  apply SpaceDecider.of_computable (D.computable.ite ((ComputableInPolySpace.of_tidyPolyTime HG.computable).ite G F) F)
  intro q
  by_cases hu : pairFst q ∈ valid P
  · by_cases hwidth : (leftWord q).length = labelWidth Q (pairFst q) ∧ (rightWord q).length = labelWidth Q (pairFst q)
    · have hs' : ImplicitGraph.word (labelWidth Q (pairFst q)) (Nat.fromBitsLE (leftWord q)) = leftWord q := by
        rw [← hwidth.1, ImplicitGraph.word_fromBitsLE]
      have ht'' : ImplicitGraph.word (labelWidth Q (pairFst q)) (Nat.fromBitsLE (rightWord q)) = rightWord q := by
        rw [← hwidth.2, ImplicitGraph.word_fromBitsLE]
      simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, hu, hwidth.1, hwidth.2, true_and,
        decide_true, ite_true, decide_eq_true_eq, hs', ht'']
    · simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, hu, decide_true, ite_true,
        hwidth, decide_false, ite_false, Bool.false_eq_true]
      tauto
  · simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, hu, false_and, decide_false, ite_false, Bool.false_eq_true]

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c d : Index P Q u) {x y : solutionSet P Q u (AlgebraicSliceBooleanCells.truth S (pairFst u))}
    (hx : x ∈ AlgebraicSliceBooleanCells.restrictedPiece P Q S u c)
    (hy : y ∈ AlgebraicSliceBooleanCells.restrictedPiece P Q S u d) :
    pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈ language P Q S ↔
      JoinedIn univ x y := by
  change _ ∧ _ ∧ _ ∧ _ ↔ _
  simp only [leftWord, rightWord, pairFst_pair, pairSnd_pair, hu, AlgebraicSliceCellLabels.label_length, true_and]
  have hx' : x ∈ (cover P Q S u hu).piece
      ⟨AlgebraicSliceCellLabels.label P Q u c, AlgebraicSliceCellLabels.label_length P Q u c⟩ := by
    rw [piece_label]
    exact hx
  have hy' : y ∈ (cover P Q S u hu).piece
      ⟨AlgebraicSliceCellLabels.label P Q u d, AlgebraicSliceCellLabels.label_length P Q u d⟩ := by
    rw [piece_label]
    exact hy
  exact ((cover P Q S u hu).joinedIn_iff_reachable (AlgebraicSliceCellLabels.label_length P Q u c)
    (AlgebraicSliceCellLabels.label_length P Q u d) hx' hy').symm

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u a b : List Bool) (hu : u ∉ valid P) :
    pair u (pair a b) ∉ language P Q S := by
  intro H
  exact hu (by simpa only [pairFst_pair] using H.1)

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    language P Q S ∈ PSPACE := (decider h A ha S B).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceBooleanReachability
