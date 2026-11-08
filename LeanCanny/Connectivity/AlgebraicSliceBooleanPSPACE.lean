/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceBooleanCells
public import LeanCanny.Connectivity.AlgebraicSliceCellAdjacency
public import LeanCanny.Connectivity.FiniteLabelCover

/-! # Native connectivity of Boolean-defined algebraic slices

Boolean cell selection and the exact neighbor test construct the relative
incidence graph. Unused labels denote empty pieces. The resulting bit
frontier cover and native graph algorithm decide connectivity of the actual
circuit-defined solution set, without a supplied cover or adjacency oracle.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceBooleanPSPACE
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover AlgebraicSliceBooleanAtoms
open Turing.MultiTapeTM
open scoped Classical

noncomputable def edgeLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : Language := {q |
  AlgebraicSliceCellAdjacency.leftQuery q ∈ AlgebraicSliceBooleanCells.language P Q S ∧
    AlgebraicSliceCellAdjacency.rightQuery q ∈ AlgebraicSliceBooleanCells.language P Q S ∧
      q ∈ AlgebraicSliceCellAdjacency.language P Q}

private def three (z : List Bool) : Bool := decide
  (pairFst z = [true] ∧ pairFst (pairSnd z) = [true] ∧ pairSnd (pairSnd z) = [true])
private theorem three_FP : (fun z => [three z]) ∈ FP :=
  ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    ((Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [true])).and
      (Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])))).flag_mem_FP

theorem edge_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceDecider (edgeLanguage P Q S) := by
  have L := ((AlgebraicSliceBooleanCells.decider h A ha S B).precompose
    AlgebraicSliceCellAdjacency.leftQuery AlgebraicSliceCellAdjacency.leftQuery_FP).flagEvaluator
  have R := ((AlgebraicSliceBooleanCells.decider h A ha S B).precompose
    AlgebraicSliceCellAdjacency.rightQuery AlgebraicSliceCellAdjacency.rightQuery_FP).flagEvaluator
  have E := (AlgebraicSliceCellAdjacency.decider h A ha).flagEvaluator
  apply (L.pairOutputs (R.pairOutputs E)).decider three three_FP
  intro q
  simp only [edgeLanguage, Set.mem_ofPred_eq, Set.mem_preimage, three, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem edge_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c d : Index P Q u) :
    pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈ edgeLanguage P Q S ↔
      FrontierCover.Incident (AlgebraicSliceBooleanCells.restrictedPiece P Q S u) c d := by
  change _ ∧ _ ∧ _ ↔ _
  simp only [AlgebraicSliceCellAdjacency.leftQuery, AlgebraicSliceCellAdjacency.rightQuery, pairFst_pair, pairSnd_pair,
    AlgebraicSliceBooleanCells.packet P Q S u hu]
  exact (AlgebraicSliceCellAdjacency.restricted_incident_iff P Q u hu (AlgebraicSliceBooleanCells.truth S (pairFst u)) c d).symm

noncomputable def vertex (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u word : List Bool) : Bool :=
  decide (pair u word ∈ AlgebraicSliceBooleanCells.language P Q S)
noncomputable def edge (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u a b : List Bool) : Bool :=
  decide (pair u (pair a b) ∈ edgeLanguage P Q S)

theorem vertex_spec (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (word : List Bool) : vertex P Q S u word = true ↔ ∃ c : Index P Q u,
      AlgebraicSliceCellLabels.label P Q u c = word ∧ (AlgebraicSliceBooleanCells.restrictedPiece P Q S u c).Nonempty := by
  simp only [vertex, decide_eq_true_eq]
  constructor
  · intro H
    obtain ⟨c, hc, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u word H.1
    refine ⟨c, hc, (AlgebraicSliceBooleanCells.packet P Q S u hu c).mp ?_⟩
    simpa only [hc] using H
  · rintro ⟨c, rfl, hc⟩
    exact (AlgebraicSliceBooleanCells.packet P Q S u hu c).mpr hc

theorem edge_spec (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (a b : List Bool) : edge P Q S u a b = true ↔ ∃ c d : Index P Q u,
      AlgebraicSliceCellLabels.label P Q u c = a ∧ AlgebraicSliceCellLabels.label P Q u d = b ∧
        FrontierCover.Incident (AlgebraicSliceBooleanCells.restrictedPiece P Q S u) c d := by
  simp only [edge, decide_eq_true_eq]
  constructor
  · intro H
    have ha : pair u a ∈ AlgebraicSliceBooleanCells.language P Q S := by
      simpa only [AlgebraicSliceCellAdjacency.leftQuery, pairFst_pair, pairSnd_pair] using H.1
    have hb : pair u b ∈ AlgebraicSliceBooleanCells.language P Q S := by
      simpa only [AlgebraicSliceCellAdjacency.rightQuery, pairFst_pair, pairSnd_pair] using H.2.1
    obtain ⟨c, hc, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u a ha.1
    obtain ⟨d, hd, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u b hb.1
    refine ⟨c, d, hc, hd, (edge_packet P Q S u hu c d).mp ?_⟩
    simpa only [hc, hd] using H
  · rintro ⟨c, d, rfl, rfl, h⟩
    exact (edge_packet P Q S u hu c d).mpr h

noncomputable def cover (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P) :
    BitFrontierCover (solutionSet P Q u (AlgebraicSliceBooleanCells.truth S (pairFst u))) (labelWidth Q u)
      (edge P Q S u) (vertex P Q S u) :=
  FiniteLabelCover.cover (labelWidth Q u) (AlgebraicSliceCellLabels.label P Q u)
    (AlgebraicSliceCellLabels.label_injective P Q u) (AlgebraicSliceCellLabels.label_length P Q u)
    (AlgebraicSliceBooleanCells.restrictedPiece P Q S u)
    (AlgebraicSliceCellCover.cover P Q u _) (AlgebraicSliceBooleanCells.accessible P Q S u hu)
    (edge P Q S u) (vertex P Q S u) (vertex_spec P Q S u hu) (edge_spec P Q S u hu)

theorem piece_label (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) :
    (cover P Q S u hu).piece ⟨AlgebraicSliceCellLabels.label P Q u c, AlgebraicSliceCellLabels.label_length P Q u c⟩ =
      AlgebraicSliceBooleanCells.restrictedPiece P Q S u c :=
  FiniteLabelCover.piece_label _ (AlgebraicSliceCellLabels.label_injective P Q u) _ c

theorem edge_computable {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    ComputableInPolySpace (fun p : List Bool × List Bool × List Bool => edge P Q S p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have hq := pair_computable hc (pair_computable hr.fst' hr.snd')
  exact (edge_decider h A ha S B).computable.comp (.of_tidyPolyTime hq)

theorem vertex_computable {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    ComputableInPolySpace (fun p : List Bool × List Bool => vertex P Q S p.1 p.2)
      (encPair encBits encBits) encBool := by
  have hq := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)
  exact (AlgebraicSliceBooleanCells.decider h A ha S B).computable.comp (.of_tidyPolyTime hq)

noncomputable def connectedLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : Language := {u |
  u ∈ valid P ∧ IsPreconnected (univ : Set (solutionSet P Q u (AlgebraicSliceBooleanCells.truth S (pairFst u))))}

theorem connected_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceDecider (connectedLanguage P Q S) := by
  have G := ImplicitGraph.connected_computable (edge_computable h A ha S B) (vertex_computable h A ha S B) (labelWidth_unary A)
  have F : ComputableInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_tidyPolyTime (ComputableTidilyInPolyTime.const false)
  apply SpaceDecider.of_computable ((valid_decider h ha).computable.ite G F)
  intro u
  by_cases hu : u ∈ valid P
  · simp only [connectedLanguage, Set.mem_ofPred_eq, hu, true_and, decide_true, ite_true, decide_eq_true_eq]
    exact (cover P Q S u hu).isPreconnected_iff_connected
  · simp only [connectedLanguage, Set.mem_ofPred_eq, hu, false_and, decide_false, Bool.false_eq_true, ite_false]

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    connectedLanguage P Q S ∈ PSPACE := (connected_decider h A ha S B).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceBooleanPSPACE
