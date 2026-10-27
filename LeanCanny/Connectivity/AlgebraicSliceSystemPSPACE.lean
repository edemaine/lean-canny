/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceSystemCellGraph
public import LeanCanny.Connectivity.FiniteLabelCover

/-! # Native connectivity for constructed algebraic-slice sign systems

Unused bit labels denote empty pieces. The resulting accessible cover has
native validity and relative-incidence tests, so the native implicit-graph
algorithm decides connectivity of the actual solution set. Invalid algebraic
base queries are rejected, including when the factor family is empty.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceSystemPSPACE
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover AlgebraicSliceSystemCellGraph
open Turing.MultiTapeTM
open scoped Classical

noncomputable def vertex (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) (u word : List Bool) : Bool :=
  decide (pair u word ∈ vertexLanguage P Q s)
noncomputable def edge (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) (u a b : List Bool) : Bool :=
  decide (pair u (pair a b) ∈ edgeLanguage P Q s)

theorem vertex_spec (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) (word : List Bool) :
    vertex P Q s u word = true ↔ ∃ c : Index P Q u,
      AlgebraicSliceCellLabels.label P Q u c = word ∧ (AlgebraicSliceSystemCellGraph.restrictedPiece P Q u s c).Nonempty := by
  simp only [vertex, decide_eq_true_eq]
  constructor
  · intro H
    obtain ⟨c, hc, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u word H.1
    refine ⟨c, hc, (vertex_packet P Q u hu s c).mp ?_⟩
    simpa only [hc] using H
  · rintro ⟨c, rfl, hc⟩
    exact (vertex_packet P Q u hu s c).mpr hc

theorem edge_spec (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) (a b : List Bool) :
    edge P Q s u a b = true ↔ ∃ c d : Index P Q u,
      AlgebraicSliceCellLabels.label P Q u c = a ∧ AlgebraicSliceCellLabels.label P Q u d = b ∧
        FrontierCover.Incident (AlgebraicSliceSystemCellGraph.restrictedPiece P Q u s) c d := by
  simp only [edge, decide_eq_true_eq]
  constructor
  · intro H
    have ha : pair u a ∈ vertexLanguage P Q s := by
      simpa only [AlgebraicSliceCellAdjacency.leftQuery, pairFst_pair, pairSnd_pair] using H.1
    have hb : pair u b ∈ vertexLanguage P Q s := by
      simpa only [AlgebraicSliceCellAdjacency.rightQuery, pairFst_pair, pairSnd_pair] using H.2.1
    obtain ⟨c, hc, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u a ha.1
    obtain ⟨d, hd, _⟩ := AlgebraicSliceCellLabels.exists_unique_label P Q u b hb.1
    refine ⟨c, d, hc, hd, (edge_packet P Q u hu s c d).mp ?_⟩
    simpa only [hc, hd] using H
  · rintro ⟨c, d, rfl, rfl, h⟩
    exact (edge_packet P Q u hu s c d).mpr h

noncomputable def cover (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) (s : SignType) :
    BitFrontierCover (solutionSet P Q u (fun v => ∀ i, v i = s)) (labelWidth Q u) (edge P Q s u) (vertex P Q s u) :=
  FiniteLabelCover.cover (labelWidth Q u) (AlgebraicSliceCellLabels.label P Q u)
    (AlgebraicSliceCellLabels.label_injective P Q u) (AlgebraicSliceCellLabels.label_length P Q u)
    (AlgebraicSliceSystemCellGraph.restrictedPiece P Q u s)
    (AlgebraicSliceCellCover.cover P Q u _) (AlgebraicSliceCellCover.accessible P Q u hu _)
    (edge P Q s u) (vertex P Q s u) (vertex_spec P Q u hu s) (edge_spec P Q u hu s)

theorem piece_label (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) (s : SignType)
    (c : Index P Q u) :
    (cover P Q u hu s).piece ⟨AlgebraicSliceCellLabels.label P Q u c, AlgebraicSliceCellLabels.label_length P Q u c⟩ =
      AlgebraicSliceSystemCellGraph.restrictedPiece P Q u s c :=
  FiniteLabelCover.piece_label _ (AlgebraicSliceCellLabels.label_injective P Q u) _ c

theorem edge_computable {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    ComputableTidilyInPolySpace (fun p : List Bool × List Bool × List Bool => edge P Q s p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have hq := pair_computable hc (pair_computable hr.fst' hr.snd')
  exact (edge_decider h A ha s).computable.comp (.of_polyTime hq)

theorem vertex_computable {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    ComputableTidilyInPolySpace (fun p : List Bool × List Bool => vertex P Q s p.1 p.2)
      (encPair encBits encBits) encBool := by
  have hq := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)
  exact (vertex_decider h A ha s).computable.comp (.of_polyTime hq)

noncomputable def connectedLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) : Language := {u |
  u ∈ valid P ∧ IsPreconnected (univ : Set (solutionSet P Q u (fun v => ∀ i, v i = s)))}

theorem connected_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (connectedLanguage P Q s) := by
  have G := ImplicitGraph.connected_computable (edge_computable h A ha s) (vertex_computable h A ha s) (labelWidth_unary A)
  have F : ComputableTidilyInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  apply SpaceDecider.of_computable ((valid_decider h ha).computable.ite G F)
  intro u
  by_cases hu : u ∈ valid P
  · simp only [connectedLanguage, Set.mem_ofPred_eq, hu, true_and, decide_true, ite_true, decide_eq_true_eq]
    exact (cover P Q u hu s).isPreconnected_iff_connected
  · simp only [connectedLanguage, Set.mem_ofPred_eq, hu, false_and, decide_false, Bool.false_eq_true, ite_false]

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    connectedLanguage P Q s ∈ PSPACE := (connected_decider h A ha s).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceSystemPSPACE
