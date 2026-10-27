/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellSignLanguage
public import LeanCanny.Connectivity.AlgebraicSliceCellAdjacency
public import LeanCanny.Computation.BoundedScanPSPACE

/-! # Native cell graphs for algebraic-slice sign systems

A bounded native scan selects cells on which every indexed factor has the
requested sign. In particular, sign zero selects the common real zero set.
The scan permits a binary factor count. Both vertex selection and relative
incidence are native PSPACE decisions from the original coefficient readers.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceSystemCellGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover
open scoped Classical

def factorCellQuery (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (pairSnd z) (pairSnd (pairFst z)))
theorem factorCellQuery_FP : factorCellQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))

noncomputable def vertexLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) : Language := {q |
  q ∈ AlgebraicSliceCellLabels.language P Q ∧ ∀ i < Q.count (pairFst (pairFst q)),
    factorCellQuery (pair q (BinaryNatCode.encode i)) ∈ AlgebraicSliceCellSignLanguage.language P Q s}

private def both (z : List Bool) : Bool := decide (pairFst z = [true] ∧ pairSnd z = [true])
private theorem both_FP : (fun z => [both z]) ∈ FP :=
  ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))).flag_mem_FP

theorem vertex_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (vertexLanguage P Q s) := by
  have D := (AlgebraicSliceCellSignLanguage.decider h A ha s).precompose factorCellQuery factorCellQuery_FP
  have hn : BinaryFn (fun q => Q.count (pairFst (pairFst q))) :=
    A.count_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have S := BoundedScan.decider D _ hn.bits_mem_FP _ (fun _ => rfl)
  have V := (AlgebraicSliceCellLabels.decider h A ha).flagEvaluator
  apply (V.pairOutputs S.flagEvaluator).decider both both_FP
  intro q
  simp only [vertexLanguage, BoundedScan.language, Set.mem_ofPred_eq, Set.mem_preimage,
    both, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

noncomputable def restrictedPiece (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (s : SignType) :=
  AlgebraicSliceCellCover.restrictedPiece P Q u (fun v => ∀ i, v i = s)

theorem nonempty_iff (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) (c : Index P Q u) :
    (restrictedPiece P Q u s c).Nonempty ↔
      ∀ i : Fin (Q.count (pairFst u)), AlgebraicSliceCellSignGeometry.sign P Q u i.val c = s := by
  constructor
  · rintro ⟨x, hx⟩ i
    exact (AlgebraicSliceCellSignGeometry.packet P Q u hu i c x.val hx).trans (x.property i)
  · intro H
    obtain ⟨x, hx⟩ := Geometry.OrderedRealCells.piece_nonempty (roots P Q u) c
    have hs : x ∈ solutionSet P Q u (fun v => ∀ i, v i = s) := by
      intro i
      exact (AlgebraicSliceCellSignGeometry.packet P Q u hu i c x hx).symm.trans (H i)
    exact ⟨⟨x, hs⟩, hx⟩

theorem vertex_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) (c : Index P Q u) :
    pair u (AlgebraicSliceCellLabels.label P Q u c) ∈ vertexLanguage P Q s ↔
      (restrictedPiece P Q u s c).Nonempty := by
  rw [nonempty_iff P Q u hu s c]
  change _ ∧ _ ↔ _
  rw [and_iff_right (AlgebraicSliceCellLabels.label_valid P Q u hu c)]
  simp only [pairFst_pair]
  constructor
  · intro H i
    apply (AlgebraicSliceCellSignLanguage.packet P Q u hu i c s).mp
    simpa only [factorCellQuery, pairFst_pair, pairSnd_pair] using H i.val i.isLt
  · intro H i hi
    have h := (AlgebraicSliceCellSignLanguage.packet P Q u hu ⟨i, hi⟩ c s).mpr (H ⟨i, hi⟩)
    simpa only [factorCellQuery, pairFst_pair, pairSnd_pair] using h

noncomputable def edgeLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) (s : SignType) : Language := {q |
  AlgebraicSliceCellAdjacency.leftQuery q ∈ vertexLanguage P Q s ∧
    AlgebraicSliceCellAdjacency.rightQuery q ∈ vertexLanguage P Q s ∧ q ∈ AlgebraicSliceCellAdjacency.language P Q}

private def three (z : List Bool) : Bool := decide
  (pairFst z = [true] ∧ pairFst (pairSnd z) = [true] ∧ pairSnd (pairSnd z) = [true])
private theorem three_FP : (fun z => [three z]) ∈ FP :=
  ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    ((Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [true])).and
      (Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])))).flag_mem_FP

theorem edge_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (edgeLanguage P Q s) := by
  have L := ((vertex_decider h A ha s).precompose AlgebraicSliceCellAdjacency.leftQuery AlgebraicSliceCellAdjacency.leftQuery_FP).flagEvaluator
  have R := ((vertex_decider h A ha s).precompose AlgebraicSliceCellAdjacency.rightQuery AlgebraicSliceCellAdjacency.rightQuery_FP).flagEvaluator
  have E := (AlgebraicSliceCellAdjacency.decider h A ha).flagEvaluator
  apply (L.pairOutputs (R.pairOutputs E)).decider three three_FP
  intro q
  simp only [edgeLanguage, Set.mem_ofPred_eq, Set.mem_preimage, three, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem edge_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) (c d : Index P Q u) :
    pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈ edgeLanguage P Q s ↔
      FrontierCover.Incident (restrictedPiece P Q u s) c d := by
  change _ ↔ FrontierCover.Incident (AlgebraicSliceCellCover.restrictedPiece P Q u (fun v => ∀ i, v i = s)) c d
  rw [AlgebraicSliceCellAdjacency.restricted_incident_iff P Q u hu]
  change _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _
  simp only [AlgebraicSliceCellAdjacency.leftQuery, AlgebraicSliceCellAdjacency.rightQuery, pairFst_pair, pairSnd_pair,
    vertex_packet P Q u hu]
  rfl

theorem joinedIn_iff_graph (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) {c d : Index P Q u} {x y : solutionSet P Q u (fun v => ∀ i, v i = s)}
    (hx : x ∈ restrictedPiece P Q u s c) (hy : y ∈ restrictedPiece P Q u s d) :
    JoinedIn Set.univ x y ↔ Relation.ReflTransGen (fun c d =>
      pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈ edgeLanguage P Q s) c d := by
  have he : (fun c d => pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈
      edgeLanguage P Q s) = FrontierCover.Incident (restrictedPiece P Q u s) :=
    funext fun c => funext fun d => propext (edge_packet P Q u hu s c d)
  rw [he]
  exact AlgebraicSliceCellCover.joinedIn_iff_graph P Q u hu _ hx hy

theorem preconnected_iff_graph (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (s : SignType) :
    IsPreconnected (Set.univ : Set (solutionSet P Q u (fun v => ∀ i, v i = s))) ↔ ∀ c d : Index P Q u,
      pair u (AlgebraicSliceCellLabels.label P Q u c) ∈ vertexLanguage P Q s →
      pair u (AlgebraicSliceCellLabels.label P Q u d) ∈ vertexLanguage P Q s →
      Relation.ReflTransGen (fun c d => pair u
        (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈ edgeLanguage P Q s) c d := by
  have he : (fun c d => pair u (pair (AlgebraicSliceCellLabels.label P Q u c) (AlgebraicSliceCellLabels.label P Q u d)) ∈
      edgeLanguage P Q s) = FrontierCover.Incident (restrictedPiece P Q u s) :=
    funext fun c => funext fun d => propext (edge_packet P Q u hu s c d)
  simp only [vertex_packet P Q u hu, he]
  exact AlgebraicSliceCellCover.preconnected_iff_graph P Q u hu _

theorem vertex_mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    vertexLanguage P Q s ∈ PSPACE := (vertex_decider h A ha s).mem_PSPACE

theorem edge_mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    edgeLanguage P Q s ∈ PSPACE := (edge_decider h A ha s).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceSystemCellGraph
