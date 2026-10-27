/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellLabels
public import LeanCanny.Connectivity.OrderedRealCellRestrictedIncidence

/-! # Native incidence tests for complete algebraic-slice cell covers

The native routine validates both labels and the base root, computes the
actual root count, and compares cell indices. Its result is exactly ambient
frontier incidence. For a sign-defined subset, relative incidence additionally
requires both cells to be selected by the truth predicate.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellAdjacency
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover OrderedRealCellIncidence
open scoped Classical

def leftQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))

theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) : Language := {q |
  leftQuery q ∈ AlgebraicSliceCellLabels.language P Q ∧
    rightQuery q ∈ AlgebraicSliceCellLabels.language P Q ∧
      CodeAdjacent (BoundedAlgebraicSliceRootProduct.count P Q (pairFst q))
        (Nat.fromBitsLE (pairFst (pairSnd q))) (Nat.fromBitsLE (pairSnd (pairSnd q)))}

noncomputable def accept (z : List Bool) : Bool := decide
  (pairFst (pairSnd (pairSnd z)) = [true] ∧ pairSnd (pairSnd (pairSnd z)) = [true] ∧
    CodeAdjacent (Nat.fromBitsLE (pairFst (pairSnd z)))
      (Nat.fromBitsLE (pairFst (pairSnd (pairFst z))))
      (Nat.fromBitsLE (pairSnd (pairSnd (pairFst z)))))

theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hn := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hw := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hl := BinaryFn.fromBits (mem_FP_comp hw pairFst_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp hw pairSnd_mem_FP)
  have hf := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hv := Brackets.stringEq_fppred (mem_FP_comp hf pairFst_mem_FP) (constFn_mem_FP [true])
  have hu := Brackets.stringEq_fppred (mem_FP_comp hf pairSnd_mem_FP) (constFn_mem_FP [true])
  have hleft := (hl.lt hn).and ((hn.le hr).and
    ((hr.eq (hn.add hl)).or (hr.eq ((hn.add hl).add (BinaryFn.const 1)))))
  have hright := (hr.lt hn).and ((hn.le hl).and
    ((hl.eq (hn.add hr)).or (hl.eq ((hn.add hr).add (BinaryFn.const 1)))))
  have hc : FPPred (fun z => CodeAdjacent (Nat.fromBitsLE (pairFst (pairSnd z)))
      (Nat.fromBitsLE (pairFst (pairSnd (pairFst z))))
      (Nat.fromBitsLE (pairSnd (pairSnd (pairFst z))))) := (hl.eq hr).or (hleft.or hright)
  exact (hv.and (hu.and hc)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (language P Q) := by
  have N := (BoundedAlgebraicSliceRootProduct.count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have L := ((AlgebraicSliceCellLabels.decider h A ha).precompose leftQuery leftQuery_FP).flagEvaluator
  have R := ((AlgebraicSliceCellLabels.decider h A ha).precompose rightQuery rightQuery_FP).flagEvaluator
  apply (N.pairOutputs (L.pairOutputs R)).withInput.decider accept accept_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, List.cons.injEq, and_true, decide_eq_true_eq]

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i j : Index P Q u) :
    pair u (pair (AlgebraicSliceCellLabels.label P Q u i) (AlgebraicSliceCellLabels.label P Q u j)) ∈ language P Q ↔
      FrontierCover.Incident (piece P Q u) i j := by
  change _ ∧ _ ∧ _ ↔ _
  simp only [leftQuery, rightQuery, pairFst_pair, pairSnd_pair, AlgebraicSliceCellLabels.label_value,
    and_iff_right (AlgebraicSliceCellLabels.label_valid P Q u hu i),
    and_iff_right (AlgebraicSliceCellLabels.label_valid P Q u hu j)]
  exact (code_adjacent_iff (roots P Q u) i j).trans (incident_iff_adjacent (roots P Q u) i j).symm

theorem restricted_incident_iff (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) (i j : Index P Q u) :
    FrontierCover.Incident (restrictedPiece P Q u truth) i j ↔
      (restrictedPiece P Q u truth i).Nonempty ∧ (restrictedPiece P Q u truth j).Nonempty ∧
        pair u (pair (AlgebraicSliceCellLabels.label P Q u i) (AlgebraicSliceCellLabels.label P Q u j)) ∈ language P Q := by
  rw [packet P Q u hu]
  change _ ↔ _ ∧ _ ∧ FrontierCover.Incident (Geometry.OrderedRealCells.piece (roots P Q u)) i j
  rw [incident_iff_adjacent (roots P Q u)]
  exact OrderedRealCellRestrictedIncidence.incident_iff (roots P Q u) (solutionSet P Q u truth) (stable P Q u hu truth) i j

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (u a b : List Bool) (hu : u ∉ valid P) :
    pair u (pair a b) ∉ language P Q := by
  intro H
  exact AlgebraicSliceCellLabels.invalid_base P Q u a hu (by simpa only [leftQuery, pairFst_pair, pairSnd_pair] using H.1)

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    language P Q ∈ PSPACE := (decider h A ha).mem_PSPACE

end LeanCanny.Connectivity.AlgebraicSliceCellAdjacency
