/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCircularPoint

/-! # Each valid Boolean component tag has its actual projected sample

The sample uses the same decoded joint-root bank point as the native validity
test. Projection puts it in its own original Boolean piece.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryCandidate.pointAt IntegralMixedAuxiliaryCandidate.labelWidth
  FormulaSignSlotCircularBoundedCover.root ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.kind Input.field

noncomputable def closedSample (c : List Bool) (i : Vertex (width c))
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope c i.val) :
    FormulaSignSlotCircularBoundedCover.Source c :=
  (sourceHomeomorph c).symm (AuxiliaryCandidateComponentCover.sample dimension_unary equation_FP equation_scope c ⟨i,hi⟩)

theorem closedSample_coordinate (c : List Bool) (i : Vertex (width c))
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope c i.val)
    (j : Fin (dimension c)) :
    (closedSample c i hi).val j=
      IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope c i.val (Classical.choose hi) j := rfl

attribute [local irreducible] sourceHomeomorph AuxiliaryCandidateComponentCover.sample

theorem closedSample_mem (c : List Bool) (i : Vertex (width c))
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope c i.val) :
    closedSample c i hi∈(closedCover c).piece i := by
  change sourceHomeomorph c ((sourceHomeomorph c).symm
    (AuxiliaryCandidateComponentCover.sample dimension_unary equation_FP equation_scope c ⟨i,hi⟩))∈
    (AuxiliaryCandidateComponentCover.cover dimension_unary equation_FP equation_scope c).piece i
  rw [Homeomorph.apply_symm_apply]
  change AuxiliaryCandidateComponentCover.sample dimension_unary equation_FP equation_scope c ⟨i,hi⟩∈
    SampledBitComponentCover.piece (AuxiliaryCandidateComponentCover.samples dimension_unary equation_FP equation_scope c) i
  rw [SampledBitComponentCover.piece_of_good _ i hi]
  exact mem_connectedComponent

noncomputable def rawSample (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) : Fin d.dimension→ℝ :=
  CanonicalSignRefinement.tuple d i.1
    (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1)
      (closedSample _ i.2 hi)).val

theorem rawSample_mem (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) :
    rawSample d i hi∈(data d).rawPiece i := by
  refine ⟨_,?_,rfl⟩
  exact FormulaSignSlotCircularBoundedCover.projectedPoint_mem (CanonicalSignRefinement.source d i.1)
    (closedCover _).piece (closedCover _).cover (closed_accessible _) i.2 (closedSample _ i.2 hi)
    (closedSample_mem _ i.2 hi)

noncomputable def coordinateIndex (d : Description) (i : Index d) (j : Fin d.dimension) :
    Fin (dimension (CanonicalSignRefinement.source d i.1)) :=
  FormulaSignSlotCircularBoundedCover.projectedIndex (CanonicalSignRefinement.source d i.1)
    ⟨j.val,by rw [CanonicalSignRefinement.source_dimension]; exact j.isLt⟩

theorem coordinateIndex_val (d : Description) (i : Index d) (j : Fin d.dimension) :
    (coordinateIndex d i j).val=j.val := rfl

private theorem transport_coordinate {a b : ℕ} (H : a=b) (x : Fin a→ℝ) (j : Fin b) (hj : j.val<a) :
    CanonicalSignRefinement.dimensionHomeomorph H x j=x ⟨j.val,hj⟩ := by
  cases H
  rfl

theorem rawSample_coordinate (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) (j : Fin d.dimension) :
    rawSample d i hi j=IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi) (coordinateIndex d i j) := by
  have HJ : j.val<FormulaSignSlotSource.dimension (CanonicalSignRefinement.source d i.1) := by
    rw [CanonicalSignRefinement.source_dimension]
    exact j.isLt
  unfold rawSample CanonicalSignRefinement.tuple
  rw [transport_coordinate _ _ j HJ,FormulaSignSlotCircularBoundedCover.projectedPoint_coordinate,
    closedSample_coordinate]
  unfold coordinateIndex
  rfl

theorem environment_eq (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) (j : ℕ) (hj : j<d.dimension) :
    Formula.extend (rawSample d i hi) j=Formula.extend
      (IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
        (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi)) j := by
  have HJ : j<dimension (CanonicalSignRefinement.source d i.1) := by
    have H:=(coordinateIndex d i ⟨j,hj⟩).isLt
    simpa only [coordinateIndex_val] using H
  simp only [Formula.extend,dite_eq_left hj,dite_eq_left HJ]
  exact (rawSample_coordinate d i hi ⟨j,hj⟩).trans
    (congrArg (IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi))
      (Fin.ext (coordinateIndex_val d i ⟨j,hj⟩)))

theorem rawSample_term_eval (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) (t : Term) (ht : t.arity≤d.dimension) :
    t.eval (Formula.extend (rawSample d i hi))=t.eval (Formula.extend
      (IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
        (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi))) := by
  apply Term.eval_congr
  intro j hj
  exact environment_eq d i hi j (hj.trans_le ht)

theorem rawSample_formula_holds (d : Description) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) (p : Formula) (hp : p.arity≤d.dimension) :
    p.Holds (Formula.extend (rawSample d i hi))↔p.Holds (Formula.extend
      (IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
        (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi))) := by
  apply Formula.holds_congr
  intro j hj
  exact environment_eq d i hi j (hj.trans_le hp)

noncomputable def sample (d : Description) (hd : d.WellFormed) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) : d.realization :=
  ⟨rawSample d i hi,(data d).rawPiece_subset hd i (rawSample_mem d i hi)⟩

theorem sample_mem (d : Description) (hd : d.WellFormed) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) : sample d hd i hi∈piece d i :=
  rawSample_mem d i hi

theorem sourcePoint_holds (d : Description) (hd : d.WellFormed) (i : Index d)
    (hi : AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val) :
    d.formula.Holds (Formula.extend (IntegralMixedAuxiliaryCandidate.pointAt dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val (Classical.choose hi))) :=
  (rawSample_formula_holds d i hi d.formula hd).mp (sample d hd i hi).property

end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
