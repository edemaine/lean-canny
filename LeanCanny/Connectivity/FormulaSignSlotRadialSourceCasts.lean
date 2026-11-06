/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRealization
/-! # Literal source equalities retain radial coordinates and component labels -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialSourceCasts
open LeanCanny.Encoding LeanCanny.ETR Set
open scoped Classical
attribute [local irreducible] FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial

noncomputable def source {u v : List Bool} (h : u = v)
    (A : FormulaSignSlotCircularBoundedCover.Source u) : FormulaSignSlotCircularBoundedCover.Source v := by
  cases h
  exact A
noncomputable def vertex {u v : List Bool} (h : u = v)
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width u)) : Vertex (CanonicalAuxiliaryCandidateCover.width v) := by
  cases h
  exact i
noncomputable def vector {u v : List Bool} (h : u = v)
    (a : Fin (FormulaSignSlotSource.dimension u) → ℝ) : Fin (FormulaSignSlotSource.dimension v) → ℝ :=
  CanonicalSignRefinement.dimensionHomeomorph (congrArg FormulaSignSlotSource.dimension h) a

theorem vertex_val {u v : List Bool} (h : u = v) (i : Vertex (CanonicalAuxiliaryCandidateCover.width u)) :
    (vertex h i).val = i.val := by cases h; rfl

theorem vector_extend {u v : List Bool} (h : u = v) (a : Fin (FormulaSignSlotSource.dimension u) → ℝ) :
    Formula.extend (vector h a) = Formula.extend a :=
  CanonicalSignRefinement.extend_dimensionHomeomorph _ a

theorem projected_extend {u v : List Bool} (h : u = v)
    (A : FormulaSignSlotCircularBoundedCover.Source u) :
    Formula.extend (FormulaSignSlotCircularBoundedCover.projectedPoint v (source h A)).val =
      Formula.extend (FormulaSignSlotCircularBoundedCover.projectedPoint u A).val := by
  cases h
  rfl

theorem closed_mem {u v : List Bool} (h : u = v)
    (A : FormulaSignSlotCircularBoundedCover.Source u) (i : Vertex (CanonicalAuxiliaryCandidateCover.width u))
    (hm : A ∈ (CanonicalAuxiliaryCandidateCover.closedCover u).piece i) :
    source h A ∈ (CanonicalAuxiliaryCandidateCover.closedCover v).piece (vertex h i) := by
  cases h
  exact hm

noncomputable def descriptor {u v : List Bool} (h : u = v)
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width u)) (a : Fin (FormulaSignSlotSource.dimension u) → ℝ)
    (D : FormulaSignSlotCandidateRadialDescriptor.Descriptor u i a) :
    FormulaSignSlotCandidateRadialDescriptor.Descriptor v (vertex h i) (vector h a) := by
  cases h
  exact D

private theorem numerical_extend {n m : ℕ} (h : n = m) (p : Fin n → ℝ) :
    Formula.extend (fun i : Fin m => p (Fin.cast h.symm i)) = Formula.extend p := by
  cases h
  rfl

theorem leftCenter_extend (H : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source false H)) :
    Formula.extend (FormulaSignSlotRadialJointRealization.leftCenter H A) =
      Formula.extend (FormulaSignSlotCircularBoundedCover.projectedPoint
        (FormulaSignSlotRadialJointLayout.source false H) A).val :=
  numerical_extend (FormulaSignSlotRadialJointLayout.original_dimension_eq H)
    (FormulaSignSlotCircularBoundedCover.projectedPoint (FormulaSignSlotRadialJointLayout.source false H) A).val

theorem tuple_symm_extend (d : Description) (l : CanonicalSignRefinement.Label d)
    (x : Fin d.dimension → ℝ) :
    Formula.extend ((CanonicalSignRefinement.tuple d l).symm x) = Formula.extend x := by
  have H := CanonicalSignRefinement.extend_tuple d l ((CanonicalSignRefinement.tuple d l).symm x)
  rw [Homeomorph.apply_symm_apply] at H
  exact H.symm

theorem equal_of_extend {n : ℕ} {a b : Fin n → ℝ} (h : Formula.extend a = Formula.extend b) : a = b := by
  funext i
  have H := congrFun h i.val
  simpa only [Formula.extend, dite_eq_left i.isLt] using H

end LeanCanny.Connectivity.FormulaSignSlotRadialSourceCasts
