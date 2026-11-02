/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
public import LeanCanny.Connectivity.FormulaSignSlotPartition
public import LeanCanny.Connectivity.BitPathCover
/-! # Actual finite accessible refinements of arbitrary canonical Boolean inputs

The labels are the native accepted sign words of the original formula. Each
label uses its constructed closed circular source; a recursive accessible cover
of that actual native zero source is the sole decomposition input. The union
is exactly the ORIGINAL realization, including arbitrary negation and mixed
weak/strict boundaries. No existential satisfiability compiler is used.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalSignRefinement
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def original (d : Description) := (Input.whole d).encode
noncomputable def width (d : Description) := 2*ClosedFormulaGateMetadata.count (original d)
abbrev Label (d : Description) := {w : List Bool // w.length=width d ∧ pair (original d) w∈FormulaSignSlotCircuit.language}
instance (d : Description) : Finite (Label d) := by
  apply Finite.of_injective (fun l : Label d => (⟨l.val,l.property.1⟩ : Vertex (width d)))
  intro a b H
  exact Subtype.ext (congrArg (fun v : Vertex (width d) => v.val) H)

noncomputable def source (d : Description) (l : Label d) := pair (original d) l.val

theorem source_dimension (d : Description) (l : Label d) : FormulaSignSlotSource.dimension (source d l)=d.dimension := by
  unfold source FormulaSignSlotSource.dimension
  rw [pairFst_pair]
  exact ClosedFormulaGateTruth.dimension_whole d

noncomputable def dimensionHomeomorph {m n : ℕ} (h : m=n) : (Fin m → ℝ) ≃ₜ (Fin n → ℝ) := by
  cases h
  exact Homeomorph.refl _

theorem extend_dimensionHomeomorph {m n : ℕ} (h : m=n) (x : Fin m → ℝ) :
    Formula.extend (dimensionHomeomorph h x)=Formula.extend x := by
  cases h
  rfl

noncomputable def tuple (d : Description) (l : Label d) := dimensionHomeomorph (source_dimension d l)

theorem extend_tuple (d : Description) (l : Label d) (x : Fin (FormulaSignSlotSource.dimension (source d l)) → ℝ) :
    Formula.extend (tuple d l x)=Formula.extend x := extend_dimensionHomeomorph _ _

attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root FormulaSignSlotCircularInterior.description
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count Input.field pair

structure ClosedCovers (d : Description) where
  Index : Label d → Type
  finite : ∀ l, Finite (Index l)
  closedPiece : (l : Label d) → Index l → Set (FormulaSignSlotCircularBoundedCover.Source (source d l))
  closedCover : ∀ l y, ∃ i, y∈closedPiece l i
  closedAccess : ∀ l i, FrontierCover.Accessible (closedPiece l i)

namespace ClosedCovers
instance {d : Description} (D : ClosedCovers d) (l : Label d) : Finite (D.Index l) := D.finite l
abbrev Tag {d : Description} (D : ClosedCovers d) := (l : Label d) × D.Index l
instance {d : Description} (D : ClosedCovers d) : Finite D.Tag := inferInstance

noncomputable def positiveCover {d : Description} (D : ClosedCovers d) (l : Label d) :=
  FormulaSignSlotCircularBoundedCover.positiveCover (source d l) (D.closedPiece l) (D.closedCover l) (D.closedAccess l)
noncomputable def rawPiece {d : Description} (D : ClosedCovers d) (t : D.Tag) : Set (Fin d.dimension → ℝ) :=
  tuple d t.1 '' FormulaSignSlotRadialAccess.projectedPiece (source d t.1) ((D.positiveCover t.1).piece t.2)

theorem rawPiece_subset {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) (t : D.Tag) :
    D.rawPiece t ⊆ d.realization := by
  rintro x ⟨y,HY,rfl⟩
  have H := FormulaSignSlotRadialAccess.projectedPiece_selected (source d t.1) _ HY
  apply (FormulaSignSlotTruth.canonical_selected_iff d hd _).mpr
  refine ⟨t.1.val,t.1.property.1,t.1.property.2,?_⟩
  rw [extend_tuple]
  exact H

theorem rawPiece_cover {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) (x : d.realization) :
    ∃ t : D.Tag, x.val∈D.rawPiece t := by
  obtain ⟨w,HW,HA,HX⟩ := (FormulaSignSlotTruth.canonical_selected_iff d hd x.val).mp x.property
  let l : Label d := ⟨w,HW,HA⟩
  let y := (tuple d l).symm x.val
  have HY : (FormulaSignSlotSource.stratum (source d l)).Holds (Formula.extend y) := by
    have HE := extend_tuple d l y
    rw [Homeomorph.apply_symm_apply] at HE
    rw [← HE]
    exact HX
  obtain ⟨i,HI⟩ := (FormulaSignSlotCircularBoundedCover.projected_cover_iff (source d l)
    (D.closedPiece l) (D.closedCover l) (D.closedAccess l) y).mp HY
  exact ⟨⟨l,i⟩,y,HI,(tuple d l).apply_symm_apply x.val⟩

theorem rawPiece_accessible {d : Description} (D : ClosedCovers d) (t : D.Tag) :
    FrontierCover.Accessible (D.rawPiece t) :=
  (FormulaSignSlotCircularBoundedCover.projected_accessible (source d t.1) (D.closedPiece t.1) (D.closedCover t.1) (D.closedAccess t.1) t.2).image
    (tuple d t.1).continuous (tuple d t.1).isClosedMap

noncomputable def piece {d : Description} (D : ClosedCovers d) (t : D.Tag) : Set d.realization :=
  Subtype.val ⁻¹' D.rawPiece t

theorem cover {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) : ∀ x, ∃ t, x∈D.piece t :=
  rawPiece_cover hd D

theorem accessible {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) (t : D.Tag) :
    FrontierCover.Accessible (D.piece t) := (rawPiece_accessible D t).subtype (rawPiece_subset hd D t)
end ClosedCovers
end LeanCanny.Connectivity.CanonicalSignRefinement
