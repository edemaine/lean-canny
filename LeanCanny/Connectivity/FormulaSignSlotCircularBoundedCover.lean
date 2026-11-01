/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotCircularSource
/-! # Actual recursive closed-source covers give accessible sign-piece refinements

The only decomposition premise concerns the actual native zero source of the
constructed closed circular formula. Proper projection and finite saturation
supply its closed-source component labels; circular fiber saturation transfers
them to the positive margin source. Constructed radial branches handle all
original-coordinate boundaries.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotCircularInterior
open ClosedFormulaGateTruth
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def root (c : List Bool) := (Input.whole (description c)).encode
noncomputable abbrev Source (c : List Bool) := ClosedFormulaBoundedFrontier.Source (root c)

theorem root_FP : root∈FP := FormulaSignSlotCircularSource.whole_FP

theorem root_formula (c : List Bool) : FormulaView.normalize (Input.field 2 (root c))=(description c).formula.encode := by
  simp only [root,Input.field_whole_space,FormulaView.normalize_encode]
theorem root_dimension (c : List Bool) : F.dimension (root c)=(description c).dimension := by
  unfold root
  exact dimension_whole _
theorem root_scope (c : List Bool) : (description c).formula.arity≤F.dimension (root c) := by
  rw [root_dimension]
  exact wellFormed c

theorem target_eq (c : List Bool) : Description.mk (F.dimension (root c)) (description c).formula=description c := by
  rw [root_dimension]
noncomputable def targetHomeomorph (c : List Bool) :
    ClosedFormulaBoundedFrontier.Target (description c).formula (root c) ≃ₜ (description c).realization :=
  FormulaSignSlotMarginProjection.equalityHomeomorph (target_eq c)

noncomputable def projection (c : List Bool) : Source c → (description c).realization :=
  targetHomeomorph c ∘ ClosedFormulaBoundedGate.projection (closed c) (root c) (root_formula c) (root_scope c)

theorem proper_projection (c : List Bool) : IsProperMap (projection c) :=
  (targetHomeomorph c).isProperMap.comp (ClosedFormulaBoundedGate.proper_projection (closed c) (root c) (root_formula c) (root_scope c))
theorem projection_surjective (c : List Bool) : Function.Surjective (projection c) :=
  (targetHomeomorph c).surjective.comp (ClosedFormulaBoundedFrontier.projection_surjective (closed c) (root c) (root_formula c) (root_scope c))

noncomputable def closedCover (c : List Bool) {I : Type*} [Finite I] (piece : I → Set (Source c))
    (cover : ∀ y, ∃ i, y∈piece i) (access : ∀ i, FrontierCover.Accessible (piece i)) :
    ClopenPathCover (description c).realization I :=
  ClopenPathCover.ofAccessible (fun i => projection c '' piece i)
    (fun x => by obtain ⟨y,rfl⟩ := projection_surjective c x; obtain ⟨i,hi⟩ := cover y; exact ⟨i,y,hi,rfl⟩)
    (fun i => (access i).image (proper_projection c).continuous (proper_projection c).isClosedMap)

noncomputable def positiveCover (c : List Bool) {I : Type*} [Finite I] (piece : I → Set (Source c))
    (cover : ∀ y, ∃ i, y∈piece i) (access : ∀ i, FrontierCover.Accessible (piece i)) :
    ClopenPathCover (FormulaSignSlotComponentMaxima.Positive c) I :=
  interiorCover c (closedCover c piece cover access)

theorem projected_accessible (c : List Bool) {I : Type*} [Finite I] (piece : I → Set (Source c))
    (cover : ∀ y, ∃ i, y∈piece i) (access : ∀ i, FrontierCover.Accessible (piece i)) (i : I) :
    FrontierCover.Accessible (FormulaSignSlotRadialAccess.projectedPiece c ((positiveCover c piece cover access).piece i)) :=
  FormulaSignSlotProjectedPieceAccess.accessible c (positiveCover c piece cover access) i
theorem projected_cover_iff (c : List Bool) {I : Type*} [Finite I] (piece : I → Set (Source c))
    (cover : ∀ y, ∃ i, y∈piece i) (access : ∀ i, FrontierCover.Accessible (piece i))
    (x : Fin (FormulaSignSlotSource.dimension c) → ℝ) :
    (FormulaSignSlotSource.stratum c).Holds (Formula.extend x) ↔
      ∃ i, x∈FormulaSignSlotRadialAccess.projectedPiece c ((positiveCover c piece cover access).piece i) := by
  constructor
  · intro HX
    let z : FormulaSignSlotMarginProjection.Target c :=
      ⟨x,FormulaSignSlotSource.stratum_implies_envelope c _ HX⟩
    obtain ⟨y,HY⟩ := FormulaSignSlotMarginProjection.projection_surjective c z
    have HP : 0 < FormulaSignSlotMarginProjection.value c y :=
      (FormulaSignSlotMarginProjection.value_positive_iff c y).mpr (by rw [HY]; exact HX)
    let t : FormulaSignSlotComponentMaxima.Positive c := ⟨y,HP⟩
    obtain ⟨i,HI⟩ := (positiveCover c piece cover access).cover t
    exact ⟨i,y,⟨t,HI,rfl⟩,congrArg Subtype.val HY⟩
  · rintro ⟨i,HI⟩
    exact FormulaSignSlotRadialAccess.projectedPiece_selected c _ HI
end LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
