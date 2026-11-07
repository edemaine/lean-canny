/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateBounds

/-! # Original-equation filtering is exactly Boolean-cover vertex validity

Proper projection, finite saturation, circular retraction and radial images
preserve nonemptiness label by label. No component-membership or frontier
oracle is needed to determine which Boolean-cover pieces are nonempty.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
open Set
open scoped Classical

variable (c : List Bool) {I : Type*} [Finite I]
  (p : I→Set (Source c)) (hcover : ∀ x,∃ i,x∈p i)
  (haccess : ∀ i,FrontierCover.Accessible (p i))

theorem closedCover_nonempty (i : I) :
    ((closedCover c p hcover haccess).piece i).Nonempty↔(p i).Nonempty := by
  change (FrontierCover.component (fun j=>projection c '' p j) i).Nonempty↔_
  rw [FrontierCover.component_nonempty_iff,Set.image_nonempty]

theorem positiveCover_nonempty (i : I) :
    ((positiveCover c p hcover haccess).piece i).Nonempty↔(p i).Nonempty := by
  unfold positiveCover FormulaSignSlotCircularInterior.interiorCover
  rw [ClopenPathCover.retract_piece,Set.image_nonempty]
  exact closedCover_nonempty c p hcover haccess i

theorem projectedPiece_nonempty (i : I) :
    (FormulaSignSlotRadialAccess.projectedPiece c ((positiveCover c p hcover haccess).piece i)).Nonempty↔(p i).Nonempty := by
  exact Set.image_nonempty.trans (Set.image_nonempty.trans
    (positiveCover_nonempty c p hcover haccess i))
end LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover

namespace LeanCanny.Connectivity.CanonicalSignRefinement.ClosedCovers
open Set
open scoped Classical

theorem piece_nonempty_iff {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) (i : D.Tag) :
    (D.piece i).Nonempty↔(D.closedPiece i.1 i.2).Nonempty := by
  have H : (D.piece i).Nonempty↔(D.rawPiece i).Nonempty := by
    rw [piece,Subtype.preimage_coe_nonempty,inter_eq_right.mpr (rawPiece_subset hd D i)]
  rw [H,rawPiece,Set.image_nonempty]
  exact FormulaSignSlotCircularBoundedCover.projectedPiece_nonempty _ _ _ _ _
end LeanCanny.Connectivity.CanonicalSignRefinement.ClosedCovers

namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
open LeanCanny.Encoding Set
open scoped Classical

theorem closed_nonempty_iff_good (c : List Bool) (i : Vertex (width c)) :
    ((closedCover c).piece i).Nonempty↔AuxiliaryCandidateComponentCover.Good
      dimension_unary equation_FP equation_scope c i.val := by
  exact (sourceHomeomorph c).surjective.nonempty_preimage.trans
    (AuxiliaryCandidateComponentCover.nonempty_iff_good dimension_unary equation_FP equation_scope c i)

theorem piece_nonempty_iff_good (d : Description) (hd : d.WellFormed) (i : Index d) :
    (piece d i).Nonempty↔AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val :=
  (CanonicalSignRefinement.ClosedCovers.piece_nonempty_iff hd (data d) i).trans
    (closed_nonempty_iff_good (CanonicalSignRefinement.source d i.1) i.2)
theorem exists_valid_tag (d : Description) (hd : d.WellFormed) (x : d.realization) :
    ∃ i : Index d,x∈piece d i ∧ AuxiliaryCandidateComponentCover.Good dimension_unary equation_FP equation_scope
      (CanonicalSignRefinement.source d i.1) i.2.val := by
  obtain ⟨i,hi⟩:=covers d hd x
  exact ⟨i,hi,(piece_nonempty_iff_good d hd i).mp ⟨x,hi⟩⟩
end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
