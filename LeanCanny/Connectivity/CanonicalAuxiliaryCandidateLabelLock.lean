/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
public import LeanCanny.Connectivity.ClopenPathCoverProjection
/-! # Exact candidate labels in the actual positive circular cover

Finite frontier saturation and the circular retraction preserve the original
sample's label. All lifts below lie over the SAME positive margin point.
No closure is projected through a possibly divergent circular fiber.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabelLock
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Good (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)):Prop:=
  AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c i.val

noncomputable def closedSample (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (hi :Good c i):FormulaSignSlotCircularBoundedCover.Source c:=
  (CanonicalAuxiliaryCandidateCover.sourceHomeomorph c).symm
    (AuxiliaryCandidateComponentCover.sample CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c ⟨i,hi⟩)

noncomputable def positiveProjection (c :List Bool):FormulaSignSlotCircularBoundedCover.Source c→FormulaSignSlotComponentMaxima.Positive c:=
  FormulaSignSlotCircularInterior.projection c∘FormulaSignSlotCircularBoundedCover.projection c

noncomputable def positiveCover (c :List Bool):ClopenPathCover (FormulaSignSlotComponentMaxima.Positive c) (Vertex (CanonicalAuxiliaryCandidateCover.width c)):=
  FormulaSignSlotCircularBoundedCover.positiveCover c (CanonicalAuxiliaryCandidateCover.closedCover c).piece (CanonicalAuxiliaryCandidateCover.closedCover c).cover
    (CanonicalAuxiliaryCandidateCover.closed_accessible c)

attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root
  FormulaSignSlotCircularInterior.description ClosedFormulaGateMetadata.dimension
  ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind
  Input.field FormulaView.normalize

theorem gate_joined_iff (c :List Bool) (x z :FormulaSignSlotCircularBoundedCover.Source c):
    JoinedIn univ x z ↔JoinedIn univ (FormulaSignSlotCircularBoundedCover.projection c x) (FormulaSignSlotCircularBoundedCover.projection c z):=by
  constructor
  · intro H
    exact (H.map (FormulaSignSlotCircularBoundedCover.proper_projection c).continuous.continuousOn).mono (subset_univ _)
  · intro H
    apply (ClosedFormulaBoundedGate.joined_iff (FormulaSignSlotCircularInterior.closed c)
      (FormulaSignSlotCircularBoundedCover.root c) (FormulaSignSlotCircularBoundedCover.root_formula c)
      (FormulaSignSlotCircularBoundedCover.root_scope c) x z).mpr
    have HP:=(H.map (FormulaSignSlotCircularBoundedCover.targetHomeomorph c).symm.continuous.continuousOn).mono (subset_univ _)
    simpa only [FormulaSignSlotCircularBoundedCover.projection,Function.comp_apply,Homeomorph.symm_apply_apply] using HP

theorem gate_fiber_joined (c :List Bool) (x z :FormulaSignSlotCircularBoundedCover.Source c) (he :FormulaSignSlotCircularBoundedCover.projection c x=FormulaSignSlotCircularBoundedCover.projection c z):JoinedIn univ x z:=by
  apply (gate_joined_iff c x z).mpr
  rw [he]
  exact JoinedIn.refl (mem_univ _)

theorem positive_fiber_joined (c :List Bool) (x z :FormulaSignSlotCircularBoundedCover.Source c)
    (he :positiveProjection c x=positiveProjection c z):JoinedIn univ x z:=by
  apply (gate_joined_iff c x z).mpr
  have HX:=FormulaSignSlotCircularInterior.fiber_joined c (FormulaSignSlotCircularBoundedCover.projection c x)
  have HZ:=FormulaSignSlotCircularInterior.fiber_joined c (FormulaSignSlotCircularBoundedCover.projection c z)
  change FormulaSignSlotCircularInterior.projection c (FormulaSignSlotCircularBoundedCover.projection c x)=
    FormulaSignSlotCircularInterior.projection c (FormulaSignSlotCircularBoundedCover.projection c z) at he
  rw [he] at HX
  exact HX.trans HZ.symm

theorem closedSample_mem (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)) (hi :Good c i):
    closedSample c i hi∈(CanonicalAuxiliaryCandidateCover.closedCover c).piece i:=by
  change CanonicalAuxiliaryCandidateCover.sourceHomeomorph c (closedSample c i hi)∈
    (AuxiliaryCandidateComponentCover.cover CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c).piece i
  unfold closedSample
  rw [Homeomorph.apply_symm_apply]
  change AuxiliaryCandidateComponentCover.sample CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c ⟨i,hi⟩∈
    SampledBitComponentCover.piece (AuxiliaryCandidateComponentCover.samples CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c) i
  rw [SampledBitComponentCover.piece_of_good _ i hi]
  exact mem_connectedComponent

theorem closed_mem_iff (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)) (z :FormulaSignSlotCircularBoundedCover.Source c):
    z∈(CanonicalAuxiliaryCandidateCover.closedCover c).piece i ↔∃hi :Good c i,JoinedIn univ (closedSample c i hi) z:=by
  constructor
  · intro H
    have HN:((AuxiliaryCandidateComponentCover.cover CanonicalAuxiliaryCandidateCover.dimension_unary
        CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c).piece i).Nonempty:=
      ⟨CanonicalAuxiliaryCandidateCover.sourceHomeomorph c z,H⟩
    have HI:Good c i:=(AuxiliaryCandidateComponentCover.nonempty_iff_good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope c i).mp HN
    exact ⟨HI,((CanonicalAuxiliaryCandidateCover.closedCover c).paths i _ (closedSample_mem c i HI) z H).mono (subset_univ _)⟩
  · rintro ⟨hi,H⟩
    exact (CanonicalAuxiliaryCandidateCover.closedCover c).mem_of_joined i (closedSample_mem c i hi) H

/-- This is equality of the ACTUAL finite saturation, not replacement by a
new component cover chosen to have equivalent connectivity. -/
theorem closed_saturated_piece_eq (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)):
    (FormulaSignSlotCircularBoundedCover.closedCover c (CanonicalAuxiliaryCandidateCover.closedCover c).piece (CanonicalAuxiliaryCandidateCover.closedCover c).cover
      (CanonicalAuxiliaryCandidateCover.closed_accessible c)).piece i=FormulaSignSlotCircularBoundedCover.projection c '' (CanonicalAuxiliaryCandidateCover.closedCover c).piece i:=by
  change FrontierCover.component (fun j=>FormulaSignSlotCircularBoundedCover.projection c '' (CanonicalAuxiliaryCandidateCover.closedCover c).piece j) i=FormulaSignSlotCircularBoundedCover.projection c '' (CanonicalAuxiliaryCandidateCover.closedCover c).piece i
  exact (CanonicalAuxiliaryCandidateCover.closedCover c).saturated_image_eq (FormulaSignSlotCircularBoundedCover.projection c) (FormulaSignSlotCircularBoundedCover.proper_projection c).isClosedMap
    (gate_fiber_joined c) i

theorem positive_piece_eq (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)):
    (positiveCover c).piece i=positiveProjection c '' (CanonicalAuxiliaryCandidateCover.closedCover c).piece i:=by
  unfold positiveCover FormulaSignSlotCircularBoundedCover.positiveCover FormulaSignSlotCircularInterior.interiorCover
  rw [ClopenPathCover.retract_piece,closed_saturated_piece_eq,Set.image_image]
  rfl

theorem positive_mem_iff (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c)) (y :FormulaSignSlotComponentMaxima.Positive c):
    y∈(positiveCover c).piece i ↔∃hi :Good c i,∃z :FormulaSignSlotCircularBoundedCover.Source c,
      positiveProjection c z=y ∧JoinedIn univ (closedSample c i hi) z:=by
  rw [positive_piece_eq]
  constructor
  · rintro ⟨z,hz,HP⟩
    obtain ⟨hi,HJ⟩:=(closed_mem_iff c i z).mp hz
    exact ⟨hi,z,HP,HJ⟩
  · rintro ⟨hi,z,HP,HJ⟩
    exact ⟨z,(closed_mem_iff c i z).mpr ⟨hi,HJ⟩,HP⟩

/-- ANY given lift of this very same positive point tests the same label. -/
theorem positive_mem_iff_of_lift (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (y :FormulaSignSlotComponentMaxima.Positive c) (z :FormulaSignSlotCircularBoundedCover.Source c) (hz :positiveProjection c z=y):
    y∈(positiveCover c).piece i ↔∃hi :Good c i,JoinedIn univ (closedSample c i hi) z:=by
  rw [positive_mem_iff]
  constructor
  · rintro ⟨hi,w,HP,HJ⟩
    exact ⟨hi,HJ.trans (positive_fiber_joined c w z (HP.trans hz.symm))⟩
  · rintro ⟨hi,HJ⟩
    exact ⟨hi,z,hz,HJ⟩

/-- The sign-refinement data uses precisely this cover with its original label. -/
theorem refinement_positive_mem_iff (d :Description) (l :CanonicalSignRefinement.Label d)
    (i :Vertex (CanonicalAuxiliaryCandidateCover.width (CanonicalSignRefinement.source d l)))
    (y :FormulaSignSlotComponentMaxima.Positive (CanonicalSignRefinement.source d l)):
    y∈((CanonicalAuxiliaryCandidateCover.data d).positiveCover l).piece i ↔
      ∃hi :Good (CanonicalSignRefinement.source d l) i,∃z :FormulaSignSlotCircularBoundedCover.Source (CanonicalSignRefinement.source d l),
        positiveProjection (CanonicalSignRefinement.source d l) z=y ∧
        JoinedIn univ (closedSample (CanonicalSignRefinement.source d l) i hi) z:=
  positive_mem_iff _ i y

end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabelLock
