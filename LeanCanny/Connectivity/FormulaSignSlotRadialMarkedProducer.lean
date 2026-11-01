/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProducer
/-! # Marked regularized points recover the literal original radial graph

The regularized producer is genuinely regular; its unmarked points need not
satisfy the original graph equations. At marked points the actual old tuple,
margin coordinate and affine radial identity are recovered in the producer's
concrete permuted coordinate order.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialMarkedProducer
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
open FormulaSignSlotRadialProducer
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable abbrev original (q : List Bool) := BoundedFullWriter.original readers q
noncomputable abbrev size (q : List Bool) := BoundedFullWriter.size readers q
noncomputable abbrev Physical (q : List Bool) := BoundedFullCriticalSamples.Source readers q
noncomputable abbrev Geometric (q : List Bool) :=
  BoundedRegularSource.Zeros (original q) (size q) (size q) (radius q)

noncomputable def geometricHomeomorph (q : List Bool) : Physical q ≃ₜ Geometric q :=
  (BoundedFullGeometry.coordinates (readers.dim q+3)).subtype (fun x => by
    change (BoundedFullCriticalSamples.realPolynomial readers q).eval x=0 ↔ _
    simp only [BoundedFullCriticalSamples.realPolynomial,eval_map,BoundedFullCriticalSamples.polynomial,
      BoundedFullGeometry.polynomial,eval₂_rename]
    rfl)

noncomputable def markPolynomial (q : List Bool) := BoundedFullGeometry.markPolynomial (original q) (radius q)
noncomputable abbrev Marked (q : List Bool) :=
  {z : Physical q // (markPolynomial q).eval₂ (Int.castRingHom ℝ) z.val=0}

noncomputable def markedGeometric (q : List Bool) (z : Marked q) :
    BoundedRegularSource.Marked (original q) (size q) (size q) (radius q) :=
  ⟨geometricHomeomorph q z.val,by
    change (BoundedRegularSource.markPolynomial (original q) (radius q)).eval₂ (Int.castRingHom ℝ)
      (fun i => z.val.val (BoundedFullGeometry.inputIndex (readers.dim q+3) i))=0
    simpa only [markPolynomial,BoundedFullGeometry.markPolynomial,eval₂_rename,Function.comp_def]
      using z.property⟩

private theorem bounded_projection_coordinate {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (R : ℕ)
    (z : BoundedZeroSource.Zeros p R) (i : Fin n) :
    (BoundedZeroSource.projection p R z).val i=z.val (i.castAdd 2) := by
  change (BoundedZeroSource.coordinates.symm z.val).1 i=z.val (i.castAdd 2)
  have H := congrArg (fun v : Fin (n+2) → ℝ => v (i.castAdd 2))
    (BoundedZeroSource.coordinates.apply_symm_apply z.val)
  simpa only [BoundedZeroSource.coordinates_apply,Fin.append_left] using H

noncomputable def boundedPoint (q : List Bool) (z : Marked q) :=
  BoundedRegularSource.markedProjection (original q) (size q) (size q) (radius q) (markedGeometric q z)

noncomputable def graphPoint (q : List Bool) (z : Marked q) : FormulaSignSlotRadialFeature.Lifted (root q) :=
  ⟨(boundedPoint q z).val,by
    let x : Fin (readers.dim q) → ℝ := (boundedPoint q z).val
    have H : (original q).eval₂ (Int.castRingHom ℝ) x=0 := (boundedPoint q z).property.1
    unfold original at H
    rw [original_eq] at H
    exact (FormulaSignSlotRadialEquation.polynomial_zero (root q) _).mp H⟩

noncomputable def physicalIndex (q : List Bool) (i : Fin (readers.dim q)) : Fin (readers.dim q+4) :=
  BoundedFullGeometry.inputIndex (readers.dim q+3) ((i.castAdd 2).castAdd 2)

theorem graphPoint_coordinate (q : List Bool) (z : Marked q) (i : Fin (readers.dim q)) :
    (graphPoint q z).val i=z.val.val (physicalIndex q i) := by
  change (BoundedRegularSource.markedProjection (original q) (size q) (size q) (radius q)
    (markedGeometric q z)).val i=_
  rw [BoundedRegularSource.markedProjection,bounded_projection_coordinate]
  change (BoundedRegularSource.oldBase (original q) (size q) (size q) (radius q)
    (geometricHomeomorph q z.val)).val (i.castAdd 2)=_
  rw [BoundedRegularSource.oldBase_apply]
  rfl

theorem component_iff (q : List Bool) (z v : Marked q) :
    v.val∈connectedComponent z.val ↔ (boundedPoint q v).val∈
      connectedComponentIn (BoundedZeroSource.Bounded (original q) (radius q)) (boundedPoint q z).val := by
  have H : v.val∈connectedComponent z.val ↔ geometricHomeomorph q v.val∈
      connectedComponent (geometricHomeomorph q z.val) := by
    constructor
    · exact fun h => (geometricHomeomorph q).continuous.mapsTo_connectedComponent z.val h
    · intro h
      have HE := (geometricHomeomorph q).symm.continuous.mapsTo_connectedComponent
        (geometricHomeomorph q z.val) h
      simpa only [Homeomorph.symm_apply_apply] using HE
  exact H.trans (BoundedRegularSource.marked_component_iff (original q) (size q) (size q) (radius q)
    (BoundedFullWriter.original_degree readers q) (BoundedFullWriter.original_mass readers q)
    (markedGeometric q z) (markedGeometric q v))

noncomputable def margin (q : List Bool) (z : Marked q) := z.val.val (physicalIndex q
  (Fin.castAdd 1 (FormulaSignSlotMarginProjection.objectiveIndex (root q))))

noncomputable def quadratic (q : List Bool) (z : Marked q) :=
  z.val.val (physicalIndex q (Fin.last (FormulaSignSlotMargin.initialDimension (root q))))

theorem margin_eq (q : List Bool) (z : Marked q) : margin q z=
    FormulaSignSlotMarginProjection.value (root q) (FormulaSignSlotRadialFeature.homeomorph (root q) (graphPoint q z)) := by
  unfold margin
  rw [← graphPoint_coordinate]
  exact FormulaSignSlotRadialFeature.margin_coordinate (root q) (graphPoint q z)

theorem radial_affine (q : List Bool) (z : Marked q)
    (center : Fin (FormulaSignSlotSource.dimension (root q)) → ℝ) :
    SquaredDistanceLinearization.affine center (quadratic q z)
      (FormulaSignSlotRadialFeature.oldTuple (root q) (graphPoint q z))=
      SquaredDistanceFibers.value center (FormulaSignSlotRadialFeature.oldTuple (root q) (graphPoint q z)) := by
  unfold quadratic
  rw [← graphPoint_coordinate]
  exact FormulaSignSlotRadialFeature.radial_affine (root q) center (graphPoint q z)

noncomputable def markedHomeomorph (q : List Bool) : Marked q ≃ₜ
    BoundedRegularSource.Marked (original q) (size q) (size q) (radius q) :=
  (geometricHomeomorph q).subtype (fun x => by
    rw [markPolynomial,BoundedFullGeometry.markPolynomial,eval₂_rename]
    rfl)

noncomputable def boundedGraphPoint (q : List Bool) (y : FormulaSignSlotRadialFeature.Lifted (root q))
    (hy : BoundedZeroSource.radial y.val≤(BoundedZeroSource.radiusSquared (radius q) : ℝ)) :
    BoundedZeroSource.Bounded (original q) (radius q) :=
  ⟨y.val,by
    unfold original
    rw [original_eq]
    exact (FormulaSignSlotRadialEquation.polynomial_zero (root q) _).mpr y.property,hy⟩

noncomputable def lift (q : List Bool) (y : FormulaSignSlotRadialFeature.Lifted (root q))
    (hy : BoundedZeroSource.radial y.val≤(BoundedZeroSource.radiusSquared (radius q) : ℝ)) : Marked q :=
  (markedHomeomorph q).symm (BoundedRegularSource.markedLift (original q) (size q) (size q) (radius q)
    (boundedGraphPoint q y hy))

theorem boundedPoint_lift (q : List Bool) (y : FormulaSignSlotRadialFeature.Lifted (root q))
    (hy : BoundedZeroSource.radial y.val≤(BoundedZeroSource.radiusSquared (radius q) : ℝ)) :
    boundedPoint q (lift q y hy)=boundedGraphPoint q y hy := by
  have H : markedGeometric q (lift q y hy)=BoundedRegularSource.markedLift
      (original q) (size q) (size q) (radius q) (boundedGraphPoint q y hy) := by
    change markedHomeomorph q ((markedHomeomorph q).symm _)=_
    exact (markedHomeomorph q).apply_symm_apply _
  unfold boundedPoint
  rw [H,BoundedRegularSource.markedProjection_lift]

theorem graphPoint_lift (q : List Bool) (y : FormulaSignSlotRadialFeature.Lifted (root q))
    (hy : BoundedZeroSource.radial y.val≤(BoundedZeroSource.radiusSquared (radius q) : ℝ)) :
    graphPoint q (lift q y hy)=y := by
  apply Subtype.ext
  change (boundedPoint q (lift q y hy)).val=y.val
  rw [boundedPoint_lift]
  rfl

end LeanCanny.Connectivity.FormulaSignSlotRadialMarkedProducer
