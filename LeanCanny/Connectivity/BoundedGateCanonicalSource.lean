/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateEndpointSemantics
public import LeanCanny.Connectivity.BoundedGateProjection
/-! # Every allowed original point has its canonical bounded source extension -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem residual_eval (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) (i : Fin (F.count c)) :
    (BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend y.val)=
      radius F c (circles F c ha hk y).val.1-‖(circles F c ha hk y).val.2 i‖^2 := by
  have HW (j : Fin 2) : Formula.extend y.val (F.dimension c+2*i.val+j.val)=
      (circles F c ha hk y).val.2 i j := by
    have HJ : F.dimension c+2*i.val+j.val < total F c := by
      have H:=i.isLt; have H':=j.isLt; dsimp [total,base]; omega
    simp only [Formula.extend,dite_eq_left HJ]
    exact (circles_fresh F c ha hk y i j).symm
  have H0 := HW 0
  have H1 := HW 1
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero] at H0 H1
  have HN (w : CircularWitness.Plane) : ‖w‖^2=(w 0)^2+(w 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  simp only [BoundedMonotoneGateEndpoint.residual,Term.eval,witnessIndex,dimension,index,
    BoundedMonotoneGateSource.query,pairFst_pair,pairSnd_pair,List.length_replicate,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero,Int.cast_neg,Int.cast_one]
  rw [H0,H1,radius_eval F c ha hk y,HN]
  ring

theorem canonical_source (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3)
    (x : WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c)) :
    (BoundedMonotoneGateSource.polynomial F c).eval
      (Formula.extend (extendPoint F c (MonotoneGateCanonicalPoint.point F c x.val)))=0 := by
  let z := WeakBooleanWitness.centerSection _ _ (MonotoneGateArithmetic.predicate_mono F c hk) x
  let y : ZeroSet F c := (MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm z
  have HE : circles F c ha hk y=z := Homeomorph.apply_symm_apply _ _
  have HY : y.val=MonotoneGateCanonicalPoint.point F c x.val := rfl
  rw [← HY]
  rw [BoundedMonotoneGateSource.polynomial_zero]
  constructor
  · change (MonotoneGateSource.polynomial F c).eval (Formula.extend (encode F c (y.val,_)))=0
    rw [old_eval F c _ _ ((MonotoneGateSource.polynomial_arity F c ha).trans (by
      dsimp [MonotoneGateSource.outputDimension,total,base]; omega))]
    exact y.property
  · intro i hi
    let r := (BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i)).eval (Formula.extend y.val)
    have HR : r=radius F c x.val-max (MonotoneGateCircles.atomValue F c ⟨i,hi⟩ x.val) 0 := by
      change (BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i)).eval _=_
      rw [residual_eval F c ha hk y ⟨i,hi⟩,HE]
      exact congrArg (fun v => radius F c x.val-v) (BoundedCircularCoordinates.canonical_sq _)
    have HN : 0≤r := by rw [HR]; exact sub_nonneg.mpr (atom_radius F c x.val ⟨i,hi⟩)
    change (BoundedMonotoneGateSource.slack F (BoundedMonotoneGateSource.query c i)).eval
      (Formula.extend (encode F c (y.val,_)))=0
    rw [slack_eval F c ha hk y _ ⟨i,hi⟩,HE]
    change ‖WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c ⟨i,hi⟩ x.val)‖^2+
      ‖WeakBooleanWitness.canonical r‖^2-radius F c x.val=0
    rw [BoundedCircularCoordinates.canonical_sq,BoundedCircularCoordinates.canonical_sq,max_eq_left HN,HR]
    ring

end LeanCanny.Connectivity.BoundedGateCoordinates
