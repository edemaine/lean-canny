/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateBounds
public import LeanCanny.Connectivity.MonotoneGateCircles
public import LeanCanny.Geometry.BoundedWitnessCompactness
/-! # Literal old-coordinate and slack-coordinate semantics of the bounded writer -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def circles (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) :=
  MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk y

theorem circles_old (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) (i : Fin (F.dimension c)) :
    (circles F c ha hk y).val.1 i=y.val ⟨i.val,by have H:=i.isLt; dsimp [total,base]; omega⟩ := rfl

theorem circles_fresh (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) (i : Fin (F.count c)) (j : Fin 2) :
    (circles F c ha hk y).val.2 i j=y.val ⟨F.dimension c+2*i.val+j.val,by
      have H:=i.isLt; have HJ:=j.isLt; dsimp [total,base]; omega⟩ := by
  change y.val _ = y.val _
  apply congrArg y.val
  apply Fin.ext
  dsimp [FiniteCircularCoordinates.freshIndex]
  omega

theorem atom_eval (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) (i : Fin (F.count c)) :
    (F.atom (BoundedMonotoneGateSource.query c i)).eval (Formula.extend y.val)=
      MonotoneGateCircles.atomValue F c i (circles F c ha hk y).val.1 := by
  apply Term.eval_congr
  intro j hj
  have HJ : j < F.dimension c := hj.trans_le (ha i.val i.isLt)
  have HY : j < total F c := by dsimp [total,base]; omega
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HY]
  exact (circles_old F c ha hk y ⟨j,HJ⟩).symm

noncomputable def encode (F : Family) (c : List Bool)
    (y : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane)) :
    Fin (BoundedMonotoneGateSource.total F c) → ℝ :=
  FiniteCircularCoordinates.encode (total F c) (F.count c) y

theorem old_eval (F : Family) (c : List Bool)
    (z : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (t : Term) (ht : t.arity≤total F c) :
    t.eval (Formula.extend (encode F c z))=t.eval (Formula.extend z.1) :=
  FiniteCircularCoordinates.old_eval _ _ z t ht

end LeanCanny.Connectivity.BoundedGateCoordinates
