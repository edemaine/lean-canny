/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildParameters
public import LeanCanny.Algebra.RationalParentUpdateSame

/-! # Closure of rational parent coordinates under regular child sampling

The generalized child source supplies native separable parameters and rational
coordinates. Updating the complete ambient tuple gives another parent family
and another joint input. At a child parameter, denominator nonvanishing passes
from the retained parent. Regular child parameters retain a root of the old
parent equation. Filtering ancestor validity remains separate; the full
primitive parameter polynomial can also have extraneous roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildParents
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open RationalCoordinateFamily
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildCoordinates.parameter RationalParentChildCoordinates.coordinate

noncomputable def raw (F : Inputs) : Family where
  coordinate := RationalParentChildCoordinates.coordinate F
  degree := RationalParentChildCoordinates.coordinateDegree F
  mass := RationalParentChildCoordinates.coordinateMass F
  degree_le q := (RationalParentChildCoordinates.coordinate_bounds F q).1
  numerator_mass q := (RationalParentChildCoordinates.coordinate_bounds F q).2.1
  denominator_mass q := (RationalParentChildCoordinates.coordinate_bounds F q).2.2

theorem raw_access {F : Inputs} (h : F.Access) : Access (raw F) :=
  ⟨RationalParentChildCoordinates.coordinateDegree_binary h,
    RationalParentChildCoordinates.coordinateMass_binary h,
    (RationalParentChildCoordinates.coefficient_evaluators h).1,
    (RationalParentChildCoordinates.coefficient_evaluators h).2⟩

noncomputable def coordinates (F : Inputs) : Family := extend (raw F) (RationalParentChildSource.count F)

theorem coordinates_access {F : Inputs} (h : F.Access) : Access (coordinates F) :=
  extend_access (raw_access h) (BinaryFn.ofUnary (RationalParentChildSource.count_unary h))

noncomputable def parameter (F : Inputs) : SeparablePolynomialFamily.Source where
  polynomial := RationalParentChildCoordinates.parameter F
  degree := RationalParentChildCoordinates.parameterDegree F
  mass := RationalParentChildCoordinates.baseHeight F
  degree_le u := (RationalParentChildCoordinates.parameter_bounds F u).1
  mass_le u := (RationalParentChildCoordinates.parameter_bounds F u).2
  separable u := RationalParentChildCoordinates.parameter_separable F u

theorem parameter_access {F : Inputs} (h : F.Access) : SeparablePolynomialFamily.Access (parameter F) :=
  ⟨RationalParentChildCoordinates.parameterDegree_binary h,
    RationalParentChildCoordinates.baseHeight_binary h,
    RationalParentChildCoordinates.parameter_coefficient_evaluator h⟩

theorem coordinates_defined (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : ((parameter F).polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    Defined (coordinates F) u theta :=
  extend_defined (raw F) _ u theta (fun i hi =>
    (RationalParentChildCoordinates.parameter_root_coordinates F u theta ht ⟨i, hi⟩).1)

theorem coordinates_point (F : Inputs) (u : List Bool) (theta : ℝ) (i : ℕ) :
    point (coordinates F) u theta i = Formula.extend (RationalParentChildParameters.decode F u theta) i := by
  rw [coordinates, extend_point]
  by_cases hi : i < RationalParentChildSource.count F u
  · rw [ite_eq_left hi]
    change i < F.joint.block.dim u + 1 at hi
    simp only [point, raw, Formula.extend, RationalParentChildSource.count, hi, dite_true, RationalParentChildParameters.decode]
  · rw [ite_eq_right hi]
    change ¬ i < F.joint.block.dim u + 1 at hi
    simp only [Formula.extend, RationalParentChildSource.count, hi, dite_false]

def first (F : Inputs) (u : List Bool) : Fin (RationalParentChildSource.count F u) :=
  ⟨0, by unfold RationalParentChildSource.count; omega⟩

noncomputable def retained (F : Inputs) (u : List Bool) (theta : ℝ) : ℝ :=
  RationalParentChildParameters.decode F u theta (first F u)
noncomputable def spatialPoint (F : Inputs) (u : List Bool) (theta : ℝ) : Fin (F.joint.block.dim u) → ℝ :=
  fun i => RationalParentChildParameters.decode F u theta i.succ

theorem retained_point (F : Inputs) (u : List Bool) (theta : ℝ) :
    point (coordinates F) u theta 0 = retained F u theta := by
  rw [coordinates_point]
  simp only [Formula.extend, RationalParentChildSource.count, Nat.zero_lt_succ, dite_true, retained, first]

theorem retained_of_decode (F : Inputs) (u : List Bool) (theta t : ℝ)
    (y : Fin (F.joint.block.dim u) → ℝ)
    (he : RationalParentChildParameters.decode F u theta = Fin.cons t y) : retained F u theta = t := by
  rw [retained, he]
  have hf : first F u = (0 : Fin (F.joint.block.dim u + 1)) := Fin.ext (by simp [first])
  rw [hf, Fin.cons_zero]

theorem retained_root (F : Inputs) (u : List Bool) (theta : RationalParentChildParameters.RegularParameters F u) :
    (F.joint.parent.polynomial u).eval₂ (Int.castRingHom ℝ) (retained F u theta.val) = 0 := by
  have hc : Fin.cons (retained F u theta.val) (spatialPoint F u theta.val) =
      RationalParentChildParameters.decode F u theta.val := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, retained, first]
      apply congrArg (RationalParentChildParameters.decode F u theta.val)
      exact Fin.ext (by simp)
    · simp only [Fin.cons_succ, spatialPoint]
  have H := (RationalParentJointGeometry.root_iff F.joint F.directionWidth F.direction u (F.pivot u)
    (retained F u theta.val) (spatialPoint F u theta.val)).mp (by rw [hc]; exact theta.property.2.1)
  exact H.1

noncomputable def ambient (F : Inputs) : Family :=
  RationalParentUpdate.same F.joint.block.parent (coordinates F) F.joint.block.offset F.joint.block.dim

theorem ambient_access {F : Inputs} (h : F.Access) : Access (ambient F) :=
  RationalParentUpdate.same_access h.joint.block.parent (coordinates_access h)
    h.joint.block.offset (BinaryFn.ofUnary h.joint.block.dim)

theorem ambient_defined (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : ((parameter F).polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0)
    (hP : Defined F.joint.block.parent u (retained F u theta)) : Defined (ambient F) u theta := by
  apply RationalParentUpdate.same_defined F.joint.block.parent (coordinates F)
    F.joint.block.offset F.joint.block.dim u theta (coordinates_defined F u theta ht)
  rw [retained_point]
  exact hP

theorem ambient_point (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : ((parameter F).polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0) (i : ℕ) :
    point (ambient F) u theta i = RationalParentBlockCodes.assignment F.joint.block.parent
      F.joint.block.offset F.joint.block.dim u (retained F u theta) (spatialPoint F u theta) i := by
  rw [ambient, RationalParentUpdate.same_point _ _ _ _ _ _ (coordinates_defined F u theta ht), retained_point]
  by_cases hi : BoundedCriticalSampleBlockSource.InBlock (F.joint.block.offset u) (F.joint.block.dim u) i
  · rw [ite_eq_left hi, coordinates_point]
    have hj : i - F.joint.block.offset u + 1 < F.joint.block.dim u + 1 := by
      unfold BoundedCriticalSampleBlockSource.InBlock at hi
      omega
    simp only [Formula.extend, RationalParentChildSource.count, hj, dite_true, RationalParentBlockCodes.assignment, hi, dite_true, spatialPoint]
    rfl
  · rw [ite_eq_right hi]
    simp only [RationalParentBlockCodes.assignment, hi, dite_false]

noncomputable def next (F : Inputs) (offset dim : List Bool → ℕ) : RationalParentJointSource.Inputs where
  block := ⟨ambient F, F.joint.block.source, offset, dim⟩
  parent := parameter F

theorem next_access {F : Inputs} (h : F.Access) {offset dim : List Bool → ℕ}
    (ho : BinaryFn offset) (hk : UnaryFn dim) : (next F offset dim).Access :=
  ⟨⟨ambient_access h, h.joint.block.source, ho, hk⟩, parameter_access h⟩

end LeanCanny.Encoding.RationalParentChildParents
