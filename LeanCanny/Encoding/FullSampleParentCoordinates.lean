/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalParentUpdate
public import LeanCanny.Encoding.BoundedCriticalSampleCoordinateTests
public import LeanCanny.Encoding.BoundedFullSampleChildActualSamples

/-! # Derived child samples as rational ambient parents

The common rational-coordinate interface accepts both original sample tuples
and regular child tuples. Updating the original ambient point through a
child's retained parent parameter gives native readers for the entire new
ambient point, including coordinates outside the sampled block. Every
denominator is proved nonzero at each actual child parameter.
-/

@[expose] public section
namespace LeanCanny.Encoding.FullSampleParentCoordinates
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open RationalCoordinateFamily
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate
  BoundedCriticalSampleLabels.parameter BoundedFullSampleChildCoordinates.coordinate
  BoundedFullSampleChildCoordinates.parameter

noncomputable def rawFull (P : BoundedFullWriter.Readers) : Family where
  coordinate := BoundedCriticalRationalCoordinates.coordinate P
  degree := BoundedCriticalRationalCoordinates.coordinateDegree P
  mass := BoundedCriticalRationalCoordinates.coordinateMass P
  degree_le q := (BoundedCriticalRationalCoordinates.coordinate_bounds P q).1
  numerator_mass q := (BoundedCriticalRationalCoordinates.coordinate_bounds P q).2.1
  denominator_mass q := (BoundedCriticalRationalCoordinates.coordinate_bounds P q).2.2

theorem rawFull_access {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : Access (rawFull P) :=
  ⟨BoundedCriticalRationalCoordinates.coordinateDegree_binary h,
    BoundedCriticalRationalCoordinates.coordinateMass_binary h,
    (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).1,
    (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).2⟩

noncomputable def full (P : BoundedFullWriter.Readers) : Family := extend (rawFull P) (fun c => P.dim c + 4)

theorem full_access {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : Access (full P) :=
  extend_access (rawFull_access h ha) ((BinaryFn.ofUnary h.dim).add (BinaryFn.const 4))

theorem full_defined (P : BoundedFullWriter.Readers) (c : List Bool)
    (p : BoundedFullCriticalSamples.Samples P c) : Defined (full P) c (BoundedCriticalSampleLabels.parameter P c p).val :=
  extend_defined (rawFull P) _ c _ (fun i hi =>
    BoundedCriticalSampleCoordinateTests.denominator_nonzero P c p ⟨i, hi⟩)

theorem full_point (P : BoundedFullWriter.Readers) (c : List Bool)
    (p : BoundedFullCriticalSamples.Samples P c) (i : ℕ) :
    point (full P) c (BoundedCriticalSampleLabels.parameter P c p).val i = Formula.extend p.val i := by
  rw [full, extend_point]
  by_cases hi : i < P.dim c + 4
  · rw [ite_eq_left hi]
    simp only [point, rawFull, Formula.extend, hi, dite_true]
    exact BoundedCriticalSampleCoordinateTests.coordinate_eval P c p ⟨i, hi⟩
  · rw [ite_eq_right hi]
    simp only [Formula.extend, hi, dite_false]

noncomputable def rawChild (F : Inputs) : Family where
  coordinate := BoundedFullSampleChildCoordinates.coordinate F
  degree := BoundedFullSampleChildCoordinates.coordinateDegree F
  mass := BoundedFullSampleChildCoordinates.coordinateMass F
  degree_le q := (BoundedFullSampleChildCoordinates.coordinate_bounds F q).1
  numerator_mass q := (BoundedFullSampleChildCoordinates.coordinate_bounds F q).2.1
  denominator_mass q := (BoundedFullSampleChildCoordinates.coordinate_bounds F q).2.2

theorem rawChild_access {F : Inputs} (h : F.PolyTime) : Access (rawChild F) :=
  ⟨BoundedFullSampleChildCoordinates.coordinateDegree_binary h,
    BoundedFullSampleChildCoordinates.coordinateMass_binary h,
    (BoundedFullSampleChildCoordinates.coefficient_evaluators h).1,
    (BoundedFullSampleChildCoordinates.coefficient_evaluators h).2⟩

noncomputable def child (F : Inputs) : Family := extend (rawChild F) (BoundedFullSampleChildSource.count F)

theorem child_access {F : Inputs} (h : F.PolyTime) : Access (child F) :=
  extend_access (rawChild_access h) (BinaryFn.ofUnary (BoundedFullSampleChildSource.count_unary h))

theorem child_defined (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (BoundedFullSampleChildCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    Defined (child F) u theta :=
  extend_defined (rawChild F) _ u theta (fun i hi =>
    (BoundedFullSampleChildCoordinates.parameter_root_coordinates F u theta ht ⟨i, hi⟩).1)

noncomputable def childParameter (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    BoundedFullSampleChildParameters.RegularParameters F u :=
  (BoundedFullSampleChildParameters.regularEquiv F u).symm x.val

theorem decode_childParameter (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    BoundedFullSampleChildParameters.decode F u (childParameter F u p x).val = x.val.val.val :=
  congrArg (fun z : BoundedFullSampleChildParameters.Candidates F u => z.val.val)
    ((BoundedFullSampleChildParameters.regularEquiv F u).apply_symm_apply x.val)

theorem child_point (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) (i : ℕ) :
    point (child F) u (childParameter F u p x).val i = Formula.extend x.val.val.val i := by
  rw [child, extend_point]
  by_cases hi : i < BoundedFullSampleChildSource.count F u
  · rw [ite_eq_left hi]
    change i < F.block.dim u + 1 at hi
    simp only [point, rawChild, Formula.extend, hi, dite_true]
    exact congrFun (decode_childParameter F u p x) ⟨i, hi⟩
  · rw [ite_eq_right hi]
    change ¬ i < F.block.dim u + 1 at hi
    simp only [Formula.extend, hi, dite_false]

theorem child_retained (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    point (child F) u (childParameter F u p x).val 0 =
      (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val := by
  rw [child_point]
  simpa only [Formula.extend, Nat.zero_lt_succ, dite_true, BoundedFullSampleChildParentThom.first] using x.property

noncomputable def ambient (F : Inputs) : Family :=
  RationalParentUpdate.update (full F.block.parent) (child F) F.block.offset F.block.dim

theorem ambient_access {F : Inputs} (h : F.PolyTime) : Access (ambient F) :=
  RationalParentUpdate.access (full_access h.block.parent h.parentArity) (child_access h)
    h.block.offset (BinaryFn.ofUnary h.block.dim)

theorem ambient_defined (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    Defined (ambient F) u (childParameter F u p x).val := by
  apply RationalParentUpdate.defined_update (full F.block.parent) (child F) F.block.offset F.block.dim
    u (childParameter F u p x).val (child_defined F u _ (childParameter F u p x).property.1)
  rw [child_retained]
  exact full_defined F.block.parent (pairFst u) p

theorem ambient_point (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) (i : ℕ) :
    point (ambient F) u (childParameter F u p x).val i =
      BoundedCriticalSampleBlockSource.assignment p.val (F.block.offset u) (F.block.dim u)
        (BoundedFullSampleChildActualSamples.point F u p x) i := by
  rw [ambient, RationalParentUpdate.point_update _ _ _ _ _ _
    (child_defined F u _ (childParameter F u p x).property.1), child_retained]
  by_cases hi : BoundedCriticalSampleBlockSource.InBlock (F.block.offset u) (F.block.dim u) i
  · rw [ite_eq_left hi, child_point]
    have hj : i - F.block.offset u + 1 < F.block.dim u + 1 := by
      unfold BoundedCriticalSampleBlockSource.InBlock at hi
      omega
    simp only [Formula.extend, hj, dite_true, BoundedCriticalSampleBlockSource.assignment,
      hi, dite_true, BoundedFullSampleChildActualSamples.point]
    rfl
  · rw [ite_eq_right hi, full_point]
    simp only [BoundedCriticalSampleBlockSource.assignment, hi, dite_false]

end LeanCanny.Encoding.FullSampleParentCoordinates
