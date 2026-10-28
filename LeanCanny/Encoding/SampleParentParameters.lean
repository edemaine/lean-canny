/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparablePolynomialFamily
public import LeanCanny.Encoding.FullSampleParentCoordinates
public import LeanCanny.Encoding.BoundedCriticalParameterSeparable

/-! # Native separable parameters for original and derived parents -/

@[expose] public section
namespace LeanCanny.Encoding.SampleParentParameters
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open SeparablePolynomialFamily
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedFullSampleChildCoordinates.parameter

noncomputable def full (P : BoundedFullWriter.Readers) : Source where
  polynomial := BoundedCriticalRationalCoordinates.parameter P
  degree := BoundedCriticalRationalCoordinates.parameterDegree P
  mass := BoundedCriticalRationalCoordinates.baseHeight P
  degree_le u := (BoundedCriticalRationalCoordinates.parameter_bounds P u).1
  mass_le u := (BoundedCriticalRationalCoordinates.parameter_bounds P u).2
  separable u := BoundedCriticalRationalCoordinates.parameter_separable P u

theorem full_access {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) : Access (full P) :=
  ⟨BoundedCriticalRationalCoordinates.parameterDegree_binary h,
    BoundedCriticalRationalCoordinates.baseHeight_binary h,
    BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha⟩

noncomputable def child (F : BoundedFullSampleChildSource.Inputs) : Source where
  polynomial := BoundedFullSampleChildCoordinates.parameter F
  degree := BoundedFullSampleChildCoordinates.parameterDegree F
  mass := BoundedFullSampleChildCoordinates.baseHeight F
  degree_le u := (BoundedFullSampleChildCoordinates.parameter_bounds F u).1
  mass_le u := (BoundedFullSampleChildCoordinates.parameter_bounds F u).2
  separable u := BoundedFullSampleChildCoordinates.parameter_separable F u

theorem child_access {F : BoundedFullSampleChildSource.Inputs} (h : F.PolyTime) : Access (child F) :=
  ⟨BoundedFullSampleChildCoordinates.parameterDegree_binary h,
    BoundedFullSampleChildCoordinates.baseHeight_binary h,
    BoundedFullSampleChildCoordinates.parameter_coefficient_evaluator h⟩

theorem child_root (F : BoundedFullSampleChildSource.Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    ((child F).polynomial u).eval₂ (Int.castRingHom ℝ)
      (FullSampleParentCoordinates.childParameter F u p x).val = 0 :=
  (FullSampleParentCoordinates.childParameter F u p x).property.1

end LeanCanny.Encoding.SampleParentParameters
