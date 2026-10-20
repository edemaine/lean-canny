/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularMacaulay
public import LeanCanny.Algebra.PartialCoefficientSpace

/-! # Spatial and parameter blocks for the full regular tube system

The first block contains the homogenizing variable, reciprocal, and original
point. Directions and the three perturbation parameters form the second block.
The combined layout preserves the actual integer coefficient reader's order.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev Spatial (bits : List Bool) := Option (Option (TubeSource.Coordinate bits))
abbrev Parameter (bits : List Bool) := Sum (Point (TubeIndexed.arity bits)) TubePolynomial.Parameter

noncomputable def spatialCount (bits : List Bool) : ℕ := pointCount (TubeIndexed.arity bits) + 1 + 1
noncomputable def parameterCount (bits : List Bool) : ℕ := pointCount (TubeIndexed.arity bits) + 3
noncomputable def nativeCount (bits : List Bool) : ℕ := TubeIndexed.projectionDimension bits + 1 + 1


theorem counts_add (bits : List Bool) : spatialCount bits + parameterCount bits = nativeCount bits := by
  unfold spatialCount parameterCount nativeCount TubeIndexed.projectionDimension TubeProjectionEncoding.dimension
  omega

theorem spatialCount_unary : UnaryFn spatialCount :=
  ((TubeProjectionQuery.pointCount_unary TubeIndexed.arity_unary).add (UnaryFn.const 1)).add (UnaryFn.const 1)

theorem parameterCount_unary : UnaryFn parameterCount :=
  (TubeProjectionQuery.pointCount_unary TubeIndexed.arity_unary).add (UnaryFn.const 3)

theorem nativeCount_unary : UnaryFn nativeCount :=
  (TubeIndexed.projectionDimension_unary.add (UnaryFn.const 1)).add (UnaryFn.const 1)

noncomputable def spatialEquiv (bits : List Bool) : Spatial bits ≃ Fin (spatialCount bits) :=
  TubeRegularMacaulay.coordinateEquiv (TubeIndexed.arity bits)

noncomputable def parameterEquiv (bits : List Bool) : Parameter bits ≃ Fin (parameterCount bits) :=
  (Equiv.sumCongr (pointEquiv (TubeIndexed.arity bits)) TubeEncoding.parameterEquiv).trans finSumFinEquiv

noncomputable def fullEquiv (bits : List Bool) : Sum (Spatial bits) (Parameter bits) ≃ Fin (nativeCount bits) :=
  (TubeRegularMacaulay.splitVariables (TubeIndexed.arity bits)).symm.trans (TubeRegularHomogenization.outputEquiv bits)

theorem full_left (bits : List Bool) (i : Spatial bits) : (fullEquiv bits (.inl i)).val = (spatialEquiv bits i).val := by
  rcases i with _ | (_ | i) <;> rfl

theorem full_right (bits : List Bool) (i : Parameter bits) :
    (fullEquiv bits (.inr i)).val = spatialCount bits + (parameterEquiv bits i).val := by
  cases i with
  | inl i =>
    change (pointCount (TubeIndexed.arity bits) + (pointEquiv (TubeIndexed.arity bits) i).val + 1 + 1) =
      pointCount (TubeIndexed.arity bits) + 1 + 1 + (pointEquiv (TubeIndexed.arity bits) i).val
    omega
  | inr p =>
    change (pointCount (TubeIndexed.arity bits) + pointCount (TubeIndexed.arity bits) +
      (TubeEncoding.parameterEquiv p).val + 1 + 1) =
      pointCount (TubeIndexed.arity bits) + 1 + 1 + (pointCount (TubeIndexed.arity bits) + (TubeEncoding.parameterEquiv p).val)
    omega

noncomputable def nativePolynomial (source active row : List Bool → List Bool) (c : List Bool) :
    MvPolynomial (TubeRegularHomogenization.Native (source c)) ℤ :=
  TubeRegularHomogenization.polynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
    (TubeRegularBits.decodedIndex source row c)

noncomputable def spatialPolynomial (source active row : List Bool → List Bool) (c : List Bool) :
    MvPolynomial (Spatial (source c)) (TubeMacaulay.Coefficients (TubeIndexed.arity (source c))) :=
  TubeRegularMacaulay.spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
    (TubeRegularBits.decodedIndex source row c)

noncomputable def flatPolynomial (source active row : List Bool → List Bool) (c : List Bool) :
    MvPolynomial (Sum (Spatial (source c)) (Parameter (source c))) ℤ :=
  NestedPolynomial.flatten (spatialPolynomial source active row c)

theorem flat_eq (source active row : List Bool → List Bool) (c : List Bool) :
    flatPolynomial source active row c =
      MvPolynomial.rename (TubeRegularMacaulay.splitVariables (TubeIndexed.arity (source c))) (nativePolynomial source active row c) :=
  TubeRegularMacaulay.flatten_spatial _ _ _

theorem flat_coefficient (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    (flatPolynomial source active row c).coeff (FixedWidthPolynomial.nativeExponent (fullEquiv (source c)) (TubeIndexed.blockWidth (source c)) r) =
      (nativePolynomial source active row c).coeff (FixedWidthPolynomial.nativeExponent (TubeRegularHomogenization.outputEquiv (source c))
        (TubeIndexed.blockWidth (source c)) r) := by
  rw [flat_eq]
  exact PartialCoefficient.coeff_rename_native _ _ _ _ _ _

theorem flat_support_fits (source active row : List Bool → List Bool) (c : List Bool)
    (m : Sum (Spatial (source c)) (Parameter (source c)) →₀ ℕ) (hm : m ∈ (flatPolynomial source active row c).support)
    (i : Sum (Spatial (source c)) (Parameter (source c))) : m i < 2 ^ TubeIndexed.blockWidth (source c) := by
  rw [flat_eq] at hm
  dsimp +instances only [TubeIndexed.arity, Spatial, Parameter] at *
  rw [MvPolynomial.support_rename_of_injective (TubeRegularMacaulay.splitVariables _).injective] at hm
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
  calc
    _ = e ((TubeRegularMacaulay.splitVariables (CompactSource.term (source c)).arity).symm i) :=
      Finsupp.mapDomain_equiv_apply _ _
    _ < _ := TubeRegularHomogenization.support_fits _ _ _ e he _

end LeanCanny.ETR.TubeParameter
