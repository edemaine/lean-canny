/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeExpanded
import Mathlib.Tactic.Ring

/-! # The dense and sparse parts of an active tube

Only the two constraints arising from the source equation contain its dense
polynomial. Expanding their squares leaves the source square with multiplicity
zero, one, or two; source times a linear shift; and the zero-source tube.
The latter contains only the radius and affine box/shift constraints.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial Algebra.NestedPolynomial
open scoped BigOperators

variable {ι : Type*}

def sourceSquareWeight : PolynomialPerturbation.Constraint ι → ℤ
  | .inl _ => 1
  | .inr _ => 0

noncomputable def sourceLinear : PolynomialPerturbation.Constraint ι → MvPolynomial (IntegerCoordinate ι) ℤ
  | .inl false => C 2 * X (.inl (.inr (.inl false)))
  | .inl true => C (-2) * X (.inl (.inr (.inl true)))
  | .inr _ => 0

noncomputable def integerSpatial (p : MvPolynomial ι ℤ) : MvPolynomial (IntegerCoordinate ι) ℤ :=
  rename (fun i => Sum.inl (Sum.inl i)) p

theorem flatten_constraint_square (p : MvPolynomial ι ℤ) (i : PolynomialPerturbation.Constraint ι) :
    flatten (constraint p i) ^ 2 = C (sourceSquareWeight i) * integerSpatial (p ^ 2) +
      integerSpatial p * sourceLinear i + flatten (constraint (0 : MvPolynomial ι ℤ) i) ^ 2 := by
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp [constraint, sourceSquareWeight, sourceLinear, integerSpatial, flatten_spatial] <;> ring

noncomputable def squareMultiplicity (s : Finset (PolynomialPerturbation.Constraint ι)) : ℤ :=
  ∑ i ∈ s, sourceSquareWeight i

noncomputable def linearShift (s : Finset (PolynomialPerturbation.Constraint ι)) : MvPolynomial (IntegerCoordinate ι) ℤ :=
  ∑ i ∈ s, sourceLinear i

theorem squareMultiplicity_eq [DecidableEq ι] (s : Finset (PolynomialPerturbation.Constraint ι)) :
    squareMultiplicity s = (if Sum.inl false ∈ s then 1 else 0) + (if Sum.inl true ∈ s then 1 else 0) := by
  classical
  have h (i : PolynomialPerturbation.Constraint ι) : sourceSquareWeight i =
      (if i = .inl false then 1 else 0) + (if i = .inl true then 1 else 0) := by
    rcases i with b | ⟨j, b⟩ <;> cases b <;> simp [sourceSquareWeight]
  simp only [squareMultiplicity, h, Finset.sum_add_distrib]
  simp

theorem linearShift_eq [DecidableEq ι] (s : Finset (PolynomialPerturbation.Constraint ι)) :
    linearShift s = (if Sum.inl false ∈ s then C 2 * X (.inl (.inr (.inl false))) else 0) +
      (if Sum.inl true ∈ s then C (-2) * X (.inl (.inr (.inl true))) else 0) := by
  classical
  have h (i : PolynomialPerturbation.Constraint ι) : sourceLinear i =
      (if i = .inl false then C 2 * X (.inl (.inr (.inl false))) else 0) +
      (if i = .inl true then C (-2) * X (.inl (.inr (.inl true))) else 0) := by
    rcases i with b | ⟨j, b⟩ <;> cases b <;> simp [sourceLinear]
  simp only [linearShift, h, Finset.sum_add_distrib]
  simp

variable [Fintype ι]

theorem integerPolynomial_decomposition (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    integerPolynomial p s = C (squareMultiplicity s) * integerSpatial (p ^ 2) +
      integerSpatial p * linearShift s + integerPolynomial (0 : MvPolynomial ι ℤ) s := by
  classical
  simp only [integerPolynomial, polynomial, energy, map_sub, map_add, map_pow, map_sum]
  simp_rw [flatten_constraint_square p]
  simp only [Finset.sum_add_distrib, squareMultiplicity, linearShift, map_sum, Finset.sum_mul, Finset.mul_sum]
  ring

end LeanCanny.Geometry.TubePolynomial
