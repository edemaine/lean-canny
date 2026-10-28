/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry
public import LeanCanny.Encoding.BoundedCriticalParameterSeparable
public import LeanCanny.Algebra.RetainedParameterSystem
public import LeanCanny.Encoding.RegularRootLabels

/-! # A joint integer system for parent parameters and child critical points

Row zero retains the already constructed separable parameter equation.
The remaining rows are the actual block critical equations. Common degree,
mass, exponent-width, and root-label allowances have native binary controls.
These are candidate systems: parent filtering and good-direction selection
remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedCriticalRationalCoordinates.parameterDegree BoundedCriticalRationalCoordinates.baseHeight
  BoundedCriticalSampleBlockEncoding.budget BoundedCriticalSampleBlockCriticalSource.massExponent

noncomputable def system (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) :
    Fin (k u + 1) → MvPolynomial (Fin (k u + 1)) ℤ :=
  RetainedParameterSystem.system (BoundedCriticalRationalCoordinates.parameter P (pairFst u))
    (fun i => BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits u b i)

noncomputable def degree (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  max (BoundedCriticalRationalCoordinates.parameterDegree P (pairFst u))
    (BoundedCriticalSampleBlockEncoding.budget P read u)

noncomputable def massExponent (P : Readers) (read : List Bool → List Bool) (k w : List Bool → ℕ) (u : List Bool) : ℕ :=
  max (BoundedCriticalRationalCoordinates.baseHeight P (pairFst u))
    (BoundedCriticalSampleBlockCriticalSource.massExponent P read k w u)

noncomputable def width (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ := (degree P read u).size

theorem degree_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (degree P read) :=
  BivariateRationalTermReader.max_binary
    ((BoundedCriticalRationalCoordinates.parameterDegree_binary h).comp pairFst_mem_FP)
    (BoundedCriticalSampleBlockEncoding.budget_binary h read hr)

theorem massExponent_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k w : List Bool → ℕ} (hk : UnaryFn k) (hw : UnaryFn w) : BinaryFn (massExponent P read k w) :=
  BivariateRationalTermReader.max_binary ((BoundedCriticalRationalCoordinates.baseHeight_binary h).comp pairFst_mem_FP)
    (BoundedCriticalSampleBlockCriticalSource.massExponent_binary h read hr hk hw)

theorem width_unary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    UnaryFn (width P read) :=
  (UnaryFn.length (degree_binary h read hr).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (degree P read u))

theorem degree_pos (P : Readers) (read : List Bool → List Bool) (u : List Bool) : 0 < degree P read u := by
  have h : 0 < BoundedCriticalSampleBlockEncoding.budget P read u := by
    unfold BoundedCriticalSampleBlockEncoding.budget
    omega
  exact h.trans_le (Nat.le_max_right _ _)

theorem polynomial_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) :
    (system P read o k w bits u b i).totalDegree ≤ degree P read u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (IndexedMultivariateRational.parameter_degree _ _).trans
      ((BoundedCriticalRationalCoordinates.parameter_bounds P (pairFst u)).1.trans (Nat.le_max_left _ _))
  · exact (BoundedCriticalSampleBlockCriticalSource.polynomial_degree P read o k w bits u b j).trans (Nat.le_max_right _ _)

theorem polynomial_mass (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) :
    MvMass.mass (system P read o k w bits u b i) ≤ 2 ^ massExponent P read k w u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (RetainedParameterPolynomial.mass _).trans
      ((BoundedCriticalRationalCoordinates.parameter_bounds P (pairFst u)).2.trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
  · exact (BoundedCriticalSampleBlockCriticalSource.polynomial_mass P read o k w bits u b j).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem degree_lt_width (P : Readers) (read : List Bool → List Bool) (u : List Bool) :
    degree P read u < 2 ^ width P read u := Nat.lt_size_self _

noncomputable def labelWidth (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) : ℕ :=
  Geometry.RegularAffineRootCount.labelWidth (k u + 1) (degree P read u)

theorem labelWidth_unary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : UnaryFn (labelWidth P read k) :=
  RegularRootLabels.width_unary (hk.add (UnaryFn.const 1)) (degree_binary h read hr)

end LeanCanny.Encoding.BoundedCriticalSampleJointSource
