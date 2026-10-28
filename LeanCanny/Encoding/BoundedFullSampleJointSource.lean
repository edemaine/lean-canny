/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleBlockCritical
public import LeanCanny.Encoding.BoundedCriticalParameterSeparable
public import LeanCanny.Algebra.RetainedParameterSystem
public import LeanCanny.Encoding.RegularRootLabels

/-! # A joint integer system for parent parameters and child critical points

Row zero retains the already constructed separable parameter equation.
The remaining rows are the actual block critical equations. Common degree,
mass, exponent-width, and root-label allowances have native binary controls.
These are full-source candidate systems: parent filtering and good-direction selection
remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open BoundedFullSampleBlock
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedCriticalRationalCoordinates.parameterDegree BoundedCriticalRationalCoordinates.baseHeight
  BoundedFullSampleBlock.degreeBound BoundedFullSampleBlockCriticalSource.massExponent

noncomputable def system (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) :
    Fin (F.dim u + 1) → MvPolynomial (Fin (F.dim u + 1)) ℤ :=
  RetainedParameterSystem.system (BoundedCriticalRationalCoordinates.parameter F.parent (pairFst u))
    (fun i => BoundedFullSampleBlockCriticalSource.polynomial F w bits u b i)

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  max (BoundedCriticalRationalCoordinates.parameterDegree F.parent (pairFst u))
    (degreeBound F u)

noncomputable def massExponent (F : Inputs) (w : List Bool → ℕ) (u : List Bool) : ℕ :=
  max (BoundedCriticalRationalCoordinates.baseHeight F.parent (pairFst u))
    (BoundedFullSampleBlockCriticalSource.massExponent F w u)

noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degree F u).size

theorem degree_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (degree F) :=
  BivariateRationalTermReader.max_binary
    ((BoundedCriticalRationalCoordinates.parameterDegree_binary h.parent).comp pairFst_mem_FP)
    (degreeBound_binary h)

theorem massExponent_binary {F : Inputs} (h : F.PolyTime)
    {w : List Bool → ℕ} (hw : UnaryFn w) : BinaryFn (massExponent F w) :=
  BivariateRationalTermReader.max_binary
    ((BoundedCriticalRationalCoordinates.baseHeight_binary h.parent).comp pairFst_mem_FP)
    (BoundedFullSampleBlockCriticalSource.massExponent_binary h hw)

theorem width_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (width F) :=
  (UnaryFn.length (degree_binary h).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (degree F u))

theorem degree_pos (F : Inputs) (u : List Bool) : 0 < degree F u :=
  (degreeBound_pos F u).trans_le (Nat.le_max_right _ _)

theorem polynomial_degree (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) :
    (system F w bits u b i).totalDegree ≤ degree F u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (IndexedMultivariateRational.parameter_degree _ _).trans
      ((BoundedCriticalRationalCoordinates.parameter_bounds F.parent (pairFst u)).1.trans (Nat.le_max_left _ _))
  · exact (BoundedFullSampleBlockCriticalSource.polynomial_degree F w bits u b j).trans (Nat.le_max_right _ _)

theorem polynomial_mass (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) :
    MvMass.mass (system F w bits u b i) ≤ 2 ^ massExponent F w u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (RetainedParameterPolynomial.mass _).trans
      ((BoundedCriticalRationalCoordinates.parameter_bounds F.parent (pairFst u)).2.trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
  · exact (BoundedFullSampleBlockCriticalSource.polynomial_mass F w bits u b j).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem degree_lt_width (F : Inputs) (u : List Bool) :
    degree F u < 2 ^ width F u := Nat.lt_size_self _

noncomputable def labelWidth (F : Inputs) (u : List Bool) : ℕ :=
  Geometry.RegularAffineRootCount.labelWidth (F.dim u + 1) (degree F u)

theorem labelWidth_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (labelWidth F) :=
  RegularRootLabels.width_unary (h.dim.add (UnaryFn.const 1)) (degree_binary h)

end LeanCanny.Encoding.BoundedFullSampleJointSource
