/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentFullBlockCritical
public import LeanCanny.Algebra.SeparablePolynomialFamily
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
namespace LeanCanny.Encoding.RationalParentJointSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open RationalParentFullBlock (degreeBound degreeBound_pos degreeBound_binary)
open scoped Classical
attribute [local irreducible] RationalParentFullBlock.degreeBound RationalParentFullBlockCriticalSource.massExponent

structure Inputs where
  block : RationalParentFullBlock.Inputs
  parent : SeparablePolynomialFamily.Source

structure Inputs.Access (F : Inputs) : Prop where
  block : F.block.Access
  parent : SeparablePolynomialFamily.Access F.parent

noncomputable def system (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.block.dim u)) :
    Fin (F.block.dim u + 1) → MvPolynomial (Fin (F.block.dim u + 1)) ℤ :=
  RetainedParameterSystem.system (F.parent.polynomial u)
    (fun i => RationalParentFullBlockCriticalSource.polynomial F.block w bits u b i)

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  max (F.parent.degree u)
    (degreeBound F.block u)

noncomputable def massExponent (F : Inputs) (w : List Bool → ℕ) (u : List Bool) : ℕ :=
  max (F.parent.mass u)
    (RationalParentFullBlockCriticalSource.massExponent F.block w u)

noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degree F u).size

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  BivariateRationalTermReader.max_binary
    h.parent.degree
    (degreeBound_binary h.block)

theorem massExponent_binary {F : Inputs} (h : F.Access)
    {w : List Bool → ℕ} (hw : UnaryFn w) : BinaryFn (massExponent F w) :=
  BivariateRationalTermReader.max_binary
    h.parent.mass
    (RationalParentFullBlockCriticalSource.massExponent_binary h.block hw)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (degree_binary h).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (degree F u))

theorem degree_pos (F : Inputs) (u : List Bool) : 0 < degree F u :=
  (degreeBound_pos F.block u).trans_le (Nat.le_max_right _ _)

theorem polynomial_degree (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.block.dim u)) (i : Fin (F.block.dim u + 1)) :
    (system F w bits u b i).totalDegree ≤ degree F u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (IndexedMultivariateRational.parameter_degree _ _).trans
      ((F.parent.degree_le u).trans (Nat.le_max_left _ _))
  · exact (RationalParentFullBlockCriticalSource.polynomial_degree F.block w bits u b j).trans (Nat.le_max_right _ _)

theorem polynomial_mass (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.block.dim u)) (i : Fin (F.block.dim u + 1)) :
    MvMass.mass (system F w bits u b i) ≤ 2 ^ massExponent F w u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (RetainedParameterPolynomial.mass _).trans
      ((F.parent.mass_le u).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
  · exact (RationalParentFullBlockCriticalSource.polynomial_mass F.block w bits u b j).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem degree_lt_width (F : Inputs) (u : List Bool) :
    degree F u < 2 ^ width F u := Nat.lt_size_self _

noncomputable def labelWidth (F : Inputs) (u : List Bool) : ℕ :=
  Geometry.RegularAffineRootCount.labelWidth (F.block.dim u + 1) (degree F u)

theorem labelWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (labelWidth F) :=
  RegularRootLabels.width_unary (h.block.dim.add (UnaryFn.const 1)) (degree_binary h)

end LeanCanny.Encoding.RationalParentJointSource
