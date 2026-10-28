/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentJointCoordinate
public import LeanCanny.Encoding.RationalParentJointWidth
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Native homogenized rows for regular child coordinate equations

Query metadata may be attached through any native context extractor. The
joint integer source remains implicit, and every original coefficient call
is included in the space certificate.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentJointRows
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open RationalParentJointSource (Inputs)
open scoped Classical
attribute [local irreducible] RationalParentJointSource.system RationalParentJointSource.degree
  RationalParentJointCoordinate.width HomogenizationPolynomialBits.integerValue
  RationalParentJointWidth.value AffineCoordinateRowsBits.value

noncomputable def value (F : Inputs) (w : List Bool → ℕ)
    (bits context : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.block.dim u))
    (coordinate : (u : List Bool) → Fin (F.block.dim (context u) + 1))
    (row : (u : List Bool) → Fin (F.block.dim (context u) + 2))
    (parameter modulus : List Bool → List Bool) : List Bool → List Bool :=
  AffineCoordinateRowsBits.value (fun u => F.block.dim (context u) + 1)
    (RationalParentJointCoordinate.width F ∘ context)
    (RationalParentJointSource.degree F ∘ context)
    (fun u => RationalParentJointSource.system F w bits (context u) (pivot (context u)))
    coordinate row parameter modulus

theorem evaluator {F : Inputs} (h : F.Access)
    {w : List Bool → ℕ} (hw : UnaryFn w)
    {bits context : List Bool → List Bool} (E : SpaceFunction bits) (hctx : context ∈ FP)
    (pivot : (u : List Bool) → Fin (F.block.dim u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (F.block.dim (context u) + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (row : (u : List Bool) → Fin (F.block.dim (context u) + 2)) (hi : UnaryFn (fun u => (row u).val))
    {parameter modulus : List Bool → List Bool} (ht : parameter ∈ FP) (hm : modulus ∈ FP)
    (htS : ∀ u, (TermView.term (F.block.source.source u)).arity ≤ F.block.source.dim u) :
    SpaceFunction (value F w bits context pivot coordinate row parameter modulus) := by
  have hn := (h.block.dim.comp hctx).add (UnaryFn.const 1)
  have hW : UnaryFn (RationalParentJointCoordinate.width F ∘ context) :=
    (RationalParentJointCoordinate.width_unary h).comp hctx
  let tail := AffineCoordinateRowsBits.tailRow (fun u => F.block.dim (context u) + 1) (fun _ => by omega) row
  have htai : UnaryFn (fun u => (tail u).val) := AffineCoordinateRowsBits.tailRow_unary hn _ row hi
  have EJW := RationalParentJointWidth.evaluator h hw hW E pivot hp hctx tail htai hm htS
  have EJ : SpaceFunction (HomogenizationPolynomialBits.integerValue (fun u => F.block.dim (context u) + 1)
      (RationalParentJointCoordinate.width F ∘ context)
      (fun u => RationalParentJointSource.system F w bits (context u) (pivot (context u)) (tail u)) modulus) := by
    simpa only [RationalParentJointWidth.value] using EJW
  exact AffineCoordinateRowsBits.evaluator hn hW ((RationalParentJointSource.degree_binary h).comp hctx)
    (fun _ => by omega) (fun u => RationalParentJointCoordinate.width_pos F (context u))
    (fun u => RationalParentJointSource.system F w bits (context u) (pivot (context u)))
    coordinate hc row hi ht hm EJ

end LeanCanny.Encoding.RationalParentJointRows
