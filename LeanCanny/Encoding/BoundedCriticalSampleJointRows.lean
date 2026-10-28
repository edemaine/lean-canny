/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointCoordinate
public import LeanCanny.Encoding.BoundedCriticalSampleJointWidth
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Native homogenized rows for regular child coordinate equations

Query metadata may be attached through any native context extractor. The
joint integer source remains implicit, and every original coefficient call
is included in the space certificate.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointRows
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleJointSource.system BoundedCriticalSampleJointSource.degree
  BoundedCriticalSampleJointCoordinate.width HomogenizationPolynomialBits.integerValue
  BoundedCriticalSampleJointWidth.value AffineCoordinateRowsBits.value

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits context : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k (context u) + 1))
    (row : (u : List Bool) → Fin (k (context u) + 2))
    (parameter modulus : List Bool → List Bool) : List Bool → List Bool :=
  AffineCoordinateRowsBits.value (fun u => k (context u) + 1)
    (BoundedCriticalSampleJointCoordinate.width P read k ∘ context)
    (BoundedCriticalSampleJointSource.degree P read ∘ context)
    (fun u => BoundedCriticalSampleJointSource.system P read o k w bits (context u) (pivot (context u)))
    coordinate row parameter modulus

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w)
    {bits context : List Bool → List Bool} (hbits : bits ∈ FP) (hctx : context ∈ FP)
    (pivot : (u : List Bool) → Fin (k u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (k (context u) + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (row : (u : List Bool) → Fin (k (context u) + 2)) (hi : UnaryFn (fun u => (row u).val))
    {parameter modulus : List Bool → List Bool} (ht : parameter ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P read o k w bits context pivot coordinate row parameter modulus) := by
  have hn := (hk.comp hctx).add (UnaryFn.const 1)
  have hW : UnaryFn (BoundedCriticalSampleJointCoordinate.width P read k ∘ context) :=
    (BoundedCriticalSampleJointCoordinate.width_unary h read hr hk).comp hctx
  let tail := AffineCoordinateRowsBits.tailRow (fun u => k (context u) + 1) (fun _ => by omega) row
  have htai : UnaryFn (fun u => (tail u).val) := AffineCoordinateRowsBits.tailRow_unary hn _ row hi
  have E := BoundedCriticalSampleJointWidth.evaluator h read hr ho hk hw hW hbits pivot hp hctx tail htai hm ha
  have EJ : SpaceFunction (HomogenizationPolynomialBits.integerValue (fun u => k (context u) + 1)
      (BoundedCriticalSampleJointCoordinate.width P read k ∘ context)
      (fun u => BoundedCriticalSampleJointSource.system P read o k w bits (context u) (pivot (context u)) (tail u)) modulus) := by
    simpa only [BoundedCriticalSampleJointWidth.value] using E
  exact AffineCoordinateRowsBits.evaluator hn hW ((BoundedCriticalSampleJointSource.degree_binary h read hr).comp hctx)
    (fun _ => by omega) (fun u => BoundedCriticalSampleJointCoordinate.width_pos P read k (context u))
    (fun u => BoundedCriticalSampleJointSource.system P read o k w bits (context u) (pivot (context u)))
    coordinate hc row hi ht hm EJ

end LeanCanny.Encoding.BoundedCriticalSampleJointRows
