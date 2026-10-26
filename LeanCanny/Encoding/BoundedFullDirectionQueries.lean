/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullCriticalKernel
public import LeanCanny.Encoding.FermatCriticalDirection
public import LeanCanny.ETR.NumericLiteralFP

/-! # Full-source critical kernels from actual direction records

Direction entries are read from fixed-width binary blocks, with a width
computed from the original source controls. The shared Hessian query copies
their signed integer literals without converting their values to unary.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullDirectionQueries
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation BoundedFullWriter
open scoped Classical

noncomputable def width (P : Readers) (c : List Bool) : ℕ :=
  LeanCanny.Algebra.FermatBoundedCriticalDirection.binaryWidth (P.dim c + 3) (degree P c)

theorem degree_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    degree (P.comp f) c = degree P (f c) := rfl

noncomputable def direction (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℤ :=
  FixedWidthQuery.coordinate (width P) record c i

theorem direction_comp (P : Readers) (record f : List Bool → List Bool) (c : List Bool) :
    direction (P.comp f) (record ∘ f) c = direction P record (f c) := rfl

theorem direction_at (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    direction P record c = direction P (fun _ => record c) c := rfl

theorem direction_eq (P Q : Readers) (r s : List Bool → List Bool) (c d : List Bool)
    (hd : P.dim c = Q.dim d) (hN : degree P c = degree Q d) (hr : r c = s d) :
    direction P r c = direction Q s d := by
  funext i
  simp only [direction, FixedWidthQuery.coordinate, width, hd, hN, hr]

theorem width_unary {P : Readers} (h : P.PolyTime) : UnaryFn (width P) :=
  FermatCriticalDirection.binaryWidth_unary (h.dim.add (UnaryFn.const 3)) (degree_binary h)

theorem width_pos (P : Readers) (c : List Bool) : 0 < width P c := by
  unfold width LeanCanny.Algebra.FermatBoundedCriticalDirection.binaryWidth
  omega

theorem recordLength_unary {P : Readers} (h : P.PolyTime) : UnaryFn (fun c => (P.dim c + 3) * width P c) :=
  (h.dim.add (UnaryFn.const 3)).mul (width_unary h)

theorem direction_eq_assignment (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (j : Fin (P.dim c + 3)) : direction P record c j.val =
      (FermatCriticalDirection.assignment (P.dim c + 3) (degree P c) (record c) j : ℤ) := rfl

theorem literal_mem_FP {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP) :
    (fun p => (Term.const (-direction P record (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP := by
  have hw := (width_unary h).comp pairFst_mem_FP
  have hb := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP hr)
    ((UnaryFn.length pairSnd_mem_FP).mul hw)) hw
  exact mem_FP_of_eq (Term.negNat_toBits_mem_FP (BinaryFn.fromBits hb)) (fun _ => rfl)

theorem encode_mem_FP {P : Readers} {record : List Bool → List Bool} {chart : List Bool → ℕ}
    (h : P.PolyTime) (hr : record ∈ FP) (hi : UnaryFn chart) :
    (fun c => encode (BoundedFullCriticalKernel.query P (direction P record c) (chart c) c)) ∈ FP :=
  BoundedFullCriticalKernel.encode_mem_FP h hi (literal_mem_FP h hr)

theorem bad_evaluator {P : Readers} {record : List Bool → List Bool}
    {chart : (c : List Bool) → Fin (P.dim c + 4)} (h : P.PolyTime) (hr : record ∈ FP)
    (hi : UnaryFn (fun c => (chart c).val))
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P c)
      (direction P record c) (chart c))]) :=
  BoundedFullCriticalKernel.bad_evaluator h hi (literal_mem_FP h hr) ht

theorem empty_evaluator {P : Readers} {record : List Bool → List Bool}
    {chart : (c : List Bool) → Fin (P.dim c + 4)} (h : P.PolyTime) (hr : record ∈ FP)
    (hi : UnaryFn (fun c => (chart c).val))
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (¬ CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P c)
      (direction P record c) (chart c))]) :=
  BoundedFullCriticalKernel.empty_evaluator h hi (literal_mem_FP h hr) ht

end LeanCanny.Encoding.BoundedFullDirectionQueries
