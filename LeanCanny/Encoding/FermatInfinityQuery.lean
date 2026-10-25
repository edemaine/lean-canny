/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatSweepKernelCertificate
public import LeanCanny.ETR.ComplexInfinityFinite
public import LeanCanny.ETR.ComplexInfinityEncoding
public import LeanCanny.ETR.ComplexCircuitPSPACE

/-! # Native infinity-chart tests from the actual sampled record

The source leading coefficient cancels, so the query writer needs only the
dimension, binary degree, chart index, and fixed-width direction record.
The supplied record reader is composed with literal generation and ETR;
no feasibility or coefficient oracle is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatInfinityQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open FermatSweepCertificate
open scoped Classical

def value (dim degree : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) (j : ℕ) : ℕ :=
  FixedWidthQuery.coordinate (fun c => width (dim c) (degree c)) record c (j - 1)

def coefficient (dim degree : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) (j : ℕ) : ℤ :=
  value dim degree record c j

def query (dim degree index : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) : List Gate :=
  Infinity.query (dim c + 1) (degree c - 1).bits (coefficient dim degree record c) (index c)

def dataQuery (record : List Bool) (n N chart : ℕ) : List Gate :=
  Infinity.query (n + 1) (N - 1).bits
    (fun k => (Nat.fromBitsLE ((record.drop ((k - 1) * width n N)).take (width n N)) : ℤ)) chart

theorem query_eq_data (dim degree index : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) :
    query dim degree index record c = dataQuery (record c) (dim c) (degree c) (index c) := rfl

theorem coefficientLiteral_mem_FP {dim degree : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hr : record ∈ FP) :
    (fun q => (Term.const (-(coefficient dim degree record (pairFst q) (pairSnd q).length))).toData.toBits) ∈ FP := by
  have hw := UnaryFn.comp (f := fun c => width (dim c) (degree c)) (g := pairFst)
    (width_unary hd hN) pairFst_mem_FP
  have hj := (UnaryFn.length pairSnd_mem_FP).sub (UnaryFn.const 1)
  have hrp := mem_FP_comp (f := pairFst) (g := record) pairFst_mem_FP hr
  have hb := take_mem_FP (drop_mem_FP hrp (hj.mul hw)) hw
  have h := Term.negNat_toBits_mem_FP (BinaryFn.fromBits hb)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem encode_mem_FP {dim degree index : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hi : UnaryFn index) (hr : record ∈ FP) :
    (fun c => encode (query dim degree index record c)) ∈ FP :=
  Infinity.encode_mem_FP (hd.add (UnaryFn.const 1)) hi (hN.sub (BinaryFn.const 1)).bits_mem_FP
    (coefficientLiteral_mem_FP hd hN hr)

theorem value_succ (dim degree : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) (j : Fin (dim c)) :
    value dim degree record c (j.val + 1) = direction (dim c) (degree c) (record c) j := rfl

theorem query_correct (dim degree index : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) (a : ℚ) (ha : a ≠ 0) (hN : 0 < degree c) (hi : index c < dim c + 1) :
    Satisfiable (query dim degree index record c) ↔ InfinityBad a (degree c) (record c) ⟨index c, hi⟩ := by
  rw [query, Infinity.query_satisfiable_fin (dim c) (degree c - 1).bits
    (coefficient dim degree record c) ⟨index c, hi⟩,
    infinity_bad_iff_reduced a ha (degree c) hN (record c) ⟨index c, hi⟩]
  have he : degree c - 1 + 1 = degree c := by omega
  simp only [Nat.fromBitsLE_bits, he, coefficient, value_succ, Int.cast_natCast]

noncomputable def bad (dim degree index : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) : List Bool := [decide (Satisfiable (query dim degree index record c))]

noncomputable def empty (dim degree index : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) : List Bool := [decide (¬ Satisfiable (query dim degree index record c))]

theorem bad_evaluator {dim degree index : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hi : UnaryFn index) (hr : record ∈ FP) :
    SpaceFunction (bad dim degree index record) := feasible_generated (encode_mem_FP hd hN hi hr)

theorem empty_evaluator {dim degree index : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hi : UnaryFn index) (hr : record ∈ FP) :
    SpaceFunction (empty dim degree index record) := empty_generated (encode_mem_FP hd hN hi hr)

theorem bad_correct (dim degree index : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) (a : ℚ) (ha : a ≠ 0) (hN : 0 < degree c) (hi : index c < dim c + 1) :
    bad dim degree index record c = [decide (InfinityBad a (degree c) (record c) ⟨index c, hi⟩)] := by
  simp only [bad, query_correct dim degree index record c a ha hN hi]

theorem empty_correct (dim degree index : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) (a : ℚ) (ha : a ≠ 0) (hN : 0 < degree c) (hi : index c < dim c + 1) :
    empty dim degree index record c = [decide (¬ InfinityBad a (degree c) (record c) ⟨index c, hi⟩)] := by
  simp only [empty, query_correct dim degree index record c a ha hN hi]

end LeanCanny.Encoding.FermatInfinityQuery
