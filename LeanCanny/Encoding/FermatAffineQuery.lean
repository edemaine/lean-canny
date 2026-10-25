/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatSampledIdentity
public import LeanCanny.Encoding.FermatFrozenSource
public import LeanCanny.Encoding.FermatInfinityQuery
public import LeanCanny.ETR.ComplexSampledPSPACE

/-! # Native affine-chart tests from the actual source and sampled record

The compiled term, both binary exponents, and the record's actual sample and
direction fields generate the complete shared critical-kernel query. Its
native PSPACE tests match the existing affine bad-root predicate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatAffineQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open FermatSweepCertificate MvPolynomial
open scoped Classical

def direction (dim degree : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) (k : ℕ) : ℤ :=
  FermatInfinityQuery.coefficient dim degree record c (k + 1)

theorem direction_eq (dim degree : List Bool → ℕ) (record : List Bool → List Bool)
    (c : List Bool) (j : Fin (dim c)) :
    direction dim degree record c j.val = (FermatSweepCertificate.direction (dim c) (degree c) (record c) j : ℤ) := rfl

theorem directionLiteral_mem_FP {dim degree : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hr : record ∈ FP) :
    (fun p => (Term.const (-direction dim degree record (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP := by
  have hp := mem_FP_pair pairFst_mem_FP (((UnaryFn.length pairSnd_mem_FP).add (UnaryFn.const 1)).mem_FP)
  have h := mem_FP_comp hp (FermatInfinityQuery.coefficientLiteral_mem_FP hd hN hr)
  exact mem_FP_of_eq h (fun p => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, direction])

noncomputable def query (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) : List Gate :=
  SampledSource.kernelQuery source (fun c => (degree c - 1).bits) (fun c => (exponent c).bits)
    (FermatFrozenSource.sourceStart source dim) (fun c => dim c + 1) chart
    (fun c => (FermatFrozenSource.sampleValue dim degree record c : ℤ)) a (direction dim degree record) c

noncomputable def dataQuery (source record : List Bool) (n N E chart : ℕ) (a : ℤ) : List Gate :=
  let t := TermView.term source
  let start := max t.toData.size (n + 1)
  CriticalKernel.query start (n + 1)
    (SampledSource.program t.toData.size start (n + 1) (sample n N record : ℤ) a t (N - 1).bits E.bits)
    (SampledSource.output start (n + 1) t (N - 1).bits E.bits)
    (fun k => (Nat.fromBitsLE ((record.drop (k * width n N)).take (width n N)) : ℤ)) chart

theorem query_eq_data (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) :
    query source record dim degree exponent chart a c =
      dataQuery (source c) (record c) (dim c) (degree c) (exponent c) (chart c) (a c) := rfl

theorem encode_mem_FP {source record : List Bool → List Bool} {dim degree exponent chart : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hr : record ∈ FP) (hd : UnaryFn dim)
    (hN : BinaryFn degree) (hE : BinaryFn exponent) (hi : UnaryFn chart)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    (fun c => encode (query source record dim degree exponent chart a c)) ∈ FP :=
  SampledSource.kernelQuery_encode_mem_FP ht (FermatFrozenSource.sourceStart_unary ht hd)
    (hd.add (UnaryFn.const 1)) hi (Term.nat_toBits_mem_FP (FermatFrozenSource.sample_binary hd hN hr)) ha
    (hN.sub (BinaryFn.const 1)).bits_mem_FP hE.bits_mem_FP (directionLiteral_mem_FP hd hN hr)

theorem query_correct (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low)
    (hN : 0 < degree c) (hi : chart c < dim c + 1) :
    Satisfiable (query source record dim degree exponent chart a c) ↔
      AffineBad (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c) ⟨chart c, hi⟩ := by
  have hc := SampledSource.kernel_satisfiable (TermView.term (source c)).toData.size
    (FermatFrozenSource.sourceStart source dim c) (dim c + 1)
    (FermatFrozenSource.sampleValue dim degree record c : ℤ) (a c) (TermView.term (source c))
    (degree c - 1).bits (exponent c).bits (direction dim degree record c) (chart c)
    (Term.arity_le_dataSize _) (Nat.le_max_left ..) (Nat.le_max_right ..) hi
  simp only [query, SampledSource.kernelQuery]
  rw [hc]
  have hs := sampled_source_identity (TermView.term (source c)) low ht (a c) (degree c) (record c)
    (degree c - 1).bits (exponent c).bits (by rw [Nat.fromBitsLE_bits]; omega)
  simp only [Nat.fromBitsLE_bits] at hs
  exact (CriticalKernel.bad_iff_finite _ _ hs (direction dim degree record c) ⟨chart c, hi⟩).trans
    (finite_bad_iff_affine _ _ _ _ _ (fun j => direction_eq dim degree record c j) ⟨chart c, hi⟩)

noncomputable def bad (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) : List Bool := [decide (Satisfiable (query source record dim degree exponent chart a c))]

noncomputable def empty (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) : List Bool := [decide (¬ Satisfiable (query source record dim degree exponent chart a c))]

theorem bad_evaluator {source record : List Bool → List Bool} {dim degree exponent chart : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hr : record ∈ FP) (hd : UnaryFn dim)
    (hN : BinaryFn degree) (hE : BinaryFn exponent) (hi : UnaryFn chart)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (bad source record dim degree exponent chart a) := feasible_generated (encode_mem_FP ht hr hd hN hE hi ha)

theorem empty_evaluator {source record : List Bool → List Bool} {dim degree exponent chart : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hr : record ∈ FP) (hd : UnaryFn dim)
    (hN : BinaryFn degree) (hE : BinaryFn exponent) (hi : UnaryFn chart)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (empty source record dim degree exponent chart a) := empty_generated (encode_mem_FP ht hr hd hN hE hi ha)

theorem bad_correct (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (hN : 0 < degree c) (hi : chart c < dim c + 1) :
    bad source record dim degree exponent chart a c =
      [decide (AffineBad (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c) ⟨chart c, hi⟩)] := by
  simp only [bad, query_correct source record dim degree exponent chart a c low ht hN hi]

theorem empty_correct (source record : List Bool → List Bool) (dim degree exponent chart : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (hN : 0 < degree c) (hi : chart c < dim c + 1) :
    empty source record dim degree exponent chart a c =
      [decide (¬ AffineBad (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c) ⟨chart c, hi⟩)] := by
  simp only [empty, query_correct source record dim degree exponent chart a c low ht hN hi]

end LeanCanny.Encoding.FermatAffineQuery
