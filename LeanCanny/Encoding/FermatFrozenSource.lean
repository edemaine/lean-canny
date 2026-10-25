/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatSweepCertificate
public import LeanCanny.ETR.ComplexFrozenSlice
public import LeanCanny.ETR.NumericLiteralFP

/-! # Frozen source circuits from the actual sweep-sample record

The finite certificate's sample field is read in binary. The source compiler,
wire reindexing, sample literal, and fresh-wire metadata all have native time
certificates. The original source polynomial remains explicit in correctness.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatFrozenSource
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open FermatSweepCertificate

def sampleValue (dim degree : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) : ℕ :=
  sample (dim c) (degree c) (record c)

theorem sample_binary {dim degree : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hr : record ∈ FP) : BinaryFn (sampleValue dim degree record) := by
  have hw := width_unary hd hN
  have h := BinaryFn.fromBits (take_mem_FP (drop_mem_FP hr (hd.mul hw)) hw)
  exact h.of_eq (fun c => rfl)

noncomputable def sourceStart (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) : ℕ :=
  max (TermView.term (source c)).toData.size (dim c + 1)
noncomputable def sourceProgram (source : List Bool → List Bool) (dim degree : List Bool → ℕ)
    (record : List Bool → List Bool) (c : List Bool) : List Operation :=
  FrozenSource.program (TermView.term (source c)).toData.size (sourceStart source dim c)
    (sampleValue dim degree record c : ℤ) (TermView.term (source c))
noncomputable def sourceOutput (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) : ℕ :=
  FrozenSource.output (TermView.term (source c)).toData.size (sourceStart source dim c) (TermView.term (source c))

theorem sourceStart_unary {source : List Bool → List Bool} {dim : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) : UnaryFn (sourceStart source dim) :=
  (FrozenSource.source_start_unary ht).max (hd.add (UnaryFn.const 1))

theorem sourceOutput_unary {source : List Bool → List Bool} {dim : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) : UnaryFn (sourceOutput source dim) :=
  FrozenSource.output_unary ht (sourceStart_unary ht hd)

theorem sourceLength_unary {source : List Bool → List Bool} {dim degree : List Bool → ℕ}
    {record : List Bool → List Bool} (ht : source ∈ FP) :
    UnaryFn (fun c => (sourceProgram source dim degree record c).length) := FrozenSource.length_unary ht

theorem encode_mem_FP {source record : List Bool → List Bool} {dim degree : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) (hN : BinaryFn degree) (hr : record ∈ FP) :
    (fun c => encode (StraightLine.gates (sourceStart source dim c) (sourceProgram source dim degree record c))) ∈ FP :=
  FrozenSource.encode_mem_FP ht (sourceStart_unary ht hd) (Term.nat_toBits_mem_FP (sample_binary hd hN hr))

theorem wellFormed (source record : List Bool → List Bool) (dim degree : List Bool → ℕ) (c : List Bool) :
    StraightLine.WellFormed (sourceStart source dim c) (sourceProgram source dim degree record c) :=
  FrozenSource.wellFormed _ _ _ _ (Term.arity_le_dataSize _) (Nat.le_max_left ..)

theorem output_lt (source record : List Bool → List Bool) (dim degree : List Bool → ℕ) (c : List Bool) :
    sourceOutput source dim c < sourceStart source dim c + (sourceProgram source dim degree record c).length :=
  FrozenSource.output_lt _ _ _ _ (Term.arity_le_dataSize _) (Nat.le_max_left ..)

theorem symbolic_output_slice (source record : List Bool → List Bool) (dim degree : List Bool → ℕ)
    (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) :
    (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (sourceStart source dim c)
      (sourceProgram source dim degree record c) (sourceOutput source dim c)).map (Int.castRingHom ℂ) = rename Fin.val
        ((LeanCanny.Algebra.CoordinateSlicePolynomial.family low).map
          (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (sample (dim c) (degree c) (record c) : ℂ))) := by
  simpa only [sourceStart, sourceProgram, sourceOutput, sampleValue, Int.cast_natCast] using
    FrozenSource.symbolic_output_map_slice (TermView.term (source c)).toData.size (sourceStart source dim c)
      (sampleValue dim degree record c : ℤ) (TermView.term (source c)) low ht
      (Term.arity_le_dataSize _) (Nat.le_max_left ..)

end LeanCanny.Encoding.FermatFrozenSource
