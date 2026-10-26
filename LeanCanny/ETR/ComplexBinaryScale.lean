/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSampledSource

/-! # Binary powers of two on shared wires

Only the constant two and the exponent word are serialized. This block also
provides composition of native encoders for consecutive operation lists.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical

theorem StraightLine.encode_append_mem_FP {start : List Bool → ℕ} {a b : List Bool → List Operation}
    (ha : (fun c => encode (gates (start c) (a c))) ∈ FP)
    (hb : (fun c => encode (gates (start c + (a c).length) (b c))) ∈ FP) :
    (fun c => encode (gates (start c) (a c ++ b c))) ∈ FP := by
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp ha contents_mem_FP)
    (mem_FP_comp hb contents_mem_FP)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode]
  rw [gates_append, encode_eq_wrap, forest_append]

namespace BinaryScale

def program (start : ℕ) (bits : List Bool) : List Operation :=
  .constant 2 :: Power.program start (start + 1) bits
def output (start : ℕ) (bits : List Bool) : ℕ := Power.output (start + 1) bits

theorem program_length (start : ℕ) (bits : List Bool) :
    (program start bits).length = 2 * bits.length + 2 := by
  simp only [program, List.length_cons, Power.program_length]

theorem next_eq (start : ℕ) (bits : List Bool) :
    start + (program start bits).length = output start bits + 1 := by
  rw [program_length]
  unfold output Power.output
  omega

theorem wellFormed (start : ℕ) (bits : List Bool) : StraightLine.WellFormed start (program start bits) :=
  ⟨trivial, Power.wellFormed start (start + 1) (by omega) bits⟩

theorem output_lt (start : ℕ) (bits : List Bool) :
    output start bits < start + (program start bits).length := by rw [next_eq]; omega

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (start : ℕ) (bits : List Bool)
    (hr : Differential.Realizes wire start (program start bits)) :
    wire (output start bits) = C ((2 : ℤ) ^ Nat.fromBitsLE bits) := by
  apply Differential.eq_of_eval_complex
  intro x
  have hg := Differential.realizes_gates_eval wire start (program start bits) hr x
  have hc : (wire start).eval₂ (Int.castRingHom ℂ) x = 2 :=
    hg (.constant start 2) (List.mem_cons_self ..)
  have hp := Power.sound start (start + 1) bits (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x)
    (fun g h => hg g (List.mem_cons_of_mem _ h))
  simpa only [output, hc, eval₂_C, eval₂_pow, map_pow, Int.coe_castRingHom, Int.cast_ofNat] using hp

theorem output_unary {start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hs : UnaryFn start) (hb : bits ∈ FP) : UnaryFn (fun c => output (start c) (bits c)) :=
  ((hs.add (UnaryFn.const 1)).add ((UnaryFn.const 2).mul (UnaryFn.length hb))).of_eq (fun _ => rfl)

theorem length_unary {start : List Bool → ℕ} {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    UnaryFn (fun c => (program (start c) (bits c)).length) :=
  (((UnaryFn.const 2).mul (UnaryFn.length hb)).add (UnaryFn.const 2)).of_eq
    (fun c => (program_length (start c) (bits c)).symm)

theorem encode_mem_FP {start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hs : UnaryFn start) (hb : bits ∈ FP) :
    (fun c => encode (StraightLine.gates (start c) (program (start c) (bits c)))) ∈ FP := by
  have h := mem_FP_comp (appendFn_mem_FP
    (constantGateBits_mem_FP hs (constFn_mem_FP (Term.const 2).toData.toBits))
    (Power.forest_mem_FP hs (hs.add (UnaryFn.const 1)) hb)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, constantGateBits_encode, encode_eq_wrap, program,
    StraightLine.gates, Operation.gate, forest_cons]
  rfl

end BinaryScale
end LeanCanny.ETR.ComplexCircuit
