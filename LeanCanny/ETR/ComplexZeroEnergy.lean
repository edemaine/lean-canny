/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBinaryScale

/-! # A shared sum-of-squares zero energy

The source, radial sum and radius are previously computed wires. Their
combination uses six operations regardless of the sizes of those values.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.ZeroEnergy
open MvPolynomial LeanCanny.Encoding.Brackets

def program (source radial radius start : ℕ) : List Operation :=
  [.constant (-1), .mul radius start, .add radial (start + 1),
    .mul (start + 2) (start + 2), .mul source source, .add (start + 4) (start + 3)]
def output (start : ℕ) : ℕ := start + 5

theorem program_length (source radial radius start : ℕ) : (program source radial radius start).length = 6 := rfl

theorem wellFormed (source radial radius start : ℕ) (hq : source < start) (hs : radial < start)
    (hr : radius < start) : StraightLine.WellFormed start (program source radial radius start) := by
  simp only [program, StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨trivial, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (source radial radius start : ℕ)
    (hr : Differential.Realizes wire start (program source radial radius start)) :
    wire (output start) = wire source ^ 2 + (wire radial - wire radius) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, _⟩ := hr
  change wire start = C (-1) at h0
  change wire (start + 1) = wire radius * wire start at h1
  change wire (start + 2) = wire radial + wire (start + 1) at h2
  change wire (start + 3) = wire (start + 2) * wire (start + 2) at h3
  change wire (start + 4) = wire source * wire source at h4
  change wire (output start) = wire (start + 4) + wire (start + 3) at h5
  rw [h5, h4, h3, h2, h1, h0]
  simp only [map_neg, map_one]
  ring

theorem encode_mem_FP {source radial radius start : List Bool → ℕ}
    (hq : UnaryFn source) (hr : UnaryFn radial) (hR : UnaryFn radius) (hs : UnaryFn start) :
    (fun c => encode (StraightLine.gates (start c) (program (source c) (radial c) (radius c) (start c)))) ∈ FP := by
  have h0 := constantGateBits_mem_FP hs (constFn_mem_FP (Term.const (-1)).toData.toBits)
  have h1 := arithmeticGateBits_mem_FP 2 (hs.add (UnaryFn.const 1)) hR hs
  have h2 := arithmeticGateBits_mem_FP 1 (hs.add (UnaryFn.const 2)) hr (hs.add (UnaryFn.const 1))
  have h3 := arithmeticGateBits_mem_FP 2 (hs.add (UnaryFn.const 3)) (hs.add (UnaryFn.const 2)) (hs.add (UnaryFn.const 2))
  have h4 := arithmeticGateBits_mem_FP 2 (hs.add (UnaryFn.const 4)) hq hq
  have h5 := arithmeticGateBits_mem_FP 1 (hs.add (UnaryFn.const 5)) (hs.add (UnaryFn.const 4)) (hs.add (UnaryFn.const 3))
  have h := mem_FP_comp (appendFn_mem_FP h0 (appendFn_mem_FP h1 (appendFn_mem_FP h2
    (appendFn_mem_FP h3 (appendFn_mem_FP h4 h5))))) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, constantGateBits_encode, mulGateBits_encode, addGateBits_encode,
    encode_eq_wrap, program, StraightLine.gates, Operation.gate, forest_cons, forest_nil,
    List.append_nil, Nat.add_assoc]

end LeanCanny.ETR.ComplexCircuit.ZeroEnergy
