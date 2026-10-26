/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBinaryScale

/-! # Combining a computed scale and shift with a source wire -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.ScaleShift
open MvPolynomial LeanCanny.Encoding.Brackets

def program (source scale shift start : ℕ) : List Operation :=
  [.constant (-1), .mul shift start, .mul scale source, .add (start + 2) (start + 1)]
def output (start : ℕ) : ℕ := start + 3

theorem program_length (source scale shift start : ℕ) : (program source scale shift start).length = 4 := rfl

theorem wellFormed (source scale shift start : ℕ) (hq : source < start) (hs : scale < start)
    (hr : shift < start) : StraightLine.WellFormed start (program source scale shift start) := by
  simp only [program, StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨trivial, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (source scale shift start : ℕ)
    (hr : Differential.Realizes wire start (program source scale shift start)) :
    wire (output start) = wire scale * wire source - wire shift := by
  obtain ⟨h0, h1, h2, h3, _⟩ := hr
  change wire start = C (-1) at h0
  change wire (start + 1) = wire shift * wire start at h1
  change wire (start + 2) = wire scale * wire source at h2
  change wire (output start) = wire (start + 2) + wire (start + 1) at h3
  rw [h3, h2, h1, h0]
  simp only [map_neg, map_one]
  ring

theorem encode_mem_FP {source scale shift start : List Bool → ℕ}
    (hq : UnaryFn source) (hscale : UnaryFn scale) (hshift : UnaryFn shift) (hs : UnaryFn start) :
    (fun c => encode (StraightLine.gates (start c) (program (source c) (scale c) (shift c) (start c)))) ∈ FP := by
  have h0 := constantGateBits_mem_FP hs (constFn_mem_FP (Term.const (-1)).toData.toBits)
  have h1 := arithmeticGateBits_mem_FP 2 (hs.add (UnaryFn.const 1)) hshift hs
  have h2 := arithmeticGateBits_mem_FP 2 (hs.add (UnaryFn.const 2)) hscale hq
  have h3 := arithmeticGateBits_mem_FP 1 (hs.add (UnaryFn.const 3)) (hs.add (UnaryFn.const 2)) (hs.add (UnaryFn.const 1))
  have h := mem_FP_comp (appendFn_mem_FP h0 (appendFn_mem_FP h1 (appendFn_mem_FP h2 h3))) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, constantGateBits_encode, mulGateBits_encode, addGateBits_encode,
    encode_eq_wrap, program, StraightLine.gates, Operation.gate, forest_cons, forest_nil,
    List.append_nil, Nat.add_assoc]

end LeanCanny.ETR.ComplexCircuit.ScaleShift
