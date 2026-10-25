/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexPowerEncoding

/-! # Shared networks for denominator-cleared regular levels

Given an earlier source wire, the network computes `2^E * p - 1` from the
little-endian exponent bits. The integer `2^E` is computed on shared wires,
and is never materialized as an integer literal in the query encoding.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Dyadic
open LeanCanny.Encoding.Brackets Turing.MultiTapeTM
open scoped Classical

def productWire (start : ℕ) (bits : List Bool) : ℕ := Power.output (start + 1) bits + 1
def output (start : ℕ) (bits : List Bool) : ℕ := productWire start bits + 2

def program (source start : ℕ) (bits : List Bool) : List Operation :=
  [.constant 2] ++ Power.program start (start + 1) bits ++
    [.mul source (Power.output (start + 1) bits), .constant (-1),
      .add (productWire start bits) (productWire start bits + 1)]

def gates (source start : ℕ) (bits : List Bool) : List Gate :=
  [.constant start 2] ++ Power.gates start (start + 1) bits ++
    [.mul (productWire start bits) source (Power.output (start + 1) bits),
      .constant (productWire start bits + 1) (-1),
      .add (output start bits) (productWire start bits) (productWire start bits + 1)]

theorem gates_eq (source start : ℕ) (bits : List Bool) :
    StraightLine.gates start (program source start bits) = gates source start bits := by
  simp only [program, StraightLine.gates_append, List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, StraightLine.gates, Operation.gate, Power.program_length,
    Power.gates, gates, productWire, output]
  rw [show start + (1 + (2 * bits.length + 1)) = Power.output (start + 1) bits + 1 by
    unfold Power.output
    omega]

theorem wellFormed (source start : ℕ) (hsource : source < start) (bits : List Bool) :
    StraightLine.WellFormed start (program source start bits) := by
  rw [program, StraightLine.wellFormed_append, StraightLine.wellFormed_append]
  refine ⟨⟨by simp [StraightLine.WellFormed, Operation.InputsBelow],
    Power.wellFormed start (start + 1) (by omega) bits⟩, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Power.program_length,
    StraightLine.WellFormed, Operation.InputsBelow, productWire, Power.output]
  exact ⟨⟨by omega, by omega⟩, trivial, ⟨by omega, by omega⟩, trivial⟩

theorem sound (source start : ℕ) (bits : List Bool) (env : ℕ → ℂ)
    (h : ∀ g ∈ gates source start bits, g.Holds env) :
    env (output start bits) = (2 : ℂ) ^ Nat.fromBitsLE bits * env source - 1 := by
  have hc := h (.constant start 2) (by simp [gates])
  have hp : ∀ g ∈ Power.gates start (start + 1) bits, g.Holds env := by
    intro g hg
    exact h g (by simp only [gates, List.mem_append]; exact Or.inl (Or.inr hg))
  have he := Power.sound start (start + 1) bits env hp
  have hm := h (.mul (productWire start bits) source (Power.output (start + 1) bits)) (by simp [gates])
  have hn := h (.constant (productWire start bits + 1) (-1)) (by simp [gates])
  have ha := h (.add (output start bits) (productWire start bits) (productWire start bits + 1)) (by simp [gates])
  simp only [Gate.Holds, Int.cast_ofNat, Int.cast_neg, Int.cast_one] at hc hm hn ha
  rw [ha, hm, hn, he, hc]
  ring

theorem exists_completion (source start : ℕ) (hsource : source < start)
    (bits : List Bool) (env : ℕ → ℂ) :
    ∃ out : ℕ → ℂ, (∀ i < start, out i = env i) ∧ (∀ g ∈ gates source start bits, g.Holds out) ∧
      out (output start bits) = (2 : ℂ) ^ Nat.fromBitsLE bits * env source - 1 := by
  obtain ⟨out, hp, hg⟩ := StraightLine.exists_completion env start (program source start bits)
    (wellFormed source start hsource bits)
  rw [gates_eq] at hg
  refine ⟨out, hp, hg, ?_⟩
  rw [sound source start bits out hg, hp source hsource]

theorem program_length (source start : ℕ) (bits : List Bool) :
    (program source start bits).length = 2 * bits.length + 5 := by
  simp only [program, List.length_append, List.length_cons, List.length_nil, Power.program_length]
  omega

theorem gate_arity_le (source start : ℕ) (hsource : source < start) (bits : List Bool)
    (g : Gate) (hg : g ∈ gates source start bits) : g.arity ≤ output start bits + 1 := by
  rw [← gates_eq] at hg
  have h := StraightLine.gates_arity start (program source start bits)
    (wellFormed source start hsource bits) g hg
  rw [program_length] at h
  simp only [output, productWire, Power.output]
  omega

theorem productWire_unary {start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hs : UnaryFn start) (he : bits ∈ FP) : UnaryFn (fun c => productWire (start c) (bits c)) :=
  (((hs.add (UnaryFn.const 1)).add ((UnaryFn.const 2).mul (UnaryFn.length he))).add
    (UnaryFn.const 1)).of_eq (fun _ => rfl)

theorem encode_mem_FP {source start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn source) (hs : UnaryFn start) (he : bits ∈ FP) :
    (fun c => encode (gates (source c) (start c) (bits c))) ∈ FP := by
  have hpow := Power.forest_mem_FP hs (hs.add (UnaryFn.const 1)) he
  have hwire := ((hs.add (UnaryFn.const 1)).add ((UnaryFn.const 2).mul (UnaryFn.length he)))
  have hprod := productWire_unary hs he
  have hc := constantGateBits_mem_FP hs (constFn_mem_FP (Term.const 2).toData.toBits)
  have hm := arithmeticGateBits_mem_FP 2 hprod hp hwire
  have hn := constantGateBits_mem_FP (hprod.add (UnaryFn.const 1))
    (constFn_mem_FP (Term.const (-1)).toData.toBits)
  have ha := arithmeticGateBits_mem_FP 1 (hprod.add (UnaryFn.const 2)) hprod (hprod.add (UnaryFn.const 1))
  have h := mem_FP_comp
    (appendFn_mem_FP (appendFn_mem_FP hc hpow) (appendFn_mem_FP (appendFn_mem_FP hm hn) ha)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, constantGateBits_encode, mulGateBits_encode, addGateBits_encode]
  rw [encode_eq_wrap, gates, forest_append, forest_append]
  simp only [forest_cons, forest_nil, List.append_nil, output, List.append_assoc]
  rfl

end LeanCanny.ETR.ComplexCircuit.Dyadic
