/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexDifferential
public import LeanCanny.ETR.ComplexCircuitTransform

/-! # Native polynomial-time generation of derivative networks

The local writer copies integer constants and emits a bounded number of gates
with unary indices. The total network transformer preserves the derivative
program codec exactly, without expanding the polynomial at any source wire.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Differential
open LeanCanny.Encoding.Brackets

def gate : Gate → List Gate
  | .constant out z => [.constant (valueWire out) z, .constant (valueWire out + 1) 0,
      .constant (valueWire out + 2) 0, .constant (derivativeWire out) 0]
  | .add out left right => [.add (valueWire out) (valueWire left) (valueWire right),
      .constant (valueWire out + 1) 0, .constant (valueWire out + 2) 0,
      .add (derivativeWire out) (derivativeWire left) (derivativeWire right)]
  | .mul out left right => [.mul (valueWire out) (valueWire left) (valueWire right),
      .mul (valueWire out + 1) (derivativeWire left) (valueWire right),
      .mul (valueWire out + 2) (valueWire left) (derivativeWire right),
      .add (derivativeWire out) (valueWire out + 1) (valueWire out + 2)]
  | .zero wire => [.zero (valueWire wire), .zero (derivativeWire wire)]

theorem gate_operation (out : ℕ) (op : Operation) :
    gate (op.gate out) = StraightLine.gates (valueWire out) (operation out op) := by cases op <;> rfl

theorem gates_program (start : ℕ) (ops : List Operation) :
    StraightLine.gates (valueWire start) (program start ops) =
      (StraightLine.gates start ops).flatMap gate := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    rw [program, StraightLine.gates_append, operation_length,
      show valueWire start + 4 = valueWire (start + 1) by unfold valueWire; omega, ih]
    rw [StraightLine.gates, List.flatMap_cons, gate_operation]

def zeroConstantBits (out : ℕ) : List Bool := constantGateBits out (Term.const 0).toData.toBits

theorem zeroConstantBits_mem_FP {out : List Bool → ℕ} (ho : UnaryFn out) :
    (fun c => zeroConstantBits (out c)) ∈ FP :=
  constantGateBits_mem_FP ho (constFn_mem_FP _)

theorem zeroConstantBits_encode (out : ℕ) : zeroConstantBits out = (Gate.constant out 0).encode :=
  constantGateBits_encode out 0

def constantBits (out : ℕ) (value : List Bool) : List Bool :=
  constantGateBits (valueWire out) value ++ zeroConstantBits (valueWire out + 1) ++
    zeroConstantBits (valueWire out + 2) ++ zeroConstantBits (derivativeWire out)

def addBits (out left right : ℕ) : List Bool :=
  arithmeticGateBits 1 (valueWire out) (valueWire left) (valueWire right) ++
    zeroConstantBits (valueWire out + 1) ++ zeroConstantBits (valueWire out + 2) ++
    arithmeticGateBits 1 (derivativeWire out) (derivativeWire left) (derivativeWire right)

def mulBits (out left right : ℕ) : List Bool :=
  arithmeticGateBits 2 (valueWire out) (valueWire left) (valueWire right) ++
    arithmeticGateBits 2 (valueWire out + 1) (derivativeWire left) (valueWire right) ++
    arithmeticGateBits 2 (valueWire out + 2) (valueWire left) (derivativeWire right) ++
    arithmeticGateBits 1 (derivativeWire out) (valueWire out + 1) (valueWire out + 2)

def zeroBits (wire : ℕ) : List Bool := zeroGateBits (valueWire wire) ++ zeroGateBits (derivativeWire wire)

theorem valueWire_unary {i : List Bool → ℕ} (hi : UnaryFn i) : UnaryFn (fun c => valueWire (i c)) :=
  ((UnaryFn.const 4).mul hi).of_eq (fun _ => rfl)

theorem derivativeWire_unary {i : List Bool → ℕ} (hi : UnaryFn i) : UnaryFn (fun c => derivativeWire (i c)) :=
  ((valueWire_unary hi).add (UnaryFn.const 3)).of_eq (fun _ => rfl)

theorem constantBits_mem_FP {out : List Bool → ℕ} {value : List Bool → List Bool}
    (ho : UnaryFn out) (hv : value ∈ FP) : (fun c => constantBits (out c) (value c)) ∈ FP := by
  have h := appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (constantGateBits_mem_FP (valueWire_unary ho) hv)
    (zeroConstantBits_mem_FP ((valueWire_unary ho).add (UnaryFn.const 1))))
    (zeroConstantBits_mem_FP ((valueWire_unary ho).add (UnaryFn.const 2))))
    (zeroConstantBits_mem_FP (derivativeWire_unary ho))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem addBits_mem_FP {out left right : List Bool → ℕ}
    (ho : UnaryFn out) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => addBits (out c) (left c) (right c)) ∈ FP := by
  have h := appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (arithmeticGateBits_mem_FP 1 (valueWire_unary ho) (valueWire_unary hl) (valueWire_unary hr))
    (zeroConstantBits_mem_FP ((valueWire_unary ho).add (UnaryFn.const 1))))
    (zeroConstantBits_mem_FP ((valueWire_unary ho).add (UnaryFn.const 2))))
    (arithmeticGateBits_mem_FP 1 (derivativeWire_unary ho) (derivativeWire_unary hl) (derivativeWire_unary hr))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem mulBits_mem_FP {out left right : List Bool → ℕ}
    (ho : UnaryFn out) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => mulBits (out c) (left c) (right c)) ∈ FP := by
  have h := appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (arithmeticGateBits_mem_FP 2 (valueWire_unary ho) (valueWire_unary hl) (valueWire_unary hr))
    (arithmeticGateBits_mem_FP 2 ((valueWire_unary ho).add (UnaryFn.const 1))
      (derivativeWire_unary hl) (valueWire_unary hr)))
    (arithmeticGateBits_mem_FP 2 ((valueWire_unary ho).add (UnaryFn.const 2))
      (valueWire_unary hl) (derivativeWire_unary hr)))
    (arithmeticGateBits_mem_FP 1 (derivativeWire_unary ho) ((valueWire_unary ho).add (UnaryFn.const 1))
      ((valueWire_unary ho).add (UnaryFn.const 2)))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem zeroBits_mem_FP {wire : List Bool → ℕ} (hw : UnaryFn wire) : (fun c => zeroBits (wire c)) ∈ FP :=
  appendFn_mem_FP (zeroGateBits_mem_FP (valueWire_unary hw)) (zeroGateBits_mem_FP (derivativeWire_unary hw))

def constantPacket (bits : List Bool) : List Bool := constantBits (outIndex bits) (NNF.second (payload bits))
def addPacket (bits : List Bool) : List Bool := addBits (outIndex bits) (leftIndex bits) (rightIndex bits)
def mulPacket (bits : List Bool) : List Bool := mulBits (outIndex bits) (leftIndex bits) (rightIndex bits)
def zeroPacket (bits : List Bool) : List Bool := zeroBits (Codec.unaryValue (payload bits))

attribute [local irreducible] outIndex leftIndex rightIndex payload NNF.second firstChild

theorem constantPacket_mem_FP : constantPacket ∈ FP := by
  have hs := mem_FP_comp (f := payload) (g := NNF.second) payload_mem_FP NNF.second_mem_FP
  exact mem_FP_of_eq (constantBits_mem_FP outIndex_unary hs) (fun _ => rfl)

theorem addPacket_mem_FP : addPacket ∈ FP :=
  mem_FP_of_eq (addBits_mem_FP outIndex_unary leftIndex_unary rightIndex_unary) (fun _ => rfl)

theorem mulPacket_mem_FP : mulPacket ∈ FP :=
  mem_FP_of_eq (mulBits_mem_FP outIndex_unary leftIndex_unary rightIndex_unary) (fun _ => rfl)

theorem zeroPacket_mem_FP : zeroPacket ∈ FP := by
  have hi := UnaryFn.comp (f := Codec.unaryValue) (g := payload) Codec.unaryValue_unary payload_mem_FP
  exact mem_FP_of_eq (zeroBits_mem_FP hi) (fun _ => rfl)

attribute [local irreducible] constantPacket addPacket mulPacket zeroPacket

def gateBits (bits : List Bool) : List Bool :=
  if firstChild bits = (Codec.unary 0).toBits then constantPacket bits
  else if firstChild bits = (Codec.unary 1).toBits then addPacket bits
  else if firstChild bits = (Codec.unary 2).toBits then mulPacket bits
  else zeroPacket bits

theorem gateBits_mem_FP : gateBits ∈ FP := by
  have htag (i : ℕ) : FPPred (fun bits => firstChild bits = (Codec.unary i).toBits) :=
    stringEq_fppred firstChild_mem_FP (constFn_mem_FP _)
  exact mem_FP_of_eq ((htag 0).ite_mem_FP constantPacket_mem_FP
    ((htag 1).ite_mem_FP addPacket_mem_FP ((htag 2).ite_mem_FP mulPacket_mem_FP zeroPacket_mem_FP)))
    (fun _ => rfl)

theorem gateBits_encode (g : Gate) : gateBits g.encode = forest (gate g) := by
  cases g <;>
    simp [gateBits, constantPacket, addPacket, mulPacket, zeroPacket, Gate.encode, Gate.toData,
      outIndex, leftIndex, rightIndex, payload, Codec.unary_toBits_injective.eq_iff,
      constantBits, addBits, mulBits, zeroBits, constantGateBits_encode, addGateBits_encode,
      mulGateBits_encode, zeroGateBits_encode, zeroConstantBits_encode, gate,
      forest_cons, forest_nil, List.append_assoc]

theorem encode_mem_FP {query : List Bool → List Gate} (hq : (fun c => encode (query c)) ∈ FP) :
    (fun c => encode ((query c).flatMap gate)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp hq (Transform.run_mem_FP gateBits_mem_FP))
    (fun c => Transform.run_encode gateBits gate gateBits_encode (query c))

theorem program_encode_mem_FP {start : List Bool → ℕ} {ops : List Bool → List Operation}
    (hq : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (valueWire (start c)) (program (start c) (ops c)))) ∈ FP := by
  simpa only [gates_program] using encode_mem_FP hq

end LeanCanny.ETR.ComplexCircuit.Differential
