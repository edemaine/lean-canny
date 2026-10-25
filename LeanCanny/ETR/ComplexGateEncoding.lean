/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuit
public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.ETR.EquationEncoding

/-! # Native writers for real equations of complex arithmetic gates

Wire indices use the unary input interface. Integer payloads are copied
verbatim, and each shared complex wire becomes two shared real variables.
The encoded gate compiler is polynomial time on every input string.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding.Brackets

def realBits (i : ℕ) : List Bool := Term.variableBits (2 * i)
def imagBits (i : ℕ) : List Bool := Term.variableBits (2 * i + 1)

theorem realBits_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) : (fun c => realBits (i c)) ∈ FP :=
  Term.variableBits_mem_FP ((UnaryFn.const 2).mul hi)

theorem imagBits_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) : (fun c => imagBits (i c)) ∈ FP :=
  Term.variableBits_mem_FP (((UnaryFn.const 2).mul hi).add (UnaryFn.const 1))

def differenceBits (a b : List Bool) : List Bool :=
  Codec.taggedTwo 2 a (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits b)

theorem differenceBits_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun c => differenceBits (a c) (b c)) ∈ FP :=
  Codec.taggedTwo_mem_FP 2 ha (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) hb)

def constantBits (out : ℕ) (value : List Bool) : List Bool := differenceBits (realBits out) value ++ imagBits out

def addBits (out left right : ℕ) : List Bool :=
  differenceBits (realBits out) (Codec.taggedTwo 2 (realBits left) (realBits right)) ++
    differenceBits (imagBits out) (Codec.taggedTwo 2 (imagBits left) (imagBits right))

def mulBits (out left right : ℕ) : List Bool :=
  differenceBits (realBits out)
    (differenceBits (Codec.taggedTwo 3 (realBits left) (realBits right))
      (Codec.taggedTwo 3 (imagBits left) (imagBits right))) ++
    differenceBits (imagBits out)
      (Codec.taggedTwo 2 (Codec.taggedTwo 3 (realBits left) (imagBits right))
        (Codec.taggedTwo 3 (imagBits left) (realBits right)))

def zeroBits (wire : ℕ) : List Bool := realBits wire ++ imagBits wire

theorem constantBits_mem_FP {out : List Bool → ℕ} {value : List Bool → List Bool}
    (ho : UnaryFn out) (hv : value ∈ FP) : (fun c => constantBits (out c) (value c)) ∈ FP :=
  appendFn_mem_FP (differenceBits_mem_FP (realBits_mem_FP ho) hv) (imagBits_mem_FP ho)

theorem addBits_mem_FP {out left right : List Bool → ℕ} (ho : UnaryFn out) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => addBits (out c) (left c) (right c)) ∈ FP :=
  appendFn_mem_FP (differenceBits_mem_FP (realBits_mem_FP ho)
    (Codec.taggedTwo_mem_FP 2 (realBits_mem_FP hl) (realBits_mem_FP hr)))
    (differenceBits_mem_FP (imagBits_mem_FP ho)
      (Codec.taggedTwo_mem_FP 2 (imagBits_mem_FP hl) (imagBits_mem_FP hr)))

theorem mulBits_mem_FP {out left right : List Bool → ℕ} (ho : UnaryFn out) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => mulBits (out c) (left c) (right c)) ∈ FP :=
  appendFn_mem_FP (differenceBits_mem_FP (realBits_mem_FP ho)
    (differenceBits_mem_FP (Codec.taggedTwo_mem_FP 3 (realBits_mem_FP hl) (realBits_mem_FP hr))
      (Codec.taggedTwo_mem_FP 3 (imagBits_mem_FP hl) (imagBits_mem_FP hr))))
    (differenceBits_mem_FP (imagBits_mem_FP ho)
      (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 (realBits_mem_FP hl) (imagBits_mem_FP hr))
        (Codec.taggedTwo_mem_FP 3 (imagBits_mem_FP hl) (realBits_mem_FP hr))))

theorem zeroBits_mem_FP {wire : List Bool → ℕ} (hw : UnaryFn wire) : (fun c => zeroBits (wire c)) ∈ FP :=
  appendFn_mem_FP (realBits_mem_FP hw) (imagBits_mem_FP hw)

def payload (bits : List Bool) : List Bool := NNF.second bits
def outIndex (bits : List Bool) : ℕ := Codec.unaryValue (firstChild (payload bits))
def leftIndex (bits : List Bool) : ℕ := Codec.unaryValue (firstChild (NNF.second (payload bits)))
def rightIndex (bits : List Bool) : ℕ := Codec.unaryValue (NNF.second (NNF.second (payload bits)))

def constantPacket (bits : List Bool) : List Bool := constantBits (outIndex bits) (NNF.second (payload bits))
def addPacket (bits : List Bool) : List Bool := addBits (outIndex bits) (leftIndex bits) (rightIndex bits)
def mulPacket (bits : List Bool) : List Bool := mulBits (outIndex bits) (leftIndex bits) (rightIndex bits)
def zeroPacket (bits : List Bool) : List Bool := zeroBits (Codec.unaryValue (payload bits))

def gateBits (bits : List Bool) : List Bool :=
  if firstChild bits = (Codec.unary 0).toBits then constantPacket bits
  else if firstChild bits = (Codec.unary 1).toBits then addPacket bits
  else if firstChild bits = (Codec.unary 2).toBits then mulPacket bits
  else zeroPacket bits

theorem payload_mem_FP : payload ∈ FP := NNF.second_mem_FP

attribute [local irreducible] payload NNF.second firstChild

theorem outIndex_unary : UnaryFn outIndex := by
  have hfirst : (fun bits => firstChild (payload bits)) ∈ FP :=
    mem_FP_comp (f := payload) (g := firstChild) payload_mem_FP firstChild_mem_FP
  apply UnaryFn.of_eq (UnaryFn.comp (f := Codec.unaryValue)
    (g := fun bits => firstChild (payload bits)) Codec.unaryValue_unary hfirst)
  intro bits
  rfl

theorem leftIndex_unary : UnaryFn leftIndex := by
  have hs : (fun bits => NNF.second (payload bits)) ∈ FP :=
    mem_FP_comp (f := payload) (g := NNF.second) payload_mem_FP NNF.second_mem_FP
  have hleft : (fun bits => firstChild (NNF.second (payload bits))) ∈ FP :=
    mem_FP_comp (f := fun bits => NNF.second (payload bits)) (g := firstChild) hs firstChild_mem_FP
  apply UnaryFn.of_eq (UnaryFn.comp (f := Codec.unaryValue)
    (g := fun bits => firstChild (NNF.second (payload bits))) Codec.unaryValue_unary hleft)
  intro bits
  rfl

theorem rightIndex_unary : UnaryFn rightIndex := by
  have hs : (fun bits => NNF.second (payload bits)) ∈ FP :=
    mem_FP_comp (f := payload) (g := NNF.second) payload_mem_FP NNF.second_mem_FP
  have hright : (fun bits => NNF.second (NNF.second (payload bits))) ∈ FP :=
    mem_FP_comp (f := fun bits => NNF.second (payload bits)) (g := NNF.second) hs NNF.second_mem_FP
  apply UnaryFn.of_eq (UnaryFn.comp (f := Codec.unaryValue)
    (g := fun bits => NNF.second (NNF.second (payload bits))) Codec.unaryValue_unary hright)
  intro bits
  rfl

attribute [local irreducible] outIndex leftIndex rightIndex

theorem constantPacket_mem_FP : constantPacket ∈ FP := by
  have hs : (fun bits => NNF.second (payload bits)) ∈ FP :=
    mem_FP_comp (f := payload) (g := NNF.second) payload_mem_FP NNF.second_mem_FP
  apply mem_FP_of_eq (constantBits_mem_FP outIndex_unary hs)
  intro bits
  rfl

theorem addPacket_mem_FP : addPacket ∈ FP := by
  apply mem_FP_of_eq (addBits_mem_FP outIndex_unary leftIndex_unary rightIndex_unary)
  intro bits
  rfl

theorem mulPacket_mem_FP : mulPacket ∈ FP := by
  apply mem_FP_of_eq (mulBits_mem_FP outIndex_unary leftIndex_unary rightIndex_unary)
  intro bits
  rfl

theorem zeroPacket_mem_FP : zeroPacket ∈ FP := by
  have hi := UnaryFn.comp (f := Codec.unaryValue) (g := payload) Codec.unaryValue_unary payload_mem_FP
  apply mem_FP_of_eq (zeroBits_mem_FP hi)
  intro bits
  rfl

attribute [local irreducible] constantPacket addPacket mulPacket zeroPacket

theorem gateBits_mem_FP : gateBits ∈ FP := by
  have htag (i : ℕ) : FPPred (fun bits => firstChild bits = (Codec.unary i).toBits) :=
    stringEq_fppred firstChild_mem_FP (constFn_mem_FP _)
  have h := (htag 0).ite_mem_FP constantPacket_mem_FP
    ((htag 1).ite_mem_FP addPacket_mem_FP ((htag 2).ite_mem_FP mulPacket_mem_FP zeroPacket_mem_FP))
  apply mem_FP_of_eq h
  intro bits
  simp only [gateBits]

@[simp] theorem realBits_toBits (i : ℕ) : realBits i = (realWire i).toData.toBits := Term.variableBits_eq _
@[simp] theorem imagBits_toBits (i : ℕ) : imagBits i = (imagWire i).toData.toBits := Term.variableBits_eq _

@[simp] theorem differenceBits_toBits (a b : Term) :
    differenceBits a.toData.toBits b.toData.toBits = (difference a b).toData.toBits := by
  simp only [differenceBits, difference, Term.add_toBits, Term.mul_toBits]

theorem constantBits_toBits (out : ℕ) (z : ℤ) :
    constantBits out (Term.const z).toData.toBits = SumSquares.forest (Gate.constant out z).equations := by
  simp only [constantBits, realBits_toBits, imagBits_toBits, differenceBits_toBits, Gate.equations,
    SumSquares.forest_cons, SumSquares.forest_nil, List.append_nil]

theorem addBits_toBits (out left right : ℕ) :
    addBits out left right = SumSquares.forest (Gate.add out left right).equations := by
  simp only [addBits, realBits_toBits, imagBits_toBits, ← Term.add_toBits, differenceBits_toBits,
    Gate.equations, SumSquares.forest_cons, SumSquares.forest_nil, List.append_nil]

theorem mulBits_toBits (out left right : ℕ) :
    mulBits out left right = SumSquares.forest (Gate.mul out left right).equations := by
  simp only [mulBits, realBits_toBits, imagBits_toBits, ← Term.add_toBits, ← Term.mul_toBits,
    differenceBits_toBits, Gate.equations, SumSquares.forest_cons, SumSquares.forest_nil, List.append_nil]

theorem zeroBits_toBits (wire : ℕ) : zeroBits wire = SumSquares.forest (Gate.zero wire).equations := by
  simp only [zeroBits, realBits_toBits, imagBits_toBits, Gate.equations, SumSquares.forest_cons,
    SumSquares.forest_nil, List.append_nil]

@[simp] theorem firstChild_pairData (a b : Data) : firstChild (pairData a b).toBits = a.toBits := by
  simp [pairData, firstChild_toBits]

@[simp] theorem second_pairData (a b : Data) : NNF.second (pairData a b).toBits = b.toBits := by
  simp [NNF.second, pairData, remainingChildren_toBits, firstChild_toBits]

theorem gateBits_encode (g : Gate) : gateBits g.encode = SumSquares.forest g.equations := by
  cases g <;>
    simp [gateBits, constantPacket, addPacket, mulPacket, zeroPacket, Gate.encode, Gate.toData,
      outIndex, leftIndex, rightIndex, payload,
      Codec.unary_toBits_injective.eq_iff, constantBits_toBits, addBits_toBits, mulBits_toBits, zeroBits_toBits]

end LeanCanny.ETR.ComplexCircuit
