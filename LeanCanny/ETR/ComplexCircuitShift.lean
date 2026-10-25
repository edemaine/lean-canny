/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitCapturedTransform

/-! # Native relocation of shared arithmetic circuits

Adding a unary offset to every wire preserves the local equations and acyclic
program structure. The encoded scanner retains the original binary integer
payloads and includes the cost of its input-dependent offset.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding.Brackets

def Gate.shift (b : ℕ) : Gate → Gate
  | .constant out z => .constant (b + out) z
  | .add out left right => .add (b + out) (b + left) (b + right)
  | .mul out left right => .mul (b + out) (b + left) (b + right)
  | .zero wire => .zero (b + wire)

theorem Gate.shift_holds (b : ℕ) (g : Gate) (env : ℕ → ℂ) :
    (Gate.shift b g).Holds env ↔ g.Holds (fun i => env (b + i)) := by cases g <;> rfl

def Operation.shift (b : ℕ) : Operation → Operation
  | .constant z => .constant z
  | .add left right => .add (b + left) (b + right)
  | .mul left right => .mul (b + left) (b + right)

theorem Operation.shift_gate (b out : ℕ) (op : Operation) :
    (Operation.shift b op).gate (b + out) = Gate.shift b (op.gate out) := by cases op <;> rfl

theorem Operation.shift_inputsBelow (b out : ℕ) (op : Operation) (h : op.InputsBelow out) :
    (Operation.shift b op).InputsBelow (b + out) := by
  cases op with
  | constant z => trivial
  | add left right => exact ⟨Nat.add_lt_add_left h.1 b, Nat.add_lt_add_left h.2 b⟩
  | mul left right => exact ⟨Nat.add_lt_add_left h.1 b, Nat.add_lt_add_left h.2 b⟩

theorem StraightLine.shift_gates (b start : ℕ) (ops : List Operation) :
    StraightLine.gates (b + start) (ops.map (Operation.shift b)) =
      (StraightLine.gates start ops).map (Gate.shift b) := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons, StraightLine.gates, Operation.shift_gate, Nat.add_assoc, ih]

theorem StraightLine.shift_wellFormed (b start : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed (b + start) (ops.map (Operation.shift b)) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    exact ⟨Operation.shift_inputsBelow b start op hw.1, ih (start + 1) hw.2⟩

namespace WireShift

def node (bits : List Bool) : List Bool := pairSnd bits
def offset (bits : List Bool) : ℕ := (pairFst bits).length

theorem node_mem_FP : node ∈ FP := pairSnd_mem_FP
theorem offset_unary : UnaryFn offset := (UnaryFn.length pairFst_mem_FP).of_eq (fun _ => rfl)

def gateBits (bits : List Bool) : List Bool :=
  let g := node bits
  let b := offset bits
  if firstChild g = (Codec.unary 0).toBits then
    constantGateBits (b + outIndex g) (NNF.second (payload g))
  else if firstChild g = (Codec.unary 1).toBits then
    arithmeticGateBits 1 (b + outIndex g) (b + leftIndex g) (b + rightIndex g)
  else if firstChild g = (Codec.unary 2).toBits then
    arithmeticGateBits 2 (b + outIndex g) (b + leftIndex g) (b + rightIndex g)
  else zeroGateBits (b + Codec.unaryValue (payload g))

attribute [local irreducible] node offset outIndex leftIndex rightIndex payload NNF.second firstChild

theorem gateBits_mem_FP : gateBits ∈ FP := by
  have ho := offset_unary.add (UnaryFn.comp (f := outIndex) (g := node) outIndex_unary node_mem_FP)
  have hl := offset_unary.add (UnaryFn.comp (f := leftIndex) (g := node) leftIndex_unary node_mem_FP)
  have hr := offset_unary.add (UnaryFn.comp (f := rightIndex) (g := node) rightIndex_unary node_mem_FP)
  have hp := mem_FP_comp (f := node) (g := payload) node_mem_FP payload_mem_FP
  have hc := constantGateBits_mem_FP ho (mem_FP_comp (f := fun b => payload (node b)) (g := NNF.second) hp NNF.second_mem_FP)
  have hz := zeroGateBits_mem_FP (offset_unary.add (UnaryFn.comp (f := Codec.unaryValue)
    (g := fun b => payload (node b)) Codec.unaryValue_unary hp))
  have htag (k : ℕ) := stringEq_fppred
    (mem_FP_comp (f := node) (g := firstChild) node_mem_FP firstChild_mem_FP) (constFn_mem_FP (Codec.unary k).toBits)
  have h := (htag 0).ite_mem_FP hc ((htag 1).ite_mem_FP (arithmeticGateBits_mem_FP 1 ho hl hr)
    ((htag 2).ite_mem_FP (arithmeticGateBits_mem_FP 2 ho hl hr) hz))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem gateBits_encode (b : ℕ) (g : Gate) :
    gateBits (pair (List.replicate b true) g.encode) = (Gate.shift b g).encode := by
  cases g <;>
    simp [gateBits, node, offset, pairFst_pair, pairSnd_pair, Gate.encode, Gate.toData, Gate.shift,
      outIndex, leftIndex, rightIndex, payload, Codec.unary_toBits_injective.eq_iff,
      constantGateBits_encode, addGateBits_encode, mulGateBits_encode, zeroGateBits_encode]

def run (packet : List Bool) : List Bool := CapturedTransform.run gateBits packet

theorem run_mem_FP : run ∈ FP := CapturedTransform.run_mem_FP gateBits_mem_FP

theorem run_encode (b : ℕ) (gs : List Gate) :
    run (pair (List.replicate b true) (encode gs)) = encode (gs.map (Gate.shift b)) := by
  have hw (g : Gate) : gateBits (pair (List.replicate b true) g.encode) = forest [Gate.shift b g] := by
    rw [gateBits_encode, forest_cons, forest_nil, List.append_nil]
  have hm : gs.flatMap (fun g => [Gate.shift b g]) = gs.map (Gate.shift b) := by
    induction gs with
    | nil => rfl
    | cons g gs ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]
  have h := CapturedTransform.run_encode gateBits (List.replicate b true) (fun g => [Gate.shift b g]) hw gs
  simpa only [run, hm] using h

theorem encode_mem_FP {b : List Bool → ℕ} {gs : List Bool → List Gate}
    (hb : UnaryFn b) (hg : (fun c => encode (gs c)) ∈ FP) :
    (fun c => encode ((gs c).map (Gate.shift (b c)))) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_pair hb.mem_FP hg) run_mem_FP) (fun c => run_encode (b c) (gs c))

end WireShift
end LeanCanny.ETR.ComplexCircuit
