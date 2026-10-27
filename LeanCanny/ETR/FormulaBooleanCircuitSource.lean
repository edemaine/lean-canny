/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceBooleanAtoms
public import LeanCanny.ETR.FormulaView
public import LeanCanny.ETR.TermView

/-! # Native Boolean gate readers for original formula syntax

The circuit has one slot per bracket bit, in reverse order. Formula children
occur later in the serialized source and therefore occupy earlier wires.
Atomic slots retain the original arithmetic term and its requested sign.
Malformed inputs use the existing falsum view. No gate table is materialized.
-/

@[expose] public section
namespace LeanCanny.ETR.FormulaBooleanCircuitSource
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Connectivity.AlgebraicSliceBooleanAtoms
open scoped Classical

def codes (q : List Bool) : List Bool := FormulaView.normalize (pairFst q)
theorem codes_FP : codes ∈ FP := mem_FP_comp pairFst_mem_FP FormulaView.normalize_mem_FP

def offset (q : List Bool) : ℕ := (codes q).length - 1 - Nat.fromBitsLE (pairSnd q)
theorem offset_unary : UnaryFn offset := by
  have hn := UnaryFn.length codes_FP
  have hi := UnaryFn.fromBitsLE_min pairSnd_mem_FP hn
  exact ((hn.sub (UnaryFn.const 1)).sub hi).of_eq (fun q => by dsimp [offset]; omega)

def node (q : List Bool) : List Bool := Brackets.firstNode ((codes q).drop (offset q))
theorem node_FP : node ∈ FP := mem_FP_comp (drop_mem_FP codes_FP offset_unary) Brackets.firstNode_mem_FP

def tag (q : List Bool) : List Bool := Brackets.firstChild (node q)
theorem tag_FP : tag ∈ FP := mem_FP_comp node_FP Brackets.firstChild_mem_FP

abbrev HasTag (k : ℕ) (q : List Bool) : Prop := tag q = (Codec.unary k).toBits
theorem hasTag_FP (k : ℕ) : FPPred (HasTag k) := Brackets.stringEq_fppred tag_FP (constFn_mem_FP _)

def gateTag (q : List Bool) : ℕ :=
  if HasTag 1 q ∨ HasTag 2 q then 2 else if HasTag 3 q then 3
  else if HasTag 4 q then 4 else if HasTag 5 q then 5 else 0
theorem gateTag_binary : BinaryFn gateTag :=
  BinaryFn.ite ((hasTag_FP 1).or (hasTag_FP 2)) (BinaryFn.const 2)
    (BinaryFn.ite (hasTag_FP 3) (BinaryFn.const 3)
      (BinaryFn.ite (hasTag_FP 4) (BinaryFn.const 4)
        (BinaryFn.ite (hasTag_FP 5) (BinaryFn.const 5) (BinaryFn.const 0))))

def arguments (q : List Bool) : List Bool := Brackets.afterNode (Brackets.contents (node q))
theorem arguments_FP : arguments ∈ FP :=
  mem_FP_comp (mem_FP_comp node_FP Brackets.contents_mem_FP) Brackets.afterNode_mem_FP

def firstOffset (q : List Bool) : ℕ := offset q + 1 + (tag q).length
def secondOffset (q : List Bool) : ℕ := firstOffset q + Brackets.nodeLength (arguments q)
theorem firstOffset_unary : UnaryFn firstOffset := (offset_unary.add (UnaryFn.const 1)).add (UnaryFn.length tag_FP)
theorem secondOffset_unary : UnaryFn secondOffset := firstOffset_unary.add (Brackets.nodeLength_unary.comp arguments_FP)

def left (q : List Bool) : ℕ := (codes q).length - 1 - firstOffset q
def right (q : List Bool) : ℕ := (codes q).length - 1 - secondOffset q
theorem left_binary : BinaryFn left :=
  ((BinaryFn.ofUnary (UnaryFn.length codes_FP)).sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary firstOffset_unary)
theorem right_binary : BinaryFn right :=
  ((BinaryFn.ofUnary (UnaryFn.length codes_FP)).sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary secondOffset_unary)

def termCode (q : List Bool) : List Bool := Brackets.firstNode (arguments q)
theorem termCode_FP : termCode ∈ FP := mem_FP_comp arguments_FP Brackets.firstNode_mem_FP
noncomputable def term (q : List Bool) : Term := TermView.term (termCode q)

def requested (q : List Bool) : SignType := if HasTag 2 q then -1 else 0
theorem requested_FP : (fun q => InfinitesimalSign.encode (requested q)) ∈ FP := by
  have H := (hasTag_FP 2).ite_mem_FP (constFn_mem_FP (InfinitesimalSign.encode (-1))) (constFn_mem_FP (InfinitesimalSign.encode 0))
  exact mem_FP_of_eq H (fun q => by unfold requested; split_ifs <;> rfl)

def circuit : BooleanCircuitSpace.Family where
  count c := (FormulaView.normalize c).length
  tag := gateTag
  left := left
  right := right

theorem circuit_access : BooleanCircuitSpace.Access circuit :=
  ⟨UnaryFn.length FormulaView.normalize_mem_FP, gateTag_binary, left_binary, right_binary⟩

def source : Source where
  circuit := circuit
  factor q := Nat.fromBitsLE (pairSnd q)
  sign := requested

theorem access : Access source := ⟨circuit_access, BinaryFn.fromBits pairSnd_mem_FP, requested_FP⟩

def readerQuery (read : List Bool → List Bool) (q : List Bool) : List Bool := pair (read (pairFst q)) (pairSnd q)
theorem readerQuery_FP (read : List Bool → List Bool) (hr : read ∈ FP) : readerQuery read ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP

def ofReader (read : List Bool → List Bool) : Source where
  circuit := circuit.comp read
  factor q := Nat.fromBitsLE (pairSnd q)
  sign q := requested (readerQuery read q)

attribute [local irreducible] circuit requested

theorem accessOfReader (read : List Bool → List Bool) (hr : read ∈ FP) : Access (ofReader read) := by
  have C := circuit_access.comp read hr
  have S := mem_FP_comp (readerQuery_FP read hr) requested_FP
  exact ⟨C, BinaryFn.fromBits pairSnd_mem_FP, S⟩

noncomputable def termOfReader (read : List Bool → List Bool) (q : List Bool) : Term := term (readerQuery read q)
theorem termCodeOfReader_FP (read : List Bool → List Bool) (hr : read ∈ FP) : (termCode ∘ readerQuery read) ∈ FP :=
  mem_FP_comp (readerQuery_FP read hr) termCode_FP

def wire (c pre : List Bool) : ℕ := (FormulaView.normalize c).length - 1 - pre.length

theorem offset_at (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ p.encode ++ suffix) :
    offset (pair c (BinaryNatCode.encode (wire c pre))) = pre.length := by
  have hp : 0 < p.encode.length := by simp [Formula.encode]
  simp only [offset, codes, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, wire]
  rw [hc]
  simp only [List.length_append]
  omega

theorem node_at (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ p.encode ++ suffix) :
    node (pair c (BinaryNatCode.encode (wire c pre))) = p.encode := by
  rw [node, offset_at c pre suffix p hc]
  simp only [codes, pairFst_pair, hc, List.append_assoc, List.drop_left]
  exact Brackets.firstNode_toBits_append p.toData suffix

theorem tag_at (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ p.encode ++ suffix) :
    tag (pair c (BinaryNatCode.encode (wire c pre))) = Brackets.firstChild p.encode := by
  rw [tag, node_at c pre suffix p hc]

end LeanCanny.ETR.FormulaBooleanCircuitSource
