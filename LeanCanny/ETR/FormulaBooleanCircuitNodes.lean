/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaBooleanCircuitSource

/-! # Exact gate and child positions of encoded formula nodes -/

@[expose] public section
namespace LeanCanny.ETR.FormulaBooleanCircuitSource
open LeanCanny.Encoding LeanCanny.Computation

def header (k : ℕ) : List Bool := false :: (Codec.unary k).toBits
def binary (disjoin : Bool) (p q : Formula) : Formula := if disjoin then .or p q else .and p q
def binaryTag (disjoin : Bool) : ℕ := if disjoin then 5 else 4

theorem encode_not (p : Formula) : (Formula.not p).encode = header 3 ++ p.encode ++ [true] := by
  simp [Formula.encode, Formula.toData, Data.toBits_l, header, List.append_assoc]

theorem encode_binary (d : Bool) (p q : Formula) :
    (binary d p q).encode = header (binaryTag d) ++ p.encode ++ q.encode ++ [true] := by
  cases d <;> simp [binary, binaryTag, Formula.encode, Formula.toData, Data.toBits_l, header, List.append_assoc]

def kind : Formula → ℕ
  | .falsum => 0
  | .eqZero _ | .ltZero _ => 2
  | .not _ => 3
  | .and _ _ => 4
  | .or _ _ => 5

theorem gateTag_node (z : List Bool) (p : Formula) (hn : node z = p.encode) : gateTag z = kind p := by
  simp only [gateTag, HasTag, tag, hn]
  cases p <;> simp [Formula.encode, Formula.toData, kind, Codec.unary_toBits_injective.eq_iff]

theorem requested_eq_node (z : List Bool) (t : Term) (hn : node z = (Formula.eqZero t).encode) : requested z = 0 := by
  simp [requested, HasTag, tag, hn, Formula.encode, Formula.toData, Codec.unary_toBits_injective.eq_iff]

theorem requested_lt_node (z : List Bool) (t : Term) (hn : node z = (Formula.ltZero t).encode) : requested z = -1 := by
  simp [requested, HasTag, tag, hn, Formula.encode, Formula.toData]

theorem arguments_one (z : List Bool) (k : ℕ) (d : Data) (hn : node z = (Data.l [Codec.unary k, d]).toBits) :
    arguments z = d.toBits := by
  simp only [arguments, hn, Brackets.contents_toBits, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, Brackets.afterNode_toBits_append]

theorem arguments_two (z : List Bool) (k : ℕ) (a b : Data) (hn : node z = (Data.l [Codec.unary k, a, b]).toBits) :
    arguments z = a.toBits ++ b.toBits := by
  simp only [arguments, hn, Brackets.contents_toBits, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, Brackets.afterNode_toBits_append]

theorem term_eq_node (z : List Bool) (t : Term) (hn : node z = (Formula.eqZero t).encode) : term z = t := by
  rw [term, termCode, arguments_one z 1 t.toData hn]
  have H := Brackets.firstNode_toBits_append t.toData []
  simp only [List.append_nil] at H
  rw [H, TermView.term_toBits]

theorem term_lt_node (z : List Bool) (t : Term) (hn : node z = (Formula.ltZero t).encode) : term z = t := by
  rw [term, termCode, arguments_one z 2 t.toData hn]
  have H := Brackets.firstNode_toBits_append t.toData []
  simp only [List.append_nil] at H
  rw [H, TermView.term_toBits]

theorem firstOffset_at (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ p.encode ++ suffix) :
    firstOffset (pair c (BinaryNatCode.encode (wire c pre))) = pre.length + 1 + (Brackets.firstChild p.encode).length := by
  rw [firstOffset, offset_at c pre suffix p hc, tag_at c pre suffix p hc]

theorem left_not (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ (Formula.not p).encode ++ suffix) :
    left (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header 3) := by
  rw [left, firstOffset_at c pre suffix (.not p) hc]
  simp only [codes, pairFst_pair, Formula.encode, Formula.toData, Brackets.firstChild_toBits,
    wire, header, List.length_append, List.length_cons]
  omega

theorem left_binary_at (c pre suffix : List Bool) (d : Bool) (p q : Formula)
    (hc : FormulaView.normalize c = pre ++ (binary d p q).encode ++ suffix) :
    left (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header (binaryTag d)) := by
  rw [left, firstOffset_at c pre suffix (binary d p q) hc]
  cases d <;> simp only [codes, pairFst_pair, binary, binaryTag, Bool.false_eq_true, ite_false, ite_true,
    Formula.encode, Formula.toData, Brackets.firstChild_toBits, wire, header, List.length_append, List.length_cons] <;> omega

theorem right_binary_at (c pre suffix : List Bool) (d : Bool) (p q : Formula)
    (hc : FormulaView.normalize c = pre ++ (binary d p q).encode ++ suffix) :
    right (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header (binaryTag d) ++ p.encode) := by
  have hn := node_at c pre suffix (binary d p q) hc
  rw [right, secondOffset, firstOffset_at c pre suffix (binary d p q) hc]
  cases d with
  | false =>
    rw [arguments_two _ 4 p.toData q.toData hn, Brackets.nodeLength_toBits_append]
    simp only [codes, pairFst_pair, binary, binaryTag, Bool.false_eq_true, ite_false,
      Formula.encode, Formula.toData, Brackets.firstChild_toBits, wire, header, List.length_append, List.length_cons]
    omega
  | true =>
    rw [arguments_two _ 5 p.toData q.toData hn, Brackets.nodeLength_toBits_append]
    simp only [codes, pairFst_pair, binary, binaryTag, ite_true,
      Formula.encode, Formula.toData, Brackets.firstChild_toBits, wire, header, List.length_append, List.length_cons]
    omega

theorem wire_child_lt (c pre extra suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ extra ++ p.encode ++ suffix) (he : 0 < extra.length) :
    wire c (pre ++ extra) < wire c pre := by
  have hp : 0 < p.encode.length := by simp [Formula.encode]
  simp only [wire, hc, List.length_append]
  omega

end LeanCanny.ETR.FormulaBooleanCircuitSource
