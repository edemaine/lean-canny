/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaBooleanCircuitNodes
public import LeanCanny.Computation.BooleanCircuitValues

/-! # Truth preservation for original formula Boolean circuits -/

@[expose] public section
namespace LeanCanny.ETR.FormulaBooleanCircuitSource
open LeanCanny.Encoding LeanCanny.Computation BooleanCircuitSpace
open scoped Classical

def evalSign (σ : Term → SignType) : Formula → Bool
  | .falsum => false
  | .eqZero t => decide (σ t = 0)
  | .ltZero t => decide (σ t = -1)
  | .not p => !(evalSign σ p)
  | .and p q => evalSign σ p && evalSign σ q
  | .or p q => evalSign σ p || evalSign σ q

noncomputable def atom (σ : Term → SignType) (q : List Bool) : Bool := decide (σ (term q) = requested q)

attribute [local irreducible] FormulaView.normalize term requested node gateTag left right

private theorem op_zero (a l r : Bool) : operation 0 a l r = false := by cases a <;> cases l <;> cases r <;> decide
private theorem op_atom (a l r : Bool) : operation 2 a l r = a := by cases a <;> cases l <;> cases r <;> decide
private theorem op_not (a l r : Bool) : operation 3 a l r = !l := by cases a <;> cases l <;> cases r <;> decide
private theorem op_and (a l r : Bool) : operation 4 a l r = (l && r) := by cases a <;> cases l <;> cases r <;> decide
private theorem op_or (a l r : Bool) : operation 5 a l r = (l || r) := by cases a <;> cases l <;> cases r <;> decide

private theorem wire_binary (σ : Term → SignType) (c pre suffix : List Bool) (d : Bool) (p q : Formula)
    (hc : FormulaView.normalize c = pre ++ (binary d p q).encode ++ suffix)
    (hL : wireValue circuit (atom σ) c (wire c (pre ++ header (binaryTag d))) = evalSign σ p)
    (hR : wireValue circuit (atom σ) c (wire c (pre ++ header (binaryTag d) ++ p.encode)) = evalSign σ q) :
    wireValue circuit (atom σ) c (wire c pre) = evalSign σ (binary d p q) := by
  have hn := node_at c pre suffix (binary d p q) hc
  have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre))) = binaryTag d := by
    have H := gateTag_node _ (binary d p q) hn
    cases d <;> exact H
  have hcL : FormulaView.normalize c = pre ++ header (binaryTag d) ++ p.encode ++ (q.encode ++ [true] ++ suffix) := by
    simpa only [encode_binary, List.append_assoc] using hc
  have hcR : FormulaView.normalize c = pre ++ (header (binaryTag d) ++ p.encode) ++ q.encode ++ ([true] ++ suffix) := by
    simpa only [encode_binary, List.append_assoc] using hc
  have hl : wire c (pre ++ header (binaryTag d)) < wire c pre :=
    wire_child_lt c pre _ _ p hcL (by simp [header])
  have hr : wire c (pre ++ header (binaryTag d) ++ p.encode) < wire c pre := by
    simpa only [List.append_assoc] using wire_child_lt c pre _ _ q hcR (by simp [header])
  have hleft : circuit.left (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header (binaryTag d)) :=
    left_binary_at c pre suffix d p q hc
  have hright : circuit.right (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header (binaryTag d) ++ p.encode) :=
    right_binary_at c pre suffix d p q hc
  rw [wireValue_step, ht, hleft, hright, read_wire circuit (atom σ) c _ _ hl, read_wire circuit (atom σ) c _ _ hr, hL, hR]
  cases d <;> simp only [binary, binaryTag, Bool.false_eq_true, ite_false, ite_true, op_and, op_or, evalSign]

theorem wire_formula (σ : Term → SignType) (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize c = pre ++ p.encode ++ suffix) :
    wireValue circuit (atom σ) c (wire c pre) = evalSign σ p := by
  induction p generalizing pre suffix with
  | falsum =>
    have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre))) = 0 :=
      gateTag_node _ .falsum (node_at c pre suffix .falsum hc)
    rw [wireValue_step, ht, op_zero]
    rfl
  | eqZero t =>
    have hn := node_at c pre suffix (.eqZero t) hc
    have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre))) = 2 := gateTag_node _ (.eqZero t) hn
    rw [wireValue_step, ht, op_atom]
    simp only [atom, term_eq_node _ t hn, requested_eq_node _ t hn, evalSign]
  | ltZero t =>
    have hn := node_at c pre suffix (.ltZero t) hc
    have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre))) = 2 := gateTag_node _ (.ltZero t) hn
    rw [wireValue_step, ht, op_atom]
    simp only [atom, term_lt_node _ t hn, requested_lt_node _ t hn, evalSign]
  | not p ih =>
    have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre))) = 3 :=
      gateTag_node _ (.not p) (node_at c pre suffix (.not p) hc)
    have hcL : FormulaView.normalize c = (pre ++ header 3) ++ p.encode ++ ([true] ++ suffix) := by
      simpa only [encode_not, List.append_assoc] using hc
    have hl : wire c (pre ++ header 3) < wire c pre := wire_child_lt c pre _ _ p hcL (by simp [header])
    have hleft : circuit.left (pair c (BinaryNatCode.encode (wire c pre))) = wire c (pre ++ header 3) := left_not c pre suffix p hc
    rw [wireValue_step, ht, op_not, hleft, read_wire circuit (atom σ) c _ _ hl, ih _ _ hcL]
    rfl
  | and p q ihp ihq =>
    apply wire_binary σ c pre suffix false p q hc
    · apply ihp _ (q.encode ++ [true] ++ suffix)
      have H : FormulaView.normalize c = pre ++ (binary false p q).encode ++ suffix := hc
      simpa only [encode_binary, List.append_assoc] using H
    · apply ihq _ ([true] ++ suffix)
      have H : FormulaView.normalize c = pre ++ (binary false p q).encode ++ suffix := hc
      simpa only [encode_binary, List.append_assoc] using H
  | or p q ihp ihq =>
    apply wire_binary σ c pre suffix true p q hc
    · apply ihp _ (q.encode ++ [true] ++ suffix)
      have H : FormulaView.normalize c = pre ++ (binary true p q).encode ++ suffix := hc
      simpa only [encode_binary, List.append_assoc] using H
    · apply ihq _ ([true] ++ suffix)
      have H : FormulaView.normalize c = pre ++ (binary true p q).encode ++ suffix := hc
      simpa only [encode_binary, List.append_assoc] using H

theorem value_formula (σ : Term → SignType) (c : List Bool) :
    BooleanCircuitSpace.value circuit (atom σ) c = evalSign σ (FormulaView.formula c) := by
  have he := FormulaView.normalize_eq_formula c
  have hn : 0 < circuit.count c := by
    change 0 < (FormulaView.normalize c).length
    rw [he]
    simp [Formula.encode]
  rw [value_eq_wireValue circuit (atom σ) c hn]
  exact wire_formula σ c [] [] (FormulaView.formula c) (by simpa only [List.nil_append, List.append_nil] using he)

theorem evalSign_holds (env : ℕ → ℝ) (p : Formula) :
    evalSign (fun t => SignType.sign (t.eval env)) p = true ↔ p.Holds env := by
  induction p <;> simp_all [evalSign, Formula.Holds, sign_eq_zero_iff, sign_eq_neg_one_iff, Bool.eq_false_iff]

theorem value_holds (env : ℕ → ℝ) (c : List Bool) :
    BooleanCircuitSpace.value circuit (atom (fun t => SignType.sign (t.eval env))) c = true ↔ (FormulaView.formula c).Holds env := by
  rw [value_formula, evalSign_holds]

end LeanCanny.ETR.FormulaBooleanCircuitSource
