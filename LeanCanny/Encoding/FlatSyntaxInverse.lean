/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import LeanCanny.Encoding.FlatSyntax
public import LeanCanny.ETR.NumericLiteralFP
public import LeanCanny.Computation.PolyTimeIteration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold

/-! # A native inverse compiler for flat polynomial syntax

The right-to-left prefix parser retains subtrees on a stack. A round-trip test
and the original grammar reject malformed flat input. No search over candidate
syntax trees is needed, so changing the input convention costs no CH level.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatSyntaxInverse

open Turing.MultiTapeTM LeanCanny.ETR Brackets FlatSyntax

def literal (token : List Bool) : List Bool :=
  if token.take 2 = [false, true] then
    (Term.const (-(Nat.fromBitsLE (token.drop 2) : ℤ))).toData.toBits
  else (Term.const (Nat.fromBitsLE (token.drop 2) : ℤ)).toData.toBits

theorem literal_FP : literal ∈ FP := by
  have hn := BinaryFn.fromBits (drop_mem_FP id_mem_FP (UnaryFn.const 2))
  exact (stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 2)) (constFn_mem_FP [false, true])).ite_mem_FP
    (Term.negNat_toBits_mem_FP hn) (Term.nat_toBits_mem_FP hn)

def unaryNode (tag : ℕ) (stack : List Bool) : List Bool :=
  Codec.taggedOne tag (firstNode stack) ++ afterNode stack

def binaryNode (tag : ℕ) (stack : List Bool) : List Bool :=
  Codec.taggedTwo tag (firstNode stack) (firstNode (afterNode stack)) ++ afterNode (afterNode stack)

theorem unaryNode_FP (tag : ℕ) : unaryNode tag ∈ FP :=
  appendFn_mem_FP (Codec.taggedOne_mem_FP tag firstNode_mem_FP) afterNode_mem_FP

theorem binaryNode_FP (tag : ℕ) : binaryNode tag ∈ FP :=
  appendFn_mem_FP (Codec.taggedTwo_mem_FP tag firstNode_mem_FP
    (mem_FP_comp afterNode_mem_FP firstNode_mem_FP))
    (mem_FP_comp afterNode_mem_FP afterNode_mem_FP)

def step (stack token : List Bool) : List Bool :=
  if token.take 1 = [false] then literal token ++ stack
  else
    let k := token.length - 1
    if k = 0 then binaryNode 2 stack
    else if k = 1 then binaryNode 3 stack
    else if k = 2 then Formula.falsum.encode ++ stack
    else if k = 3 then unaryNode 1 stack
    else if k = 4 then unaryNode 2 stack
    else if k = 5 then unaryNode 3 stack
    else if k = 6 then binaryNode 4 stack
    else if k = 7 then binaryNode 5 stack
    else Term.variableBits (k - 8) ++ stack

theorem step_FP : (fun packet => step (pairFst packet) (pairSnd packet)) ∈ FP := by
  have hs := pairFst_mem_FP
  have ht := pairSnd_mem_FP
  have hk := (UnaryFn.length ht).sub (UnaryFn.const 1)
  have he (k : ℕ) := FPPred.eq hk (UnaryFn.const k)
  have hu (k : ℕ) := mem_FP_comp hs (unaryNode_FP k)
  have hb (k : ℕ) := mem_FP_comp hs (binaryNode_FP k)
  exact (stringEq_fppred (take_mem_FP ht (UnaryFn.const 1)) (constFn_mem_FP [false])).ite_mem_FP
    (appendFn_mem_FP (mem_FP_comp ht literal_FP) hs)
    ((he 0).ite_mem_FP (hb 2) ((he 1).ite_mem_FP (hb 3)
      ((he 2).ite_mem_FP (appendFn_mem_FP (constFn_mem_FP _) hs)
        ((he 3).ite_mem_FP (hu 1) ((he 4).ite_mem_FP (hu 2)
          ((he 5).ite_mem_FP (hu 3) ((he 6).ite_mem_FP (hb 4)
            ((he 7).ite_mem_FP (hb 5)
              (appendFn_mem_FP (Term.variableBits_mem_FP (hk.sub (UnaryFn.const 8))) hs)))))))))

private theorem split_length (s : List Bool) : (firstNode s).length + (afterNode s).length = s.length := by
  simpa only [firstNode, afterNode, List.length_take, List.length_drop] using
    (show min (nodeLength s) s.length + (s.length - nodeLength s) = s.length by omega)

private theorem unaryNode_length (tag : ℕ) (s : List Bool) :
    (unaryNode tag s).length = s.length + 2 * tag + 4 := by
  have h := split_length s
  simp only [unaryNode, Codec.taggedOne, wrap, List.length_cons, List.length_append,
    Data.length_toBits, Codec.unary_size, List.length_nil]
  omega

private theorem binaryNode_length (tag : ℕ) (s : List Bool) :
    (binaryNode tag s).length = s.length + 2 * tag + 4 := by
  have h := split_length s
  have h' := split_length (afterNode s)
  simp only [binaryNode, Codec.taggedTwo, wrap, List.length_cons, List.length_append,
    Data.length_toBits, Codec.unary_size, List.length_nil]
  omega

private theorem step_length (s token : List Bool) :
    (step s token).length ≤ s.length + (literal token).length + 2 * token.length + 20 := by
  simp only [step]
  split_ifs <;> simp only [List.length_append, unaryNode_length, binaryNode_length,
    Term.variableBits_eq, Data.length_toBits, Term.toData, Data.cons_size,
    Data.size_empty, Codec.unary_size, Formula.encode, Formula.toData] <;> omega

def parse (bits : List Bool) : List Bool :=
  firstNode ((frames bits).foldr (fun token stack => step stack token) [])

theorem parse_FP : parse ∈ FP := by
  obtain ⟨a, d, ha⟩ := literal_FP.polyBounded_length.exists_le
  have hl := ComputableTidilyInPolyTime.listReverseWithInput
    computableInDegree_frames.computableInPolyTime.tidy
  let inputList := fun w : List Bool => (frames w).reverse
  have hlist : ComputableTidilyInPolyTime inputList encBits (encList encBits) := hl
  have hs' : ComputableTidilyInPolyTime (fun q : List Bool × List Bool => step q.1 q.2)
      (encPair encBits encBits) encBits := by
    simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using
      step_FP.comp (pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
        (ComputableTidilyInPolyTime.snd encBits encBits))
  have h := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (step := fun (_ : Bool) stack token => step stack token) (ComputableTidilyInPolyTime.const false)
    hlist (ComputableTidilyInPolyTime.const ([] : List Bool))
    (hs'.comp (((ComputableTidilyInPolyTime.fst (encPair encBool encBits) encBits).snd').prod
      (ComputableTidilyInPolyTime.snd (encPair encBool encBits) encBits)))
    (growth := fun w => a * ((encList encBits (inputList w)).length + 1) ^ d +
      2 * (encList encBits (inputList w)).length + 20)
    (by exact (((PolyBounded.const a).mul
      ((hlist.polyBounded_length.add (.const 1)).pow d)).add
        ((PolyBounded.const 2).mul hlist.polyBounded_length)).add (.const 20))
    (by
      intro w stack token ht
      have htlen : token.length ≤ (encList encBits (inputList w)).length := by
        have hm : token.length ≤ ((inputList w).map (fun v => v.length)).sum :=
          List.single_le_sum (fun v _ => Nat.zero_le v) token.length (List.mem_map_of_mem ht)
        exact hm.trans (sum_length_le_length_encList encBits (inputList w))
      have hmag := (ha token).trans (Nat.mul_le_mul_left a
        (Nat.pow_le_pow_left (Nat.add_le_add_right htlen 1) d))
      simp only [encBits_apply] at hmag
      simpa only [encBits_apply] using (step_length stack token).trans (by omega))
  have h' := firstNode_mem_FP.comp h
  apply mem_FP_of_eq h'
  intro w
  simp only [parse, inputList, List.foldl_reverse, Function.comp_def]

def tokenStep (token : Token) (stack : List Bool) : List Bool := step stack (tokenEncoding token)

private theorem literal_integer (z : ℤ) : literal (tokenEncoding (.inl z)) = (Term.const z).toData.toBits := by
  cases z with
  | ofNat n => simp [literal, tokenEncoding, Nat.fromBitsLE_bits]
  | negSucc n =>
    simp only [literal, tokenEncoding, encSum_inl, encIntBin_negSucc, List.take_succ_cons,
      List.take_zero, List.drop_succ_cons, List.drop_zero, ite_true, Nat.fromBitsLE_bits]
    rw [show -((n + 1 : ℕ) : ℤ) = Int.negSucc n by omega]

private theorem unaryNode_append (tag : ℕ) (d : Data) (tail : List Bool) :
    unaryNode tag (d.toBits ++ tail) = (Data.l [Codec.unary tag, d]).toBits ++ tail := by
  rw [unaryNode, firstNode_toBits_append, afterNode_toBits_append, Codec.taggedOne_toBits]

private theorem binaryNode_append (tag : ℕ) (a b : Data) (tail : List Bool) :
    binaryNode tag (a.toBits ++ b.toBits ++ tail) =
      (Data.l [Codec.unary tag, a, b]).toBits ++ tail := by
  simp only [binaryNode, List.append_assoc, firstNode_toBits_append, afterNode_toBits_append,
    Codec.taggedTwo_toBits]

theorem fold_term (t : Term) (stack : List Bool) :
    (termTokens t).foldr tokenStep stack = t.toData.toBits ++ stack := by
  induction t generalizing stack with
  | const z =>
    simp only [termTokens, List.foldr_cons, List.foldr_nil, tokenStep, step, tokenEncoding,
      encSum_inl, List.take_succ_cons, List.take_zero, ite_true]
    rw [← literal_integer z]
    rfl
  | var i => simp [termTokens, tokenStep, step, tokenEncoding, Term.variableBits_eq]
  | add a b ha hb =>
    rw [termTokens, List.foldr_cons, List.foldr_append, hb, ha]
    change binaryNode 2 (a.toData.toBits ++ (b.toData.toBits ++ stack)) = _
    rw [← List.append_assoc, binaryNode_append]
    rfl
  | mul a b ha hb =>
    rw [termTokens, List.foldr_cons, List.foldr_append, hb, ha]
    change binaryNode 3 (a.toData.toBits ++ (b.toData.toBits ++ stack)) = _
    rw [← List.append_assoc, binaryNode_append]
    rfl

theorem fold_formula (p : Formula) (stack : List Bool) :
    (formulaTokens p).foldr tokenStep stack = p.encode ++ stack := by
  induction p generalizing stack with
  | falsum => rfl
  | eqZero t =>
    rw [formulaTokens, List.foldr_cons, fold_term]
    change unaryNode 1 (t.toData.toBits ++ stack) = _
    exact unaryNode_append 1 t.toData stack
  | ltZero t =>
    rw [formulaTokens, List.foldr_cons, fold_term]
    change unaryNode 2 (t.toData.toBits ++ stack) = _
    exact unaryNode_append 2 t.toData stack
  | not p hp =>
    rw [formulaTokens, List.foldr_cons, hp]
    change unaryNode 3 (p.toData.toBits ++ stack) = _
    exact unaryNode_append 3 p.toData stack
  | and p q hp hq =>
    rw [formulaTokens, List.foldr_cons, List.foldr_append, hq, hp]
    change binaryNode 4 (p.toData.toBits ++ (q.toData.toBits ++ stack)) = _
    rw [← List.append_assoc, binaryNode_append]
    rfl
  | or p q hp hq =>
    rw [formulaTokens, List.foldr_cons, List.foldr_append, hq, hp]
    change binaryNode 5 (p.toData.toBits ++ (q.toData.toBits ++ stack)) = _
    rw [← List.append_assoc, binaryNode_append]
    rfl

theorem parse_formula (p : Formula) : parse (encoding (formulaTokens p)) = p.encode := by
  rw [parse, encoding, frames_encList, List.foldr_map]
  change firstNode ((formulaTokens p).foldr (fun token stack => step stack (tokenEncoding token)) []) = _
  have hfold : (formulaTokens p).foldr (fun token stack => step stack (tokenEncoding token)) [] = p.encode := by
    exact (fold_formula p []).trans (List.append_nil _)
  rw [hfold]
  change firstNode p.toData.toBits = p.toData.toBits
  simpa only [List.append_nil] using firstNode_toBits_append p.toData []

end LeanCanny.Encoding.FlatSyntaxInverse
