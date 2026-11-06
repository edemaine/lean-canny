/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ContextTreeFold
public import LeanCanny.ETR.NNFFP
public import LeanCanny.ETR.IntegerResidueFP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-! # Flat library encodings of arithmetic syntax

Library list framing is applied once per token. The native tree pass translates
the established syntax format to the library encoding of a flat token list.
-/
@[expose] public section
set_option maxHeartbeats 400000

namespace LeanCanny.Encoding.FlatSyntax
open Turing.MultiTapeTM Brackets ETR

abbrev Token := ℤ ⊕ ℕ
def tokenEncoding : Token ↪ List Bool := encSum encIntBin encUnary
def encoding : List Token ↪ List Bool := encList tokenEncoding
def op (k : ℕ) : Token := .inr k

def termTokens : Term → List Token
  | .const z => [.inl z]
  | .var i => [.inr (i + 8)]
  | .add a b => op 0 :: (termTokens a ++ termTokens b)
  | .mul a b => op 1 :: (termTokens a ++ termTokens b)
def formulaTokens : Formula → List Token
  | .falsum => [op 2]
  | .eqZero t => op 3 :: termTokens t
  | .ltZero t => op 4 :: termTokens t
  | .not p => op 5 :: formulaTokens p
  | .and p q => op 6 :: (formulaTokens p ++ formulaTokens q)
  | .or p q => op 7 :: (formulaTokens p ++ formulaTokens q)

def operatorBits (k : ℕ) : List Bool := frame (tokenEncoding (op k))
@[simp] theorem frame_op (k : ℕ) : frame (tokenEncoding (op k)) = operatorBits k := rfl
@[simp] theorem encoding_cons (t : Token) (ts : List Token) :
    encoding (t :: ts) = frame (tokenEncoding t) ++ encoding ts := rfl
@[simp] theorem encoding_append (a b : List Token) :
    encoding (a ++ b) = encoding a ++ encoding b := List.flatMap_append

def integerBits (bits : List Bool) : List Bool :=
  let magnitude := Codec.IntegerResidue.magnitudeDigits bits
  if Codec.IntegerResidue.negative bits then true :: BinaryNat.succ magnitude
  else false :: magnitude
theorem integerBits_mem_FP : integerBits ∈ FP := by
  have h := Codec.IntegerResidue.negative_fppred.ite_mem_FP
    (mem_FP_comp (mem_FP_comp Codec.IntegerResidue.magnitudeDigits_mem_FP BinaryNat.succ_mem_FP) (cons_mem_FP true))
    (mem_FP_comp Codec.IntegerResidue.magnitudeDigits_mem_FP (cons_mem_FP false))
  exact mem_FP_of_eq (g := integerBits) h (fun bits => by simp only [integerBits, Function.comp_apply])

@[simp] theorem integerBits_integer (z : ℤ) :
    integerBits (Codec.integer z).toBits = encIntBin z := by
  cases z <;> simp [integerBits, Codec.IntegerResidue.negative, Codec.integer,
    firstChild_toBits, Codec.IntegerResidue.magnitudeDigits,
    Codec.integerMagnitude, remainingChildren_toBits, Codec.IntegerResidue.naturalDigits_natural,
    BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Codec.unary_toBits_injective.eq_iff]

def raw (bits : List Bool) : List Bool := pairFst bits
def terms (bits : List Bool) : List Bool := pairFst (pairSnd bits)
def formulas (bits : List Bool) : List Bool := pairSnd (pairSnd bits)
def second (bits : List Bool) : List Bool := unframe (dropFrame bits)
def third (bits : List Bool) : List Bool := unframe (dropFrame (dropFrame bits))
theorem raw_FP : raw ∈ FP := pairFst_mem_FP
theorem terms_FP : terms ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem formulas_FP : formulas ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem second_FP : second ∈ FP :=
  ComputableTidilyInPolyTime.unframe.comp ComputableTidilyInPolyTime.dropFrame
theorem third_FP : third ∈ FP :=
  ComputableTidilyInPolyTime.unframe.comp
    (ComputableTidilyInPolyTime.dropFrame.comp ComputableTidilyInPolyTime.dropFrame)

def tag (bits : List Bool) : ℕ := Codec.unaryValue (firstChild (raw bits))
def argument (bits : List Bool) : List Bool := NNF.second (raw bits)
theorem tag_unary : UnaryFn tag := Codec.unaryValue_unary.comp (mem_FP_comp (f := raw) (g := firstChild) raw_FP firstChild_mem_FP)
theorem argument_FP : argument ∈ FP := mem_FP_comp raw_FP NNF.second_mem_FP

/-- Arithmetic and Boolean summaries are kept separately. -/
def finish (isFormula : Bool) (bits : List Bool) : List Bool :=
  let t := tag bits
  if isFormula then
    if t = 0 then operatorBits 2
    else if t = 1 then operatorBits 3 ++ second (terms bits)
    else if t = 2 then operatorBits 4 ++ second (terms bits)
    else if t = 3 then operatorBits 5 ++ second (formulas bits)
    else if t = 4 then operatorBits 6 ++ second (formulas bits) ++ third (formulas bits)
    else operatorBits 7 ++ second (formulas bits) ++ third (formulas bits)
  else
    if t = 0 then frame (false :: integerBits (argument bits))
    else if t = 1 then frame (true :: encUnary (Codec.unaryValue (argument bits) + 8))
    else if t = 2 then operatorBits 0 ++ second (terms bits) ++ third (terms bits)
    else operatorBits 1 ++ second (terms bits) ++ third (terms bits)

theorem frame_FP : frame ∈ FP :=
  ComputableTidilyInPolyTime.of_linear (.of_frame fun _ => rfl)
theorem finish_FP (isFormula : Bool) : finish isFormula ∈ FP := by
  have ht := mem_FP_comp terms_FP second_FP
  have hu := mem_FP_comp terms_FP third_FP
  have hp := mem_FP_comp formulas_FP second_FP
  have hq := mem_FP_comp formulas_FP third_FP
  have pref (k : ℕ) {f : List Bool → List Bool} (hf : f ∈ FP) :=
    appendFn_mem_FP (constFn_mem_FP (operatorBits k)) hf
  have hi := mem_FP_comp (mem_FP_comp argument_FP integerBits_mem_FP) (cons_mem_FP false)
  have hv := mem_FP_comp ((UnaryFn.add (Codec.unaryValue_unary.comp argument_FP) (UnaryFn.const 8)).encoded) (cons_mem_FP true)
  cases isFormula
  · have h := (FPPred.eq tag_unary (UnaryFn.const 0)).ite_mem_FP
      (mem_FP_comp hi frame_FP)
      ((FPPred.eq tag_unary (UnaryFn.const 1)).ite_mem_FP (mem_FP_comp hv frame_FP)
        ((FPPred.eq tag_unary (UnaryFn.const 2)).ite_mem_FP
          (pref 0 (appendFn_mem_FP ht hu)) (pref 1 (appendFn_mem_FP ht hu))))
    exact mem_FP_of_eq (g := finish false) h (fun bits => by simp only [finish, Function.comp_apply, Bool.false_eq_true, ite_false, List.append_assoc])
  · have h := (FPPred.eq tag_unary (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP (operatorBits 2))
      ((FPPred.eq tag_unary (UnaryFn.const 1)).ite_mem_FP (pref 3 ht)
      ((FPPred.eq tag_unary (UnaryFn.const 2)).ite_mem_FP (pref 4 ht)
      ((FPPred.eq tag_unary (UnaryFn.const 3)).ite_mem_FP (pref 5 hp)
      ((FPPred.eq tag_unary (UnaryFn.const 4)).ite_mem_FP
        (pref 6 (appendFn_mem_FP hp hq)) (pref 7 (appendFn_mem_FP hp hq))))))
    exact mem_FP_of_eq (g := finish true) h (fun bits => by simp only [finish, Function.comp_apply, ite_true, List.append_assoc])

/-- A uniform cap bounds even malformed intermediate summaries. It is chosen
above the flat encoding length of every valid source subtree. -/
def pack (d : Data) (ts ps : List (List Bool)) : List Bool :=
  pair d.toBits (pair (encList encBits ts) (encList encBits ps))

def summaries (limit : ℕ) : Data → List (List Bool) × List (List Bool)
  | .l [] => ([], [])
  | .l (d :: ds) =>
    let child := summaries limit d
    let rest := summaries limit (.l ds)
    let bits := pack d child.1 child.2
    ((finish false bits).take limit :: rest.1, (finish true bits).take limit :: rest.2)

def dataTokens (limit : ℕ) (isFormula : Bool) (d : Data) : List Bool :=
  let children := summaries limit d
  (finish isFormula (pack d children.1 children.2)).take limit

def code (limit : ℕ) (xs : List Data) : List Bool :=
  let children := summaries limit (.l xs)
  pack (.l xs) children.1 children.2

@[simp] theorem summaries_nil (limit : ℕ) : summaries limit (.l []) = ([], []) := by simp [summaries]
@[simp] theorem summaries_cons (limit : ℕ) (d : Data) (xs : List Data) :
    summaries limit (.l (d :: xs)) =
      (dataTokens limit false d :: (summaries limit (.l xs)).1,
       dataTokens limit true d :: (summaries limit (.l xs)).2) := by simp [summaries, dataTokens]

def combine (child parent : List Data) : List Data := Data.l child :: parent
def cap (bits : List Bool) : ℕ := 100 * bits.length

def combineBits (packet : List Bool) : List Bool :=
  let input := pairFst packet
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent))
    (pair (frame ((finish false child).take (cap input)) ++ terms parent)
      (frame ((finish true child).take (cap input)) ++ formulas parent))

theorem combineBits_FP : combineBits ∈ FP := by
  have hz := pairFst_mem_FP
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hl : UnaryFn (fun p => cap (pairFst p)) :=
    (UnaryFn.const 100).mul (UnaryFn.length hz)
  have term := take_mem_FP (mem_FP_comp hc (finish_FP false)) hl
  have form := take_mem_FP (mem_FP_comp hc (finish_FP true)) hl
  have h := mem_FP_pair (consNode_mem_FP (mem_FP_comp hc raw_FP) (mem_FP_comp hp raw_FP))
    (mem_FP_pair (appendFn_mem_FP (mem_FP_comp term frame_FP) (mem_FP_comp hp terms_FP))
      (appendFn_mem_FP (mem_FP_comp form frame_FP) (mem_FP_comp hp formulas_FP)))
  exact mem_FP_of_eq (g := combineBits) h (fun bits => by simp only [combineBits, Function.comp_apply])

theorem combineBits_code (z : List Bool) (child parent : List Data) :
    combineBits (pair z (pair (code (cap z) child) (code (cap z) parent))) =
      code (cap z) (combine child parent) := by
  simp [combineBits, code, pack, raw, terms, formulas, combine, dataTokens,
    encList_cons, consNode_toBits]

theorem code_growth (limit : ℕ) (child parent : List Data) :
    (code limit (combine child parent)).length ≤
      (code limit child).length + (code limit parent).length + 8 * limit + 4 := by
  have ht := List.length_take_le limit (finish false (code limit child))
  have hp := List.length_take_le limit (finish true (code limit child))
  simp only [combine, code, pack, summaries_cons, encList_cons, pair_length,
    List.length_append, length_frame, Data.length_toBits, Data.cons_size,
    dataTokens, encBits_apply, List.length_take] at *
  omega

/-- The full stack pass is polynomial time on every word, including malformed
ones; each frame combination has a polynomial additive output allowance. -/
theorem run_FP :
    (fun z => DynamicTreeFold.encode (code (cap z)) (TreeFold.run [] combine z)) ∈ FP := by
  exact DynamicTreeFold.runEncoded_mem_FP_context_of_additive
    (fun _ => ([] : List Data)) (fun _ => combine) (fun z => code (cap z))
    (fun _ => code 0 []) combineBits (constFn_mem_FP (code 0 [])) combineBits_FP
    (fun _ => by simp [code, pack]) combineBits_code
    (((PolyBound.const 800).mul PolyBound.id).add (PolyBound.const 4))
    (fun z child parent => by have H := code_growth (cap z) child parent; simp only [cap] at *; omega)

@[simp] theorem encoding_nil : encoding [] = [] := rfl
@[simp] theorem const_length (z : ℤ) :
    (encoding [.inl z]).length = 2 * z.natAbs.size + 5 := by
  change (frame (false :: encIntBin z) ++ []).length = _
  simp only [List.length_append, List.length_nil, length_frame, List.length_cons, length_encIntBin]; omega
@[simp] theorem var_length (i : ℕ) :
    (encoding [.inr (i + 8)]).length = 2 * i + 19 := by
  change (frame (true :: encUnary (i + 8)) ++ []).length = _
  simp [length_frame, encUnary_apply]; omega
theorem op_length (k : ℕ) : (operatorBits k).length = 2 * k + 3 := by
  change (frame (true :: encUnary k)).length = _
  simp [length_frame, encUnary_apply]

theorem natural_lower (n : ℕ) : n.size ≤ (Codec.natural n).size := by
  have h : ∀ bs : List Bool, bs.length ≤ (Data.l (bs.map Codec.bit)).size := by
    intro bs; induction bs with
    | nil => simp [Data.size_empty]
    | cons b bs ih => cases b <;> simp [Codec.bit, Data.cons_size, Data.size_empty] at * <;> omega
  simpa only [Codec.natural, Nat.size_eq_bits_len] using h n.bits

theorem size_succ_le (n : ℕ) : (n + 1).size ≤ n.size + 1 := by
  have h := Nat.size_le_size (show n + 1 ≤ Nat.bit true n by simp [Nat.bit_val]; omega)
  simpa only [Nat.size_bit (show Nat.bit true n ≠ 0 by simp [Nat.bit_val])] using h

theorem integer_bounds (z : ℤ) :
    (Codec.integer z).size ≤ 10 * (z.natAbs.size + 1) ∧
      z.natAbs.size + 1 ≤ 10 * (Codec.integer z).size := by
  cases z with
  | ofNat n =>
    have hu := Codec.natural_size_le n
    have hl := natural_lower n
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty ]
    change _ ≤ 10 * (n.size + 1) ∧ n.size + 1 ≤ _
    omega
  | negSucc n =>
    have hu := Codec.natural_size_le n
    have hl := natural_lower n
    have hm := Nat.size_le_size (show n ≤ n + 1 by omega)
    have hs := size_succ_le n
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty, Int.natAbs_negSucc, Nat.succ_eq_add_one]
    omega

theorem term_lengths (t : Term) :
    (encoding (termTokens t)).length ≤ 100 * t.toData.size ∧
      t.toData.size ≤ 100 * (encoding (termTokens t)).length := by
  induction t with
  | const z =>
    have h := integer_bounds z
    simp only [termTokens, const_length, Term.toData, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega
  | var i =>
    simp only [termTokens, var_length, Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size]
    omega
  | add a b ha hb =>
    have hk := op_length 0
    simp only [termTokens, encoding_cons, encoding_append, List.length_append,
      Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size, frame_op]
    change (operatorBits 0).length + _ ≤ _ ∧ _
    omega
  | mul a b ha hb =>
    have hk := op_length 1
    simp only [termTokens, encoding_cons, encoding_append, List.length_append,
      Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size, frame_op]
    change (operatorBits 1).length + _ ≤ _ ∧ _
    omega

theorem formula_lengths (p : Formula) :
    (encoding (formulaTokens p)).length ≤ 100 * p.toData.size ∧
      p.toData.size ≤ 100 * (encoding (formulaTokens p)).length := by
  have h2 := op_length 2
  have h3 := op_length 3
  have h4 := op_length 4
  have h5 := op_length 5
  have h6 := op_length 6
  have h7 := op_length 7
  induction p <;>
    simp only [formulaTokens, encoding_cons, encoding_append, encoding_nil,
      List.length_append, List.length_nil, Nat.add_zero, frame_op,
      Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size]
  case eqZero t => have ht := term_lengths t; omega
  case ltZero t => have ht := term_lengths t; omega
  all_goals omega

@[simp] theorem encoding_const (z : ℤ) : encoding [.inl z] = frame (false :: encIntBin z) := by
  simp only [encoding_cons, encoding_nil, List.append_nil]; rfl
@[simp] theorem encoding_var (i : ℕ) : encoding [.inr (i + 8)] = frame (true :: encUnary (i + 8)) := by
  simp only [encoding_cons, encoding_nil, List.append_nil]; rfl

theorem finish_term (limit : ℕ) (t : Term) :
    finish false (code limit t.toData.asList) = match t with
      | .const z => encoding [.inl z]
      | .var i => encoding [.inr (i + 8)]
      | .add a b => operatorBits 0 ++ dataTokens limit false a.toData ++ dataTokens limit false b.toData
      | .mul a b => operatorBits 1 ++ dataTokens limit false a.toData ++ dataTokens limit false b.toData := by
  cases t <;>
    simp [finish, tag, argument, code, pack, raw, terms, second, third,
      Term.toData, NNF.second, firstChild_toBits, remainingChildren_toBits,
      Codec.unaryValue_toBits, Data.l_asList, encList_cons, encBits_apply, tokenEncoding, encSum, encUnary_apply]

theorem finish_formula (limit : ℕ) (p : Formula) :
    finish true (code limit p.toData.asList) = match p with
      | .falsum => operatorBits 2
      | .eqZero t => operatorBits 3 ++ dataTokens limit false t.toData
      | .ltZero t => operatorBits 4 ++ dataTokens limit false t.toData
      | .not q => operatorBits 5 ++ dataTokens limit true q.toData
      | .and q r => operatorBits 6 ++ dataTokens limit true q.toData ++ dataTokens limit true r.toData
      | .or q r => operatorBits 7 ++ dataTokens limit true q.toData ++ dataTokens limit true r.toData := by
  cases p <;>
    simp [finish, tag, code, pack, raw, terms, formulas, second, third,
      Formula.toData, firstChild_toBits, Codec.unaryValue_toBits,
      Data.l_asList, encList_cons, encBits_apply]

theorem dataTokens_code (limit : ℕ) (kind : Bool) (d : Data) :
    dataTokens limit kind d = (finish kind (code limit d.asList)).take limit := by
  simp only [dataTokens, code, Data.asList_l]

theorem dataTokens_term (t : Term) (limit : ℕ) (hl : 100 * t.toData.size ≤ limit) :
    dataTokens limit false t.toData = encoding (termTokens t) := by
  have hlen := (term_lengths t).1.trans hl
  induction t generalizing limit with
  | const z =>
    rw [dataTokens_code]
    rw [finish_term]
    exact List.take_of_length_le hlen
  | var i =>
    rw [dataTokens_code]
    rw [finish_term]
    exact List.take_of_length_le hlen
  | add a b ia ib =>
    have ha : 100 * a.toData.size ≤ limit := by
      simp only [Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    have hb : 100 * b.toData.size ≤ limit := by
      simp only [Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_term]
    dsimp only
    rw [ia limit ha ((term_lengths a).1.trans ha), ib limit hb ((term_lengths b).1.trans hb)]
    simpa only [termTokens, encoding_cons, encoding_append, frame_op, List.append_assoc] using List.take_of_length_le hlen
  | mul a b ia ib =>
    have ha : 100 * a.toData.size ≤ limit := by
      simp only [Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    have hb : 100 * b.toData.size ≤ limit := by
      simp only [Term.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_term]
    dsimp only
    rw [ia limit ha ((term_lengths a).1.trans ha), ib limit hb ((term_lengths b).1.trans hb)]
    simpa only [termTokens, encoding_cons, encoding_append, frame_op, List.append_assoc] using List.take_of_length_le hlen

theorem dataTokens_formula (p : Formula) (limit : ℕ) (hl : 100 * p.toData.size ≤ limit) :
    dataTokens limit true p.toData = encoding (formulaTokens p) := by
  induction p generalizing limit with
  | falsum =>
    have hlen := (formula_lengths .falsum).1.trans hl
    rw [dataTokens_code]
    rw [finish_formula]
    simpa only [formulaTokens, encoding_cons, encoding_nil, frame_op, List.append_nil] using List.take_of_length_le hlen
  | eqZero t =>
    have hlen := (formula_lengths (.eqZero t)).1.trans hl
    have ht : 100 * t.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_formula]
    dsimp only
    rw [dataTokens_term t limit ht]
    exact List.take_of_length_le hlen
  | ltZero t =>
    have hlen := (formula_lengths (.ltZero t)).1.trans hl
    have ht : 100 * t.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_formula]
    dsimp only
    rw [dataTokens_term t limit ht]
    exact List.take_of_length_le hlen
  | not p ih =>
    have hlen := (formula_lengths (.not p)).1.trans hl
    have hp : 100 * p.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_formula]
    dsimp only
    rw [ih limit hp]
    exact List.take_of_length_le hlen
  | and p q ip iq =>
    have hlen := (formula_lengths (.and p q)).1.trans hl
    have hp : 100 * p.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    have hq : 100 * q.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_formula]
    dsimp only
    rw [ip limit hp, iq limit hq]
    simpa only [formulaTokens, encoding_cons, encoding_append, frame_op, List.append_assoc] using List.take_of_length_le hlen
  | or p q ip iq =>
    have hlen := (formula_lengths (.or p q)).1.trans hl
    have hp : 100 * p.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    have hq : 100 * q.toData.size ≤ limit := by
      simp only [Formula.toData, Data.cons_size, Data.size_empty, Codec.unary_size] at hl; omega
    rw [dataTokens_code]
    rw [finish_formula]
    dsimp only
    rw [ip limit hp, iq limit hq]
    simpa only [formulaTokens, encoding_cons, encoding_append, frame_op, List.append_assoc] using List.take_of_length_le hlen

theorem fold_identity (d : Data) : TreeFold.foldData ([] : List Data) combine d = d.asList := by
  induction d using Data.inductionL with
  | nil => simp only [TreeFold.foldData, List.map_nil, List.foldr_nil, Data.l_asList]
  | cons x xs hx hxs =>
    simpa only [TreeFold.foldData, List.map_cons, List.foldr_cons, combine,
      Data.l_asList, hx, Data.asList_l] using congrArg (List.cons x) hxs

def extract (bits : List Bool) : List Bool := unframe (formulas (pairFst (bits.drop 1)))
theorem extract_FP : extract ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp (mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1))
    pairFst_mem_FP) formulas_FP) ComputableTidilyInPolyTime.unframe
  exact mem_FP_of_eq (g := extract) h (fun _ => rfl)

def translate (bits : List Bool) : List Bool :=
  extract (DynamicTreeFold.encode (code (cap bits)) (TreeFold.run [] combine bits))
theorem translate_FP : translate ∈ FP := mem_FP_comp run_FP extract_FP

theorem translate_data (d : Data) : translate d.toBits = dataTokens (cap d.toBits) true d := by
  simp [translate, extract, TreeFold.run_toBits, fold_identity, combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, pack, formulas,
    dataTokens, encList_cons, encBits_apply]

theorem translate_formula (p : Formula) : translate p.encode = encoding (formulaTokens p) := by
  rw [Formula.encode, translate_data]
  exact dataTokens_formula p _ (by simp [cap, Data.length_toBits])

end LeanCanny.Encoding.FlatSyntax
