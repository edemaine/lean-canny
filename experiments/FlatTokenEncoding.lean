/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCanny.Abstract
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Lean.Util.CollectAxioms

/-! # Flat token encoding prototype

Prefix tokens describe the same syntax as the formal abstract. Integer leaves
use the library's binary sign-magnitude encoding; variables use unary indices.
The library list encoder frames each token once, independently of tree depth.

This experiment does not change the public encoding or claim a new PSPACE
transfer. Its parser consumes decoded token lists. Round-trip correctness,
the translation to the current input bits, semantics, injectivity, and linear
bit-length bounds are checked below. A native resource certificate for the complete bit-level
translation, including rejection of malformed words, is still needed before
this could replace the current encoding.
-/

namespace LeanCanny.FlatTokenPrototype
open Abstract Turing.MultiTapeTM

/-- Tokens are integer constants, variable indices, or one of eight operators:
addition, multiplication, false, equality, strict inequality, not, and, or. -/
abbrev Token := ℤ ⊕ (ℕ ⊕ Fin 8)

def op (i : Fin 8) : Token := .inr (.inr i)

def termTokens {n : ℕ} : Term n → List Token
  | .const z => [.inl z]
  | .var i => [.inr (.inl i.val)]
  | .add a b => op 0 :: (termTokens a ++ termTokens b)
  | .mul a b => op 1 :: (termTokens a ++ termTokens b)

def formulaTokens {n : ℕ} : Formula n → List Token
  | .falsum => [op 2]
  | .eqZero t => op 3 :: termTokens t
  | .ltZero t => op 4 :: termTokens t
  | .not p => op 5 :: formulaTokens p
  | .and p q => op 6 :: (formulaTokens p ++ formulaTokens q)
  | .or p q => op 7 :: (formulaTokens p ++ formulaTokens q)

private def operatorEncoding : Fin 8 ↪ List Bool :=
  ⟨fun i => encUnary i.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

def tokenEncoding : Token ↪ List Bool :=
  encSum encIntBin (encSum encUnary operatorEncoding)

def encoding : List Token ↪ List Bool := encList tokenEncoding

def encode {n : ℕ} (p : Formula n) : List Bool := encoding (formulaTokens p)

/-- Query headers use library pairing at fixed depth. The point-query payload
is a list of exactly three formula token lists, never a recursive pairing of
syntax subtrees. -/
def encodeSpace (n : ℕ) (p : Formula n) : List Bool :=
  encPair encUnary encoding (n, formulaTokens p)

def encodePoint (n : ℕ) (p : Formula n) (ab : Formula n × Formula n) : List Bool :=
  encPair encUnary (encList encoding)
    (n, [formulaTokens p, formulaTokens ab.1, formulaTokens ab.2])

/-- Erasing finite index bounds gives the existing implementation syntax. -/
def rawTerm {n : ℕ} : Term n → ETR.Term
  | .const z => .const z
  | .var i => .var i.val
  | .add a b => .add (rawTerm a) (rawTerm b)
  | .mul a b => .mul (rawTerm a) (rawTerm b)

def rawFormula {n : ℕ} : Formula n → ETR.Formula
  | .falsum => .falsum
  | .eqZero t => .eqZero (rawTerm t)
  | .ltZero t => .ltZero (rawTerm t)
  | .not p => .not (rawFormula p)
  | .and p q => .and (rawFormula p) (rawFormula q)
  | .or p q => .or (rawFormula p) (rawFormula q)

/-- A typed stack rejects operators with operands of the wrong syntactic kind. -/
abbrev Stack := List (ETR.Term ⊕ ETR.Formula)

def step : Token → Stack → Option Stack
  | .inl z, s => some (.inl (.const z) :: s)
  | .inr (.inl i), s => some (.inl (.var i) :: s)
  | .inr (.inr k), s => match k.val, s with
    | 0, .inl a :: .inl b :: s => some (.inl (.add a b) :: s)
    | 1, .inl a :: .inl b :: s => some (.inl (.mul a b) :: s)
    | 2, s => some (.inr .falsum :: s)
    | 3, .inl t :: s => some (.inr (.eqZero t) :: s)
    | 4, .inl t :: s => some (.inr (.ltZero t) :: s)
    | 5, .inr p :: s => some (.inr (.not p) :: s)
    | 6, .inr p :: .inr q :: s => some (.inr (.and p q) :: s)
    | 7, .inr p :: .inr q :: s => some (.inr (.or p q) :: s)
    | _, _ => none

def run (tokens : List Token) (s : Option Stack) : Option Stack :=
  tokens.foldr (fun token state => state.bind (step token)) s

theorem run_append (a b : List Token) (s : Option Stack) :
    run (a ++ b) s = run a (run b s) := by
  simp [run, List.foldr_append]

theorem term_roundtrip {n : ℕ} (t : Term n) (s : Option Stack) :
    run (termTokens t) s = s.map (fun s => .inl (rawTerm t) :: s) := by
  induction t generalizing s <;> cases s <;>
    simp_all [termTokens, rawTerm, run, op, step]

theorem formula_roundtrip {n : ℕ} (p : Formula n) (s : Option Stack) :
    run (formulaTokens p) s = s.map (fun s => .inr (rawFormula p) :: s) := by
  have ht := @term_roundtrip n
  induction p generalizing s <;> cases s <;>
    simp_all [formulaTokens, rawFormula, run, op, step]

def parse (tokens : List Token) : Option ETR.Formula := do
  match ← run tokens (some []) with
  | [.inr p] => some p
  | _ => none

theorem parse_formula {n : ℕ} (p : Formula n) :
    parse (formulaTokens p) = some (rawFormula p) := by
  simp [parse, formula_roundtrip]

theorem rawTerm_eval {n : ℕ} (t : Term n) (x : Fin n → ℝ) :
    (rawTerm t).eval (ETR.Formula.extend x) = t.eval x := by
  induction t <;>
    simp_all [rawTerm, ETR.Term.eval, Term.eval, ETR.Formula.extend]

theorem rawFormula_holds {n : ℕ} (p : Formula n) (x : Fin n → ℝ) :
    (rawFormula p).Holds (ETR.Formula.extend x) ↔ x ∈ p.solutionSet := by
  induction p <;> simp_all [rawFormula, ETR.Formula.Holds, Formula.solutionSet, rawTerm_eval]

private theorem unary_code (n : ℕ) : (ETR.Codec.unary n).toBits = AbstractEncoding.unary n := by
  simp [ETR.Codec.unary, AbstractEncoding.unary, AbstractEncoding.node, Data.toBits_l]

private theorem bit_code (b : Bool) : (ETR.Codec.bit b).toBits = AbstractEncoding.bit b := by
  cases b <;> simp [ETR.Codec.bit, AbstractEncoding.bit, AbstractEncoding.node, Data.toBits_l]

private theorem integer_code (z : ℤ) : (ETR.Codec.integer z).toBits = AbstractEncoding.integer z := by
  cases z <;> simp [ETR.Codec.integer, ETR.Codec.natural, AbstractEncoding.integer,
    AbstractEncoding.node, Data.toBits_l, unary_code, List.map_map, Function.comp_def, bit_code]

theorem rawTerm_code {n : ℕ} (t : Term n) : (rawTerm t).toData.toBits = AbstractEncoding.term (@Term.rec n) t := by
  induction t <;> simp_all [rawTerm, AbstractEncoding.term, ETR.Term.toData,
    Data.toBits_l, unary_code, integer_code, AbstractEncoding.node]

theorem rawFormula_code {n : ℕ} (p : Formula n) : (rawFormula p).encode = p.encode := by
  induction p <;> simp_all [rawFormula, Formula.encode, AbstractEncoding.formula, ETR.Formula.encode,
    ETR.Formula.toData, Data.toBits_l, unary_code, rawTerm_code, AbstractEncoding.node]

/-- On valid token streams, parsing recovers exactly the old binary input. -/
theorem translate_formula {n : ℕ} (p : Formula n) :
    (parse (formulaTokens p)).map ETR.Formula.encode = some p.encode := by
  simp [parse_formula, rawFormula_code]

theorem rawTerm_injective {n : ℕ} : Function.Injective (@rawTerm n) := by
  intro a b h
  induction a generalizing b <;> cases b <;> simp [rawTerm] at h
  all_goals aesop (add safe Fin.ext)

theorem rawFormula_injective {n : ℕ} : Function.Injective (@rawFormula n) := by
  intro a b h
  induction a generalizing b <;> cases b <;>
    simp [rawFormula, rawTerm_injective.eq_iff] at h
  all_goals aesop

/-- The binary serialization determines the entire original finite formula. -/
theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro p q h
  have ht := encoding.injective h
  apply rawFormula_injective
  exact Option.some.inj (by simpa only [parse_formula] using congrArg parse ht)

/-- Source weight counts a unit per operator, unary variable length plus one,
and binary coefficient length plus one. -/
def tokenWeight : Token → ℕ
  | .inl z => z.natAbs.size + 1
  | .inr (.inl i) => i + 1
  | .inr (.inr _) => 1

def weight (tokens : List Token) : ℕ := (tokens.map tokenWeight).sum

theorem framed_token_length (t : Token) :
    (frame (tokenEncoding t)).length ≤ 21 * tokenWeight t := by
  rcases t with z | (i | k)
  · change (frame (false :: encIntBin z)).length ≤ 21 * (z.natAbs.size + 1)
    simp only [length_frame, List.length_cons, length_encIntBin]
    omega

  · change (frame (true :: false :: List.replicate i true)).length ≤ 21 * (i + 1)
    simp only [length_frame, List.length_cons, List.length_replicate]
    omega
  · change (frame (true :: true :: List.replicate k.val true)).length ≤ 21
    simp only [length_frame, List.length_cons, List.length_replicate]
    have := k.isLt
    omega

theorem weight_le_framed_token_length (t : Token) :
    tokenWeight t ≤ (frame (tokenEncoding t)).length := by
  rcases t with z | (i | k)
  · change z.natAbs.size + 1 ≤ (frame (false :: encIntBin z)).length
    simp only [length_frame, List.length_cons, length_encIntBin]
    omega
  · change i + 1 ≤ (frame (true :: false :: List.replicate i true)).length
    simp only [length_frame, List.length_cons, List.length_replicate]
    omega
  · change 1 ≤ (frame (true :: true :: List.replicate k.val true)).length
    simp only [length_frame, List.length_cons, List.length_replicate]
    omega

theorem encoding_length (tokens : List Token) :
    (encoding tokens).length ≤ 21 * weight tokens := by
  induction tokens with
  | nil => simp [encoding, weight]
  | cons t ts ih =>
    have ht := framed_token_length t
    simpa [encoding, encList_cons, weight, Nat.mul_add] using Nat.add_le_add ht ih

theorem weight_le_encoding_length (tokens : List Token) :
    weight tokens ≤ (encoding tokens).length := by
  induction tokens with
  | nil => simp [encoding, weight]
  | cons t ts ih =>
    have ht := weight_le_framed_token_length t
    simpa [encoding, encList_cons, weight] using Nat.add_le_add ht ih

def termWeight {n : ℕ} : Term n → ℕ
  | .const z => z.natAbs.size + 1
  | .var i => i.val + 1
  | .add a b | .mul a b => 1 + termWeight a + termWeight b

def formulaWeight {n : ℕ} : Formula n → ℕ
  | .falsum => 1
  | .eqZero t | .ltZero t => 1 + termWeight t
  | .not p => 1 + formulaWeight p
  | .and p q | .or p q => 1 + formulaWeight p + formulaWeight q

theorem term_weight {n : ℕ} (t : Term n) : weight (termTokens t) = termWeight t := by
  induction t <;> simp_all [termTokens, termWeight, weight, tokenWeight, op, Nat.add_assoc]

theorem formula_weight {n : ℕ} (p : Formula n) :
    weight (formulaTokens p) = formulaWeight p := by
  have ht : ∀ t : Term n, (List.map tokenWeight (termTokens t)).sum = termWeight t := term_weight
  induction p <;>
    simp_all [formulaTokens, formulaWeight, weight, tokenWeight, op, Nat.add_assoc]

/-- Serialization is linear in the original tree's weighted size, regardless
of how unbalanced or deeply nested that tree is. -/
theorem formula_encoding_length {n : ℕ} (p : Formula n) :
    (encode p).length ≤ 21 * formulaWeight p := by
  simpa only [encode, formula_weight] using encoding_length (formulaTokens p)

theorem formula_weight_le_encoding_length {n : ℕ} (p : Formula n) :
    formulaWeight p ≤ (encode p).length := by
  simpa only [encode, formula_weight] using weight_le_encoding_length (formulaTokens p)

/-- A binary word determines at most one token list. -/
theorem token_list_injective : Function.Injective encoding := encoding.injective

end LeanCanny.FlatTokenPrototype

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`LeanCanny.FlatTokenPrototype).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  if checked = 0 then throwError "No prototype declarations found"
  logInfo m!"Audited {checked} flat-token prototype declarations: only standard axioms."
