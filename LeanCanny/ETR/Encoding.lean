/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Syntax
public import LeanCanny.Encoding.Data
public import LeanCanny.Encoding.BinaryNatCode

/-!
# A canonical finite encoding of ETR

Formulas are tagged rose trees serialized with the local balanced-bracket bit encoding.
Tags and variable indices are unary; integer magnitudes use canonical little-endian binary.
Negative integers store `n` for `-(n+1)`, so there is no second encoding of zero.

The decoder rejects malformed trees and noncanonical bitstrings. Its two round-trip laws
identify the accepted strings exactly with encoded formulas. No computability or complexity
bound for the parser is asserted in this module.
-/

@[expose] public section

namespace LeanCanny.ETR.Codec


/-- Unary fields are lists of empty nodes. Used for tags and variable indices. -/
def unary (n : ℕ) : Data := .l (List.replicate n (.l []))

def readUnary : Data → Option ℕ
  | .l xs => if xs = List.replicate xs.length (.l []) then some xs.length else none

@[simp] theorem readUnary_unary (n : ℕ) : readUnary (unary n) = some n := by
  simp [readUnary, unary]

def bit (b : Bool) : Data := if b then .l [.l []] else .l []

def readBit : Data → Option Bool
  | .l [] => some false
  | .l [.l []] => some true
  | _ => none

@[simp] theorem readBit_bit (b : Bool) : readBit (bit b) = some b := by
  cases b <;> rfl

def natural (n : ℕ) : Data := .l (n.bits.map bit)

def readNatural : Data → Option ℕ
  | .l xs => do
      let bits ← xs.mapM readBit
      BinaryNatCode.decode? bits

@[simp] theorem mapM_readBit (bits : List Bool) :
    (bits.map bit).mapM readBit = some bits := by
  induction bits <;> simp_all

@[simp] theorem readNatural_natural (n : ℕ) : readNatural (natural n) = some n := by
  change ((n.bits.map bit).mapM readBit).bind BinaryNatCode.decode? = some n
  rw [mapM_readBit]
  exact BinaryNatCode.decode?_encode n

def integer : ℤ → Data
  | .ofNat n => .l [unary 0, natural n]
  | .negSucc n => .l [unary 1, natural n]

def readInteger : Data → Option ℤ
  | .l [sign, value] => do
      let s ← readUnary sign
      let n ← readNatural value
      match s with
      | 0 => some (.ofNat n)
      | 1 => some (.negSucc n)
      | _ => none
  | _ => none

@[simp] theorem readInteger_integer (z : ℤ) : readInteger (integer z) = some z := by
  cases z <;> simp [integer, readInteger]

end LeanCanny.ETR.Codec

namespace LeanCanny.ETR
open Codec

namespace Term

/-- Constructor tags: constant 0, variable 1, addition 2, multiplication 3. -/
def toData : Term → Data
  | .const z => .l [unary 0, integer z]
  | .var i => .l [unary 1, unary i]
  | .add a b => .l [unary 2, a.toData, b.toData]
  | .mul a b => .l [unary 3, a.toData, b.toData]

def fromData : Data → Option Term
  | .l [tag, value] => do
      let k ← readUnary tag
      match k with
      | 0 => .const <$> readInteger value
      | 1 => .var <$> readUnary value
      | _ => none
  | .l [tag, a, b] => do
      let k ← readUnary tag
      let x ← fromData a
      let y ← fromData b
      match k with
      | 2 => some (.add x y)
      | 3 => some (.mul x y)
      | _ => none
  | _ => none

@[simp] theorem fromData_toData (t : Term) : fromData t.toData = some t := by
  induction t <;> simp_all [toData, fromData]

theorem toData_injective : Function.Injective toData := by
  intro a b h
  have := congrArg fromData h
  simpa using this

end Term

namespace Formula

/-- Constructor tags: false 0, equality 1, strict inequality 2, negation 3, and 4, or 5. -/
def toData : Formula → Data
  | .falsum => .l [unary 0]
  | .eqZero t => .l [unary 1, t.toData]
  | .ltZero t => .l [unary 2, t.toData]
  | .not p => .l [unary 3, p.toData]
  | .and p q => .l [unary 4, p.toData, q.toData]
  | .or p q => .l [unary 5, p.toData, q.toData]

def fromData : Data → Option Formula
  | .l [tag] => do
      let k ← readUnary tag
      if k = 0 then some .falsum else none
  | .l [tag, value] => do
      let k ← readUnary tag
      match k with
      | 1 => .eqZero <$> Term.fromData value
      | 2 => .ltZero <$> Term.fromData value
      | 3 => .not <$> fromData value
      | _ => none
  | .l [tag, a, b] => do
      let k ← readUnary tag
      let p ← fromData a
      let q ← fromData b
      match k with
      | 4 => some (.and p q)
      | 5 => some (.or p q)
      | _ => none
  | _ => none

@[simp] theorem fromData_toData (p : Formula) : fromData p.toData = some p := by
  induction p <;> simp_all [toData, fromData]

/-- The binary input supplied to a Turing machine. -/
def encode (p : Formula) : List Bool := p.toData.toBits

/-- Parse one complete canonical formula, rejecting every other input. -/
def decode (bits : List Bool) : Option Formula := do
  let d ← Data.fromBits bits
  let p ← fromData d
  if p.encode = bits then some p else none

@[simp] theorem decode_encode (p : Formula) : decode p.encode = some p := by
  simp [decode, encode]

/-- Successful parsing recognizes precisely the canonical encoding of the result. -/
theorem decode_eq_some_iff (bits : List Bool) (p : Formula) :
    decode bits = some p ↔ bits = p.encode := by
  constructor
  · intro h
    unfold decode at h
    cases hd : Data.fromBits bits with
    | none => simp [hd] at h
    | some d =>
      rw [hd] at h
      change (fromData d).bind (fun q => if q.encode = bits then some q else none) = some p at h
      cases hp : fromData d with
      | none => simp [hp] at h
      | some q =>
        rw [hp] at h
        change (if q.encode = bits then some q else none) = some p at h
        split at h
        next he => cases h; exact he.symm
        next => simp at h
  · rintro rfl
    exact decode_encode p

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa using this

/-- The input-size measure is the literal bit length, including constants and variable names. -/
def inputSize (p : Formula) : ℕ := p.encode.length

@[simp] theorem inputSize_eq_dataSize (p : Formula) : p.inputSize = p.toData.size :=
  Data.length_toBits _

end Formula

/-- ETR as a language of *all* binary strings; malformed strings are rejected. -/
def language : Set (List Bool) := {bits | ∃ p, Formula.decode bits = some p ∧ p.Satisfiable}

/-- Encoded inputs have exactly their intended existential real semantics. -/
@[simp] theorem encode_mem_language (p : Formula) : p.encode ∈ language ↔ p.Satisfiable := by
  simp [language]

/-- Membership supplies a genuine formula and identifies the entire input with its encoding. -/
theorem mem_language_iff (bits : List Bool) :
    bits ∈ language ↔ ∃ p : Formula, bits = p.encode ∧ p.Satisfiable := by
  simp [language, Formula.decode_eq_some_iff]

theorem not_mem_language_of_decode_none {bits : List Bool} (h : Formula.decode bits = none) :
    bits ∉ language := by
  simp [language, h]

end LeanCanny.ETR
