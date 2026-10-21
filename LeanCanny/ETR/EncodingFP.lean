/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EncodingBounds
public import LeanCanny.Encoding.BracketAccess

/-!
# Polynomial-time operations on the ETR syntax codec

These are certified bitstring implementations, agreeing with the existing typed
codec on all encoded arguments. Unary fields are both writable and recognizable
in polynomial time. Tagged constructors manipulate already encoded subtrees.
-/

@[expose] public section

namespace LeanCanny.ETR

open LeanCanny.Encoding.Brackets

namespace Codec

theorem unary_toBits (n : ℕ) :
    (unary n).toBits = wrap (List.replicate n [false, true]).flatten := by
  simp [unary, Data.toBits_l, wrap]

theorem unary_toBits_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => (unary (n z)).toBits) ∈ FP := by
  refine mem_FP_of_eq (mem_FP_comp (repeatWord_mem_FP hn [false, true]) wrap_mem_FP)
    (fun z => (unary_toBits (n z)).symm)

theorem unary_toBits_injective : Function.Injective (fun n => (unary n).toBits) := by
  intro i j h
  have hlen := congrArg List.length h
  simp only [Data.length_toBits, unary_size] at hlen
  omega

/-- The only possible unary payload of a string of the given literal length. -/
def unaryValue (bits : List Bool) : ℕ := (bits.length - 2) / 2

theorem unaryValue_unary : UnaryFn unaryValue :=
  ((UnaryFn.length id_mem_FP).sub (UnaryFn.const 2)).div (UnaryFn.const 2)

@[simp] theorem unaryValue_toBits (n : ℕ) : unaryValue (unary n).toBits = n := by
  simp only [unaryValue, Data.length_toBits, unary_size]
  omega

/-- Canonical unary fields are recognized by checking against their length-determined value. -/
def IsUnary (bits : List Bool) : Prop := bits = (unary (unaryValue bits)).toBits

instance isUnaryDecidable (bits : List Bool) : Decidable (IsUnary bits) := by
  unfold IsUnary
  infer_instance

theorem isUnary_iff (bits : List Bool) : IsUnary bits ↔ ∃ n : ℕ, bits = (unary n).toBits := by
  constructor
  · intro h
    exact ⟨unaryValue bits, h⟩
  · rintro ⟨n, rfl⟩
    simp [IsUnary]

theorem isUnary_fppred : FPPred IsUnary :=
  stringEq_fppred id_mem_FP (unary_toBits_mem_FP unaryValue_unary)

/-- A tagged node with one encoded field. -/
def taggedOne (tag : ℕ) (field : List Bool) : List Bool := wrap ((unary tag).toBits ++ field)

/-- A tagged node with two encoded fields. -/
def taggedTwo (tag : ℕ) (first second : List Bool) : List Bool :=
  wrap ((unary tag).toBits ++ first ++ second)

theorem taggedOne_mem_FP (tag : ℕ) {field : List Bool → List Bool} (hfield : field ∈ FP) :
    (fun z => taggedOne tag (field z)) ∈ FP :=
  mem_FP_comp (appendFn_mem_FP (constFn_mem_FP (unary tag).toBits) hfield) wrap_mem_FP

theorem taggedTwo_mem_FP (tag : ℕ) {first second : List Bool → List Bool}
    (hfirst : first ∈ FP) (hsecond : second ∈ FP) :
    (fun z => taggedTwo tag (first z) (second z)) ∈ FP :=
  mem_FP_comp (appendFn_mem_FP
    (appendFn_mem_FP (constFn_mem_FP (unary tag).toBits) hfirst) hsecond) wrap_mem_FP

@[simp] theorem taggedOne_toBits (tag : ℕ) (d : Data) :
    taggedOne tag d.toBits = (Data.l [unary tag, d]).toBits := by
  simp [taggedOne, wrap, Data.toBits_l]

@[simp] theorem taggedTwo_toBits (tag : ℕ) (d e : Data) :
    taggedTwo tag d.toBits e.toBits = (Data.l [unary tag, d, e]).toBits := by
  simp [taggedTwo, wrap, Data.toBits_l, List.append_assoc]

end Codec

namespace Term

/-- The fresh-variable writer agrees with the term codec for every index. -/
def variableBits (i : ℕ) : List Bool := Codec.taggedOne 1 (Codec.unary i).toBits

@[simp] theorem variableBits_eq (i : ℕ) : variableBits i = (var i).toData.toBits := by
  simp only [variableBits, Codec.taggedOne_toBits, toData]

theorem variableBits_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) :
    (fun z => variableBits (i z)) ∈ FP :=
  Codec.taggedOne_mem_FP 1 (Codec.unary_toBits_mem_FP hi)

@[simp] theorem add_toBits (t u : Term) :
    (add t u).toData.toBits = Codec.taggedTwo 2 t.toData.toBits u.toData.toBits := by
  simp only [Codec.taggedTwo_toBits, toData]

@[simp] theorem mul_toBits (t u : Term) :
    (mul t u).toData.toBits = Codec.taggedTwo 3 t.toData.toBits u.toData.toBits := by
  simp only [Codec.taggedTwo_toBits, toData]

end Term

namespace Formula

/-- The outer constructor tag, independent of any subformula parsing. -/
def constructorTag : Formula → ℕ
  | .falsum => 0
  | .eqZero _ => 1
  | .ltZero _ => 2
  | .not _ => 3
  | .and _ _ => 4
  | .or _ _ => 5

theorem firstChild_encode (p : Formula) :
    firstChild p.encode = (Codec.unary p.constructorTag).toBits := by
  cases p <;> simp only [encode, toData, firstChild_toBits, constructorTag]

theorem constructorTag_eq_one_iff (p : Formula) :
    p.constructorTag = 1 ↔ ∃ t : Term, p = .eqZero t := by
  cases p <;> simp [constructorTag]

@[simp] theorem eqZero_encode (t : Term) :
    (eqZero t).encode = Codec.taggedOne 1 t.toData.toBits := by
  simp only [encode, Codec.taggedOne_toBits, toData]

@[simp] theorem ltZero_encode (t : Term) :
    (ltZero t).encode = Codec.taggedOne 2 t.toData.toBits := by
  simp only [encode, Codec.taggedOne_toBits, toData]

end Formula
end LeanCanny.ETR
