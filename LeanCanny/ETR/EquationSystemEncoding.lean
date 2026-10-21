/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationMaskFP

/-!
# Polynomial-time assembly of encoded equation systems

A system is a self-delimiting pair of a unary fresh-variable counter and an
encoded term list. Conjunction concatenates lists; disjunction writes a Boolean
selector and masks both branches. These operations agree exactly with the
existing typed compiler, including term order and the next variable index.
-/

@[expose] public section

namespace LeanCanny.ETR

open LeanCanny.Encoding.Brackets

namespace SumSquares

@[simp] theorem listBits_length (ts : List Term) : (listBits ts).length = Term.listDataSize ts + 2 := by
  induction ts with
  | nil => simp [listBits, Data.size_empty]
  | cons t ts ih =>
      simp only [listBits, Data.length_toBits, List.map_cons, Data.cons_size] at *
      rw [ih]
      rfl

@[simp] theorem consNode_listBits (t : Term) (ts : List Term) :
    consNode t.toData.toBits (listBits ts) = listBits (t :: ts) := by
  simp only [listBits, List.map_cons, consNode_toBits]

end SumSquares

namespace EquationSystem

def encode (s : EquationSystem) : List Bool :=
  pair (Codec.unary s.next).toBits (SumSquares.listBits s.terms)

@[simp] theorem encode_length (s : EquationSystem) : s.encode.length = s.dataSize + 4 * s.next + 8 := by
  simp only [encode, pair_length, Data.length_toBits, Codec.unary_size,
    SumSquares.listBits_length, dataSize]
  omega

def appendTerms (left right : List Bool) : List Bool := wrap (contents left ++ contents right)

theorem appendTerms_mem_FP {left right : List Bool → List Bool} (hl : left ∈ FP) (hr : right ∈ FP) :
    (fun z => appendTerms (left z) (right z)) ∈ FP := by
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp hl contents_mem_FP)
    (mem_FP_comp hr contents_mem_FP)) wrap_mem_FP
  refine mem_FP_of_eq h (fun z => ?_)
  simp only [appendTerms, Function.comp_apply]

theorem appendTerms_listBits (ts us : List Term) :
    appendTerms (SumSquares.listBits ts) (SumSquares.listBits us) = SumSquares.listBits (ts ++ us) := by
  rw [appendTerms, SumSquares.contents_listBits, SumSquares.contents_listBits, ← EquationMask.wrap_forest]
  simp only [SumSquares.forest, List.map_append, List.flatten_append]

def conjunctionBits (packet : List Bool) : List Bool :=
  let a := pairFst packet
  let b := pairSnd packet
  pair (pairFst b) (appendTerms (pairSnd a) (pairSnd b))

theorem conjunctionBits_mem_FP : conjunctionBits ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hb := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hn := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have h := mem_FP_pair hn (appendTerms_mem_FP ha hb)
  refine mem_FP_of_eq h (fun z => ?_)
  simp only [conjunctionBits, Function.comp_apply]

@[simp] theorem conjunctionBits_encode (a b : EquationSystem) :
    conjunctionBits (pair a.encode b.encode) = (a.conjunction b).encode := by
  simp only [conjunctionBits, encode, pairFst_pair, pairSnd_pair, appendTerms_listBits, conjunction]

def disjunctionBits (packet : List Bool) : List Bool :=
  let a := pairFst packet
  let b := pairSnd packet
  let i := Codec.unaryValue (pairFst b)
  let left := EquationMask.mask (pair (Term.variableBits i) (pairSnd a))
  let right := EquationMask.mask (pair (Term.oneMinusBits i) (pairSnd b))
  pair (Codec.unary (i + 1)).toBits
    (consNode (Term.booleanBits i) (appendTerms left right))

theorem disjunctionBits_mem_FP : disjunctionBits ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hb := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hn := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hi := Codec.unaryValue_unary.comp hn
  have hl := mem_FP_comp (mem_FP_pair (Term.variableBits_mem_FP hi) ha) EquationMask.mask_mem_FP
  have hr := mem_FP_comp (mem_FP_pair (Term.oneMinusBits_mem_FP hi) hb) EquationMask.mask_mem_FP
  have ht := consNode_mem_FP (Term.booleanBits_mem_FP hi) (appendTerms_mem_FP hl hr)
  have h := mem_FP_pair (Codec.unary_toBits_mem_FP (hi.add (UnaryFn.const 1))) ht
  refine mem_FP_of_eq h (fun z => ?_)
  simp only [disjunctionBits, Function.comp_apply]

@[simp] theorem disjunctionBits_encode (a b : EquationSystem) :
    disjunctionBits (pair a.encode b.encode) = (a.disjunction b).encode := by
  simp only [disjunctionBits, encode, pairFst_pair, pairSnd_pair, Codec.unaryValue_toBits,
    Term.variableBits_eq, Term.oneMinusBits_toBits, EquationMask.mask_pair,
    appendTerms_listBits, Term.booleanBits_toBits, SumSquares.consNode_listBits, disjunction]

end EquationSystem
end LeanCanny.ETR
