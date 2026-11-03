/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRowCode
/-! # Constructive original row codes for retained references and sums

Retained indices are newest first. Their encoded producer labels are
birth-1-index. These constructors never inspect any algebra element or root.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRowConstructor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def referenceWord (birth i : ℕ) : List Bool:=
  pair [decide (i<birth)] (BinaryNatCode.encode (birth-1-i))

theorem referenceWord_FP {birth i : List Bool→ℕ} (hb : BinaryFn birth) (hi : BinaryFn i) :
    (fun q=>referenceWord (birth q) (i q))∈FP:=
  mem_FP_pair (hi.lt hb).flag_mem_FP ((hb.sub (BinaryFn.const 1)).sub hi).bits_mem_FP

theorem referenceWord_decode (birth i : ℕ) (hi : i<birth) :
    IntegralMixedCausalRowCode.atom (referenceWord birth i) birth=.reference i:=by
  have HL : birth-1-i<birth:=by omega
  simp only [IntegralMixedCausalRowCode.atom,IntegralMixedCausalRowCode.active,
    IntegralMixedCausalRowCode.reference,referenceWord,pairFst_pair,pairSnd_pair,
    List.getElem?_cons_zero,Option.getD_some,decide_eq_true_eq,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    hi,HL,true_and,ite_true,show birth-1-(birth-1-i)=i by omega]

def sumWord (left right : List Bool) :=pair [true] (pair left right)

theorem sumWord_FP {left right : List Bool→List Bool} (hl : left∈FP) (hr : right∈FP) :
    (fun q=>sumWord (left q) (right q))∈FP:=mem_FP_pair (constFn_mem_FP [true]) (mem_FP_pair hl hr)

abbrev Atom (birth : ℕ):=Option (Fin birth)

noncomputable def Atom.value {birth : ℕ} : Atom birth→AffineExpr
  | none=>.constant 0
  | some i=>.reference i.val

def Atom.word {birth : ℕ} : Atom birth→List Bool
  | none=>[]
  | some i=>referenceWord birth i.val

theorem Atom.decode {birth : ℕ} (a : Atom birth) :
    IntegralMixedCausalRowCode.atom a.word birth=a.value:=by
  cases a with
  | none=>
    have H : ¬IntegralMixedCausalRowCode.active [] birth:=fun h=>Bool.false_ne_true h.1
    exact ite_eq_right H
  | some i=>exact referenceWord_decode birth i.val i.isLt

inductive Row (birth : ℕ) where
  | single (a : Atom birth)
  | sum (left right : Atom birth)

noncomputable def Row.value {birth : ℕ} : Row birth→AffineExpr
  | .single a=>a.value
  | .sum a b=>.add a.value b.value

def Row.base {birth : ℕ} : Row birth→List Bool
  | .single a=>a.word
  | .sum _ _=>[]

def Row.midpoint {birth : ℕ} : Row birth→List Bool
  | .single _=>[]
  | .sum a b=>sumWord a.word b.word

theorem Row.decode {birth : ℕ} (r : Row birth) :
    IntegralMixedCausalRowCode.expression r.base r.midpoint birth=r.value:=by
  cases r with
  | single a=>
    simp only [base,midpoint,value,IntegralMixedCausalRowCode.expression,
      show IntegralMixedCausalRowCode.midpoint []=false from rfl,Bool.false_eq_true,ite_false,Atom.decode]
  | sum a b=>
    simp only [base,midpoint,value,sumWord,IntegralMixedCausalRowCode.expression,
      IntegralMixedCausalRowCode.midpoint,pairFst_pair,pairSnd_pair,List.getElem?_cons_zero,
      Option.getD_some,ite_true,Atom.decode]

end LeanCanny.Encoding.IntegralMixedCausalRowConstructor
