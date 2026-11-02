/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedUnitRowCode
public import LeanCanny.Algebra.IntegralMixedAffineCode
public import LeanCanny.ETR.EncodingFP
/-! # Native causal reference and midpoint rows

An atom is the original pair flag/binary producer label. A midpoint entry is
pair flag (pair leftAtom rightAtom); an absent midpoint uses the original
single atom. Invalid producer labels contribute zero. No bank value is read.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRowCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def active (atom : List Bool) (birth : ℕ) : Prop :=
  (pairFst atom)[0]?.getD false=true ∧ Nat.fromBitsLE (pairSnd atom)<birth

def reference (atom : List Bool) (birth : ℕ) := birth-1-Nat.fromBitsLE (pairSnd atom)
noncomputable def atom (code : List Bool) (birth : ℕ) : AffineExpr :=
  if active code birth then .reference (reference code birth) else .constant 0

def midpoint (code : List Bool) : Bool := (pairFst code)[0]?.getD false
noncomputable def expression (base mid : List Bool) (birth : ℕ) : AffineExpr :=
  if midpoint mid then .add (atom (pairFst (pairSnd mid)) birth) (atom (pairSnd (pairSnd mid)) birth)
  else atom base birth

theorem atom_eq_unit (rows : List Bool) (birth i : ℕ) :
    atom (WordList.get rows i) birth=IntegralMixedUnitRowCode.expression rows birth i := rfl

theorem atom_causal (code : List Bool) (birth j : ℕ) (he : atom code birth=.reference j) : j<birth := by
  unfold atom at he
  split_ifs at he with ha
  · cases he
    unfold reference active at *
    omega

theorem atom_encode_FP {code : List Bool→List Bool} {birth : List Bool→ℕ}
    (hc : code∈FP) (hb : UnaryFn birth) :
    (fun q => IntegralMixedAffineCode.encode (atom (code q) (birth q)))∈FP := by
  have HP := mem_FP_comp hc pairSnd_mem_FP
  have HF := FPPred.getBit (mem_FP_comp hc pairFst_mem_FP) (UnaryFn.const 0)
  have HA : FPPred (fun q => active (code q) (birth q)) :=
    (HF.and ((BinaryFn.fromBits HP).lt (BinaryFn.ofUnary hb))).of_iff (fun _ => Iff.rfl)
  have HU := (hb.sub (UnaryFn.const 1)).sub (UnaryFn.fromBitsLE_min HP hb)
  have HR : UnaryFn (fun q => reference (code q) (birth q)) := HU.of_eq (fun q => by
    change birth q-1-min (Nat.fromBitsLE (pairSnd (code q))) (birth q)=_
    unfold reference
    omega)
  exact mem_FP_of_eq (HA.ite_mem_FP (ETR.Term.variableBits_mem_FP HR)
    (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0)))) (fun q => by
      unfold atom
      split_ifs <;> simp only [ETR.Term.variableBits_eq,IntegralMixedAffineCode.encode,IntegralMixedAffineCode.term])

theorem expression_encode_FP {base mid : List Bool→List Bool} {birth : List Bool→ℕ}
    (hc : base∈FP) (hm : mid∈FP) (hb : UnaryFn birth) :
    (fun q => IntegralMixedAffineCode.encode (expression (base q) (mid q) (birth q)))∈FP := by
  have HL := atom_encode_FP (mem_FP_comp (mem_FP_comp hm pairSnd_mem_FP) pairFst_mem_FP) hb
  have HR := atom_encode_FP (mem_FP_comp (mem_FP_comp hm pairSnd_mem_FP) pairSnd_mem_FP) hb
  have HF := FPPred.getBit (mem_FP_comp hm pairFst_mem_FP) (UnaryFn.const 0)
  apply mem_FP_of_eq (HF.ite_mem_FP (ETR.Codec.taggedTwo_mem_FP 2 HL HR) (atom_encode_FP hc hb))
  intro q
  simp only [Function.comp_apply]
  unfold expression midpoint
  split_ifs <;> simp only [IntegralMixedAffineCode.encode,IntegralMixedAffineCode.term,ETR.Codec.taggedTwo_toBits,ETR.Term.toData]

end LeanCanny.Encoding.IntegralMixedCausalRowCode
