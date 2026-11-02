/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
/-! # Native original affine bodies for causal records

All emitted affine syntax is obtained from bounded original producer labels.
Literal scales1/2 and optional midpoint rows require no bank evaluation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalUnitBodyBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalUnitRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem field_FP {code : List Bool→List Bool} (hc : code∈FP) (i : ℕ) :
    (fun q => IntegralMixedUnitRecordCode.field (code q) i)∈FP :=
  mem_FP_comp (f:=code) (g:=fun w => WordList.get w i) hc (IntegralMixedCommandHeaderBits.get_FP i)

theorem row_encode_FP {code : List Bool→List Bool} {birth index : List Bool→ℕ}
    (hc : code∈FP) (hb : UnaryFn birth) (hi : BinaryFn index) (physical : Bool) :
    (fun q => IntegralMixedAffineCode.encode (row (code q) physical (birth q) (index q)))∈FP := by
  have HR (i : ℕ) := mem_FP_comp (g:=WordList.reader)
    (mem_FP_pair (field_FP hc i) hi.bits_mem_FP) WordList.reader_FP
  have HE (i : ℕ) : (fun q => WordList.get (IntegralMixedUnitRecordCode.field (code q) i) (index q))∈FP :=
    mem_FP_of_eq (HR i) (fun q => by simp only [Function.comp_apply,WordList.reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])
  exact IntegralMixedCausalRowCode.expression_encode_FP (HE _) (HE _) hb

theorem scale_encode_FP {code : List Bool→List Bool} {index : List Bool→ℕ}
    (hc : code∈FP) (hi : UnaryFn index) (physical : Bool) :
    (fun q => SignStatisticBits.integerCode (scale (code q) physical (index q)))∈FP := by
  have HF := FPPred.getBit (field_FP hc (if physical then 12 else 13)) hi
  exact mem_FP_of_eq (HF.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode 2))
    (constFn_mem_FP (SignStatisticBits.integerCode 1))) (fun q => by
      simp only [scale,double]; split_ifs <;> rfl)

noncomputable def rows (n birth : ℕ) (code : List Bool) (physical : Bool) :=
  WordList.encode ((List.range (n+1)).map fun i => IntegralMixedAffineCode.encode (row code physical birth i))
noncomputable def scales (n : ℕ) (code : List Bool) (physical : Bool) :=
  WordList.encode ((List.range (n+1)).map fun i => SignStatisticBits.integerCode (scale code physical i))

private noncomputable def rowEntry (physical : Bool) (z : List Bool) :=
  pair (IntegralMixedAffineCode.encode (row (pairFst (pairFst z)) physical
    (pairFst (pairSnd (pairFst z))).length (pairSnd z).length)) []
private noncomputable def scaleEntry (physical : Bool) (z : List Bool) :=
  pair (SignStatisticBits.integerCode (scale (pairFst (pairFst z)) physical (pairSnd z).length)) []

/-- Packet: original record, unary creating birth, unary physical dimension. -/
noncomputable def rowsWriter (physical : Bool) (p : List Bool) :=
  rows (pairSnd (pairSnd p)).length (pairFst (pairSnd p)).length (pairFst p) physical
noncomputable def scalesWriter (physical : Bool) (p : List Bool) :=
  scales (pairSnd (pairSnd p)).length (pairFst p) physical

attribute [local irreducible] row scale

theorem rowsWriter_FP (physical : Bool) : rowsWriter physical∈FP := by
  have HC := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HB := UnaryFn.length (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
  have HE : rowEntry physical∈FP := mem_FP_pair (row_encode_FP HC HB (BinaryFn.ofUnary UnaryFn.index) physical) (constFn_mem_FP [])
  have HI := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (cons_mem_FP true)
  have H := flatMap_range_mem_FP HE HI
  apply mem_FP_of_eq H
  intro p
  simp only [rowsWriter,rows,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    rowEntry,pairFst_pair,pairSnd_pair,List.length_cons,List.length_replicate,Function.comp_apply]

theorem scalesWriter_FP (physical : Bool) : scalesWriter physical∈FP := by
  have HE : scaleEntry physical∈FP := mem_FP_pair
    (scale_encode_FP (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) UnaryFn.index physical) (constFn_mem_FP [])
  have HI := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (cons_mem_FP true)
  apply mem_FP_of_eq (flatMap_range_mem_FP HE HI)
  intro p
  simp only [scalesWriter,scales,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    scaleEntry,pairFst_pair,pairSnd_pair,List.length_cons,List.length_replicate,Function.comp_apply]

noncomputable def body (n birth : ℕ) (code : List Bool) :=
  if IntegralMixedUnitRecordCode.critical code then WordList.encode [rows n birth code true,scales n code true]
  else WordList.encode [rows n birth code false,scales n code false,
    BinaryNatCode.encode (IntegralMixedUnitRecordCode.height n code)]

noncomputable def writer (p : List Bool) :=
  body (pairSnd (pairSnd p)).length (pairFst (pairSnd p)).length (pairFst p)

theorem writer_FP : writer∈FP := by
  have HF := FPPred.getBit (mem_FP_comp pairFst_mem_FP (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0)
  have HP := mem_FP_pair (rowsWriter_FP true) (mem_FP_pair (scalesWriter_FP true) (constFn_mem_FP []))
  have HC : (fun p => IntegralMixedUnitRecordCode.height (pairSnd (pairSnd p)).length (pairFst p)) |> BinaryFn :=
    (BinaryFn.fromBits (field_FP pairFst_mem_FP 5)).mod
      (((BinaryFn.fromBits (field_FP pairFst_mem_FP 2)).mod
        (BinaryFn.ofUnary (UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))).add (BinaryFn.const 1))
  have HV := mem_FP_pair (rowsWriter_FP false) (mem_FP_pair (scalesWriter_FP false)
    (mem_FP_pair HC.bits_mem_FP (constFn_mem_FP [])))
  exact mem_FP_of_eq (HF.ite_mem_FP HP HV) (fun p => by
    simp only [Function.comp_apply,writer,body,WordList.encode,rowsWriter,scalesWriter]; rfl)

private theorem ofFn_range {α : Type} (f : ℕ→α) (N : ℕ) :
    List.ofFn (fun i : Fin N => f i.val)=(List.range N).map f := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

theorem record_body {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    (record S hn birth code hcap).template.body=body n birth code := by
  have HR (p : Bool) := ofFn_range (fun i => IntegralMixedAffineCode.encode (row code p birth i)) (n+1)
  have HS (p : Bool) := ofFn_range (fun i => SignStatisticBits.integerCode (scale code p i)) (n+1)
  cases hh : IntegralMixedUnitRecordCode.critical code
  · simp only [record,body,hh,Bool.false_eq_true,ite_false,IntegralMixedCausalRecordBits.Template.body]
    change WordList.encode [WordList.encode (List.ofFn (fun i : Fin (n+1) => IntegralMixedAffineCode.encode (row code false birth i.val))),
      WordList.encode (List.ofFn (fun i : Fin (n+1) => SignStatisticBits.integerCode (scale code false i.val))),
      BinaryNatCode.encode (IntegralMixedUnitRecordCode.height n code)]=_
    rw [HR,HS]
    rfl
  · simp only [record,body,hh,ite_true,IntegralMixedCausalRecordBits.Template.body]
    change WordList.encode [WordList.encode (List.ofFn (fun i : Fin (n+1) => IntegralMixedAffineCode.encode (row code true birth i.val))),
      WordList.encode (List.ofFn (fun i : Fin (n+1) => SignStatisticBits.integerCode (scale code true i.val)))]=_
    rw [HR,HS]
    rfl

end LeanCanny.Encoding.IntegralMixedCausalUnitBodyBits
