/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRowConstructor
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
/-! # Exact original critical records in the existing restricted decoder

The grammar is precisely zero/reference/two-atom sum rows and scale1/scale2.
Its encoder uses the existing physical fields0,1,3,4,6,12,14, without changing
any decoder. Arbitrary affine expressions are not claimed representable.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def word (offset objective coordinate : ℕ) (base mid doubles : List Bool) :=
  WordList.encode [[true],
    BinaryNatCode.encode offset,
    [],
    BinaryNatCode.encode objective,
    BinaryNatCode.encode coordinate,
    [],
    base,
    [],
    [],
    [],
    [],
    [],
    doubles,
    [],
    mid,
    []]

theorem word_FP {offset objective coordinate : List Bool→ℕ} {base mid doubles : List Bool→List Bool}
    (ho : BinaryFn offset) (hj : BinaryFn objective) (hk : BinaryFn coordinate)
    (hb : base∈FP) (hm : mid∈FP) (hd : doubles∈FP) :
    (fun q=>word (offset q) (objective q) (coordinate q) (base q) (mid q) (doubles q))∈FP:=by
  have H0:=constFn_mem_FP ([] : List Bool)
  have HE:=(mem_FP_pair (constFn_mem_FP [true]) (mem_FP_pair ho.bits_mem_FP (mem_FP_pair H0 (mem_FP_pair hj.bits_mem_FP (mem_FP_pair hk.bits_mem_FP (mem_FP_pair H0 (mem_FP_pair hb (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair hd (mem_FP_pair H0 (mem_FP_pair hm (mem_FP_pair H0 H0))))))))))))))))
  exact mem_FP_of_eq HE (fun q=>by simp only [word,WordList.encode])

structure Data (n birth : ℕ) where
  offset : Fin (n+1)
  objective : Fin (n-offset.val+1)
  coordinate : Fin (n-offset.val+1)
  double : Fin (n+1)→Bool
  rows : Fin (n+1)→Row birth

noncomputable def Data.rule {n birth : ℕ} (d : Data n birth) : CriticalRule n where
  offset:=d.offset
  objective:=d.objective.val
  coordinate:=d.coordinate.val
  scales i:=if d.double i then 2 else 1
  scales_ne_zero i:=by split_ifs <;> norm_num
  heights i:=(d.rows i).value

def Data.code {n birth : ℕ} (d : Data n birth) : List Bool:=
  word d.offset.val d.objective.val d.coordinate.val
    (WordList.encode (List.ofFn (fun i=>(d.rows i).base)))
    (WordList.encode (List.ofFn (fun i=>(d.rows i).midpoint))) (List.ofFn d.double)

@[simp] theorem field_0 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 0=[true]:=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,Option.getD_some]

@[simp] theorem field_1 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 1=BinaryNatCode.encode d.offset.val:=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_3 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 3=BinaryNatCode.encode d.objective.val:=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_4 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 4=BinaryNatCode.encode d.coordinate.val:=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_6 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 6=WordList.encode (List.ofFn (fun i=>(d.rows i).base)):=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_12 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 12=List.ofFn d.double:=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_14 {n birth : ℕ} (d : Data n birth) :
    IntegralMixedUnitRecordCode.field d.code 14=WordList.encode (List.ofFn (fun i=>(d.rows i).midpoint)):=by
  simp only [Data.code,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem row_decode {n birth : ℕ} (d : Data n birth) (i : Fin (n+1)) :
    IntegralMixedCausalUnitRecordBits.row d.code true birth i.val=(d.rows i).value:=by
  simp only [IntegralMixedCausalUnitRecordBits.row,ite_true,field_6,field_14,WordList.get_encode,
    List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Row.decode]

theorem scale_decode {n birth : ℕ} (d : Data n birth) (i : Fin (n+1)) :
    IntegralMixedCausalUnitRecordBits.scale d.code true i.val=if d.double i then 2 else 1:=by
  simp only [IntegralMixedCausalUnitRecordBits.scale,IntegralMixedCausalUnitRecordBits.double,
    ite_true,field_12,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

theorem rule_decode {n birth : ℕ} (d : Data n birth) :
    IntegralMixedCausalUnitRecordBits.physical n birth d.code=d.rule:=by
  simp only [IntegralMixedCausalUnitRecordBits.physical,IntegralMixedCanonicalUnitRuleBits.physical,
    IntegralMixedUnitRecordCode.physicalOffset,field_1,field_3,field_4,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    Nat.mod_eq_of_lt d.offset.isLt,Nat.mod_eq_of_lt d.objective.isLt,Nat.mod_eq_of_lt d.coordinate.isLt,
    Data.rule,scale_decode,row_decode]

theorem command_decode {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n) (d : Data n birth)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth d.code hcap).template.command Q hQ=.critical d.rule:=by
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,field_0,
    List.getElem?_cons_zero,Option.getD_some,ite_true,IntegralMixedCausalRecordBits.Template.command,rule_decode]

end LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
