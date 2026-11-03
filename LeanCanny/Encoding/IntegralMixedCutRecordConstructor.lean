/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
public import LeanCanny.Encoding.IntegralMixedCausalCutDegree
/-! # Native virtual cut words for the existing causal decoder

Positive frozen offsets encode offset-1 in field2. Virtual rows/scales use
fields7/15/13, while current Q remains the literal bit10. The chosen degree
uses the existing field9 writer; no polynomial or integer denominator is
serialized here.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRowConstructor IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def tagIndex : Tag→ℕ
  | .coordinate=>0
  | .squarefree=>1
  | .value=>2
  | .limitCoordinate=>3

def word (offset objective coordinate height tag choice : ℕ) (base mid doubles : List Bool) (current : Bool):=
  WordList.encode [[],
    [],
    BinaryNatCode.encode (offset-1),
    BinaryNatCode.encode objective,
    BinaryNatCode.encode coordinate,
    BinaryNatCode.encode height,
    [],
    base,
    BinaryNatCode.encode choice,
    [],
    [current],
    BinaryNatCode.encode tag,
    [],
    doubles,
    [],
    mid]

theorem word_FP {offset objective coordinate height tag choice : List Bool→ℕ}
    {base mid doubles : List Bool→List Bool} {current : List Bool→Bool}
    (ho : BinaryFn offset) (hj : BinaryFn objective) (hk : BinaryFn coordinate) (hh : BinaryFn height)
    (ht : BinaryFn tag) (hc : BinaryFn choice) (hb : base∈FP) (hm : mid∈FP) (hd : doubles∈FP)
    (hcur : (fun q=>[current q])∈FP) :
    (fun q=>word (offset q) (objective q) (coordinate q) (height q) (tag q) (choice q)
      (base q) (mid q) (doubles q) (current q))∈FP:=by
  have H0:=constFn_mem_FP ([] : List Bool)
  have HE:=(mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair (ho.sub (BinaryFn.const 1)).bits_mem_FP (mem_FP_pair hj.bits_mem_FP (mem_FP_pair hk.bits_mem_FP (mem_FP_pair hh.bits_mem_FP (mem_FP_pair H0 (mem_FP_pair hb (mem_FP_pair hc.bits_mem_FP (mem_FP_pair H0 (mem_FP_pair hcur (mem_FP_pair ht.bits_mem_FP (mem_FP_pair H0 (mem_FP_pair hd (mem_FP_pair H0 (mem_FP_pair hm H0))))))))))))))))
  exact mem_FP_of_eq HE (fun q=>by simp only [word,WordList.encode])

structure Data (n birth : ℕ) where
  critical : IntegralMixedCriticalRecordConstructor.Data n birth
  positive : 0<critical.offset.val
  height : Fin critical.offset.val
  current : Bool

theorem Data.ambient_positive {n birth : ℕ} (d : Data n birth) : 0<n:=by
  have H:=d.critical.offset.isLt
  have HP:=d.positive
  omega

def Data.baseCode {n birth : ℕ} (d : Data n birth) (t : Tag) (choice : ℕ) : List Bool:=
  word d.critical.offset.val d.critical.objective.val d.critical.coordinate.val d.height.val (tagIndex t) choice
    (WordList.encode (List.ofFn (fun i=>(d.critical.rows i).base)))
    (WordList.encode (List.ofFn (fun i=>(d.critical.rows i).midpoint))) (List.ofFn d.critical.double) d.current

def Data.code {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) : List Bool:=
  IntegralMixedCausalRecordDegree.withDegree (d.baseCode t choice) degree

noncomputable def Data.rule {n birth : ℕ} (d : Data n birth) (Q : ℤ) (hQ : Q≠0) : IntegralMixedCriticalSweep.Rule n where
  critical:=d.critical.rule
  height:=⟨d.height.val,d.height.isLt.trans d.critical.offset.isLt⟩
  height_frozen:=d.height.isLt
  slope:=if d.current then Q else 1
  slope_ne_zero:=by split_ifs; exact hQ; exact one_ne_zero

noncomputable def Data.cut {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (t : Tag) (choice degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) : Cut P B where
  critical:=d.critical.rule
  height:=⟨d.height.val,d.height.isLt.trans d.critical.offset.isLt⟩
  frozen:=d.height.isLt
  tag:=t
  coordinate:=d.critical.coordinate.val
  choice:=choice
  degree:=degree
  source_cap:=hd
  degree_cap:=hd.trans hcap
  current:=d.current

@[simp] theorem field_0 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 0=[]:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_0]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,Option.getD_some]

@[simp] theorem field_2 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 2=BinaryNatCode.encode (d.critical.offset.val-1):=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_2]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_3 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 3=BinaryNatCode.encode d.critical.objective.val:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_3]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_4 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 4=BinaryNatCode.encode d.critical.coordinate.val:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_4]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_5 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 5=BinaryNatCode.encode d.height.val:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_5]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_7 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 7=WordList.encode (List.ofFn (fun i=>(d.critical.rows i).base)):=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_7]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_8 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 8=BinaryNatCode.encode choice:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_8]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_10 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 10=[d.current]:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_10]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_11 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 11=BinaryNatCode.encode (tagIndex t):=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_11]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_13 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 13=List.ofFn d.critical.double:=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_13]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

@[simp] theorem field_15 {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.field (d.code t choice degree) 15=WordList.encode (List.ofFn (fun i=>(d.critical.rows i).midpoint)):=by
  rw [Data.code,IntegralMixedCausalRecordDegree.field_15]
  simp only [Data.baseCode,word,IntegralMixedUnitRecordCode.field,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem offset_decode {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    IntegralMixedUnitRecordCode.virtualOffset n (d.code t choice degree)=d.critical.offset.val:=by
  simp only [IntegralMixedUnitRecordCode.virtualOffset,field_2,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HP:=d.positive
  have HB:=d.critical.offset.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem row_decode {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) (i : Fin (n+1)) :
    IntegralMixedCausalUnitRecordBits.row (d.code t choice degree) false birth i.val=(d.critical.rows i).value:=by
  simp only [IntegralMixedCausalUnitRecordBits.row,Bool.false_eq_true,ite_false,field_7,field_15,WordList.get_encode,
    List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Row.decode]

theorem scale_decode {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) (i : Fin (n+1)) :
    IntegralMixedCausalUnitRecordBits.scale (d.code t choice degree) false i.val=if d.critical.double i then 2 else 1:=by
  simp only [IntegralMixedCausalUnitRecordBits.scale,IntegralMixedCausalUnitRecordBits.double,
    Bool.false_eq_true,ite_false,field_13,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

theorem virtual_critical {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    (IntegralMixedCausalUnitRecordBits.virtual n d.ambient_positive birth (d.code t choice degree)).critical=d.critical.rule:=by
  simp only [IntegralMixedCausalUnitRecordBits.virtual,IntegralMixedCanonicalUnitRuleBits.virtual,
    offset_decode,field_3,field_4,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    Nat.mod_eq_of_lt d.critical.objective.isLt,Nat.mod_eq_of_lt d.critical.coordinate.isLt,
    IntegralMixedCriticalRecordConstructor.Data.rule,scale_decode,row_decode]

theorem virtual_height {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    (IntegralMixedCausalUnitRecordBits.virtual n d.ambient_positive birth (d.code t choice degree)).height=
      ⟨d.height.val,d.height.isLt.trans d.critical.offset.isLt⟩:=by
  apply Fin.ext
  change IntegralMixedUnitRecordCode.height n (d.code t choice degree)=d.height.val
  simp only [IntegralMixedUnitRecordCode.height,field_5,BinaryNatCode.encode,Nat.fromBitsLE_bits,offset_decode,
    Nat.mod_eq_of_lt d.height.isLt]

theorem cut_decode {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (t : Tag) (choice degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    IntegralMixedCausalUnitRecordBits.cut P d.ambient_positive birth (d.code t choice degree) hcap=
      d.cut P t choice degree hd hcap:=by
  have Htag : IntegralMixedCausalUnitRecordBits.tag (d.code t choice degree)=t:=by
    simp only [IntegralMixedCausalUnitRecordBits.tag,field_11,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    cases t <;> rfl
  have HD : IntegralMixedCanonicalUnitRuleBits.writtenDegree P (d.code t choice degree)=degree:=
    IntegralMixedCausalRecordDegree.writtenDegree P (d.baseCode t choice) degree hd
  simp only [IntegralMixedCausalUnitRecordBits.cut,virtual_critical,virtual_height,Htag,
    IntegralMixedCausalUnitRecordBits.current,field_10,List.getElem?_cons_zero,Option.getD_some,
    field_4,field_8,BinaryNatCode.encode,Nat.fromBitsLE_bits,HD,Data.cut]

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor
