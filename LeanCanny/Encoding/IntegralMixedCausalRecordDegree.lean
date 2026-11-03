/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
/-! # Native selection of a specialized degree in an existing causal record

Only the stored degree changes. The source, affine rows, scale bits, selected
factor label, and current-denominator mode are preserved exactly. This does
not assert that arbitrary spatial rules are representable by unit records.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordDegree
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedUnitRecordCode (field)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def withDegree (code : List Bool) (d : ℕ) : List Bool:=
  WordList.encode [field code 0,
    field code 1,
    field code 2,
    field code 3,
    field code 4,
    field code 5,
    field code 6,
    field code 7,
    field code 8,
    BinaryNatCode.encode d,
    field code 10,
    field code 11,
    field code 12,
    field code 13,
    field code 14,
    field code 15]

theorem withDegree_FP {code : List Bool→List Bool} {d : List Bool→ℕ}
    (hc : code∈FP) (hd : BinaryFn d) : (fun q=>withDegree (code q) (d q))∈FP:=by
  have HF (i : ℕ) : (fun q=>field (code q) i)∈FP:=
    mem_FP_comp (f:=code) (g:=fun w=>field w i) hc (IntegralMixedCommandHeaderBits.get_FP i)
  have HE:=(mem_FP_pair (HF 0) (mem_FP_pair (HF 1) (mem_FP_pair (HF 2) (mem_FP_pair (HF 3) (mem_FP_pair (HF 4) (mem_FP_pair (HF 5) (mem_FP_pair (HF 6) (mem_FP_pair (HF 7) (mem_FP_pair (HF 8) (mem_FP_pair hd.bits_mem_FP (mem_FP_pair (HF 10) (mem_FP_pair (HF 11) (mem_FP_pair (HF 12) (mem_FP_pair (HF 13) (mem_FP_pair (HF 14) (mem_FP_pair (HF 15) (constFn_mem_FP ([] : List Bool))))))))))))))))))
  exact mem_FP_of_eq HE (fun q=>by simp only [withDegree,WordList.encode])

theorem field_withDegree (code : List Bool) (d i : ℕ) (hi : i<16) :
    field (withDegree code d) i=if i=9 then BinaryNatCode.encode d else field code i:=by
  interval_cases i <;> simp only [field,withDegree,WordList.get_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,ite_true,ite_false,
    Nat.reduceEqDiff]

@[simp] theorem field_0 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 0=field code 0:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 0 (by omega)

@[simp] theorem field_1 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 1=field code 1:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 1 (by omega)

@[simp] theorem field_2 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 2=field code 2:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 2 (by omega)

@[simp] theorem field_3 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 3=field code 3:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 3 (by omega)

@[simp] theorem field_4 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 4=field code 4:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 4 (by omega)

@[simp] theorem field_5 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 5=field code 5:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 5 (by omega)

@[simp] theorem field_6 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 6=field code 6:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 6 (by omega)

@[simp] theorem field_7 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 7=field code 7:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 7 (by omega)

@[simp] theorem field_8 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 8=field code 8:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 8 (by omega)

@[simp] theorem field_9 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 9=BinaryNatCode.encode d:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 9 (by omega)

@[simp] theorem field_10 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 10=field code 10:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 10 (by omega)

@[simp] theorem field_11 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 11=field code 11:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 11 (by omega)

@[simp] theorem field_12 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 12=field code 12:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 12 (by omega)

@[simp] theorem field_13 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 13=field code 13:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 13 (by omega)

@[simp] theorem field_14 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 14=field code 14:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 14 (by omega)

@[simp] theorem field_15 (code : List Bool) (d : ℕ) :
    field (withDegree code d) 15=field code 15:=by
  simpa only [ite_true,ite_false,Nat.reduceEqDiff] using field_withDegree code d 15 (by omega)

theorem writtenDegree {n : ℕ} (S : SpatialSource n) (code : List Bool) (d : ℕ)
    (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree) :
    IntegralMixedCanonicalUnitRuleBits.writtenDegree S (withDegree code d)=d:=by
  rw [IntegralMixedCanonicalUnitRuleBits.writtenDegree,field_9,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd)]

theorem physical (n birth : ℕ) (code : List Bool) (d : ℕ) :
    IntegralMixedCausalUnitRecordBits.physical n birth (withDegree code d)=
      IntegralMixedCausalUnitRecordBits.physical n birth code:=by
  simp only [IntegralMixedCausalUnitRecordBits.physical,IntegralMixedCanonicalUnitRuleBits.physical,
    IntegralMixedUnitRecordCode.physicalOffset,IntegralMixedCausalUnitRecordBits.scale,
    IntegralMixedCausalUnitRecordBits.double,IntegralMixedCausalUnitRecordBits.row,
    field_1,field_3,field_4,field_6,field_12,field_14,ite_true]

theorem virtual (n : ℕ) (hn : 0<n) (birth : ℕ) (code : List Bool) (d : ℕ) :
    IntegralMixedCausalUnitRecordBits.virtual n hn birth (withDegree code d)=
      IntegralMixedCausalUnitRecordBits.virtual n hn birth code:=by
  simp only [IntegralMixedCausalUnitRecordBits.virtual,IntegralMixedCanonicalUnitRuleBits.virtual,
    IntegralMixedUnitRecordCode.virtualOffset,IntegralMixedUnitRecordCode.height,
    IntegralMixedCausalUnitRecordBits.scale,IntegralMixedCausalUnitRecordBits.double,
    IntegralMixedCausalUnitRecordBits.row,field_2,field_3,field_4,field_5,field_7,
    field_13,field_15,Bool.false_eq_true,ite_false]

end LeanCanny.Encoding.IntegralMixedCausalRecordDegree
