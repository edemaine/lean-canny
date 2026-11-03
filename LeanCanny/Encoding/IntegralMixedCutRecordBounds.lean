/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordKind
public import LeanCanny.Encoding.IntegralMixedCriticalRecordBounds
/-! # Chosen virtual cut code size uses the original scalar width

The semantic selected degree need not be FP. Its binary record occupies at
most B+1 bits, as does every selected factor choice. Original affine row
words and bounded spatial indices supply the remaining fixed sixteen fields.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCausalRecordBits
open IntegralMixedCriticalRecordConstructor (tableBudget)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def fieldBudget (n birth B : ℕ) : ℕ:=tableBudget n birth+(n+1).size+B+5
def codeBudget (n birth B : ℕ) : ℕ:=(2*fieldBudget n birth B+2)*16

theorem Data.code_word {n birth : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ) :
    d.code t choice degree=WordList.encode [[],[],BinaryNatCode.encode (d.critical.offset.val-1),
      BinaryNatCode.encode d.critical.objective.val,BinaryNatCode.encode d.critical.coordinate.val,
      BinaryNatCode.encode d.height.val,[],WordList.encode (List.ofFn (fun i=>(d.critical.rows i).base)),
      BinaryNatCode.encode choice,BinaryNatCode.encode degree,[d.current],BinaryNatCode.encode (tagIndex t),[],
      List.ofFn d.critical.double,[],WordList.encode (List.ofFn (fun i=>(d.critical.rows i).midpoint))] :=by
  simp only [Data.code,IntegralMixedCausalRecordDegree.withDegree,Data.baseCode,word,
    IntegralMixedUnitRecordCode.field,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]

theorem Data.code_length {n birth B : ℕ} (d : Data n birth) (t : Tag) (choice degree : ℕ)
    (hc : choice≤2^B) (hd : degree≤2^B) : (d.code t choice degree).length≤codeBudget n birth B :=by
  have HB:=d.critical.base_length
  have HM:=d.critical.midpoint_length
  have HO:=Nat.size_le_size (show d.critical.offset.val-1≤n+1 by have H:=d.critical.offset.isLt; omega)
  have HJ:=Nat.size_le_size (d.critical.objective.isLt.le.trans (Nat.add_le_add_right (Nat.sub_le n d.critical.offset.val) 1))
  have HK:=Nat.size_le_size (d.critical.coordinate.isLt.le.trans (Nat.add_le_add_right (Nat.sub_le n d.critical.offset.val) 1))
  have HH:=Nat.size_le_size (d.height.isLt.le.trans d.critical.offset.isLt.le)
  have HC : choice.size≤B+1:=by simpa only [Nat.size_pow] using Nat.size_le_size hc
  have HD : degree.size≤B+1:=by simpa only [Nat.size_pow] using Nat.size_le_size hd
  have HT : (tagIndex t).size≤2:=by cases t <;> decide
  have HN : n+1≤tableBudget n birth:=by
    unfold tableBudget
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n+1)
      (show 1≤2*IntegralMixedCriticalRecordConstructor.rowBudget birth+2 by omega)
  rw [d.code_word]
  have HF : ∀ w∈[([] : List Bool),[],BinaryNatCode.encode (d.critical.offset.val-1),
      BinaryNatCode.encode d.critical.objective.val,BinaryNatCode.encode d.critical.coordinate.val,
      BinaryNatCode.encode d.height.val,[],WordList.encode (List.ofFn (fun i=>(d.critical.rows i).base)),
      BinaryNatCode.encode choice,BinaryNatCode.encode degree,[d.current],BinaryNatCode.encode (tagIndex t),[],
      List.ofFn d.critical.double,[],WordList.encode (List.ofFn (fun i=>(d.critical.rows i).midpoint))],
      w.length≤fieldBudget n birth B:=by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try simp only [List.length_cons,List.length_nil,List.length_ofFn,
      BinaryNatCode.encode,Nat.size_eq_bits_len]
    all_goals unfold fieldBudget; omega
  have H:=WordList.length_le _ (fieldBudget n birth B) HF
  simpa only [codeBudget,List.length_cons,List.length_nil] using H

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor
