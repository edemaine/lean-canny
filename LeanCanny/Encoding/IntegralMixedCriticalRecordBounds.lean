/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
/-! # Original bit bounds for a chosen critical-frame record

The payload consists only of bounded spatial indices, at most two retained
references per physical row, and scale bits. No real root or integer source
coefficient is serialized in this record.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
open LeanCanny.Algebra IntegralMixedCausalRowConstructor
open scoped Classical

def rowBudget (birth : ℕ):=3*birth.size+18
def tableBudget (n birth : ℕ):=(2*rowBudget birth+2)*(n+1)
def codeBudget (n birth : ℕ):=(2*(tableBudget n birth+(n+1).size+1)+2)*16

theorem atom_length {birth : ℕ} (a : Atom birth) : a.word.length≤birth.size+4:=by
  cases a with
  | none=>simp only [Atom.word,List.length_nil]; omega
  | some i=>
    have H:=Nat.size_le_size (show birth-1-i.val≤birth by omega)
    simp only [Atom.word,referenceWord,pair_length,List.length_cons,List.length_nil,
      BinaryNatCode.encode,Nat.size_eq_bits_len]
    omega

theorem row_base_length {birth : ℕ} (r : Row birth) : r.base.length≤rowBudget birth:=by
  cases r with
  | single a=>have H:=atom_length a; change a.word.length≤3*birth.size+18; omega
  | sum a b=>simp only [Row.base,List.length_nil]; exact Nat.zero_le _

theorem row_midpoint_length {birth : ℕ} (r : Row birth) : r.midpoint.length≤rowBudget birth:=by
  cases r with
  | single a=>simp only [Row.midpoint,List.length_nil]; exact Nat.zero_le _
  | sum a b=>
    have HA:=atom_length a
    have HB:=atom_length b
    simp only [Row.midpoint,sumWord,pair_length,List.length_cons,List.length_nil,rowBudget]
    omega

theorem Data.base_length {n birth : ℕ} (d : Data n birth) :
    (WordList.encode (List.ofFn (fun i=>(d.rows i).base))).length≤tableBudget n birth:=by
  have H:=WordList.length_le (List.ofFn (fun i=>(d.rows i).base)) (rowBudget birth) (by
    intro w hw
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hw
    exact row_base_length _)
  simpa only [List.length_ofFn,Fintype.card_fin,tableBudget] using H

theorem Data.midpoint_length {n birth : ℕ} (d : Data n birth) :
    (WordList.encode (List.ofFn (fun i=>(d.rows i).midpoint))).length≤tableBudget n birth:=by
  have H:=WordList.length_le (List.ofFn (fun i=>(d.rows i).midpoint)) (rowBudget birth) (by
    intro w hw
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hw
    exact row_midpoint_length _)
  simpa only [List.length_ofFn,Fintype.card_fin,tableBudget] using H

theorem Data.code_length {n birth : ℕ} (d : Data n birth) : d.code.length≤codeBudget n birth:=by
  have HB:=d.base_length
  have HM:=d.midpoint_length
  have HO:=Nat.size_le_size (Nat.le_of_lt d.offset.isLt)
  have HJ:=Nat.size_le_size (d.objective.isLt.le.trans (Nat.add_le_add_right (Nat.sub_le n d.offset.val) 1))
  have HK:=Nat.size_le_size (d.coordinate.isLt.le.trans (Nat.add_le_add_right (Nat.sub_le n d.offset.val) 1))
  have HT : n+1≤tableBudget n birth:=by
    change n+1≤(2*rowBudget birth+2)*(n+1)
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n+1) (show 1≤2*rowBudget birth+2 by omega)
  let V:=tableBudget n birth+(n+1).size+1
  have Hfields : ∀w∈[([true] : List Bool),BinaryNatCode.encode d.offset.val,[],BinaryNatCode.encode d.objective.val,
      BinaryNatCode.encode d.coordinate.val,[],WordList.encode (List.ofFn (fun i=>(d.rows i).base)),[],[],[],[],[],
      List.ofFn d.double,[],WordList.encode (List.ofFn (fun i=>(d.rows i).midpoint)),[]],w.length≤V:=by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try simp only [List.length_cons,List.length_nil,List.length_ofFn,
      BinaryNatCode.encode,Nat.size_eq_bits_len]
    all_goals dsimp only [V]; omega
  have H:=WordList.length_le _ V Hfields
  simpa only [Data.code,word,codeBudget,List.length_cons,List.length_nil] using H

end LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
