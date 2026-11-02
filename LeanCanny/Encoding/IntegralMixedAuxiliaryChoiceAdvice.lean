/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecords
public import LeanCanny.Encoding.FixedWidthNatVector
/-! # Fixed-width original advice for bounded auxiliary cut choices -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def extended {N : ℕ} (labels : Fin N → ℕ × ℕ) (i : ℕ) :=
  if h : i<N then labels ⟨i,h⟩ else (0,0)

def values {N : ℕ} (labels : Fin N → ℕ × ℕ) (i : ℕ) :=
  if i<N then (extended labels i).1 else (extended labels (i-N)).2

def encode {N : ℕ} (B : ℕ) (labels : Fin N → ℕ × ℕ) :=
  FixedWidthNatVector.encode (2*N) B (values labels)

theorem encode_length {N : ℕ} (B : ℕ) (labels : Fin N → ℕ × ℕ) :
    (encode B labels).length=2*N*B := FixedWidthNatVector.length_encode _ _ _

def block (W : List Bool → ℕ) (shift : List Bool → ℕ) (p : List Bool) :=
  Nat.fromBitsLE (((pairSnd (pairFst p)).drop
    ((shift (pairFst p)+(pairSnd p).length)*W (pairFst (pairFst p)))).take (W (pairFst (pairFst p))))

theorem block_binary {W shift : List Bool → ℕ} (hW : UnaryFn W) (hs : UnaryFn shift) : BinaryFn (block W shift) :=
  BinaryFn.fromBits (take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    (((hs.comp pairFst_mem_FP).add UnaryFn.index).mul
      (hW.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))))
    (hW.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)))

def choice (W : List Bool → ℕ) := block W (fun _ => 0)
def degree (n W : List Bool → ℕ) := block W (fun q => n (pairFst q))

theorem choice_binary {W : List Bool → ℕ} (hW : UnaryFn W) : BinaryFn (choice W) :=
  block_binary hW (UnaryFn.const 0)
theorem degree_binary {n W : List Bool → ℕ} (hn : UnaryFn n) (hW : UnaryFn W) : BinaryFn (degree n W) :=
  block_binary hW (hn.comp pairFst_mem_FP)

theorem choice_encode (n W : List Bool → ℕ) (original : List Bool) (labels : Fin (n original) → ℕ × ℕ)
    (i : Fin (n original)) (hc : (labels i).1<2^W original) :
    choice W (pair (pair original (encode (W original) labels)) (List.replicate i.val true))=(labels i).1 := by
  simp only [choice,block,pairFst_pair,pairSnd_pair,List.length_replicate,Nat.zero_add]
  have H := FixedWidthNatVector.decode_block (2*n original) (W original) (values labels) i.val
    (by have HI:=i.isLt; omega) (by simpa only [values,ite_eq_left i.isLt,extended,dite_eq_left i.isLt] using hc)
  simpa only [encode,values,ite_eq_left i.isLt,extended,dite_eq_left i.isLt] using H

theorem degree_encode (n W : List Bool → ℕ) (original : List Bool) (labels : Fin (n original) → ℕ × ℕ)
    (i : Fin (n original)) (hd : (labels i).2<2^W original) :
    degree n W (pair (pair original (encode (W original) labels)) (List.replicate i.val true))=(labels i).2 := by
  simp only [degree,block,pairFst_pair,pairSnd_pair,List.length_replicate]
  have HI : ¬n original+i.val<n original := by omega
  have H := FixedWidthNatVector.decode_block (2*n original) (W original) (values labels) (n original+i.val)
    (by have HI':=i.isLt; omega) (by
      simpa only [values,ite_eq_right HI,Nat.add_sub_cancel_left,extended,dite_eq_left i.isLt] using hd)
  simpa only [encode,values,ite_eq_right HI,Nat.add_sub_cancel_left,extended,dite_eq_left i.isLt] using H

noncomputable def prepare (n : List Bool → ℕ) (t : List Bool → Term) :=
  IntegralMixedAuxiliaryLimitRecords.prepare (fun q => n (pairFst q)) (fun _ => 0)
    (choice (scalarWidth n t)) (degree n (scalarWidth n t))

theorem prepare_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : prepare n t∈FP :=
  IntegralMixedAuxiliaryLimitRecords.prepare_FP (hn.comp pairFst_mem_FP) (BinaryFn.const 0)
    (choice_binary (scalarWidth_unary hn ht)) (degree_binary hn (scalarWidth_unary hn ht))

end LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
