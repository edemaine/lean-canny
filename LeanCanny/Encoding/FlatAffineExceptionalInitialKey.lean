/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalInitialRealBounds
/-! # Native saved keys for the correlated initial bank

The writer preserves the original root word and selects exactly the original
integer-bank prefix. Its length depends on the birth count, not on any real root.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineExceptionalBankSource (births)

def key (F : Inputs) (input : List Bool → List Bool) (root : List Bool) : List Bool :=
  pair root (pair (BinaryNatCode.encode (births F (input root))) [])

theorem key_FP {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP) :
    key F input ∈ FP := by
  have H : BinaryFn (fun root => births F (input root)) :=
    (BinaryFn.ofUnary (FlatAffineExceptionalBankSource.births_unary hF)).comp hi
  exact mem_FP_pair id_mem_FP (mem_FP_pair H.bits_mem_FP (constFn_mem_FP []))

theorem key_root (F : Inputs) (input : List Bool → List Bool) (root : List Bool) :
    pairFst (key F input root)=root := pairFst_pair _ _

theorem key_prefix (P : IntegralCriticalHistoryTask.Parameters) (F : Inputs)
    (input : List Bool → List Bool) (root : List Bool)
    (hm : births F (input root) ≤ P.cap root+1) :
    IntegralMixedFullHistoryFamilyBits.prefixLength P (key F input root)=births F (input root) := by
  simp only [IntegralMixedFullHistoryFamilyBits.prefixLength,key,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left hm

end LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
