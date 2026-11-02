/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankOrderTerm
/-! # Native positive saved-prefix writers for retained-coordinate order

The original root and context are retained exactly. An arbitrary binary
requested birth is incremented; the existing family clamps to its horizon.
Thus sampling is positive even for malformed or overlarge birth requests.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankOrderKey
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)

def key (birth : List Bool→ℕ) (context : List Bool→List Bool) (c : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt c (birth c+1) (context c)
theorem key_FP (birth : List Bool→ℕ) (hb : BinaryFn birth) (context : List Bool→List Bool) (hc : context∈FP) :
    key birth context∈FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (hb.add (BinaryFn.const 1)).bits_mem_FP hc)
theorem root (birth : List Bool→ℕ) (context : List Bool→List Bool) (c : List Bool) :
    pairFst (key birth context c)=c := pairFst_pair _ _
theorem context (birth : List Bool→ℕ) (payload : List Bool→List Bool) (c : List Bool) :
    pairSnd (pairSnd (key birth payload c))=payload c := by simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairSnd_pair]
theorem prefix_length (P : Parameters) (birth : List Bool→ℕ) (context : List Bool→List Bool) (c : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P (key birth context c)=min (birth c+1) (P.cap c+1) := by
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
    key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem positive_prefix (P : Parameters) (birth : List Bool→ℕ) (context : List Bool→List Bool) (c : List Bool) :
    0<IntegralMixedFramedHistoryFamilyBits.prefixLength P (key birth context c) := by
  rw [prefix_length]
  exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
theorem positive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (birth : List Bool→ℕ) (context : List Bool→List Bool) (c : List Bool) :
    0<(atKey P D H (key birth context c)).count :=
  (positive_prefix P birth context c).trans_eq
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H (key birth context c)).symm

end LeanCanny.Encoding.IntegralFramedBankOrderKey
