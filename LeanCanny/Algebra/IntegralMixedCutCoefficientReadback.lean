/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutCoefficientQuery
public import LeanCanny.Algebra.IntegralMixedFramedFullCutProbe
/-! # Finite coefficient probes retain the exact active parent

The original scalar radix fits the task cap. Thus every coefficient in
the finite guards and every valid lower choice is read without clipping.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask

theorem query_active (P : Parameters) (z : List Bool) :
    IntegralMixedFramedFullCutProbeBits.Active P (query P z) ↔
      IntegralMixedFramedFullCutProbeBits.Active P (pairFst z) := by
  unfold IntegralMixedFramedFullCutProbeBits.Active IntegralMixedVirtualCaps.valid IntegralMixedVirtualContextBits.context
  rw [query_birth,query_root,query_get]
  simp only [reduceCtorEq,ite_false]

theorem scalar_cap (P : Parameters) (c : List Bool) :
    2^P.width (RankedHistoryTask.root c)≤numericCap P (RankedHistoryTask.root c) :=
  (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem coefficient_packet (P : Parameters) (c : List Bool) (e k : ℕ)
    (he : e≤2^P.width (RankedHistoryTask.root c)) :
    get P .coefficient (query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))))=e := by
  rw [query_get]
  simp only [reduceCtorEq,ite_false,ite_true,coefficient,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (he.trans (scalar_cap P c))

theorem choice_packet (P : Parameters) (c : List Bool) (e k : ℕ)
    (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    get P .slot8 (query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))))=k := by
  rw [query_get]
  simp only [reduceCtorEq,ite_false,ite_true,choice,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (hk.trans (scalar_cap P c))

end LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits
