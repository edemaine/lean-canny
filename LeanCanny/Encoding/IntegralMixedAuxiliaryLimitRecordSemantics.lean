/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
public import LeanCanny.Geometry.CanonicalAuxiliaryTerminal
public import LeanCanny.Algebra.IntegralMixedCanonicalDilationRoot
/-! # The auxiliary limit record is the literal canonical dilation rule -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem critical_record (n k m0 c d : ℕ) : IntegralMixedUnitRecordCode.critical (record n k m0 c d)=false := by
  unfold IntegralMixedUnitRecordCode.critical
  rw [record_field]
  rfl

theorem virtual_offset (n k m0 c d : ℕ) (hk : k≤n) :
    IntegralMixedUnitRecordCode.virtualOffset (n+2) (record n k m0 c d)=k+1 := by
  unfold IntegralMixedUnitRecordCode.virtualOffset
  rw [record_field]
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem height_zero (n k m0 c d : ℕ) :
    IntegralMixedUnitRecordCode.height (n+2) (record n k m0 c d)=0 := by
  unfold IntegralMixedUnitRecordCode.height
  rw [record_field]
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact Nat.zero_mod _

theorem row_expression (n k m0 i : ℕ) (hi : i<n+3) :
    IntegralMixedUnitRowCode.expression (rows n k m0) (m0+k) i =
      if 0 < i ∧ i<k+1 then .reference (k-i) else .constant 0 := by
  unfold IntegralMixedUnitRowCode.expression IntegralMixedUnitRowCode.active
    IntegralMixedUnitRowCode.reference IntegralMixedUnitRowCode.producer
  rw [rows_get _ _ _ _ hi]
  simp only [row,pairFst_pair,pairSnd_pair,List.getElem?_cons_zero,Option.getD_some,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,decide_eq_true_eq]
  by_cases ha : 0 < i ∧ i<k+1
  · have hb : m0+i-1<m0+k := by omega
    simp only [ha,hb,and_self,ite_true]
    congr 1
    omega
  · simp only [ha,false_and,ite_false]

theorem row_heightExpr (n k m0 c d : ℕ) (_hk : k≤n) (i : Fin (n+3)) :
    IntegralMixedUnitRowCode.expression (IntegralMixedUnitRecordCode.field (record n k m0 c d) 7) (m0+k) i.val =
      IntegralMixedCanonicalDilation.heightExpr (n:=n+1) (frontSelector k m0) i := by
  rw [record_field]
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  rw [row_expression _ _ _ _ i.isLt]
  unfold IntegralMixedCanonicalDilation.heightExpr
  by_cases h0 : i.val=0
  · rw [dite_eq_left h0]
    simp only [h0,Nat.lt_irrefl,false_and,ite_false]
  · rw [dite_eq_right h0]
    by_cases hi : i.val < k+1
    · rw [dite_eq_left hi,ite_eq_left (by omega : 0 < i.val ∧ i.val < k+1)]
      change AffineExpr.reference (k-i.val)=.reference (k-1-(i.val-1))
      congr 1
      omega
    · rw [dite_eq_right hi,ite_eq_right (by omega : ¬(0 < i.val ∧ i.val < k+1))]

private theorem critical_ext {n : ℕ} (r s : CriticalRule n)
    (ho : r.offset=s.offset) (hj : r.objective=s.objective) (hc : r.coordinate=s.coordinate)
    (hs : r.scales=s.scales) (hh : r.heights=s.heights) : r=s := by
  cases r
  cases s
  cases ho
  cases hj
  cases hc
  cases hs
  cases hh
  rfl

private theorem sweep_ext {n : ℕ} (r s : IntegralMixedCriticalSweep.Rule n)
    (hr : r.critical=s.critical) (hh : r.height=s.height) (hs : r.slope=s.slope) : r=s := by
  cases r
  cases s
  cases hr
  cases hh
  cases hs
  rfl

theorem virtual_rule (n k m0 c d : ℕ) (hk : k≤n) :
    IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d) =
      IntegralMixedCanonicalDilation.rule (n:=n+1) (by omega : k≤n+1) (frontSelector k m0) := by
  apply sweep_ext
  · apply critical_ext
    · apply Fin.ext
      exact virtual_offset _ _ _ _ _ hk
    · change Nat.fromBitsLE (IntegralMixedUnitRecordCode.field (record n k m0 c d) 3) %
        ((n+2)-IntegralMixedUnitRecordCode.virtualOffset (n+2) (record n k m0 c d)+1) = (n+1)-k
      rw [record_field,virtual_offset _ _ _ _ _ hk]
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
      rw [Nat.mod_eq_of_lt (by omega)]
    · change Nat.fromBitsLE (IntegralMixedUnitRecordCode.field (record n k m0 c d) 4) % _ = 0
      rw [record_field]
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
      exact Nat.zero_mod _
    · rfl
    · funext i
      exact row_heightExpr _ _ _ _ _ hk i
  · apply Fin.ext
    exact height_zero _ _ _ _ _
  · rfl

theorem coordinate_self (n k m0 : ℕ) (hk : k≤n) :
    IntegralMixedCanonicalDilation.coordinateIndex (n:=n+1) (by omega : k≤n+1)
      (frontSelector k m0) (⟨k,by omega⟩ : Fin (n+1)) (Nat.le_refl k) = 0 := by
  apply Fin.ext
  change k-k=0
  omega
end LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
