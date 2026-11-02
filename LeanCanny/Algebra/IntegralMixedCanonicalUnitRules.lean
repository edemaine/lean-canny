/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedUnitRecordCode
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
/-! # Literal critical and limit-cut rules from canonical original records

Unit row selectors name actual retained producers. The formal nilpotent
coordinate is introduced by the existing sweep semantics, outside these rows.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalUnitRuleBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedUnitRecordCode (field physicalOffset virtualOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def physical (n birth : ℕ) (code : List Bool) : CriticalRule n where
  offset := ⟨physicalOffset n code, Nat.mod_lt _ (Nat.succ_pos _)⟩
  objective := Nat.fromBitsLE (field code 3) % (n-physicalOffset n code+1)
  coordinate := Nat.fromBitsLE (field code 4) % (n-physicalOffset n code+1)
  scales _ := 1
  scales_ne_zero _ := one_ne_zero
  heights i := IntegralMixedUnitRowCode.expression (field code 6) birth i.val

noncomputable def virtual (n : ℕ) (hn : 0<n) (birth : ℕ) (code : List Bool) : IntegralMixedCriticalSweep.Rule n where
  critical := {
    offset := ⟨virtualOffset n code, Nat.lt_succ_of_le (IntegralMixedUnitRecordCode.virtualOffset_le n hn code)⟩
    objective := Nat.fromBitsLE (field code 3) % (n-virtualOffset n code+1)
    coordinate := Nat.fromBitsLE (field code 4) % (n-virtualOffset n code+1)
    scales _ := 1
    scales_ne_zero _ := one_ne_zero
    heights i := IntegralMixedUnitRowCode.expression (field code 7) birth i.val }
  height := ⟨IntegralMixedUnitRecordCode.height n code, IntegralMixedUnitRecordCode.height_lt_arity n hn code⟩
  height_frozen := IntegralMixedUnitRecordCode.height_lt_offset n code
  slope := 1
  slope_ne_zero := one_ne_zero

noncomputable def kind {n : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool) :
    IntegralMixedRelativeCuts.Kind S (virtual n hn birth code) :=
  .limitCoordinate ⟨Nat.fromBitsLE (field code 4) % (n-virtualOffset n code+1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨Nat.fromBitsLE (field code 8) % IntegralMixedLimitCoordinate.ChoiceBound S (virtual n hn birth code), Nat.mod_lt _ (Nat.succ_pos _)⟩

def writtenDegree {n : ℕ} (S : SpatialSource n) (code : List Bool) :=
  Nat.fromBitsLE (field code 9) % (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree+1)

theorem writtenDegree_bound {n : ℕ} (S : SpatialSource n) (code : List Bool) :
    writtenDegree S code ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

noncomputable def selection {n : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool) :
    IntegralMixedFullHistoryFamilyBits.Selection S :=
  ⟨virtual n hn birth code, kind S hn birth code, writtenDegree S code, writtenDegree_bound S code⟩

noncomputable def command {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree ≤ 2^B) : IntegralMixedFullHistoryScript.Command S B :=
  if IntegralMixedUnitRecordCode.critical code then .critical (physical n birth code)
  else .cut (virtual n hn birth code) (kind S hn birth code) (writtenDegree S code)
    (writtenDegree_bound S code) ((writtenDegree_bound S code).trans hcap)

theorem command_noninteger {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree ≤ 2^B)
    (p : Polynomial ℤ) (hp : p≠0) (hd : p.natDegree≤2^B) : command S hn birth code hcap ≠ .integer p hp hd := by
  unfold command
  split_ifs <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem physical_causal (n birth : ℕ) (code : List Bool) (i : Fin (n+1)) (j : ℕ)
    (he : (physical n birth code).heights i = .reference j) : j < birth := by
  change IntegralMixedUnitRowCode.expression (field code 6) birth i.val = .reference j at he
  unfold IntegralMixedUnitRowCode.expression at he
  split_ifs at he with ha
  · cases he
    exact IntegralMixedUnitRowCode.active_bound _ _ _ ha

theorem virtual_causal (n : ℕ) (hn : 0<n) (birth : ℕ) (code : List Bool) (i : Fin (n+1)) (j : ℕ)
    (he : ((virtual n hn birth code).critical).heights i = .reference j) : j < birth := by
  change IntegralMixedUnitRowCode.expression (field code 7) birth i.val = .reference j at he
  unfold IntegralMixedUnitRowCode.expression at he
  split_ifs at he with ha
  · cases he
    exact IntegralMixedUnitRowCode.active_bound _ _ _ ha
end LeanCanny.Algebra.IntegralMixedCanonicalUnitRuleBits
