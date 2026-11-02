/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalRecord
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Encoding.IntegralMixedCausalRowCode
/-! # Original unit-selector records for causal critical and cut commands

The first ten fields retain the canonical record layout. Field10 is the
current-denominator mode bit and field11 selects one of the four cut kinds.
Neither the source descriptor nor any interpreted denominator is serialized.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalUnitRecordBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRecordBits
open IntegralMixedUnitRecordCode (field)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def current (code : List Bool) : Bool := (field code 10)[0]?.getD false

def tag (code : List Bool) : Tag :=
  match Nat.fromBitsLE (field code 11) % 4 with
  | 0 => .coordinate
  | 1 => .squarefree
  | 2 => .value
  | _ => .limitCoordinate

/-- Separate literal scale bits preserve the old ten-field record layout. -/
def double (code : List Bool) (physical : Bool) (i : ℕ) : Bool :=
  (field code (if physical then 12 else 13))[i]?.getD false

def scale (code : List Bool) (physical : Bool) (i : ℕ) : ℤ :=
  if double code physical i then 2 else 1

noncomputable def row (code : List Bool) (physical : Bool) (birth i : ℕ) : AffineExpr :=
  IntegralMixedCausalRowCode.expression
    (WordList.get (field code (if physical then 6 else 7)) i)
    (WordList.get (field code (if physical then 14 else 15)) i) birth

noncomputable def physical (n birth : ℕ) (code : List Bool) : CriticalRule n :=
  { IntegralMixedCanonicalUnitRuleBits.physical n birth code with
    scales i := scale code true i.val
    scales_ne_zero i := by unfold scale; split_ifs <;> norm_num
    heights i := row code true birth i.val }

noncomputable def virtual (n : ℕ) (hn : 0<n) (birth : ℕ) (code : List Bool) : IntegralMixedCriticalSweep.Rule n :=
  { IntegralMixedCanonicalUnitRuleBits.virtual n hn birth code with
    critical := { (IntegralMixedCanonicalUnitRuleBits.virtual n hn birth code).critical with
      scales i := scale code false i.val
      scales_ne_zero i := by unfold scale; split_ifs <;> norm_num
      heights i := row code false birth i.val } }

noncomputable def cut {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) : Cut S B where
  critical := (virtual n hn birth code).critical
  height := (virtual n hn birth code).height
  frozen := (virtual n hn birth code).height_frozen
  tag := tag code
  coordinate := Nat.fromBitsLE (field code 4)
  choice := Nat.fromBitsLE (field code 8)
  degree := IntegralMixedCanonicalUnitRuleBits.writtenDegree S code
  source_cap := IntegralMixedCanonicalUnitRuleBits.writtenDegree_bound S code
  degree_cap := (IntegralMixedCanonicalUnitRuleBits.writtenDegree_bound S code).trans hcap
  current := current code

noncomputable def record {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) : Record n B where
  source := S
  source_cap := (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (n+1) S.degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree).trans hcap
  template := if IntegralMixedUnitRecordCode.critical code then
    .critical (physical n birth code)
    else .cut (cut S hn birth code hcap)

theorem record_source {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    (record S hn birth code hcap).source=S := rfl

theorem cut_slope {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) : ((cut S hn birth code hcap).rule Q hQ).slope = if current code then Q else 1 := rfl

theorem cut_rows {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (i : Fin (n+1)) : (cut S hn birth code hcap).critical.heights i = row code false birth i.val := rfl

end LeanCanny.Algebra.IntegralMixedCausalUnitRecordBits
