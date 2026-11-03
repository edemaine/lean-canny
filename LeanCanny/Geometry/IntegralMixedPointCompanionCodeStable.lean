/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionBounds
/-! # Retained frame shifts preserve chronological producer bytes

The newest-first reference index increases with the birth. Its original
producer label stays fixed. Thus the correctly shifted point rule, unlike
an arbitrary copied raw last record, has literally the same encoded word.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem laterAtom_word (a : Atom m) : (laterAtom a).word=a.word :=by
  cases a with
  | none=>rfl
  | some i=>
    have HE : (m+1)-1-(i.val+1)=m-1-i.val:=by have :=i.isLt;omega
    simp only [laterAtom,Option.map_some,Atom.word,referenceWord,Fin.val_succ,
      Nat.add_lt_add_iff_right,show i.val<m from i.isLt,decide_true,HE]

theorem laterRow_base (r : Row m) : (laterRow r).base=r.base :=by
  cases r <;> simp only [laterRow,Row.base,laterAtom_word]

theorem laterRow_midpoint (r : Row m) : (laterRow r).midpoint=r.midpoint :=by
  cases r <;> simp only [laterRow,Row.midpoint,laterAtom_word]

theorem shiftRows_base (rows : Fin (n+1)→Row m) (k : ℕ) (i : Fin (n+1)) :
    (shiftRows rows k i).base=(rows i).base :=by
  induction k with
  | zero=>rfl
  | succ k ih=>exact (laterRow_base _).trans ih

theorem shiftRows_midpoint (rows : Fin (n+1)→Row m) (k : ℕ) (i : Fin (n+1)) :
    (shiftRows rows k i).midpoint=(rows i).midpoint :=by
  induction k with
  | zero=>rfl
  | succ k ih=>exact (laterRow_midpoint _).trans ih

theorem pointData_code_stable (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g j : Free frozen) (k : ℕ) :
    (pointData frozen double rows g k j).code=(pointData frozen double rows g 0 j).code :=by
  simp only [pointData,originalPointData,IntegralMixedCriticalRecordConstructor.Data.code,
    shiftRows_base,shiftRows_midpoint]
  rfl

theorem codes_replicate (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (k : ℕ) :
    codes frozen double rows g (List.replicate k g)=
      List.replicate k (pointData frozen double rows g 0 g).code :=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    simp only [List.replicate_succ,codes,pointData_code_stable,ih]

end LeanCanny.Geometry.IntegralMixedPointCompanion
