/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
public import LeanCanny.Geometry.IntegralMixedFrozenFramePointScalar
public import LeanCanny.Geometry.IntegralMixedFrozenFrameLevel
/-! # The existing frozen-frame point rule has a literal original record

This constructs actual Frames in the existing zero/reference/two-atom grammar.
Frozen-first reordering preserves the grammar. Advancement is closed; a level
update is closed when the updated old row is a single atom. Repeated levels
of an already summed row require a separate alias or a larger grammar.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def originalFrame {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth) : Frame n where
  frozen:=frozen
  scales i:=if double i then 2 else 1
  scales_ne_zero i:=by split_ifs <;> norm_num
  heights i:=(rows i).value

noncomputable def originalPointData {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth)
    (g j : Fin (n+1)) (hg : g∉frozen) (hj : j∉frozen) : IntegralMixedCriticalRecordConstructor.Data n birth where
  offset:=⟨frozen.card,FrozenCoordinateOrdering.card_lt frozen g hg⟩
  objective:=freeCoordinate (originalFrame frozen double rows) g hg
  coordinate:=freeCoordinate (originalFrame frozen double rows) j hj
  double i:=double (FrozenCoordinateOrdering.permutation frozen i)
  rows i:=rows (FrozenCoordinateOrdering.permutation frozen i)

theorem originalPointData_rule {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth)
    (g j : Fin (n+1)) (hg : g∉frozen) (hj : j∉frozen) :
    (originalPointData frozen double rows g j hg hj).rule=
      pointRule (originalFrame frozen double rows) g hg j hj:=rfl

theorem originalPointData_decode {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth)
    (g j : Fin (n+1)) (hg : g∉frozen) (hj : j∉frozen) :
    IntegralMixedCausalUnitRecordBits.physical n birth (originalPointData frozen double rows g j hg hj).code=
      pointRule (originalFrame frozen double rows) g hg j hj:=
  (rule_decode _).trans (originalPointData_rule frozen double rows g j hg hj)

def laterAtom {birth : ℕ} : Atom birth→Atom (birth+1):=Option.map Fin.succ

def laterRow {birth : ℕ} : Row birth→Row (birth+1)
  | .single a=>.single (laterAtom a)
  | .sum a b=>.sum (laterAtom a) (laterAtom b)

theorem laterAtom_value {birth : ℕ} (a : Atom birth) : (laterAtom a).value=later a.value:=by
  cases a <;> rfl

theorem laterRow_value {birth : ℕ} (r : Row birth) : (laterRow r).value=later r.value:=by
  cases r <;> simp only [laterRow,Row.value,later,laterAtom_value]

theorem originalFrame_advance {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth) (r : Fin (n+1)) :
    advance (originalFrame frozen double rows) r=
      originalFrame (insert r frozen) (fun i=>if i=r then false else double i)
        (fun i=>if i=r then .single (some 0) else laterRow (rows i)):=by
  simp only [advance,originalFrame]
  congr 1
  · funext i
    by_cases hi : i=r
    · simp only [hi,ite_true,Bool.false_eq_true,ite_false]
    · simp only [hi,ite_false]
  · funext i
    by_cases hi : i=r
    · subst i
      simp only [ite_true,Row.value,Atom.value]
      rfl
    · simp only [hi,ite_false]
      exact (laterRow_value _).symm

theorem originalFrame_level {n birth : ℕ} (frozen : Finset (Fin (n+1)))
    (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row birth) (r : Fin (n+1))
    (a : Atom birth) (hr : rows r=.single a) :
    level (originalFrame frozen double rows) r=
      originalFrame (insert r frozen) double (fun i=>if i=r then .sum (laterAtom a) (some 0) else laterRow (rows i)):=by
  simp only [level,originalFrame]
  congr 1
  funext i
  by_cases hi : i=r
  · subst i
    simp only [ite_true,hr,Row.value]
    rw [laterAtom_value]
    rfl
  · simp only [hi,ite_false]
    exact (laterRow_value _).symm

end LeanCanny.Geometry.IntegralMixedFrozenFrame
