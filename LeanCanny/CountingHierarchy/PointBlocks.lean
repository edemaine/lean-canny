/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Native padded evaluation points with separate variable blocks -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM

def paddedPoint (n : ℕ) (z : List ℕ) : List ℕ := (List.range n).map (fun i => z[i]?.getD 0)

def joinedPoint (n m : ℕ) (x z : List ℕ) : List ℕ := paddedPoint n x ++ paddedPoint m z

@[simp] theorem paddedPoint_length (n : ℕ) (z : List ℕ) : (paddedPoint n z).length = n := by simp [paddedPoint]

@[simp] theorem paddedPoint_get (n : ℕ) (z : List ℕ) (i : ℕ) (hi : i < n) :
    (paddedPoint n z)[i]?.getD 0 = z[i]?.getD 0 := by simp [paddedPoint, hi]

@[simp] theorem joinedPoint_length (n m : ℕ) (x z : List ℕ) : (joinedPoint n m x z).length = n + m := by
  simp only [joinedPoint, List.length_append, paddedPoint_length]

theorem joinedPoint_left (n m : ℕ) (x z : List ℕ) (i : Fin n) :
    (joinedPoint n m x z)[i.val]?.getD 0 = x[i.val]?.getD 0 := by
  simp only [joinedPoint, List.getElem?_append, paddedPoint_length, i.isLt, ite_true, paddedPoint_get]

theorem joinedPoint_right (n m : ℕ) (x z : List ℕ) (i : Fin m) :
    (joinedPoint n m x z)[n + i.val]?.getD 0 = z[i.val]?.getD 0 := by
  simp only [joinedPoint, List.getElem?_append, paddedPoint_length,
    Nat.not_lt.mpr (Nat.le_add_right n i.val), ite_false, Nat.add_sub_cancel_left, paddedPoint_get _ _ _ i.isLt]

@[fun_prop] theorem paddedPoint_polyTime {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {z : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => paddedPoint (n w) (z w)) enc (encList encNat) := by
  have hrange := ComputableInPolyTime.range.comp hn
  have hindex : ComputableInPolyTime (fun q : α × ℕ => q.2) (encPair enc encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hread : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0)
      (encPair enc encUnary) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp (ComputableInPolyTime.fst enc encUnary)) hindex
  exact ComputableInPolyTime.mapWithInput hrange hread

@[fun_prop] theorem joinedPoint_polyTime {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ} {x z : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hx : ComputableInPolyTime x enc (encList encNat)) (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => joinedPoint (n w) (m w) (x w) (z w)) enc (encList encNat) :=
  (ComputableTidilyInPolyTime.listAppend' (paddedPoint_polyTime hn hx).tidy
    (paddedPoint_polyTime hm hz).tidy).computableInPolyTime

end LeanCanny.CountingHierarchy
