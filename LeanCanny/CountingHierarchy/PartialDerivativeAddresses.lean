/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TranslatedPoint

/-! # Short coefficient addresses for first and mixed second derivatives -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM

@[expose] def firstPartialAddress (n i : ℕ) : List ℕ :=
  (List.range n).map (fun k => if k = i then 1 else 0)

@[expose] def secondPartialAddress (n i j : ℕ) : List ℕ :=
  (List.range n).map (fun k => (if k = j then 1 else 0) + (if k = i then 1 else 0))

theorem firstPartialAddress_get {n k : ℕ} (i : ℕ) (hk : k < n) :
    (firstPartialAddress n i)[k]?.getD 0 = if k = i then 1 else 0 := by
  simp [firstPartialAddress, hk]

theorem secondPartialAddress_get {n k : ℕ} (i j : ℕ) (hk : k < n) :
    (secondPartialAddress n i j)[k]?.getD 0 =
      (if k = j then 1 else 0) + (if k = i then 1 else 0) := by
  simp [secondPartialAddress, hk]

theorem firstPartialAddress_polyTime {α : Type} {enc : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun w => firstPartialAddress (n w) (i w)) enc (encList encNat) := by
  have hk := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hi' := hi.comp (ComputableInPolyTime.fst enc encUnary)
  have htest : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = i q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hi'
  have hval : ComputableInPolyTime (fun q : α × ℕ => if q.2 = i q.1 then 1 else 0)
      (encPair enc encUnary) encNat := by
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (.const (1 : ℕ)) (.const 0)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hval

theorem secondPartialAddress_polyTime {α : Type} {enc : α ↪ List Bool} {n i j : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun w => secondPartialAddress (n w) (i w) (j w)) enc (encList encNat) := by
  have hk := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hi' := hi.comp (ComputableInPolyTime.fst enc encUnary)
  have hj' := hj.comp (ComputableInPolyTime.fst enc encUnary)
  have htesti : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = i q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hi'
  have htestj : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = j q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hj'
  have hval := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.ite' htestj (.const (1 : ℕ)) (.const 0))
    (ComputableInPolyTime.ite' htesti (.const (1 : ℕ)) (.const 0))
  simp only [decide_eq_true_eq] at hval
  have hres := ComputableInPolyTime.mapWithInput
    (f := fun w k => (if k = j w then 1 else 0) + (if k = i w then 1 else 0))
    (ComputableInPolyTime.range.comp hn) hval
  simpa only [secondPartialAddress, decide_eq_true_eq, Function.comp_apply] using hres

end LeanCanny.CountingHierarchy
