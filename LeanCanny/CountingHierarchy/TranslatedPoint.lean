/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.GridEnumeration

/-! # Polynomial-time modular translation of evaluation points -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] def translatedPoint (p n : ℕ) (z y : List ℕ) : List ℕ :=
  (List.range n).map (fun i => ((z[i]?.getD 0) + (y[i]?.getD 0)) % p)

@[simp] theorem translatedPoint_length (p n : ℕ) (z y : List ℕ) :
    (translatedPoint p n z y).length = n := by simp [translatedPoint]

theorem translatedPoint_get {p n i : ℕ} (z y : List ℕ) (hi : i < n) :
    (translatedPoint p n z y)[i]?.getD 0 = ((z[i]?.getD 0) + (y[i]?.getD 0)) % p := by
  simp [translatedPoint, hi]

theorem translatedPoint_polyTime {α : Type} {enc : α ↪ List Bool}
    {p n : α → ℕ} {z y : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hy : ComputableInPolyTime y enc (encList encNat)) :
    ComputableInPolyTime (fun w => translatedPoint (p w) (n w) (z w) (y w))
      enc (encList encNat) := by
  have hf := ComputableInPolyTime.fst enc encUnary
  have hi := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hzval : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0)
      (encPair enc encUnary) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp hf) hi
  have hyval : ComputableInPolyTime (fun q : α × ℕ => (y q.1)[q.2]?.getD 0)
      (encPair enc encUnary) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hy.comp hf) hi
  have hsum := ComputableInPolyTime.binary_add' hzval hyval
  have hval := ComputableInPolyTime.binary_mod.comp (hsum.prod (hp.comp hf))
  simpa only [translatedPoint, List.getD_eq_getElem?_getD, Function.comp_apply] using
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hval

end LeanCanny.CountingHierarchy
