/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CodedRootLabelData

/-! # Correctness and completeness of bounded derivative-label decoding -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] def rootSignEncoding (s : SignType) : ℕ :=
  if s = 0 then 0 else if s = 1 then 1 else 2

theorem rootSignCode_encoding (s : SignType) : rootSignCode (rootSignEncoding s) = s := by
  cases s <;> decide

theorem rootSignEncoding_lt_three (s : SignType) : rootSignEncoding s < 3 := by
  cases s <;> decide

@[expose] def encodeRootLabel {D : ℕ} (L : List (Fin D × SignType)) : List (ℕ × ℕ) :=
  L.map (fun t => (t.1.val, rootSignEncoding t.2))

/-- Every allowed mathematical label has a code with exactly its length.
No search for a polynomial, critical point or algebraic number is encoded. -/
theorem codedRootLabel_encode {D N : ℕ} (hD : 0 < D)
    (L : List (Fin D × SignType)) (hL : L.length ≤ N) :
    codedRootLabel D N hD (encodeRootLabel L) = L := by
  have hlen : (encodeRootLabel L).length ≤ N := by
    simpa only [encodeRootLabel, List.length_map] using hL
  rw [codedRootLabel, List.take_of_length_le hlen, encodeRootLabel, List.map_map]
  calc
    _ = L.map id := by
      apply congrArg (fun f => L.map f)
      funext t
      apply Prod.ext
      · apply Fin.ext
        exact Nat.mod_eq_of_lt t.1.isLt
      · exact rootSignCode_encoding t.2
    _ = L := List.map_id L

theorem rootSignResidue_cast {p : ℕ} [Fact p.Prime] (k : ℕ) :
    (rootSignResidue p k : ZMod p) = ((rootSignCode k : ℤ) : ZMod p) := by
  by_cases hzero : k % 3 = 0
  · simp [rootSignResidue, rootSignCode, hzero]
  · by_cases hone : k % 3 = 1
    · simp [rootSignResidue, rootSignCode, hone]
    · rw [rootSignResidue, ite_eq_right hzero, ite_eq_right hone,
        modularSub_cast (Fact.out : p.Prime).pos]
      simp [rootSignCode, hzero, hone]

/-- The total native target reader agrees with the mathematical decoder
on every test that is actually used by the fixed-width label polynomial. -/
theorem codedRootLabelTarget_cast {p D N : ℕ} [Fact p.Prime] (hD : 0 < D)
    (data : List (ℕ × ℕ)) (i : Fin (N + 1)) :
    (codedRootLabelTarget p data i.val : ZMod p) =
      ((derivativeLabelTargets N (codedRootLabel D N hD data) i : ℤ) : ZMod p) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [codedRootLabelTarget, derivativeLabelTargets]
  · simp only [codedRootLabelTarget, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
      Nat.add_sub_cancel, derivativeLabelTargets, Fin.cases_succ, derivativeListTarget]
    rw [codedRootLabel, List.getElem?_map, List.getElem?_take_of_lt j.isLt]
    cases he : data[j.val]? with
    | none => simp [rootSignResidue]
    | some t =>
      simp only [Option.getD_some, Option.map_some, Option.elim_some]
      exact rootSignResidue_cast t.2

end LeanCanny.CountingHierarchy
