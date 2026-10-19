/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Data/List/SignVariations.lean.
Changes: selected proof slice, project namespace, real specialization where needed,
and compatibility with the pinned Mathlib. See STURM_SOURCES.md.
-/
module

public import Mathlib.Data.List.SignVariations

/-! # List sign-variation recurrence and invariance under nonzero scaling
-/

public section

namespace LeanCanny.Algebra.Sturm

open List

section

variable {R : Type*} [Zero R] [LinearOrder R]

/-- The sign of the first nonzero entry of a list, or `0` if every entry is zero. -/
def firstSign (l : List R) : SignType :=
  ((l.filter (fun v => decide (v ≠ 0))).head?.map SignType.sign).getD 0

@[simp, grind =]
theorem firstSign_nil : firstSign ([] : List R) = 0 := (rfl)

@[simp, grind =]
theorem firstSign_zero_cons (l : List R) : firstSign (0 :: l) = firstSign l := by
  simp [firstSign]

@[simp, grind =]
theorem firstSign_cons_of_ne_zero {a : R} (l : List R) (ha : a ≠ 0) :
    firstSign (a :: l) = SignType.sign a := by
  simp [firstSign, ha]

/-- Prepending an entry `a` adds one sign variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons {a : R} (l : List R) :
    List.signVariations (a :: l) =
      (if SignType.sign a * firstSign l = -1 then 1 else 0) + List.signVariations l := by
  by_cases ha : a = 0
  · subst a
    simp
  · induction l with
    | nil => simp [firstSign]
    | cons b l ih =>
      by_cases hb : b = 0
      · subst b
        simpa only [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
          firstSign_zero_cons] using ih
      · rw [firstSign_cons_of_ne_zero l hb, List.signVariations_cons_cons_of_ne_zero l ha hb]
        have ha' : SignType.sign a ≠ 0 := by simpa using ha
        have hb' : SignType.sign b ≠ 0 := by simpa using hb
        have h : (if SignType.sign a = SignType.sign b then (0 : ℕ) else 1) =
            (if SignType.sign a * SignType.sign b = -1 then 1 else 0) := by
          revert ha' hb'
          cases SignType.sign a <;> cases SignType.sign b <;> decide
        rw [h, Nat.add_comm]

end


variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying every entry on the left by a nonzero constant preserves the sign
variations. -/
theorem signVariations_map_mul_left (l : List R) {c : R} (hc : c ≠ 0) :
    List.signVariations (l.map (c * ·)) = List.signVariations l := by
  rcases hc.lt_or_gt with hc | hc
  · exact signVariations_map_of_sign_eq_neg (fun x => by rw [sign_mul, sign_neg hc, neg_one_mul]) l
  · exact signVariations_map (fun x => by rw [sign_mul, sign_pos hc, one_mul]) l

end LeanCanny.Algebra.Sturm
