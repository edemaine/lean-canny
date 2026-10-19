/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Data/List/PermanencesMinusVariations.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open List

section

private def gapWeight (k : ℕ) : ℤ :=
  if Even k then (-1) ^ (Nat.choose k 2) else 0

private def pmvAux (a : SignType) (k : ℕ) : List SignType → ℤ
  | [] => 0
  | b :: l => if b = 0 then pmvAux a (k + 1) l
    else gapWeight k * (a : ℤ) * (b : ℤ) + pmvAux b 0 l

private theorem pmvAux_zero (k : ℕ) (l : List SignType) :
    pmvAux 0 k l = pmvAux 0 0 l := by
  induction l generalizing k with
  | nil => rfl
  | cons b l ih =>
    by_cases hb : b = 0
    · simp [pmvAux, hb, ih]
    · simp [pmvAux, hb]

private theorem pmvAux_replicate (a : SignType) (k n : ℕ) :
    pmvAux a k (List.replicate n 0) = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, pmvAux, ih]

private theorem pmvAux_replicate_append (a : SignType) (k n : ℕ) (l : List SignType) :
    pmvAux a k (List.replicate n 0 ++ l) = pmvAux a (k + n) l := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, pmvAux, ite_true, ih]
    exact congrArg (fun t => pmvAux a t l) (by omega)

/-- Sum over consecutive nonzero entries, retaining the parity and length of
each intervening zero gap. Leading and trailing zeros contribute nothing. -/
def permanencesMinusVariations {R : Type*} [Zero R] [LinearOrder R]
    (l : List R) : ℤ := pmvAux 0 0 (l.map SignType.sign)

variable {R S : Type*} [Zero R] [LinearOrder R] [Zero S] [LinearOrder S]

@[simp] theorem permanencesMinusVariations_nil :
    (permanencesMinusVariations ([] : List R)) = 0 := (rfl)

@[simp] theorem permanencesMinusVariations_zero_cons (l : List R) :
    (permanencesMinusVariations (0 :: l)) = (permanencesMinusVariations l) := by
  simp [permanencesMinusVariations, pmvAux, pmvAux_zero]

@[simp] theorem permanencesMinusVariations_singleton (a : R) :
    (permanencesMinusVariations [a]) = 0 := by
  simp [permanencesMinusVariations, pmvAux]

@[simp] theorem permanencesMinusVariations_replicate_zero (n : ℕ) :
    (permanencesMinusVariations (List.replicate n (0 : R))) = 0 := by
  simp [permanencesMinusVariations, pmvAux_replicate]

/-- A prefix of zeros is ignored. -/
@[simp] theorem permanencesMinusVariations_replicate_zero_append
    (n : ℕ) (l : List R) :
    (permanencesMinusVariations (List.replicate n 0 ++ l)) =
      (permanencesMinusVariations l) := by
  simp [permanencesMinusVariations, pmvAux_replicate_append, pmvAux_zero]

private theorem pmvAux_append_replicate (a : SignType) (k n : ℕ) (l : List SignType) :
    pmvAux a k (l ++ List.replicate n 0) = pmvAux a k l := by
  induction l generalizing a k with
  | nil => simp [pmvAux, pmvAux_replicate]
  | cons b l ih => simp [pmvAux, ih]

/-- A suffix of zeros is ignored. -/
@[simp] theorem permanencesMinusVariations_append_replicate_zero
    (l : List R) (n : ℕ) :
    (permanencesMinusVariations (l ++ List.replicate n 0)) =
      (permanencesMinusVariations l) := by
  simp [permanencesMinusVariations, pmvAux_append_replicate]

/-- A list with only its head possibly nonzero has no adjacent nonzero pair. -/
@[simp] theorem permanencesMinusVariations_cons_replicate_zero
    (a : R) (n : ℕ) : (permanencesMinusVariations (a :: List.replicate n 0)) = 0 := by
  simpa using permanencesMinusVariations_append_replicate_zero [a] n

/-- Recursion across a zero gap ending at a nonzero entry. This also specifies
the sign correction for even gaps and the cancellation for odd gaps. -/
theorem permanencesMinusVariations_cons_replicate_zero_append
    {a b : R} (hb : b ≠ 0) (k : ℕ) (l : List R) :
    (permanencesMinusVariations (a :: (List.replicate k 0 ++ b :: l))) =
      (if Even k then (-1 : ℤ) ^ (Nat.choose k 2) *
        (SignType.sign a : ℤ) * (SignType.sign b : ℤ) else 0) +
      (permanencesMinusVariations (b :: l)) := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [permanencesMinusVariations, pmvAux, ha, hb,
      pmvAux_replicate_append, gapWeight]

/-- Without an intervening zero, an adjacent pair contributes the product of
its signs. -/
theorem permanencesMinusVariations_cons_cons {a b : R}
    (hb : b ≠ 0) (l : List R) :
    (permanencesMinusVariations (a :: b :: l)) =
      (SignType.sign a : ℤ) * (SignType.sign b : ℤ) +
        (permanencesMinusVariations (b :: l)) := by
  simpa using permanencesMinusVariations_cons_replicate_zero_append hb 0 l

private theorem pmvAux_append_cons (s a : SignType) (ha : a ≠ 0) (k : ℕ)
    (l m : List SignType) :
    pmvAux s k (l ++ a :: m) = pmvAux s k (l ++ [a]) + pmvAux a 0 m := by
  induction l generalizing s k with
  | nil => simp [pmvAux, ha]
  | cons b l ih =>
    simp only [List.cons_append, pmvAux, ih]
    split_ifs <;> omega

/-- Joining two blocks whose boundary entries are nonzero adds precisely the
contribution of the intervening zero gap to their separate statistics. -/
theorem permanencesMinusVariations_append_replicate_zero_cons
    (l m : List R) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    (permanencesMinusVariations (l ++ a :: (List.replicate k 0 ++ b :: m))) =
      (permanencesMinusVariations (l ++ [a])) +
        (if Even k then (-1 : ℤ) ^ (Nat.choose k 2) *
          (SignType.sign a : ℤ) * (SignType.sign b : ℤ) else 0) +
        (permanencesMinusVariations (b :: m)) := by
  simp only [permanencesMinusVariations, List.map_append, List.map_cons,
    List.map_replicate, sign_zero, List.map_nil]
  rw [pmvAux_append_cons _ _ (sign_ne_zero.mpr ha)]
  simp [pmvAux_replicate_append, pmvAux, hb, gapWeight, add_assoc]

/-- The statistic depends only on the ordered list of signs, including zeros. -/
theorem permanencesMinusVariations_congr {l : List R} {m : List S}
    (h : l.map SignType.sign = m.map SignType.sign) :
    (permanencesMinusVariations l) = (permanencesMinusVariations m) := by
  simp only [permanencesMinusVariations, h]

/-- Sign-preserving maps preserve permanences minus variations. -/
theorem permanencesMinusVariations_map {f : R → S}
    (hf : ∀ x, SignType.sign (f x) = SignType.sign x) (l : List R) :
    (permanencesMinusVariations (l.map f)) = (permanencesMinusVariations l) := by
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left fun x _ => hf x

@[simp] theorem permanencesMinusVariations_map_sign (l : List R) :
    (permanencesMinusVariations (l.map SignType.sign)) = (permanencesMinusVariations l) := by
  apply permanencesMinusVariations_map
  intro x
  cases SignType.sign x <;> decide

private theorem pmvAux_neg (a : SignType) (k : ℕ) (l : List SignType) :
    pmvAux (-a) k (l.map (- ·)) = pmvAux a k l := by
  induction l generalizing a k with
  | nil => rfl
  | cons b l ih => simp [pmvAux, ih]

/-- Reversing every sign preserves the products of consecutive nonzero signs. -/
theorem permanencesMinusVariations_map_of_sign_eq_neg {f : R → S}
    (hf : ∀ x, SignType.sign (f x) = -SignType.sign x) (l : List R) :
    (permanencesMinusVariations (l.map f)) = (permanencesMinusVariations l) := by
  have h : (l.map f).map SignType.sign = (l.map SignType.sign).map (- ·) := by
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => hf x
  simp only [permanencesMinusVariations, h]
  simpa using pmvAux_neg 0 0 (l.map SignType.sign)

/-- Multiplying every entry by a nonzero constant preserves permanences minus
variations. -/
@[simp] theorem permanencesMinusVariations_map_mul_left {K : Type*} [Ring K]
    [LinearOrder K] [IsStrictOrderedRing K] {c : K} (hc : c ≠ 0) (l : List K) :
    (permanencesMinusVariations (l.map (c * ·))) = (permanencesMinusVariations l) := by
  rcases hc.lt_or_gt with hc | hc
  · exact permanencesMinusVariations_map_of_sign_eq_neg
      (fun x => by simp [sign_mul, sign_neg hc]) l
  · exact permanencesMinusVariations_map (fun x => by simp [sign_mul, sign_pos hc]) l

/-- On a list with no zeros, permanences minus variations is the number of
adjacent pairs minus twice the number of sign changes. -/
theorem permanencesMinusVariations_eq_length_sub_two_mul_signVariations
    (l : List R) (h : ∀ a ∈ l, a ≠ 0) :
    (permanencesMinusVariations l) = ((l.length - 1 : ℕ) : ℤ) - 2 * l.signVariations := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have ha := h a (by simp)
      have hb := h b (by simp)
      have ht : ∀ x ∈ b :: l, x ≠ 0 := fun x hx => h x (by simp [hx])
      rw [permanencesMinusVariations_cons_cons hb,
        List.signVariations_cons_cons_of_ne_zero _ ha hb, ih ht]
      have hs : (SignType.sign a : ℤ) * (SignType.sign b : ℤ) =
          1 - 2 * (if SignType.sign a = SignType.sign b then (0 : ℤ) else 1) := by
        have ha' := sign_ne_zero.mpr ha
        have hb' := sign_ne_zero.mpr hb
        revert ha' hb'
        cases SignType.sign a <;> cases SignType.sign b <;> decide
      simp only [hs, List.length_cons, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one, Nat.cast_ite, Nat.cast_zero]
      omega

end

end LeanCanny.Algebra.PrincipalSubresultant
