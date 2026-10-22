/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinatePath
public import LeanCanny.Algebra.BalancedPrimitiveCoordinates

/-! # Ascending leaf paths agree with the balanced tree decoder

Stage h recovers the child containing the selected leaf from its parent.
The ancestor index is j/2^h and its local leaf offset is j mod 2^h.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedLeafPath
open Polynomial UnivariateRational
open BalancedPrimitiveTree

def ancestor (j h : ℕ) : ℕ := j / 2 ^ h

theorem ancestor_succ (j h : ℕ) : ancestor j (h + 1) = ancestor j h / 2 := by
  simp only [ancestor, Nat.div_div_eq_div_mul, pow_succ]

theorem ancestor_split (j h : ℕ) : ancestor j h = 2 * ancestor j (h + 1) + ancestor j h % 2 := by
  rw [ancestor_succ]
  have H := Nat.mod_add_div (ancestor j h) 2
  omega

theorem residue_split (j h : ℕ) : j % 2 ^ (h + 1) = (ancestor j h % 2) * 2 ^ h + j % 2 ^ h := by
  rw [pow_succ, Nat.mod_mul, Nat.mul_comm (2 ^ h) _, Nat.add_comm]
  rfl

noncomputable def step (a : ℕ → SeparableIntegerPolynomial) (j h : ℕ) : Coordinate :=
  let i := ancestor j (h + 1)
  if ancestor j h % 2 = 1 then (node a h (2 * i)).rightCoordinate (node a h (2 * i + 1))
  else (node a h (2 * i)).leftCoordinate (node a h (2 * i + 1))

theorem walk_spec {K : Type*} [Field K] [CharZero K] (a : ℕ → SeparableIntegerPolynomial)
    (j h : ℕ) (theta : K) (ht : (node a h (ancestor j h)).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    RationalCoordinatePath.Defined (step a j) h theta ∧
      RationalCoordinatePath.evalPath (step a j) h theta = coordinate h (decode a h (ancestor j h) theta) (j % 2 ^ h) := by
  induction h generalizing theta with
  | zero => exact ⟨trivial, rfl⟩
  | succ h ih =>
    let i := ancestor j (h + 1)
    let p := node a h (2 * i)
    let q := node a h (2 * i + 1)
    have hr := SeparableIntegerPolynomial.decode_root_over p q theta ht
    have hd := SeparableIntegerPolynomial.denominator_ne_zero_over p q theta ht
    have ha := ancestor_split j h
    have hm := Nat.mod_two_eq_zero_or_one (ancestor j h)
    have hsmall := Nat.mod_lt j (Nat.two_pow_pos h)
    rcases hm with hz | ho
    · have hai : ancestor j h = 2 * i := by omega
      have hs : step a j h = p.leftCoordinate q := by simp only [step, hz, Nat.zero_ne_one, ite_false]; rfl
      have he : (step a j h).eval theta = (p.decode q theta).1 := by rw [hs]; rfl
      have hden : (step a j h).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 := by rw [hs]; exact hd
      have hchild : (node a h (ancestor j h)).polynomial.eval₂ (Int.castRingHom K) (p.decode q theta).1 = 0 := by
        rw [hai]; exact hr.1
      have H := ih _ hchild
      have hres : j % 2 ^ (h + 1) = j % 2 ^ h := by rw [residue_split, hz, zero_mul, zero_add]
      refine ⟨⟨hden, ?_⟩, ?_⟩
      · rw [he]; exact H.1
      · change RationalCoordinatePath.evalPath (step a j) h ((step a j h).eval theta) = _
        rw [he, coordinate, decode, hres, ite_eq_left hsmall]
        simpa only [hai] using H.2
    · have hai : ancestor j h = 2 * i + 1 := by omega
      have hs : step a j h = p.rightCoordinate q := by simp only [step, ho, ite_true]; rfl
      have he : (step a j h).eval theta = (p.decode q theta).2 := by rw [hs]; rfl
      have hden : (step a j h).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 := by rw [hs]; exact hd
      have hchild : (node a h (ancestor j h)).polynomial.eval₂ (Int.castRingHom K) (p.decode q theta).2 = 0 := by
        rw [hai]; exact hr.2.1
      have H := ih _ hchild
      have hres : j % 2 ^ (h + 1) = 2 ^ h + j % 2 ^ h := by rw [residue_split, ho, one_mul]
      have hnot : ¬ j % 2 ^ (h + 1) < 2 ^ h := by omega
      refine ⟨⟨hden, ?_⟩, ?_⟩
      · rw [he]; exact H.1
      · change RationalCoordinatePath.evalPath (step a j) h ((step a j h).eval theta) = _
        rw [he, coordinate, decode, ite_eq_right hnot, hres, Nat.add_sub_cancel_left]
        simpa only [hai] using H.2

end LeanCanny.Algebra.BalancedLeafPath

namespace LeanCanny.Algebra.RationalCoordinatePath
open UnivariateRational

theorem trace_congr {K : Type*} [Field K] (f g : ℕ → Coordinate) (k : ℕ)
    (he : ∀ s < k, f s = g s) (x : K) :
    (Defined f k x ↔ Defined g k x) ∧ evalPath f k x = evalPath g k x := by
  induction k generalizing x with
  | zero => exact ⟨Iff.rfl, rfl⟩
  | succ k ih =>
    have H := ih (fun s hs => he s (by omega)) ((g k).eval x)
    simp only [Defined, evalPath, he k (by omega)]
    exact ⟨and_congr Iff.rfl H.1, H.2⟩

end LeanCanny.Algebra.RationalCoordinatePath
