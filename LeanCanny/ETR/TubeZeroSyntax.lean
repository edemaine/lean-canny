/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeEncoding
public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.FinitePolynomial
import Mathlib.Tactic.Ring

/-! # Sparse syntax for the zero-source tube

The radius uses every shift coordinate; the active constraints are affine
box/shift expressions. A short expression therefore represents the complete
zero-source tube, with symbolic alpha, epsilon, and delta variables.
-/

@[expose] public section

namespace LeanCanny.ETR.Term

theorem finitePolynomial_square (t : Term) (A : ℕ) : finitePolynomial A t.square = finitePolynomial A t ^ 2 := by
  simp only [square, finitePolynomial, pow_two]

end LeanCanny.ETR.Term

namespace LeanCanny.ETR.SumSquares
open MvPolynomial

theorem finitePolynomial_accumulate (ts : List Term) (acc : Term) (A : ℕ) :
    Term.finitePolynomial A (accumulate ts acc) = Term.finitePolynomial A acc +
      (ts.map (fun t => Term.finitePolynomial A t ^ 2)).sum := by
  induction ts generalizing acc with
  | nil => simp [accumulate]
  | cons t ts ih =>
    change Term.finitePolynomial A (accumulate ts (.add t.square acc)) = _
    rw [ih]
    simp only [Term.finitePolynomial, Term.square, List.map_cons, List.sum_cons, pow_two]
    ring

end LeanCanny.ETR.SumSquares

namespace LeanCanny.ETR.TubeZero
open MvPolynomial
open Geometry TubeEncoding
open scoped BigOperators

def oneMinusEpsilon (n : ℕ) : Term :=
  .add (.const 1) (.mul (.const (-1)) (.var (n + constraintCount n + 1)))

def constraint (n j : ℕ) : Term :=
  if j < 2 then .var (n + j) else
    let i := (j - 2) / 2
    if j % 2 = 0 then .add (.add (.var i) (oneMinusEpsilon n)) (.var (n + j))
    else .add (.add (oneMinusEpsilon n) (.mul (.const (-1)) (.var i))) (.var (n + j))

def radiusTerms (n : ℕ) : List Term := (List.range (constraintCount n)).map (fun j => Term.var (n + j))
def activeTerms (n : ℕ) (bits : List Bool) : List Term :=
  (List.range (constraintCount n)).map (fun j => if bits[j]?.getD false then constraint n j else Term.const 0)

def radius (n : ℕ) : Term := .add (SumSquares.accumulate (radiusTerms n) (.const 0))
  (.mul (.const (-1)) (Term.var (n + constraintCount n + 2)).square)

def term (n : ℕ) (bits : List Bool) : Term :=
  .add (.add (radius n).square (SumSquares.accumulate (activeTerms n bits) (.const 0)))
    (.mul (.const (-1)) (.var (n + constraintCount n)))

theorem finitePolynomial_variable (n : ℕ) (j : Coordinate n) :
    Term.finitePolynomial (dimension n) (.var (coordinateEquiv n j).val) = X (coordinateEquiv n j) := by
  simp only [Term.finitePolynomial, (coordinateEquiv n j).isLt, dite_true]

theorem finitePolynomial_shift (n : ℕ) (j : Constraint n) :
    Term.finitePolynomial (dimension n) (.var (n + (constraintEquiv n j).val)) =
      X (coordinateEquiv n (.inl (.inr j))) := by
  simpa only [index_shift] using finitePolynomial_variable n (.inl (.inr j))

theorem finitePolynomial_oneMinusEpsilon (n : ℕ) :
    Term.finitePolynomial (dimension n) (oneMinusEpsilon n) = 1 - X (coordinateEquiv n (.inr (some false))) := by
  have he := finitePolynomial_variable n (.inr (some false))
  simp only [index_epsilon] at he
  change C (1 : ℤ) + C (-1) * Term.finitePolynomial (dimension n) (.var (n + constraintCount n + 1)) = _
  rw [he]
  simp only [map_one, map_neg]
  ring

theorem finitePolynomial_constraint (n : ℕ) (j : Constraint n) :
    Term.finitePolynomial (dimension n) (constraint n (constraintEquiv n j).val) =
      rename (coordinateEquiv n) (Algebra.NestedPolynomial.flatten
        (TubePolynomial.constraint (0 : MvPolynomial (Fin n) ℤ) j)) := by
  have hs := finitePolynomial_shift n j
  rcases j with b | ⟨i, b⟩
  · cases b
    · simpa [constraint, TubePolynomial.constraint, TubePolynomial.flatten_spatial] using hs
    · simpa [constraint, TubePolynomial.constraint, TubePolynomial.flatten_spatial] using hs
  · have hx := finitePolynomial_variable n (.inl (.inl i))
    simp only [index_point] at hx
    cases b
    · have hd : (2 + 2 * i.val - 2) / 2 = i.val := by omega
      have hm : (2 + 2 * i.val) % 2 = 0 := by omega
      simp only [constraintIndex_box, Bool.false_eq_true, ite_false, Nat.add_zero] at hs ⊢
      rw [constraint, ite_eq_right (by omega), hd, ite_eq_left hm]
      change (Term.finitePolynomial (dimension n) (.var i.val) +
        Term.finitePolynomial (dimension n) (oneMinusEpsilon n)) +
          Term.finitePolynomial (dimension n) (.var (n + (2 + 2 * i.val))) = _
      rw [hx, finitePolynomial_oneMinusEpsilon, hs]
      simp [TubePolynomial.constraint]
      ring
    · have hd : (2 + 2 * i.val + 1 - 2) / 2 = i.val := by omega
      have hm : ¬ (2 + 2 * i.val + 1) % 2 = 0 := by omega
      simp only [constraintIndex_box, ite_true] at hs ⊢
      rw [constraint, ite_eq_right (by omega), hd, ite_eq_right hm]
      change (Term.finitePolynomial (dimension n) (oneMinusEpsilon n) +
        C (-1) * Term.finitePolynomial (dimension n) (.var i.val)) +
          Term.finitePolynomial (dimension n) (.var (n + (2 + 2 * i.val + 1))) = _
      rw [hx, finitePolynomial_oneMinusEpsilon, hs]
      simp [TubePolynomial.constraint]
      ring

theorem sum_map_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem finitePolynomial_radius (n : ℕ) :
    Term.finitePolynomial (dimension n) (radius n) =
      rename (coordinateEquiv n) (Algebra.NestedPolynomial.flatten (TubePolynomial.radius (Fin n))) := by
  have hd := finitePolynomial_variable n (.inr (some true))
  simp only [index_delta] at hd
  have hsum : (∑ k : Fin (constraintCount n), Term.finitePolynomial (dimension n) (.var (n + k.val)) ^ 2) =
      ∑ j : Constraint n, X (coordinateEquiv n (.inl (.inr j))) ^ 2 := by
    rw [← Equiv.sum_comp (constraintEquiv n)]
    apply Finset.sum_congr rfl
    intro j _
    rw [finitePolynomial_shift]
  change Term.finitePolynomial (dimension n) (SumSquares.accumulate (radiusTerms n) (.const 0)) +
    C (-1) * Term.finitePolynomial (dimension n) (Term.var (n + constraintCount n + 2)).square = _
  rw [Term.finitePolynomial_square, hd, SumSquares.finitePolynomial_accumulate]
  simp only [show Term.finitePolynomial (dimension n) (.const 0) = 0 from by simp [Term.finitePolynomial], zero_add, radiusTerms, List.map_map]
  rw [sum_map_range]
  simp only [Function.comp_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun k => Term.finitePolynomial (dimension n) (.var (n + k)) ^ 2), hsum]
  simp [TubePolynomial.radius]
  ring

theorem finitePolynomial_active (n : ℕ) (bits : List Bool) :
    Term.finitePolynomial (dimension n) (SumSquares.accumulate (activeTerms n bits) (.const 0)) =
      ∑ j ∈ activeSet n bits, (rename (coordinateEquiv n) (Algebra.NestedPolynomial.flatten
        (TubePolynomial.constraint (0 : MvPolynomial (Fin n) ℤ) j))) ^ 2 := by
  rw [SumSquares.finitePolynomial_accumulate]
  simp only [show Term.finitePolynomial (dimension n) (.const 0) = 0 from by simp [Term.finitePolynomial], zero_add, activeTerms, List.map_map]
  rw [sum_map_range]
  simp only [Function.comp_apply]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Term.finitePolynomial (dimension n) (if bits[j]?.getD false then constraint n j else Term.const 0) ^ 2)]
  rw [← Equiv.sum_comp (constraintEquiv n)]
  simp only [activeSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [finitePolynomial_constraint]
  · simp [Term.finitePolynomial]

theorem finitePolynomial_term (n : ℕ) (bits : List Bool) :
    Term.finitePolynomial (dimension n) (term n bits) =
      rename (coordinateEquiv n) (TubePolynomial.integerPolynomial (0 : MvPolynomial (Fin n) ℤ) (activeSet n bits)) := by
  have ha := finitePolynomial_variable n (.inr none)
  simp only [index_alpha] at ha
  change (Term.finitePolynomial (dimension n) (radius n).square +
    Term.finitePolynomial (dimension n) (SumSquares.accumulate (activeTerms n bits) (.const 0))) +
      C (-1) * Term.finitePolynomial (dimension n) (.var (n + constraintCount n)) = _
  rw [Term.finitePolynomial_square, finitePolynomial_radius, finitePolynomial_active, ha]
  simp [TubePolynomial.integerPolynomial, TubePolynomial.polynomial, TubePolynomial.energy]
  ring

end LeanCanny.ETR.TubeZero
