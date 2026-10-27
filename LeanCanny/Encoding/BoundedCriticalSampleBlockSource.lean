/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedMultivariateRational
public import LeanCanny.Encoding.BoundedCriticalSampleLineCorrect

/-! # Rational coordinate blocks at actual critical samples

Variable zero is the common algebraic sample parameter. A contiguous block
of original coordinates is replaced by the remaining independent variables.
All other coordinates retain the same sample's rational representation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def InBlock (o k i : ℕ) : Prop := o ≤ i ∧ i < o + k
def freeVariable (o k i : ℕ) (hi : InBlock o k i) : Fin (k + 1) := ⟨i - o + 1, by unfold InBlock at hi; omega⟩

noncomputable def coordinate (P : Readers) (o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    MvPolynomial (Fin (k u + 1)) ℤ :=
  if hi : InBlock (o u) (k u) i then if b then MvPolynomial.X (freeVariable _ _ _ hi) else 1
  else IndexedMultivariateRational.parameter (k u) (BoundedCriticalSampleLineCoordinates.base P b u i)

theorem coordinate_degree (P : Readers) (o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    (coordinate P o k b u i).totalDegree ≤ max (BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)) 1 := by
  unfold coordinate
  split_ifs
  · simp only [MvPolynomial.totalDegree_X]
    exact Nat.le_max_right _ _
  · simp only [MvPolynomial.totalDegree_one]
    omega
  · exact (IndexedMultivariateRational.parameter_degree _ _).trans
      ((BoundedCriticalSampleLineCoordinates.base_degree P b u i).trans (Nat.le_max_left _ _))

def environment (k : ℕ) (theta : ℝ) (y : Fin k → ℝ) (j : Fin (k + 1)) : ℝ :=
  if hj : j.val = 0 then theta else y ⟨j.val - 1, by omega⟩
theorem environment_zero (k : ℕ) (theta : ℝ) (y : Fin k → ℝ) : environment k theta y 0 = theta := by
  simp only [environment, Fin.val_zero, dite_true]
theorem environment_variable (o k i : ℕ) (hi : InBlock o k i) (theta : ℝ) (y : Fin k → ℝ) :
    environment k theta y (freeVariable o k i hi) = y ⟨i - o, by unfold InBlock at hi; omega⟩ := by
  simp only [environment, freeVariable, Nat.add_sub_cancel]
  rw [dite_eq_right (by omega)]

noncomputable def assignment {n : ℕ} (x : Fin n → ℝ) (o k : ℕ) (y : Fin k → ℝ) (i : ℕ) : ℝ :=
  if hi : InBlock o k i then y ⟨i - o, by unfold InBlock at hi; omega⟩ else Formula.extend x i

theorem denominator_nonzero (P : Readers) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) (i : ℕ) :
    (coordinate P o k false (pair c r) i).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y) ≠ 0 := by
  simp only [coordinate, Bool.false_eq_true, ite_false]
  split_ifs
  · simp only [MvPolynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]
  · rw [IndexedMultivariateRational.eval_parameter, environment_zero]
    exact BoundedCriticalSampleTermCoordinates.denominator_nonzero P c r x i

theorem coordinate_eval (P : Readers) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) (i : ℕ) :
    (coordinate P o k true (pair c r) i).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y) /
      (coordinate P o k false (pair c r) i).eval₂ (Int.castRingHom ℝ)
        (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y) =
          assignment x.val (o (pair c r)) (k (pair c r)) y i := by
  simp only [coordinate, assignment, Bool.false_eq_true, ite_false, ite_true]
  split_ifs with hi
  · rw [MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, div_one, environment_variable]
  · rw [IndexedMultivariateRational.eval_parameter, IndexedMultivariateRational.eval_parameter,
      environment_zero]
    exact BoundedCriticalSampleTermCoordinates.coordinate_eval P c r x i

noncomputable def finiteAssignment {n : ℕ} (x : Fin n → ℝ) (o k : ℕ) (y : Fin k → ℝ) (i : Fin n) : ℝ :=
  assignment x o k y i.val
theorem assignment_finite {n : ℕ} (x : Fin n → ℝ) (o k : ℕ) (y : Fin k → ℝ) (hk : o + k ≤ n) :
    assignment x o k y = Formula.extend (finiteAssignment x o k y) := by
  funext i
  by_cases hi : i < n
  · simp only [Formula.extend, hi, dite_true, finiteAssignment]
  · have hb : ¬InBlock o k i := by unfold InBlock; omega
    simp only [assignment, hb, dite_false, Formula.extend, hi]

theorem assignment_empty {n : ℕ} (x : Fin n → ℝ) (o : ℕ) (y : Fin 0 → ℝ) :
    assignment x o 0 y = Formula.extend x := by
  funext i
  have hi : ¬InBlock o 0 i := by unfold InBlock; omega
  simp only [assignment, hi, dite_false]

theorem assignment_drop_first {n : ℕ} (x : Fin n → ℝ) (o k : ℕ) (y : Fin k → ℝ) :
    assignment x o (k + 1) (environment k (Formula.extend x o) y) = assignment x (o + 1) k y := by
  funext i
  by_cases hi : InBlock o (k + 1) i
  · by_cases he : i = o
    · subst i
      have hn : ¬InBlock (o + 1) k o := by unfold InBlock; omega
      simp only [assignment, hi, dite_true, hn, dite_false, environment, Nat.sub_self]
    · have hn : InBlock (o + 1) k i := by unfold InBlock at *; omega
      have hz : i - o ≠ 0 := by unfold InBlock at hi; omega
      simp only [assignment, hi, hn, dite_true, environment, hz, dite_false]
      congr 1
  · have hn : ¬InBlock (o + 1) k i := by unfold InBlock at *; omega
    simp only [assignment, hi, hn, dite_false]

end LeanCanny.Encoding.BoundedCriticalSampleBlockSource
