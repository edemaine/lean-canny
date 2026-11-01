/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
public import LeanCanny.Encoding.FlatAffineExceptionalBankCriticalData
/-! # Literal affine-expression commands for the correlated exceptional bank -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalMixedHistory (initial)
open IntegralMixedHistory
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def sum (xs : List AffineExpr) : AffineExpr := xs.foldr .add (.constant 0)

theorem expression_sum {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (xs : List AffineExpr) : expression x (sum xs) = (xs.map (expression x)).sum := by
  induction xs with
  | nil => simp [sum, expression]
  | cons a xs ih => simpa only [sum, List.foldr_cons, expression, List.map_cons, List.sum_cons] using congrArg (expression x a + ·) ih

theorem expression_reference {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (i : Fin m) : expression x (.reference i.val) = cleared x i := by
  change (if hi : i.val < m then cleared x ⟨i.val,hi⟩ else 0) = _
  rw [dite_eq_left i.isLt]

def height (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (a : Fin (arity F u) → ℤ) : AffineExpr :=
  sum (List.ofFn (fun i => .scale (a i) (.reference (FlatAffineExceptionalParentBank.spatialIndex F u t i).val)))

def level (F : Inputs) (u : List Bool) : FlatAffineCriticalTower.Level (arity F u) (F.depth u) ℤ → AffineExpr
  | .constant c => .constant c
  | .height t a => height F u t a
  | .midpoint l r a => .add (height F u l a) (height F u r a)

noncomputable def shifted (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (j : Fin (arity F u)) : AffineExpr :=
  .add (level F u (FlatAffineFullSourceTower.level F u (F.depth u) j))
    (if j = h u then .reference 0 else .constant 0)

theorem initial_denominator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1) :
    commonDenominator (initial F C h S u hm) = FlatAffineExceptionalParentBank.denominator F C h S u hm := rfl

theorem initial_cleared (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1)
    (i : Fin (births F u)) : cleared (initial F C h S u hm) i = FlatAffineExceptionalParentBank.cleared F C h S u hm i := rfl

theorem height_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1)
    (t : Fin (F.depth u)) (a : Fin (arity F u) → ℤ) :
    expression (initial F C h S u hm) (height F u t a) = FlatAffineExceptionalParentBank.heightNumerator F C h S u hm t a := by
  rw [height, expression_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  exact congrArg ((a i : (initial F C h S u hm).sampler.scalarPrefix.carrier) * ·)
    ((expression_reference (initial F C h S u hm) (FlatAffineExceptionalParentBank.spatialIndex F u t i)).trans
      (initial_cleared F C h S u hm (FlatAffineExceptionalParentBank.spatialIndex F u t i)))

theorem level_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1)
    (l : FlatAffineCriticalTower.Level (arity F u) (F.depth u) ℤ) :
    expression (initial F C h S u hm) (level F u l) = FlatAffineExceptionalParentBank.levelNumerator F C h S u hm l := by
  cases l with
  | constant c => rfl
  | height t a => exact height_eq F C h S u hm t a
  | midpoint l r a => exact congrArg₂ (· + ·) (height_eq F C h S u hm l a) (height_eq F C h S u hm r a)

theorem shifted_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1)
    (j : Fin (arity F u)) :
    expression (initial F C h S u hm) (shifted F h u j) = FlatAffineExceptionalParentBank.shiftedNumerator F C h S u hm j := by
  unfold shifted FlatAffineExceptionalParentBank.shiftedNumerator
  rw [expression, level_eq]
  by_cases hj : j = h u
  · rw [ite_eq_left hj, ite_eq_left hj]
    unfold expression
    rw [dite_eq_left (by exact Nat.zero_lt_succ _)]
    rfl
  · rw [ite_eq_right hj, ite_eq_right hj]
    simp only [expression, Int.cast_zero, mul_zero, add_zero]

end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
