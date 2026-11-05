/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCore
/-! # Every joint-core root satisfies the literal source and sharing equations -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialJointLayout FormulaSignSlotRadialJointCore
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem sumSquares_append_eval (xs ys : List Term) (env : ℕ → ℝ) :
    (Term.sumSquares (xs ++ ys)).eval env = (Term.sumSquares xs).eval env + (Term.sumSquares ys).eval env := by
  induction xs with
  | nil => simp [Term.sumSquares, Term.eval]
  | cons x xs ih =>
      simp only [List.cons_append, Term.sumSquares, Term.eval, ih]
      ring
private theorem sumRows_eval (n : ℕ) (row : ℕ → Term) (env : ℕ → ℝ) :
    (sumRows n row).eval env = (Term.sumSquares ((List.range n).map row)).eval env := by
  rw [sumRows, SumSquares.eval_accumulate]
  simp only [Term.eval, Int.cast_zero, zero_add]
noncomputable def rows (q : List Bool) := [circle false q, circle true q, radial q] ++
  ((List.range (centerCount q)).map (centerRow q)) ++ ((List.range (oldCount q)).map (anchorRow q)) ++
  [radiusRow q, gapRow q]

private theorem equation_eval (q : List Bool) (env : ℕ → ℝ) :
    (equation q).eval env = (Term.sumSquares (rows q)).eval env := by
  simp only [equation, Term.eval, Term.square, centerSquares, anchorSquares, sumRows_eval,
    rows, sumSquares_append_eval, Term.sumSquares]
  ring

theorem zero_rows (q : List Bool) (env : ℕ → ℝ) :
    (equation q).eval env = 0 ↔ ∀ t ∈ rows q, t.eval env = 0 := by
  rw [equation_eval]
  exact Term.eval_sumSquares_eq_zero_iff _ _

theorem zero_iff (q : List Bool) (env : ℕ → ℝ) : (equation q).eval env = 0 ↔
    (CanonicalAuxiliaryCandidateCover.equation (source false q)).eval (fun i => env (column 0 i)) = 0 ∧
    (CanonicalAuxiliaryCandidateCover.equation (source true q)).eval (fun i => env (column 1 i)) = 0 ∧
    (FormulaSignSlotRadialFormalInput.equation (source true q)).eval (fun i => env (column 2 i)) = 0 ∧
    (∀ i < centerCount q, env (centerVariable q i) = env (column 0 i)) ∧
    (∀ i < oldCount q, env (column 2 i) = env (column 1 i)) ∧
    env (radiusVariable q) * env radiusWitness ^ 2 = 1 ∧
    (env boundVariable - env (radiusVariable q)) * env gapWitness ^ 2 = 1 := by
  have HEmpty : ∀ t ∈ ([] : List Term), t.eval env = 0 := by simp
  rw [zero_rows]
  simp only [rows, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range]
  simp only [circle, radial, FormulaSignSlotRadialJointTermCopy.copy_eval]
  simp only [centerRow, anchorRow, radiusRow, gapRow, positiveRow,
    FormulaSignSlotRadialFormalInput.difference, Term.square, Term.eval,
    Int.cast_neg, Int.cast_one, neg_one_mul, ← pow_two,
    ← sub_eq_add_neg, sub_eq_zero, column, Bool.toNat, Bool.cond_true, Bool.cond_false, Nat.mul_zero, Nat.mul_one,
    Nat.add_zero, and_assoc, iff_true_intro HEmpty, and_true]

theorem parameter_positive (q : List Bool) (env : ℕ → ℝ) (h : (equation q).eval env = 0) :
    0 < env (radiusVariable q) ∧ env (radiusVariable q) < env boundVariable := by
  obtain ⟨_, _, _, _, _, HR, HG⟩ := (zero_iff q env).mp h
  have Hrp : 0 < env (radiusVariable q) := by nlinarith [sq_nonneg (env radiusWitness)]
  have Hgp : 0 < env boundVariable - env (radiusVariable q) := by nlinarith [sq_nonneg (env gapWitness)]
  exact ⟨Hrp, by linarith⟩

end LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
