/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerTower

/-! # Mixed degree bounds from the affine source degree -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

lemma gradient_degree_le (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (t : Fin k) (i : Fin n) :
    (gradient p D a t i).totalDegree ≤ D - 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_rename_le _ _).trans ((PartialDerivativeDegree.degree_le p i).trans (Nat.sub_le_sub_right hp 1))
  · apply IsHomogeneous.totalDegree_le
    apply IsHomogeneous.sum
    intro r _
    simpa only [one_mul] using ((isHomogeneous_X (R := ℤ) (multiplier t r)).pow (D - 1)).C_mul (a t r i)

lemma row_degree_le (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (s : Fin k → Finset (Fin n)) (a : Fin k → Fin (n + 1) → Fin n → ℤ)
    (b : (t : Fin k) → Fin n → Level n t.val ℤ) (t : Fin k) (j : Variables n) :
    (row p D s a b t j).totalDegree ≤ rowDegree D j := by
  cases j with
  | inl i => exact gradient_degree_le p D hp a t i
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · exact (totalDegree_rename_le _ _).trans hp
    · simp only [row, Fin.cases_succ, rowDegree]
      split_ifs
      · apply (totalDegree_sub _ _).trans (max_le (height_homogeneous _ _).totalDegree_le ?_)
        exact (totalDegree_add _ _).trans (max_le (levelLinear_homogeneous _ _).totalDegree_le
          (by change (C (levelConstant t (b t j)) : MvPolynomial (Index n k) ℤ).totalDegree ≤ 1; simp only [totalDegree_C]; omega))
      · simp

lemma system_degree_le (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (s : Fin k → Finset (Fin n)) (a : Fin k → Fin (n + 1) → Fin n → ℤ)
    (b : (t : Fin k) → Fin n → Level n t.val ℤ) (j : Index n k) :
    (system p D s a b j).totalDegree ≤ degrees D j :=
  row_degree_le p D hp s a b _ _

end LeanCanny.Algebra.FlatAffinePowerTower
