/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerDegreeBounds
public import LeanCanny.Encoding.FlatAffinePowerDegree
public import LeanCanny.Encoding.FlatAffinePowerMass

/-! # Actual mixed row degrees and uniform sampling bounds -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma raw_polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourceTower.count F u)) :
    (rawSystem F u i).totalDegree ≤ FlatAffinePowerTower.degrees
      (n := FlatAffineFullSourceTower.arity F u) (k := F.depth u) (FlatAffinePowerControls.degree F u) i :=
  FlatAffinePowerTower.system_degree_le _ _ (BoundedFullCriticalSamples.source_degree F.source u) _ _ _ i

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    (system F u i).totalDegree ≤ degree F u i := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [system, PositivePolynomialSystem.new_row, degree, Fin.lastCases_last, totalDegree_X, le_refl]
  · simp only [system, PositivePolynomialSystem.old_row, degree, Fin.lastCases_castSucc]
    exact (totalDegree_rename_le _ _).trans (raw_polynomial_degree F u i)

lemma degree_le (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    degree F u i ≤ FlatAffineFullSourceTower.degree F u := by
  rw [degree_numeric]
  change (if _ then (if _ then _ else if _ then _ else _) else _) ≤ FlatAffinePowerControls.degree F u + 1
  split_ifs
  · exact (Nat.sub_le _ _).trans (Nat.le_succ _)
  · exact Nat.le_succ _
  all_goals exact Nat.succ_le_succ (Nat.zero_le _)

lemma uniform_polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    (system F u i).totalDegree ≤ FlatAffineFullSourceTower.degree F u :=
  (polynomial_degree F u i).trans (degree_le F u i)

end LeanCanny.Encoding.FlatAffinePowerPositive
