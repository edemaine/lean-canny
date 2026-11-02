/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerFamilyDispatcher
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFamily
/-! # Original integer leaves of the actual creating framed instruction -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedIntegerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open scoped Classical

noncomputable def polynomial (P : Parameters) (D : Plan P) (key : List Bool) : Polynomial ℤ :=
  match (instruction P D key).command with
  | .integer p _ _ => p
  | _ => Polynomial.X

theorem polynomial_actual (P : Parameters) (D : Plan P) (key : List Bool)
    (p : Polynomial ℤ) (hp : p≠0) (hd : p.natDegree≤2^P.width (pairFst key))
    (hc : (instruction P D key).command=.integer p hp hd) : polynomial P D key=p := by
  unfold polynomial
  rw [hc]

theorem polynomial_ne_zero (P : Parameters) (D : Plan P) (key : List Bool) : polynomial P D key≠0 := by
  unfold polynomial
  split
  · assumption
  · exact Polynomial.X_ne_zero

theorem degree_cap (P : Parameters) (D : Plan P) (key : List Bool) :
    (polynomial P D key).natDegree≤2^P.width (pairFst key) := by
  unfold polynomial
  split
  · assumption
  · rw [Polynomial.natDegree_X]
    exact Nat.one_le_two_pow

end LeanCanny.Algebra.IntegralMixedFramedIntegerBits
