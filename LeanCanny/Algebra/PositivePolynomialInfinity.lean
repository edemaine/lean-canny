/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationRename
public import LeanCanny.Algebra.PositivePolynomialSystem
public import LeanCanny.Algebra.AffineFiniteCoordinates

/-! # Positive completion preserves exclusion of roots at infinity

The added coordinate has degree one and is forced to zero. Homogenization
of every old row commutes with the inclusion of the old coordinates.
-/

@[expose] public section
namespace LeanCanny.Algebra.PositivePolynomialSystem
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem noInfinity (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (h : AffineFiniteCoordinates.NoInfinity p d) :
    AffineFiniteCoordinates.NoInfinity (system p) (Fin.lastCases 1 d) := by
  intro y hy hz
  have hlast := hz (Fin.last n)
  simp only [new_row, Fin.lastCases_last] at hlast
  have he : homogenize (fun _ => 1) 1 (X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℤ) =
      X (some (Fin.last n)) := by
    simpa only [pow_one] using homogenize_X_pow (R := ℤ) (Fin.last n) 1
  rw [he, eval₂_X] at hlast
  have hold : y ∘ Option.map Fin.castSucc = 0 := by
    apply h
    · exact hy
    · intro i
      have hi := hz i.castSucc
      simp only [old_row, Fin.lastCases_castSucc] at hi
      rw [homogenize_rename, eval₂_rename] at hi
      exact hi
  funext j
  cases j with
  | none => exact hy
  | some i =>
    refine Fin.lastCases hlast (fun i => ?_) i
    exact congrFun hold (some i)

end LeanCanny.Algebra.PositivePolynomialSystem
