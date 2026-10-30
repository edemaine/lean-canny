/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialIndexing

/-! # Equality of a polynomial prefix from its retained stage records -/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialTower
open MvPolynomial
variable {n : ℕ} {R : Type*} [CommRing R]

theorem system_congr (F G : Family n R) (k : ℕ)
    (h : ∀ j < k, F.row j = G.row j) : system F k = system G k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [system, system, ih (fun j hj => h j (by omega)), h k (by omega)]

end LeanCanny.Algebra.TriangularPolynomialTower

namespace LeanCanny.Algebra.TriangularPolynomialIndexing
open MvPolynomial
variable {n : ℕ} {R : Type*} [CommRing R]

theorem system_congr (F G : TriangularPolynomialTower.Family n R) (k : ℕ)
    (h : ∀ j < k, F.row j = G.row j) : system F k = system G k :=
  congrArg (PolynomialSystemReindex.system (enumerate n k)) (TriangularPolynomialTower.system_congr F G k h)

end LeanCanny.Algebra.TriangularPolynomialIndexing
