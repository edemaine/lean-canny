/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower
public import LeanCanny.Algebra.PositivePolynomialSystem
public import LeanCanny.Geometry.TriangularPolynomialRegularity

/-! # Positive-dimensional flat systems, including the zero-depth seed

One dummy coordinate, fixed at zero, makes the full system nonempty at every
input. Root extension is unique; analytic regularity is preserved. The same
row degree and mass budgets apply, and the additional dimension is native.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositive
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MvPolynomial
open FlatFullSourceTower (Inputs degree mass)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceTower.system

def count (F : Inputs) (u : List Bool) : ℕ := FlatFullSourceTower.count F u + 1

theorem count_pos (F : Inputs) (u : List Bool) : 0 < count F u := Nat.zero_lt_succ _
theorem count_le (F : Inputs) (u : List Bool) (h : F.depth u ≤ FlatFullSourceTower.arity F u) :
    count F u ≤ FlatFullSourceTower.arity F u ^ 2 + 1 :=
  Nat.add_le_add_right (FlatFullSourceTower.count_le F u h) 1

theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) :=
  (FlatFullSourceTower.count_unary h).add (UnaryFn.const 1)

noncomputable def system (F : Inputs) (u : List Bool) :
    Fin (count F u) → MvPolynomial (Fin (count F u)) ℤ :=
  PositivePolynomialSystem.system (FlatFullSourceTower.system F u)

theorem roots_iff {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (F : Inputs) (u : List Bool) (z : Fin (count F u) → K) :
    (∀ j, (system F u j).eval₂ φ z = 0) ↔
      (∀ i, (FlatFullSourceTower.system F u i).eval₂ φ (z ∘ Fin.castSucc) = 0) ∧
        z (Fin.last (FlatFullSourceTower.count F u)) = 0 :=
  PositivePolynomialSystem.roots_iff φ _ z

theorem roots_extend_iff {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (F : Inputs) (u : List Bool) (x : Fin (FlatFullSourceTower.count F u) → K) :
    (∀ j, (system F u j).eval₂ φ (PositivePolynomialSystem.extend x) = 0) ↔
      ∀ i, (FlatFullSourceTower.system F u i).eval₂ φ x = 0 :=
  PositivePolynomialSystem.roots_extend_iff φ _ x

theorem extension_unique {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (F : Inputs) (u : List Bool) (z : Fin (count F u) → K)
    (hz : ∀ j, (system F u j).eval₂ φ z = 0) :
    PositivePolynomialSystem.extend (z ∘ Fin.castSucc) = z :=
  PositivePolynomialSystem.eq_extend z ((roots_iff φ F u z).mp hz).2

theorem analytic_regular_iff (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ) :
    (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible ↔
      (fderiv ℝ (fun y => fun i => (FlatFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) y)
        (z ∘ Fin.castSucc)).IsInvertible := by
  rw [TriangularPolynomialRegularity.analytic_iff, TriangularPolynomialRegularity.analytic_iff]
  exact PositivePolynomialSystem.regular_iff (Int.castRingHom ℝ) _ z

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (system F u i).totalDegree ≤ degree F u :=
  PositivePolynomialSystem.degree_le _ _ (FlatFullSourceTower.degree_pos F u)
    (FlatFullSourceTower.polynomial_degree F u) i

theorem polynomial_mass (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    MvMass.mass (system F u i) ≤ 2 ^ mass F u :=
  PositivePolynomialSystem.mass_le _ _ (Nat.two_pow_pos _) (FlatFullSourceTower.polynomial_mass F u) i

end LeanCanny.Encoding.FlatFullSourcePositive
