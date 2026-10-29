/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialSystem

/-! # Flat polynomial systems for an arbitrary number of dependent stages

Each stage adds n variables and n equations, retaining every earlier variable.
Uniform row degree and coefficient mass bounds remain unchanged at any depth;
the total variable count is depth*n. Exact root and Jacobian criteria unfold
stage by stage. This is an algebraic foundation for uniform sampling bounds;
it does not yet construct native coefficient readers or a recursive cover.
-/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialTower
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

@[reducible] def Variables (n : ℕ) : ℕ → Type
  | 0 => Fin 0
  | k + 1 => Variables n k ⊕ Fin n

noncomputable instance variablesFintype (n k : ℕ) : Fintype (Variables n k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin 0))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Variables n k ⊕ Fin n))

noncomputable instance variablesDecidableEq (n k : ℕ) : DecidableEq (Variables n k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq (Fin 0))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Variables n k ⊕ Fin n))

theorem variables_card (n k : ℕ) : Fintype.card (Variables n k) = k * n := by
  induction k with
  | zero => simpa only [Variables, Nat.zero_mul] using Fintype.card_fin 0
  | succ k ih =>
    change Fintype.card (Variables n k ⊕ Fin n) = (k + 1) * n
    rw [Fintype.card_sum, ih, Fintype.card_fin, Nat.add_mul, Nat.one_mul]

theorem variables_card_le (n k : ℕ) (hk : k ≤ n) : Fintype.card (Variables n k) ≤ n ^ 2 := by
  rw [variables_card, pow_two]
  exact Nat.mul_le_mul_right n hk

structure Family (n : ℕ) (R : Type*) [CommRing R] where
  row : (k : ℕ) → Fin n → MvPolynomial (Variables n (k + 1)) R

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def system (F : Family n R) : (k : ℕ) → Variables n k → MvPolynomial (Variables n k) R
  | 0 => Fin.elim0
  | k + 1 => TriangularPolynomialSystem.append (system F k) (F.row k)

theorem degree_le (F : Family n R) (k D : ℕ)
    (h : ∀ j < k, ∀ i, (F.row j i).totalDegree ≤ D) :
    ∀ i, (system F k i).totalDegree ≤ D := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i
    exact (TriangularPolynomialSystem.degree_append (system F k) (F.row k) D D
      (ih (fun j hj => h j (by omega))) (h k (by omega)) i).trans_eq (Nat.max_self D)

theorem mass_le (F : Family n ℤ) (k B : ℕ)
    (h : ∀ j < k, ∀ i, MvMass.mass (F.row j i) ≤ B) :
    ∀ i, MvMass.mass (system F k i) ≤ B := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i
    exact (TriangularPolynomialSystem.mass_append (system F k) (F.row k) B B
      (ih (fun j hj => h j (by omega))) (h k (by omega)) i).trans_eq (Nat.max_self B)

variable {K : Type*} [CommRing K]

noncomputable def Roots (φ : R →+* K) (F : Family n R) : (k : ℕ) → (Variables n k → K) → Prop
  | 0, _ => True
  | k + 1, z => Roots φ F k (z ∘ Sum.inl) ∧ ∀ i, (F.row k i).eval₂ φ z = 0

theorem roots_iff (φ : R →+* K) (F : Family n R) (k : ℕ) (z : Variables n k → K) :
    (∀ i, (system F k i).eval₂ φ z = 0) ↔ Roots φ F k z := by
  induction k with
  | zero => exact iff_true_intro (fun i => Fin.elim0 i)
  | succ k ih =>
    rw [system, TriangularPolynomialSystem.roots_append, ih]
    rfl

noncomputable def Regular (φ : R →+* K) (F : Family n R) : (k : ℕ) → (Variables n k → K) → Prop
  | 0, _ => True
  | k + 1, z => Regular φ F k (z ∘ Sum.inl) ∧
      (TriangularPolynomialSystem.spatialJacobian (F.row k)).eval₂ φ z ≠ 0

theorem regular_iff [Nontrivial K] [NoZeroDivisors K] (φ : R →+* K) (F : Family n R)
    (k : ℕ) (z : Variables n k → K) :
    (TriangularPolynomialSystem.jacobian (system F k)).eval₂ φ z ≠ 0 ↔ Regular φ F k z := by
  induction k with
  | zero =>
    simp only [TriangularPolynomialSystem.jacobian, Matrix.det_isEmpty, eval₂_one, ne_eq,
      one_ne_zero, not_false_eq_true, Regular]
  | succ k ih =>
    exact (TriangularPolynomialSystem.regular_append_iff φ (system F k) (F.row k) z).trans
      (and_congr (ih (z ∘ Sum.inl)) Iff.rfl)

end LeanCanny.Algebra.TriangularPolynomialTower
