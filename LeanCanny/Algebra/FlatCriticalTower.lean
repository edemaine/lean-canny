/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatCriticalStage
public import LeanCanny.Algebra.TriangularPolynomialIndexing

/-! # A flat tower of critical stages for one original polynomial

Each stage stores a complete ambient tuple. Coordinates outside its selected
free set copy the preceding tuple, starting from zero. All critical rows use
the same original source. Indexed row bounds are independent of tower depth.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatCriticalTower
open MvPolynomial TriangularPolynomialTower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

def previous (n : ℕ) : (k : ℕ) → Fin n → Option (Variables n k)
  | 0, _ => none
  | _ + 1, i => some (Sum.inr i)

noncomputable def family (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) : Family n R where
  row k := FlatCriticalStage.row p (s k) (base k) (v k) (previous n k)

noncomputable def system (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (k : ℕ) :
    Fin (k * n) → MvPolynomial (Fin (k * n)) R :=
  TriangularPolynomialIndexing.system (family p s base v) k

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (k : ℕ) (i : Fin (k * n)) :
    (system p s base v k i).totalDegree ≤ max p.totalDegree 1 :=
  TriangularPolynomialIndexing.degree_le _ k _
    (fun _ _ _ => FlatCriticalStage.degree_le _ _ _ _ _ _) i

theorem mass_le (p : MvPolynomial (Fin n) ℤ) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → ℤ) (k U : ℕ)
    (hv : ∀ j < k, ∀ i, (v j i).natAbs ≤ U) (i : Fin (k * n)) :
    MvMass.mass (system p s base v k i) ≤ max 2 ((p.totalDegree + 1) * (U + 1) * MvMass.mass p) :=
  TriangularPolynomialIndexing.mass_le _ k _
    (fun j hj i => FlatCriticalStage.mass_le _ _ _ _ _ U (hv j hj) i) i

variable {K : Type*} [CommRing K]

def current (n : ℕ) : (k : ℕ) → (Variables n k → K) → Fin n → K
  | 0, _, _ => 0
  | _ + 1, z, i => z (Sum.inr i)

theorem previous_value (k : ℕ) (z : Variables n (k + 1) → K) (i : Fin n) :
    FlatCriticalStage.oldValue z (previous n k i) = current n k (z ∘ Sum.inl) i := by
  cases k <;> rfl

noncomputable def Steps (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) : (k : ℕ) → (Variables n k → K) → Prop
  | 0, _ => True
  | k + 1, z => Steps φ p s base v k (z ∘ Sum.inl) ∧
      (∀ i ∈ s k, (ProjectionCriticalFamily.spatialEquation p (base k) (v k) i).eval₂ φ (z ∘ Sum.inr) = 0) ∧
        ∀ i, i ∉ s k → z (Sum.inr i) = current n k (z ∘ Sum.inl) i

theorem steps_iff (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (k : ℕ) (z : Variables n k → K) :
    Roots φ (family p s base v) k z ↔ Steps φ p s base v k z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (Roots φ (family p s base v) k (z ∘ Sum.inl) ∧
      ∀ i, (FlatCriticalStage.row p (s k) (base k) (v k) (previous n k) i).eval₂ φ z = 0) ↔ _
    rw [ih, FlatCriticalStage.roots_iff]
    simp only [previous_value, Steps]

theorem roots_iff (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (k : ℕ) (z : Fin (k * n) → K) :
    (∀ i, (system p s base v k i).eval₂ φ z = 0) ↔
      Steps φ p s base v k (z ∘ TriangularPolynomialIndexing.enumerate n k) :=
  (TriangularPolynomialIndexing.roots_iff φ _ k z).trans (steps_iff φ p s base v k _)

end LeanCanny.Algebra.FlatCriticalTower
