/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialTower
public import LeanCanny.Algebra.PolynomialSystemReindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Explicit finite indices for flat polynomial towers

The recursive sum of stage variables is enumerated in stage order without
choosing an arbitrary finite-type equivalence. Indexing preserves all root,
Jacobian, row degree, and coefficient-mass statements.
-/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialIndexing
open MvPolynomial TriangularPolynomialTower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def enumerate (n : ℕ) : (k : ℕ) → Variables n k ≃ Fin (k * n)
  | 0 => (finCongr (Nat.zero_mul n)).symm
  | k + 1 => ((Equiv.sumCongr (enumerate n k) (Equiv.refl (Fin n))).trans finSumFinEquiv).trans
      (finCongr (Nat.succ_mul k n).symm)

theorem enumerate_old (n k : ℕ) (i : Variables n k) :
    (enumerate n (k + 1) (Sum.inl i)).val = (enumerate n k i).val := rfl

theorem enumerate_new (n k : ℕ) (i : Fin n) :
    (enumerate n (k + 1) (Sum.inr i)).val = k * n + i.val := rfl

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def system (F : Family n R) (k : ℕ) : Fin (k * n) → MvPolynomial (Fin (k * n)) R :=
  PolynomialSystemReindex.system (enumerate n k) (TriangularPolynomialTower.system F k)

theorem degree_le (F : Family n R) (k D : ℕ)
    (h : ∀ j < k, ∀ i, (F.row j i).totalDegree ≤ D) (i : Fin (k * n)) :
    (system F k i).totalDegree ≤ D :=
  PolynomialSystemReindex.degree_le _ _ D (TriangularPolynomialTower.degree_le F k D h) i

theorem mass_le (F : Family n ℤ) (k B : ℕ)
    (h : ∀ j < k, ∀ i, MvMass.mass (F.row j i) ≤ B) (i : Fin (k * n)) :
    MvMass.mass (system F k i) ≤ B :=
  PolynomialSystemReindex.mass_le _ _ B (TriangularPolynomialTower.mass_le F k B h) i

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K) (F : Family n R)
    (k : ℕ) (x : Fin (k * n) → K) :
    (∀ i, (system F k i).eval₂ φ x = 0) ↔ Roots φ F k (x ∘ enumerate n k) :=
  (PolynomialSystemReindex.roots_iff φ _ _ x).trans (TriangularPolynomialTower.roots_iff φ F k _)

theorem regular_iff {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (φ : R →+* K) (F : Family n R) (k : ℕ) (x : Fin (k * n) → K) :
    (TriangularPolynomialSystem.jacobian (system F k)).eval₂ φ x ≠ 0 ↔
      Regular φ F k (x ∘ enumerate n k) :=
  (PolynomialSystemReindex.regular_iff φ _ _ x).trans (TriangularPolynomialTower.regular_iff φ F k _)

end LeanCanny.Algebra.TriangularPolynomialIndexing
