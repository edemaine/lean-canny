/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage
public import LeanCanny.Algebra.TriangularPolynomialRows

/-! # Shared ancestry for flat affine-height critical stages

Each stage uses n ambient coordinates and n+1 multipliers. Levels refer to
one or two earlier ambient blocks directly; no ancestral polynomial system
is duplicated. All rows retain the original source degree. This algebraic
tower does not yet supply native coefficient readers or a recursive cover.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalTower
open MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

def width (n : ℕ) : ℕ := n + (n + 1)

def blockEquiv (n : ℕ) : FlatAffineCriticalStage.Variables n ≃ Fin (width n) := finSumFinEquiv

abbrev Ancestors (n k : ℕ) := TriangularPolynomialTower.Variables (width n) k

def oldAmbient (k : ℕ) (j : Fin k) (i : Fin n) : Ancestors n k :=
  (TriangularPolynomialIndexing.enumerate (width n) k).symm
    (TriangularPolynomialRows.block (width n) j.val k j.isLt (blockEquiv n (Sum.inl i)))

theorem oldAmbient_index (k : ℕ) (j : Fin k) (i : Fin n) :
    (TriangularPolynomialIndexing.enumerate (width n) k (oldAmbient k j i)).val =
      j.val * width n + i.val := by
  rw [oldAmbient, Equiv.apply_symm_apply]
  rfl

inductive Level (n k : ℕ) (R : Type*) where
  | constant (c : R)
  | height (stage : Fin k) (a : Fin n → R)
  | midpoint (left right : Fin k) (a : Fin n → R)

noncomputable def Level.polynomial {k : ℕ} : Level n k R → MvPolynomial (Ancestors n k) R
  | .constant c => C c
  | .height j a => AffineHeightPolynomial.polynomial a (oldAmbient k j)
  | .midpoint l r a => AffineHeightPolynomial.midpointLevel a (oldAmbient k l) (oldAmbient k r)

theorem Level.degree_le [Nontrivial R] {k : ℕ} (b : Level n k R) : b.polynomial.totalDegree ≤ 1 := by
  cases b with
  | constant c => simp [Level.polynomial]
  | height j a => exact AffineHeightPolynomial.degree_le _ _
  | midpoint l r a => exact AffineHeightPolynomial.midpoint_degree _ _ _

def Level.Bounded {k : ℕ} (U B : ℕ) : Level n k ℤ → Prop
  | .constant c => c.natAbs ≤ B
  | .height _ a => ∀ i, (a i).natAbs ≤ U
  | .midpoint _ _ a => ∀ i, (a i).natAbs ≤ U

theorem Level.mass_le {k : ℕ} (b : Level n k ℤ) (U B : ℕ) (hb : b.Bounded U B) :
    MvMass.mass b.polynomial ≤ max B (2 * n * U) := by
  cases b with
  | constant c =>
    have hc : MvMass.mass (C c : MvPolynomial (Ancestors n k) ℤ) ≤ B := by
      simpa only [MvMass.C, Level.Bounded] using hb
    exact hc.trans (Nat.le_max_left _ _)
  | height j a =>
    exact (AffineHeightPolynomial.mass_le a _ U hb).trans
      ((calc
        n * U ≤ n * U + n * U := Nat.le_add_right _ _
        _ = 2 * n * U := by ring).trans (Nat.le_max_right _ _))
  | midpoint l r a => exact (AffineHeightPolynomial.midpoint_mass a _ _ U hb).trans (Nat.le_max_right _ _)

theorem Level.eval_height {K : Type*} [CommRing K] {k : ℕ} (φ : R →+* K)
    (j : Fin k) (a : Fin n → R) (z : Ancestors n k → K) :
    (Level.height j a).polynomial.eval₂ φ z = ∑ i, φ (a i) * z (oldAmbient k j i) :=
  AffineHeightPolynomial.eval φ a _ z

theorem Level.eval_midpoint {K : Type*} [CommRing K] {k : ℕ} (φ : R →+* K)
    (l r : Fin k) (a : Fin n → R) (z : Ancestors n k → K) :
    (Level.midpoint l r a).polynomial.eval₂ φ z =
      (∑ i, φ (a i) * z (oldAmbient k l i)) + ∑ i, φ (a i) * z (oldAmbient k r i) :=
  AffineHeightPolynomial.midpoint_eval φ a _ _ z

noncomputable def family (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → R) (b : (k : ℕ) → Fin n → Level n k R) :
    TriangularPolynomialTower.Family (width n) R where
  row k i := rename (Equiv.sumCongr (Equiv.refl (Ancestors n k)) (blockEquiv n))
    (FlatAffineCriticalStage.row p (s k) (a k) (fun j => (b k j).polynomial) ((blockEquiv n).symm i))

noncomputable def system (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → R) (b : (k : ℕ) → Fin n → Level n k R) (k : ℕ) :
    Fin (k * width n) → MvPolynomial (Fin (k * width n)) R :=
  TriangularPolynomialIndexing.system (family p s a b) k

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → R) (b : (k : ℕ) → Fin n → Level n k R)
    (k : ℕ) (i : Fin (k * width n)) :
    (system p s a b k i).totalDegree ≤ max p.totalDegree 1 := by
  apply TriangularPolynomialIndexing.degree_le
  intro j _ r
  exact (totalDegree_rename_le _ _).trans
    (FlatAffineCriticalStage.degree_le p (s j) (a j) _ (fun i => (b j i).degree_le) _)

theorem mass_le (p : MvPolynomial (Fin n) ℤ) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (k : ℕ) → Fin n → Level n k ℤ)
    (k U B : ℕ) (ha : ∀ j < k, ∀ r i, (a j r i).natAbs ≤ U)
    (hb : ∀ j < k, ∀ i, (b j i).Bounded U B) (i : Fin (k * width n)) :
    MvMass.mass (system p s a b k i) ≤ FlatAffineCriticalStage.massBound p U (max B (2 * n * U)) := by
  apply TriangularPolynomialIndexing.mass_le
  intro j hj r
  exact (MvMass.rename_le _ _).trans
    (FlatAffineCriticalStage.mass_le p (s j) (a j) _ U _ (ha j hj)
      (fun i => (b j i).mass_le U B (hb j hj i)) _)

theorem variables_le (k : ℕ) (hk : k ≤ n) : k * width n ≤ n * (2 * n + 1) := by
  have hw : width n = 2 * n + 1 := by unfold width; omega
  rw [hw]
  exact Nat.mul_le_mul_right _ hk

theorem stage_roots_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → R) (b : (k : ℕ) → Fin n → Level n k R)
    (k : ℕ) (x : Ancestors n k → K) (y : FlatAffineCriticalStage.Variables n → K) :
    (∀ i, ((family p s a b).row k i).eval₂ φ (Sum.elim x (y ∘ (blockEquiv n).symm)) = 0) ↔
      ∀ j, (FlatAffineCriticalStage.row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
        (Sum.elim x y) = 0 := by
  simp only [family, eval₂_rename]
  have he : (Sum.elim x (y ∘ (blockEquiv n).symm)) ∘
      (Equiv.sumCongr (Equiv.refl (Ancestors n k)) (blockEquiv n)) = Sum.elim x y := by
    funext v
    cases v <;> simp
  rw [he]
  exact (blockEquiv n).symm.forall_congr (fun _ => Iff.rfl)

end LeanCanny.Algebra.FlatAffineCriticalTower
