/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalCoarsening
public import LeanCanny.Algebra.FlatAffineTowerRegularity

/-! # Coarsening the last slice in a shared critical tower

The preceding stages retain their equations. A zero objective multiplier in
the last stage permits removing the varied height and making its normal the
new objective. The resulting complete root retains the entire prefix and
the newest ambient point.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineTowerCoarsening
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R K : Type*} [CommRing R] [CommRing K]

def active (s : ℕ → Finset (Fin n)) (k : ℕ) (h : Fin n) (t : ℕ) : Finset (Fin n) :=
  if t = k then (s t).erase h else s t

def directions (a : ℕ → Fin (n + 1) → Fin n → R) (k : ℕ) (h : Fin n) (t : ℕ) :
    Fin (n + 1) → Fin n → R :=
  if t = k then FlatAffineCriticalCoarsening.table (a t) h else a t

theorem prefix_roots (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (k : ℕ) (h : Fin n)
    (x : Fin (k * width n) → K)
    (hx : ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ φ x = 0) :
    ∀ i, (FlatAffineCriticalTower.system p (active s k h) (directions a k h) b k i).eval₂ φ x = 0 := by
  apply (FlatAffineTowerRegularity.roots_iff_stages φ p _ _ b k x).mpr
  intro t ht i
  simpa only [active, directions, ite_eq_right (Nat.ne_of_lt ht)] using
    (FlatAffineTowerRegularity.roots_iff_stages φ p s a b k x).mp hx t ht i

noncomputable def point (k : ℕ) (h : Fin n) (x : Fin (k * width n) → K)
    (y : Fin n → K) (mu : Fin (n + 1) → K) : Fin ((k + 1) * width n) → K :=
  FlatAffineTowerRegularity.appendPoint k x
    (Sum.elim y (FlatAffineCriticalCoarsening.multipliers mu h))

theorem point_prefix (k : ℕ) (h : Fin n) (x : Fin (k * width n) → K)
    (y : Fin n → K) (mu : Fin (n + 1) → K) :
    point k h x y mu ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega) = x :=
  FlatAffineTowerRegularity.appendPoint_prefix k x _

theorem point_current (k : ℕ) (h : Fin n) (x : Fin (k * width n) → K)
    (y : Fin n → K) (mu : Fin (n + 1) → K) (i : Fin n) :
    point k h x y mu (TriangularPolynomialRows.block (width n) k (k + 1) (by omega)
      (blockEquiv n (Sum.inl i))) = y i :=
  FlatAffineTowerRegularity.appendPoint_new k x _ (Sum.inl i)

theorem roots (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (k : ℕ) (h : Fin n)
    (x : Fin (k * width n) → K) (y : Fin n → K) (mu : Fin (n + 1) → K)
    (hx : ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ φ x = 0)
    (hz : mu 0 = 0)
    (hy : ∀ j, j ≠ Sum.inr h.succ →
      (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
        (Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) (Sum.elim y mu)) = 0) :
    ∀ i, (FlatAffineCriticalTower.system p (active s k h) (directions a k h) b (k + 1) i).eval₂ φ
      (point k h x y mu) = 0 := by
  apply (FlatAffineTowerRegularity.roots_appendPoint_iff φ p (active s k h) (directions a k h) b k x _).mpr
  refine ⟨prefix_roots φ p s a b k h x hx, ?_⟩
  simpa only [active, directions, ite_true] using
    FlatAffineCriticalCoarsening.roots φ p (s k) (a k) (fun i => (b k i).polynomial) h
      (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y mu hz hy

end LeanCanny.Algebra.FlatAffineTowerCoarsening
