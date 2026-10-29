/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineTowerRegularity
public import LeanCanny.Geometry.FlatAffineCriticalGeometry
public import LeanCanny.Geometry.FlatAffineSliceRegularity

/-! # Analytic regularity of the entire affine tower

The full derivative is invertible exactly when every actual Lagrange stage
has an invertible derivative with ancestry frozen. This criterion preserves
all earlier regular prefixes, including the empty prefix.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineTowerGeometry
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalTower FlatAffineTowerRegularity
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : Type*} [CommRing R]
variable (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
  (a : ℕ → Fin (n + 1) → Fin n → R) (b : (j : ℕ) → Fin n → Level n j R)

theorem stage_analytic_iff (j k : ℕ) (hj : j < k) (z : Fin (k * width n) → ℝ) :
    (fderiv ℝ (fun v => fun i =>
      (FlatAffineCriticalStage.row p (s j) (a j) (fun i => (b j i).polynomial) i).eval₂ φ
        (Sum.elim (stagePoint j k hj z ∘ Sum.inl) v))
      (stagePoint j k hj z ∘ Sum.inr)).IsInvertible ↔
      (FlatAffineCriticalRegularity.matrix φ p (s j) (a j) (fun i => (b j i).polynomial)
        (stagePoint j k hj z)).det ≠ 0 := by
  have he : Sum.elim (stagePoint j k hj z ∘ Sum.inl) (stagePoint j k hj z ∘ Sum.inr) =
      stagePoint j k hj z := by funext v; cases v <;> rfl
  have H := FlatAffineCriticalGeometry.analytic_iff φ p (s j) (a j) (fun i => (b j i).polynomial)
    (stagePoint j k hj z ∘ Sum.inl) (stagePoint j k hj z ∘ Sum.inr)
  rw [he] at H
  exact H

theorem analytic_iff_stages (k : ℕ) (z : Fin (k * width n) → ℝ) :
    (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) z).IsInvertible ↔
      ∀ j (hj : j < k),
        (fderiv ℝ (fun v => fun i =>
          (FlatAffineCriticalStage.row p (s j) (a j) (fun i => (b j i).polynomial) i).eval₂ φ
            (Sum.elim (stagePoint j k hj z ∘ Sum.inl) v))
          (stagePoint j k hj z ∘ Sum.inr)).IsInvertible := by
  rw [TriangularPolynomialRegularity.analytic_iff, FlatAffineTowerRegularity.regular_iff_stages]
  constructor
  · intro h j hj
    exact (stage_analytic_iff φ p s a b j k hj z).mpr (h j hj)
  · intro h j hj
    exact (stage_analytic_iff φ p s a b j k hj z).mp (h j hj)

theorem analytic_prefix (j k : ℕ) (hj : j ≤ k) (z : Fin (k * width n) → ℝ)
    (hz : (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) z).IsInvertible) :
    (fderiv ℝ (fun v => fun i => (system p s a b j i).eval₂ φ v)
      (z ∘ TriangularPolynomialRows.prefixIndex (width n) j k hj)).IsInvertible := by
  apply (TriangularPolynomialRegularity.analytic_iff φ _ _).mpr
  exact FlatAffineTowerRegularity.regular_prefix φ p s a b j k hj z
    ((TriangularPolynomialRegularity.analytic_iff φ _ _).mp hz)

theorem analytic_appendPoint_iff (k : ℕ) (x : Fin (k * width n) → ℝ)
    (y : FlatAffineCriticalStage.Variables n → ℝ) :
    (fderiv ℝ (fun v => fun i => (system p s a b (k + 1) i).eval₂ φ v) (appendPoint k x y)).IsInvertible ↔
      (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) x).IsInvertible ∧
      (fderiv ℝ (fun v => fun i =>
        (FlatAffineCriticalStage.row p (s k) (a k) (fun i => (b k i).polynomial) i).eval₂ φ
          (Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) v)) y).IsInvertible := by
  rw [TriangularPolynomialRegularity.analytic_iff, FlatAffineTowerRegularity.regular_appendPoint_iff,
    ← TriangularPolynomialRegularity.analytic_iff,
    ← FlatAffineCriticalGeometry.analytic_iff φ p (s k) (a k) (fun i => (b k i).polynomial)
      (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y]

theorem slice_surjective (k : ℕ) (z : Fin (k * width n) → ℝ)
    (hreg : (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) z).IsInvertible)
    (j : ℕ) (hj : j < k) :
    Function.Surjective (FlatAffineCriticalExtremum.derivative φ p (s j) (a j)
      (stagePoint j k hj z ∘ FlatAffineCriticalStage.ambient)) :=
  FlatAffineSliceRegularity.surjective φ p (s j) (a j) (fun i => (b j i).polynomial)
    (stagePoint j k hj z) ((FlatAffineTowerRegularity.regular_iff_stages φ p s a b k z).mp
      ((TriangularPolynomialRegularity.analytic_iff φ _ _).mp hreg) j hj)

theorem active_card_lt (k : ℕ) (z : Fin (k * width n) → ℝ)
    (hreg : (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) z).IsInvertible)
    (j : ℕ) (hj : j < k) : (s j).card < n :=
  FlatAffineSliceRegularity.active_card_lt φ p (s j) (a j) (fun i => (b j i).polynomial)
    (stagePoint j k hj z) ((FlatAffineTowerRegularity.regular_iff_stages φ p s a b k z).mp
      ((TriangularPolynomialRegularity.analytic_iff φ _ _).mp hreg) j hj)

theorem critical_tangent (k : ℕ) (z : Fin (k * width n) → ℝ)
    (hz : ∀ i, (system p s a b k i).eval₂ φ z = 0)
    (hreg : (fderiv ℝ (fun v => fun i => (system p s a b k i).eval₂ φ v) z).IsInvertible)
    (j : ℕ) (hj : j < k) (d : Fin n → ℝ)
    (hp : fderiv ℝ (fun v => p.eval₂ φ v)
      (stagePoint j k hj z ∘ FlatAffineCriticalStage.ambient) d = 0)
    (ha : ∀ r ∈ s j, ∑ i, φ (a j r.succ i) * d i = 0) :
    ∑ i, φ (a j 0 i) * d i = 0 := by
  apply FlatAffineCriticalRegularity.tangent_height_zero φ p (s j) (a j) (fun i => (b j i).polynomial)
    (stagePoint j k hj z) ((FlatAffineTowerRegularity.roots_iff_stages φ p s a b k z).mp hz j hj)
    ((FlatAffineTowerRegularity.regular_iff_stages φ p s a b k z).mp
      ((TriangularPolynomialRegularity.analytic_iff φ _ _).mp hreg) j hj) d _ ha
  rw [PolynomialCalculus.fderiv_eq, PolynomialCalculus.derivative_apply] at hp
  exact hp

end LeanCanny.Geometry.FlatAffineTowerGeometry
