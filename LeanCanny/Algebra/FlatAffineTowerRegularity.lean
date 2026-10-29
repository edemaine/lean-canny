/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalTower
public import LeanCanny.Algebra.FlatAffineCriticalRegularity
public import LeanCanny.Algebra.SpatialPolynomialReindex
public import LeanCanny.Algebra.TriangularPolynomialStageRegularity

/-! # Actual frozen-stage regularity of complete affine towers

The indexed tower is nonsingular exactly when every frozen affine Lagrange
stage is nonsingular. Every earlier prefix of a regular root remains a
regular root. At full regular roots every stage has a nonzero new multiplier.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineTowerRegularity
open MvPolynomial FlatAffineCriticalTower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R K : Type*}

noncomputable def stagePoint (j k : ℕ) (hj : j < k) (z : Fin (k * width n) → K) :
    (Ancestors n j ⊕ FlatAffineCriticalStage.Variables n) → K :=
  (z ∘ TriangularPolynomialRows.embedding (width n) j k hj) ∘
    Equiv.sumCongr (Equiv.refl (Ancestors n j)) (blockEquiv n)

noncomputable def appendPoint (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) : Fin ((k + 1) * width n) → K :=
  TriangularPolynomialStageRegularity.appendPoint k x (y ∘ (blockEquiv n).symm)

theorem appendPoint_prefix (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) :
    appendPoint k x y ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega) = x :=
  TriangularPolynomialStageRegularity.appendPoint_prefix k x _

theorem stagePoint_appendPoint (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) :
    stagePoint k (k + 1) (by omega) (appendPoint k x y) =
      Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y := by
  have he : TriangularPolynomialRows.embedding (width n) k (k + 1) (by omega) =
      TriangularPolynomialIndexing.enumerate (width n) (k + 1) := by funext v; exact Fin.ext rfl
  unfold stagePoint appendPoint
  rw [he, TriangularPolynomialStageRegularity.appendPoint_enumerate]
  funext v
  cases v <;> simp

theorem appendPoint_new (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) (v : FlatAffineCriticalStage.Variables n) :
    appendPoint k x y (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)) = y v := by
  have he : TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v) =
      TriangularPolynomialIndexing.enumerate (width n) (k + 1) (Sum.inr (blockEquiv n v)) := Fin.ext rfl
  rw [he]
  simp only [appendPoint, TriangularPolynomialStageRegularity.appendPoint, Function.comp_apply,
    Equiv.symm_apply_apply, Sum.elim_inr]

variable [CommRing R] [CommRing K]
variable (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
  (a : ℕ → Fin (n + 1) → Fin n → R) (b : (j : ℕ) → Fin n → Level n j R)

theorem stage_roots_iff (j k : ℕ) (hj : j < k) (z : Fin (k * width n) → K) :
    (∀ i, ((family p s a b).row j i).eval₂ φ
      (z ∘ TriangularPolynomialRows.embedding (width n) j k hj) = 0) ↔
      ∀ i, (FlatAffineCriticalStage.row p (s j) (a j) (fun i => (b j i).polynomial) i).eval₂ φ
        (stagePoint j k hj z) = 0 :=
  SpatialPolynomialReindex.roots_iff φ (blockEquiv n) _ _

theorem family_matrix_det (j : ℕ) (v : Ancestors n (j + 1) → K) :
    (TriangularPolynomialSystem.spatialJacobian ((family p s a b).row j)).eval₂ φ v =
      (FlatAffineCriticalRegularity.matrix φ p (s j) (a j) (fun i => (b j i).polynomial)
        (v ∘ Equiv.sumCongr (Equiv.refl (Ancestors n j)) (blockEquiv n))).det := by
  change (TriangularPolynomialSystem.spatialJacobian
    (SpatialPolynomialReindex.system (blockEquiv n)
      (FlatAffineCriticalStage.row p (s j) (a j) (fun i => (b j i).polynomial)))).eval₂ φ _ = _
  rw [SpatialPolynomialReindex.eval_spatialJacobian]
  change (eval₂Hom φ _) (Matrix.det _) = _
  rw [RingHom.map_det]
  rfl

theorem stage_matrix_det (j k : ℕ) (hj : j < k) (z : Fin (k * width n) → K) :
    (TriangularPolynomialSystem.spatialJacobian ((family p s a b).row j)).eval₂ φ
        (z ∘ TriangularPolynomialRows.embedding (width n) j k hj) =
      (FlatAffineCriticalRegularity.matrix φ p (s j) (a j) (fun i => (b j i).polynomial)
        (stagePoint j k hj z)).det := family_matrix_det φ p s a b j _

theorem roots_iff_stages (k : ℕ) (z : Fin (k * width n) → K) :
    (∀ i, (system p s a b k i).eval₂ φ z = 0) ↔
      ∀ j (hj : j < k) i,
        (FlatAffineCriticalStage.row p (s j) (a j) (fun i => (b j i).polynomial) i).eval₂ φ
          (stagePoint j k hj z) = 0 := by
  rw [system, TriangularPolynomialStageRegularity.roots_iff_stages]
  constructor
  · intro h j hj
    exact (stage_roots_iff φ p s a b j k hj z).mp (h j hj)
  · intro h j hj
    exact (stage_roots_iff φ p s a b j k hj z).mpr (h j hj)

theorem roots_prefix (j k : ℕ) (hj : j ≤ k) (z : Fin (k * width n) → K)
    (hz : ∀ i, (system p s a b k i).eval₂ φ z = 0) :
    ∀ i, (system p s a b j i).eval₂ φ
      (z ∘ TriangularPolynomialRows.prefixIndex (width n) j k hj) = 0 :=
  TriangularPolynomialStageRegularity.roots_prefix φ (family p s a b) j k hj z hz

theorem roots_appendPoint_iff (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) :
    (∀ i, (system p s a b (k + 1) i).eval₂ φ (appendPoint k x y) = 0) ↔
      (∀ i, (system p s a b k i).eval₂ φ x = 0) ∧
      ∀ i, (FlatAffineCriticalStage.row p (s k) (a k) (fun i => (b k i).polynomial) i).eval₂ φ
        (Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y) = 0 := by
  rw [system, appendPoint, TriangularPolynomialStageRegularity.roots_appendPoint_iff,
    FlatAffineCriticalTower.stage_roots_iff]
  rfl

variable [Nontrivial K] [NoZeroDivisors K]

theorem regular_iff_stages (k : ℕ) (z : Fin (k * width n) → K) :
    (TriangularPolynomialSystem.jacobian (system p s a b k)).eval₂ φ z ≠ 0 ↔
      ∀ j (hj : j < k),
        (FlatAffineCriticalRegularity.matrix φ p (s j) (a j) (fun i => (b j i).polynomial)
          (stagePoint j k hj z)).det ≠ 0 := by
  rw [system, TriangularPolynomialStageRegularity.regular_iff_stages]
  constructor
  · intro h j hj
    rw [← stage_matrix_det φ p s a b j k hj z]
    exact h j hj
  · intro h j hj
    rw [stage_matrix_det φ p s a b j k hj z]
    exact h j hj

theorem regular_prefix (j k : ℕ) (hj : j ≤ k) (z : Fin (k * width n) → K)
    (hz : (TriangularPolynomialSystem.jacobian (system p s a b k)).eval₂ φ z ≠ 0) :
    (TriangularPolynomialSystem.jacobian (system p s a b j)).eval₂ φ
      (z ∘ TriangularPolynomialRows.prefixIndex (width n) j k hj) ≠ 0 :=
  TriangularPolynomialStageRegularity.regular_prefix φ (family p s a b) j k hj z hz

theorem regular_appendPoint_iff (k : ℕ) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) :
    (TriangularPolynomialSystem.jacobian (system p s a b (k + 1))).eval₂ φ (appendPoint k x y) ≠ 0 ↔
      (TriangularPolynomialSystem.jacobian (system p s a b k)).eval₂ φ x ≠ 0 ∧
      (FlatAffineCriticalRegularity.matrix φ p (s k) (a k) (fun i => (b k i).polynomial)
        (Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y)).det ≠ 0 := by
  rw [system, appendPoint, TriangularPolynomialStageRegularity.regular_appendPoint_iff, family_matrix_det]
  have he : Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k)
      (y ∘ (blockEquiv n).symm) ∘ Equiv.sumCongr (Equiv.refl (Ancestors n k)) (blockEquiv n) =
        Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y := by
    funext v
    cases v <;> simp
  rw [he]
  rfl

theorem multiplier_ne_zero (k : ℕ) (z : Fin (k * width n) → K)
    (hz : ∀ i, (system p s a b k i).eval₂ φ z = 0)
    (hreg : (TriangularPolynomialSystem.jacobian (system p s a b k)).eval₂ φ z ≠ 0)
    (j : ℕ) (hj : j < k) :
    stagePoint j k hj z (FlatAffineCriticalStage.multiplier 0) ≠ 0 :=
  FlatAffineCriticalRegularity.multiplier_ne_zero φ p (s j) (a j) (fun i => (b j i).polynomial)
    (stagePoint j k hj z) ((roots_iff_stages φ p s a b k z).mp hz j hj)
    ((regular_iff_stages φ p s a b k z).mp hreg j hj)

end LeanCanny.Algebra.FlatAffineTowerRegularity
