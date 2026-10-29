/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialRows

/-! # Exact stage and prefix criteria for indexed polynomial towers

The full root equations and nonsingular Jacobian are equivalent to their
conditions at every frozen stage. Restricting to any earlier prefix preserves
both conditions. These statements hold at depth zero and with empty blocks.
-/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialStageRegularity
open MvPolynomial TriangularPolynomialTower TriangularPolynomialIndexing TriangularPolynomialRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R K : Type*}

theorem prefix_enumerate (n k : ℕ) (v : Variables n k) :
    prefixIndex n k (k + 1) (by omega) (enumerate n k v) =
      enumerate n (k + 1) (Sum.inl v) := Fin.ext (enumerate_old n k v).symm

noncomputable def appendPoint (k : ℕ) (x : Fin (k * n) → K) (y : Fin n → K) :
    Fin ((k + 1) * n) → K :=
  Sum.elim (x ∘ enumerate n k) y ∘ (enumerate n (k + 1)).symm

theorem appendPoint_enumerate (k : ℕ) (x : Fin (k * n) → K) (y : Fin n → K) :
    appendPoint k x y ∘ enumerate n (k + 1) = Sum.elim (x ∘ enumerate n k) y := by
  funext v
  simp only [appendPoint, Function.comp_apply, Equiv.symm_apply_apply]

theorem appendPoint_prefix (k : ℕ) (x : Fin (k * n) → K) (y : Fin n → K) :
    appendPoint k x y ∘ prefixIndex n k (k + 1) (by omega) = x := by
  funext i
  have he := prefix_enumerate n k ((enumerate n k).symm i)
  rw [Equiv.apply_symm_apply] at he
  change appendPoint k x y (prefixIndex n k (k + 1) (by omega) i) = x i
  rw [he]
  simp only [appendPoint, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Equiv.apply_symm_apply]

variable [CommRing R] [CommRing K]

theorem roots_succ_iff (φ : R →+* K) (F : Family n R) (k : ℕ)
    (z : Fin ((k + 1) * n) → K) :
    (∀ i, (TriangularPolynomialIndexing.system F (k + 1) i).eval₂ φ z = 0) ↔
      (∀ i, (TriangularPolynomialIndexing.system F k i).eval₂ φ
        (z ∘ prefixIndex n k (k + 1) (by omega)) = 0) ∧
      ∀ i, (F.row k i).eval₂ φ (z ∘ enumerate n (k + 1)) = 0 := by
  rw [TriangularPolynomialIndexing.roots_iff, TriangularPolynomialIndexing.roots_iff]
  have he : (z ∘ enumerate n (k + 1)) ∘ Sum.inl =
      (z ∘ prefixIndex n k (k + 1) (by omega)) ∘ enumerate n k := by
    funext v
    exact congrArg z (prefix_enumerate n k v).symm
  change Roots φ F k ((z ∘ enumerate n (k + 1)) ∘ Sum.inl) ∧ _ ↔ _
  rw [he]

theorem roots_appendPoint_iff (φ : R →+* K) (F : Family n R) (k : ℕ)
    (x : Fin (k * n) → K) (y : Fin n → K) :
    (∀ i, (TriangularPolynomialIndexing.system F (k + 1) i).eval₂ φ (appendPoint k x y) = 0) ↔
      (∀ i, (TriangularPolynomialIndexing.system F k i).eval₂ φ x = 0) ∧
      ∀ i, (F.row k i).eval₂ φ (Sum.elim (x ∘ enumerate n k) y) = 0 := by
  rw [roots_succ_iff, appendPoint_prefix, appendPoint_enumerate]

theorem roots_iff_stages (φ : R →+* K) (F : Family n R) (k : ℕ) (z : Fin (k * n) → K) :
    (∀ i, (TriangularPolynomialIndexing.system F k i).eval₂ φ z = 0) ↔
      ∀ j (hj : j < k) i, (F.row j i).eval₂ φ (z ∘ embedding n j k hj) = 0 := by
  induction k with
  | zero => exact ⟨fun _ j hj => by omega, fun _ i => False.elim (by have hi := i.isLt; omega)⟩
  | succ k ih =>
    rw [roots_succ_iff, ih]
    constructor
    · rintro ⟨ho, hn⟩ j hj i
      by_cases he : j = k
      · subst j
        exact hn i
      · exact ho j (by omega) i
    · intro h
      exact ⟨fun j hj i => h j (by omega) i, h k (by omega)⟩

theorem roots_prefix (φ : R →+* K) (F : Family n R) (a b : ℕ) (h : a ≤ b)
    (z : Fin (b * n) → K)
    (hz : ∀ i, (TriangularPolynomialIndexing.system F b i).eval₂ φ z = 0) :
    ∀ i, (TriangularPolynomialIndexing.system F a i).eval₂ φ (z ∘ prefixIndex n a b h) = 0 := by
  apply (roots_iff_stages φ F a _).mpr
  intro j hj i
  exact (roots_iff_stages φ F b z).mp hz j (by omega) i

variable [Nontrivial K] [NoZeroDivisors K]

theorem regular_succ_iff (φ : R →+* K) (F : Family n R) (k : ℕ)
    (z : Fin ((k + 1) * n) → K) :
    (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F (k + 1))).eval₂ φ z ≠ 0 ↔
      (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F k)).eval₂ φ
        (z ∘ prefixIndex n k (k + 1) (by omega)) ≠ 0 ∧
      (TriangularPolynomialSystem.spatialJacobian (F.row k)).eval₂ φ (z ∘ enumerate n (k + 1)) ≠ 0 := by
  rw [TriangularPolynomialIndexing.regular_iff, TriangularPolynomialIndexing.regular_iff]
  have he : (z ∘ enumerate n (k + 1)) ∘ Sum.inl =
      (z ∘ prefixIndex n k (k + 1) (by omega)) ∘ enumerate n k := by
    funext v
    exact congrArg z (prefix_enumerate n k v).symm
  change Regular φ F k ((z ∘ enumerate n (k + 1)) ∘ Sum.inl) ∧ _ ↔ _
  rw [he]

theorem regular_appendPoint_iff (φ : R →+* K) (F : Family n R) (k : ℕ)
    (x : Fin (k * n) → K) (y : Fin n → K) :
    (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F (k + 1))).eval₂ φ
      (appendPoint k x y) ≠ 0 ↔
      (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F k)).eval₂ φ x ≠ 0 ∧
      (TriangularPolynomialSystem.spatialJacobian (F.row k)).eval₂ φ
        (Sum.elim (x ∘ enumerate n k) y) ≠ 0 := by
  rw [regular_succ_iff, appendPoint_prefix, appendPoint_enumerate]

theorem regular_iff_stages (φ : R →+* K) (F : Family n R) (k : ℕ) (z : Fin (k * n) → K) :
    (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F k)).eval₂ φ z ≠ 0 ↔
      ∀ j (hj : j < k), (TriangularPolynomialSystem.spatialJacobian (F.row j)).eval₂ φ
        (z ∘ embedding n j k hj) ≠ 0 := by
  induction k with
  | zero =>
    rw [TriangularPolynomialIndexing.regular_iff]
    exact ⟨fun _ j hj => by omega, fun _ => trivial⟩
  | succ k ih =>
    rw [regular_succ_iff, ih]
    constructor
    · rintro ⟨ho, hn⟩ j hj
      by_cases he : j = k
      · subst j
        exact hn
      · exact ho j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h k (by omega)⟩

theorem regular_prefix (φ : R →+* K) (F : Family n R) (a b : ℕ) (h : a ≤ b)
    (z : Fin (b * n) → K)
    (hz : (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F b)).eval₂ φ z ≠ 0) :
    (TriangularPolynomialSystem.jacobian (TriangularPolynomialIndexing.system F a)).eval₂ φ
      (z ∘ prefixIndex n a b h) ≠ 0 := by
  apply (regular_iff_stages φ F a _).mpr
  intro j hj
  exact (regular_iff_stages φ F b z).mp hz j (by omega)

end LeanCanny.Algebra.TriangularPolynomialStageRegularity
