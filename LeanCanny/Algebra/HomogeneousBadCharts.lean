/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousBadSystem
public import LeanCanny.Algebra.JacobianKernelCharts

/-! # Separating affine bad roots from roots at infinity

When the actual bad-polynomial degree is strictly below its homogenization
degree, that appended row vanishes at infinity. Projective root-freeness is
then exactly affine regularity together with exclusion of the original rows'
roots at infinity, even for coefficient maps with a kernel.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogeneousBadSystem
open MvPolynomial
open scoped Classical Matrix

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

theorem bad_row_infinity (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (J : MvPolynomial (Fin n) R) (B : ℕ) (hJ : J.totalDegree < B)
    (y : Option (Fin n) → K) (hy : y none = 0) : (rows p d J B none).eval₂ φ y = 0 := by
  rw [rows, ← eval_map, WeightedHomogenization.map_homogenize]
  exact CoerciveCriticalHomogenization.homogenize_eval_infinity (J.map φ) B
    ((PolynomialMapDegree.degree_le φ J).trans_lt hJ) y hy

theorem root_free_iff (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (J : MvPolynomial (Fin n) R) (B : ℕ) (hp : ∀ i, (p i).totalDegree ≤ d i) (hJ : J.totalDegree < B) :
    (∀ y : Option (Fin n) → K, (∀ i, (rows p d J B i).eval₂ φ y = 0) → y = 0) ↔
      (∀ x : Fin n → K, (∀ i, (p i).eval₂ φ x = 0) → J.eval₂ φ x ≠ 0) ∧
      (∀ y : Option (Fin n) → K, y none = 0 →
        (∀ i, (rows p d J B (some i)).eval₂ φ y = 0) → y = 0) := by
  constructor
  · intro h
    constructor
    · intro x hx hxJ
      have hz := h (fun i => i.elim 1 x) (chart_root φ p d J B hp hJ.le x hx hxJ)
      have he := congrFun hz none
      exact one_ne_zero he
    · intro y hy hrows
      apply h y
      intro i
      cases i with
      | none => exact bad_row_infinity φ p d J B hJ y hy
      | some i => exact hrows i
  · rintro ⟨ha, hi⟩
    exact no_nonzero_root φ p d J B hp hJ.le ha hi

theorem jacobian_root_free_iff (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (B : ℕ) (hp : ∀ i, (p i).totalDegree ≤ d i)
    (hJ : (JacobianKernelCharts.jacobian p).totalDegree < B) :
    (∀ y : Option (Fin n) → K,
      (∀ i, (rows p d (JacobianKernelCharts.jacobian p) B i).eval₂ φ y = 0) → y = 0) ↔
      (∀ i : Fin n, ¬ ∃ x v : Fin n → K, v i = 1 ∧ (∀ j, (p j).eval₂ φ x = 0) ∧
        JacobianKernelCharts.matrix φ p x *ᵥ v = 0) ∧
      (∀ y : Option (Fin n) → K, y none = 0 →
        (∀ i, (rows p d (JacobianKernelCharts.jacobian p) B (some i)).eval₂ φ y = 0) → y = 0) := by
  rw [root_free_iff φ p d _ B hp hJ, JacobianKernelCharts.regular_iff_charts]

end LeanCanny.Algebra.HomogeneousBadSystem
