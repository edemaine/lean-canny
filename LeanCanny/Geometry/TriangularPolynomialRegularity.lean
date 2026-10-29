/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialTower
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # Analytic regularity of flat dependent polynomial stages

Freezing ancestral coordinates commutes with differentiation in the new
variables. The combined derivative is invertible exactly when the old
derivative and the frozen new-stage derivative are both invertible.
-/

@[expose] public section
namespace LeanCanny.Geometry.TriangularPolynomialRegularity
open MvPolynomial LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι κ R : Type*} [CommRing R]

noncomputable def freeze (φ : R →+* ℝ) (x : ι → ℝ) :
    MvPolynomial (ι ⊕ κ) R →+* MvPolynomial κ ℝ :=
  eval₂Hom (C.comp φ) (Sum.elim (fun i => C (x i)) X)

@[simp] theorem freeze_C (φ : R →+* ℝ) (x : ι → ℝ) (a : R) :
    freeze (κ := κ) φ x (C a) = C (φ a) := eval₂_C _ _ _

@[simp] theorem freeze_X (φ : R →+* ℝ) (x : ι → ℝ) (i : ι ⊕ κ) :
    freeze φ x (X i) = Sum.elim (fun j => C (x j)) X i := eval₂_X _ _ _

theorem eval_freeze (φ : R →+* ℝ) (x : ι → ℝ) (y : κ → ℝ) (p : MvPolynomial (ι ⊕ κ) R) :
    (freeze φ x p).eval₂ (RingHom.id ℝ) y = p.eval₂ φ (Sum.elim x y) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, eval₂_mul, hp, freeze_X, eval₂_X]
    cases i <;> simp

theorem pderiv_freeze (φ : R →+* ℝ) (x : ι → ℝ) (p : MvPolynomial (ι ⊕ κ) R) (j : κ) :
    pderiv j (freeze φ x p) = freeze φ x (pderiv (Sum.inr j) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    cases i <;> simp [hp, pderiv_X, Pi.single_apply, apply_ite]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem eval_jacobian (φ : R →+* ℝ) (p : ι → MvPolynomial ι R) (x : ι → ℝ) :
    (TriangularPolynomialSystem.jacobian p).eval₂ φ x = (PolynomialSystemRegularity.matrix φ p x).det := by
  change (eval₂Hom φ x) (Matrix.det _) = _
  rw [RingHom.map_det]
  rfl

theorem analytic_iff (φ : R →+* ℝ) (p : ι → MvPolynomial ι R) (x : ι → ℝ) :
    (fderiv ℝ (fun z => fun i => (p i).eval₂ φ z) x).IsInvertible ↔
      (TriangularPolynomialSystem.jacobian p).eval₂ φ x ≠ 0 := by
  rw [PolynomialSystemRegularity.isInvertible_iff, eval_jacobian]

omit [Fintype ι] [DecidableEq ι] in
theorem eval_spatialJacobian (φ : R →+* ℝ) (q : κ → MvPolynomial (ι ⊕ κ) R)
    (x : ι → ℝ) (y : κ → ℝ) :
    (TriangularPolynomialSystem.spatialJacobian q).eval₂ φ (Sum.elim x y) =
      (PolynomialSystemRegularity.matrix (RingHom.id ℝ) (fun i => freeze φ x (q i)) y).det := by
  change (eval₂Hom φ (Sum.elim x y)) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact (eval_freeze φ x y (pderiv (Sum.inr j) (q i))).symm.trans
    (congrArg (fun p : MvPolynomial κ ℝ => p.eval₂ (RingHom.id ℝ) y) (pderiv_freeze φ x (q i) j).symm)

theorem analytic_append_iff (φ : R →+* ℝ) (p : ι → MvPolynomial ι R)
    (q : κ → MvPolynomial (ι ⊕ κ) R) (x : ι → ℝ) (y : κ → ℝ) :
    (fderiv ℝ (fun z => fun i => (TriangularPolynomialSystem.append p q i).eval₂ φ z)
      (Sum.elim x y)).IsInvertible ↔
        (fderiv ℝ (fun z => fun i => (p i).eval₂ φ z) x).IsInvertible ∧
          (fderiv ℝ (fun z => fun i => (q i).eval₂ φ (Sum.elim x z)) y).IsInvertible := by
  have he : (fun z => fun i => (q i).eval₂ φ (Sum.elim x z)) =
      (fun z => fun i => (freeze φ x (q i)).eval₂ (RingHom.id ℝ) z) := by
    funext z i
    exact (eval_freeze φ x z (q i)).symm
  have hc : (fderiv ℝ (fun z => fun i => (q i).eval₂ φ (Sum.elim x z)) y).IsInvertible ↔
      (TriangularPolynomialSystem.spatialJacobian q).eval₂ φ (Sum.elim x y) ≠ 0 := by
    rw [he, PolynomialSystemRegularity.isInvertible_iff, eval_spatialJacobian]
  calc
    _ ↔ (TriangularPolynomialSystem.jacobian (TriangularPolynomialSystem.append p q)).eval₂
        φ (Sum.elim x y) ≠ 0 := analytic_iff φ _ _
    _ ↔ (TriangularPolynomialSystem.jacobian p).eval₂ φ x ≠ 0 ∧
        (TriangularPolynomialSystem.spatialJacobian q).eval₂ φ (Sum.elim x y) ≠ 0 := by
      simpa only [Function.comp_def, Sum.elim_inl] using
        TriangularPolynomialSystem.regular_append_iff φ p q (Sum.elim x y)
    _ ↔ _ := and_congr (analytic_iff φ p x).symm hc.symm

theorem tower_analytic_iff (φ : R →+* ℝ) (n k : ℕ) (F : TriangularPolynomialTower.Family n R)
    (z : TriangularPolynomialTower.Variables n k → ℝ) :
    (fderiv ℝ (fun y => fun i => (TriangularPolynomialTower.system F k i).eval₂ φ y) z).IsInvertible ↔
      TriangularPolynomialTower.Regular φ F k z :=
  (analytic_iff φ (TriangularPolynomialTower.system F k) z).trans
    (TriangularPolynomialTower.regular_iff φ F k z)

end LeanCanny.Geometry.TriangularPolynomialRegularity
