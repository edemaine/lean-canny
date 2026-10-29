/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.JacobianKernelCharts
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Appending polynomial stages without eliminating ancestral coordinates

The old equations use only the old variables; the new equations may depend
on both blocks. Their union has the maximum of the two degree and coefficient
mass bounds. Its block triangular Jacobian factors exactly, so regularity is
equivalent to regularity of the old system and of the new spatial block.
Both blocks may be empty.
-/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialSystem
open MvPolynomial
open scoped Classical

variable {ι κ R : Type*} [CommRing R]

noncomputable def append (p : ι → MvPolynomial ι R)
    (q : κ → MvPolynomial (ι ⊕ κ) R) : (ι ⊕ κ) → MvPolynomial (ι ⊕ κ) R :=
  Sum.elim (fun i => rename Sum.inl (p i)) q

theorem roots_append {K : Type*} [CommRing K] (φ : R →+* K)
    (p : ι → MvPolynomial ι R) (q : κ → MvPolynomial (ι ⊕ κ) R) (z : (ι ⊕ κ) → K) :
    (∀ i, (append p q i).eval₂ φ z = 0) ↔
      (∀ i, (p i).eval₂ φ (z ∘ Sum.inl) = 0) ∧ ∀ j, (q j).eval₂ φ z = 0 := by
  simp only [append, Sum.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename]

theorem degree_append (p : ι → MvPolynomial ι R) (q : κ → MvPolynomial (ι ⊕ κ) R)
    (D E : ℕ) (hp : ∀ i, (p i).totalDegree ≤ D) (hq : ∀ j, (q j).totalDegree ≤ E)
    (i : ι ⊕ κ) : (append p q i).totalDegree ≤ max D E := by
  cases i with
  | inl i => exact (totalDegree_rename_le _ _).trans ((hp i).trans (Nat.le_max_left _ _))
  | inr j => exact (hq j).trans (Nat.le_max_right _ _)

theorem mass_append (p : ι → MvPolynomial ι ℤ) (q : κ → MvPolynomial (ι ⊕ κ) ℤ)
    (B C : ℕ) (hp : ∀ i, MvMass.mass (p i) ≤ B)
    (hq : ∀ j, MvMass.mass (q j) ≤ C) (i : ι ⊕ κ) :
    MvMass.mass (append p q i) ≤ max B C := by
  cases i with
  | inl i => exact (MvMass.rename_le _ _).trans ((hp i).trans (Nat.le_max_left _ _))
  | inr j => exact (hq j).trans (Nat.le_max_right _ _)

theorem pderiv_inr_rename (p : MvPolynomial ι R) (j : κ) :
    pderiv (Sum.inr j) (rename (Sum.inl : ι → ι ⊕ κ) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, pderiv_X]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def jacobian (p : ι → MvPolynomial ι R) : MvPolynomial ι R :=
  Matrix.det (Matrix.of fun i j => pderiv j (p i))

noncomputable def spatialJacobian (q : κ → MvPolynomial (ι ⊕ κ) R) : MvPolynomial (ι ⊕ κ) R :=
  Matrix.det (Matrix.of fun i j => pderiv (Sum.inr j) (q i))

theorem jacobian_append (p : ι → MvPolynomial ι R) (q : κ → MvPolynomial (ι ⊕ κ) R) :
    jacobian (append p q) = rename Sum.inl (jacobian p) * spatialJacobian q := by
  have hm : (Matrix.of fun i j => pderiv j (append p q i)) =
      Matrix.fromBlocks (Matrix.of fun i j => rename Sum.inl (pderiv j (p i))) 0
        (Matrix.of fun i j => pderiv (Sum.inl j) (q i))
        (Matrix.of fun i j => pderiv (Sum.inr j) (q i)) := by
    ext i j
    cases i <;> cases j <;>
      simp only [append, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, pderiv_rename Sum.inl_injective,
        pderiv_inr_rename]
  change Matrix.det _ = _
  rw [hm, Matrix.det_fromBlocks_zero₁₂]
  have hd := (rename (Sum.inl : ι → ι ⊕ κ)).toRingHom.map_det (Matrix.of fun i j => pderiv j (p i))
  have hd' : (Matrix.of fun i j => rename (Sum.inl : ι → ι ⊕ κ) (pderiv j (p i))).det =
      rename Sum.inl (jacobian p) := hd.symm
  rw [hd']
  rfl

theorem regular_append_iff {K : Type*} [CommRing K] [NoZeroDivisors K] (φ : R →+* K)
    (p : ι → MvPolynomial ι R) (q : κ → MvPolynomial (ι ⊕ κ) R) (z : (ι ⊕ κ) → K) :
    (jacobian (append p q)).eval₂ φ z ≠ 0 ↔
      (jacobian p).eval₂ φ (z ∘ Sum.inl) ≠ 0 ∧ (spatialJacobian q).eval₂ φ z ≠ 0 := by
  rw [jacobian_append, eval₂_mul, eval₂_rename, mul_ne_zero_iff]

end LeanCanny.Algebra.TriangularPolynomialSystem
