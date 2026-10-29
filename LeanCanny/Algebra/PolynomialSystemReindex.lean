/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialSystem

/-! # Explicit reindexing of square polynomial systems

Renaming both equations and variables by the same equivalence preserves
roots and the Jacobian determinant. Degree and integer coefficient-mass
bounds pass to the indexed system.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialSystemReindex
open MvPolynomial
open scoped Classical

variable {ι κ R : Type*} [CommRing R]

noncomputable def system (e : ι ≃ κ) (p : ι → MvPolynomial ι R) : κ → MvPolynomial κ R :=
  fun i => rename e (p (e.symm i))

theorem degree_le (e : ι ≃ κ) (p : ι → MvPolynomial ι R) (D : ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (j : κ) : (system e p j).totalDegree ≤ D :=
  (totalDegree_rename_le _ _).trans (hp (e.symm j))

theorem mass_le (e : ι ≃ κ) (p : ι → MvPolynomial ι ℤ) (B : ℕ)
    (hp : ∀ i, MvMass.mass (p i) ≤ B) (j : κ) : MvMass.mass (system e p j) ≤ B :=
  (MvMass.rename_le _ _).trans (hp (e.symm j))

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K) (e : ι ≃ κ)
    (p : ι → MvPolynomial ι R) (x : κ → K) :
    (∀ j, (system e p j).eval₂ φ x = 0) ↔ ∀ i, (p i).eval₂ φ (x ∘ e) = 0 := by
  simp only [system, eval₂_rename]
  exact e.symm.forall_congr (fun _ => Iff.rfl)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem jacobian (e : ι ≃ κ) (p : ι → MvPolynomial ι R) :
    TriangularPolynomialSystem.jacobian (system e p) = rename e (TriangularPolynomialSystem.jacobian p) := by
  have he (j : κ) (f : MvPolynomial ι R) :
      pderiv j (rename e f) = rename e (pderiv (e.symm j) f) := by
    simpa only [e.apply_symm_apply] using pderiv_rename e.injective (e.symm j) f
  have hm : (Matrix.of fun i j => pderiv j (system e p i)) =
      (Matrix.of fun i j => rename e (pderiv j (p i))).submatrix e.symm e.symm := by
    apply Matrix.ext
    intro i j
    exact he j (p (e.symm i))
  change Matrix.det _ = _
  rw [hm, Matrix.det_submatrix_equiv_self]
  exact ((rename e).toRingHom.map_det (Matrix.of fun i j => pderiv j (p i))).symm

theorem regular_iff {K : Type*} [CommRing K] (φ : R →+* K) (e : ι ≃ κ)
    (p : ι → MvPolynomial ι R) (x : κ → K) :
    (TriangularPolynomialSystem.jacobian (system e p)).eval₂ φ x ≠ 0 ↔
      (TriangularPolynomialSystem.jacobian p).eval₂ φ (x ∘ e) ≠ 0 := by
  rw [jacobian, eval₂_rename]

end LeanCanny.Algebra.PolynomialSystemReindex
