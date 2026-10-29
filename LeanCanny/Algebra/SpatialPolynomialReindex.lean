/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialSystemReindex

/-! # Reindexing a polynomial stage with fixed ancestor variables

Changing the spatial row and variable indices together preserves the
spatial Jacobian determinant. Ancestor indices are retained literally.
-/

@[expose] public section
namespace LeanCanny.Algebra.SpatialPolynomialReindex
open MvPolynomial
open scoped Classical
variable {ι κ τ R : Type*} [CommRing R]

noncomputable def system (e : κ ≃ τ) (q : κ → MvPolynomial (ι ⊕ κ) R) :
    τ → MvPolynomial (ι ⊕ τ) R :=
  fun j => rename (Equiv.sumCongr (Equiv.refl ι) e) (q (e.symm j))

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K) (e : κ ≃ τ)
    (q : κ → MvPolynomial (ι ⊕ κ) R) (z : (ι ⊕ τ) → K) :
    (∀ j, (system e q j).eval₂ φ z = 0) ↔
      ∀ i, (q i).eval₂ φ (z ∘ Equiv.sumCongr (Equiv.refl ι) e) = 0 := by
  simp only [system, eval₂_rename]
  exact e.symm.forall_congr (fun _ => Iff.rfl)

variable [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

theorem spatialJacobian (e : κ ≃ τ) (q : κ → MvPolynomial (ι ⊕ κ) R) :
    TriangularPolynomialSystem.spatialJacobian (system e q) =
      rename (Equiv.sumCongr (Equiv.refl ι) e) (TriangularPolynomialSystem.spatialJacobian q) := by
  let E := Equiv.sumCongr (Equiv.refl ι) e
  have he (j : τ) (p : MvPolynomial (ι ⊕ κ) R) :
      pderiv (Sum.inr j) (rename E p) = rename E (pderiv (Sum.inr (e.symm j)) p) := by
    simpa only [E, Equiv.sumCongr_apply, Sum.map_inr, Equiv.apply_symm_apply] using
      pderiv_rename E.injective (Sum.inr (e.symm j)) p
  have hm : (Matrix.of fun i j => pderiv (Sum.inr j) (system e q i)) =
      (Matrix.of fun i j => rename E (pderiv (Sum.inr j) (q i))).submatrix e.symm e.symm := by
    apply Matrix.ext
    intro i j
    exact he j (q (e.symm i))
  change Matrix.det _ = _
  rw [hm, Matrix.det_submatrix_equiv_self]
  exact ((rename E).toRingHom.map_det (Matrix.of fun i j => pderiv (Sum.inr j) (q i))).symm

theorem eval_spatialJacobian {K : Type*} [CommRing K] (φ : R →+* K) (e : κ ≃ τ)
    (q : κ → MvPolynomial (ι ⊕ κ) R) (z : (ι ⊕ τ) → K) :
    (TriangularPolynomialSystem.spatialJacobian (system e q)).eval₂ φ z =
      (TriangularPolynomialSystem.spatialJacobian q).eval₂ φ
        (z ∘ Equiv.sumCongr (Equiv.refl ι) e) := by
  rw [spatialJacobian, eval₂_rename]

end LeanCanny.Algebra.SpatialPolynomialReindex
