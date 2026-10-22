/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RowSpanEliminant

/-! # A surjective specialization gives a bounded generic eliminant

A single full-rank specialization selects a nonzero maximal minor over the
original coefficient ring. The specialization need not be injective. Over
an injective field extension this minor gives every row-span target, to
which the integral bounded-certificate construction applies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.RowSpanSpecialization
open scoped Matrix Classical

variable {R K F ι κ : Type*} [CommRing R] [Field K] [Field F]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem exists_nonzero_minor (phi : R →+* K) (A : Matrix ι κ R)
    (hs : Function.Surjective (fun v => Matrix.vecMul v (A.map phi))) :
    ∃ a : κ → ι, (A.submatrix a id).det ≠ 0 := by
  by_contra! hn
  have hz (a : κ → ι) : (0 : K) ∣ ((A.map phi).submatrix a id).det := by
    have he : (A.map phi).submatrix a id = (A.submatrix a id).map phi := rfl
    rw [he]
    change (0 : K) ∣ (phi.mapMatrix (A.submatrix a id)).det
    rw [← phi.map_det, hn a, map_zero]
  exact not_isUnit_zero
    (MatrixMaximalMinorSpan.isUnit_of_dvd_maximal_minors_of_surjective (A.map phi) 0 hz hs)

theorem generic_surjective (phi : R →+* K) (psi : R →+* F)
    (hi : Function.Injective psi) (A : Matrix ι κ R)
    (hs : Function.Surjective (fun v => Matrix.vecMul v (A.map phi))) :
    Function.Surjective (fun v => Matrix.vecMul v (A.map psi)) := by
  obtain ⟨a, ha⟩ := exists_nonzero_minor phi A hs
  have hd : ((A.map psi).submatrix a id).det ≠ 0 := by
    have he : (A.map psi).submatrix a id = (A.submatrix a id).map psi := rfl
    rw [he]
    change (psi.mapMatrix (A.submatrix a id)).det ≠ 0
    rw [← psi.map_det]
    exact fun hz => ha (hi (hz.trans (map_zero psi).symm))
  have hsurj : Function.Surjective (fun v => Matrix.vecMul v ((A.map psi).submatrix a id)) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  intro w
  obtain ⟨u, hu⟩ := hsurj w
  refine ⟨Matrix.vecMul u (MatrixMinorSection.rowSelection a), ?_⟩
  change Matrix.vecMul (Matrix.vecMul u (MatrixMinorSection.rowSelection a)) (A.map psi) = w
  rw [Matrix.vecMul_vecMul]
  have hm : MatrixMinorSection.rowSelection a * A.map psi = (A.map psi).submatrix a id :=
    Matrix.one_submatrix_mul a (Equiv.refl ι) (A.map psi)
  rw [hm]
  exact hu

theorem exists_bounded_certificate {σ : Type*}
    (phi : MvPolynomial σ ℤ →+* K) (psi : MvPolynomial σ ℤ →+* F)
    (hi : Function.Injective psi)
    (A : Matrix ι κ (MvPolynomial σ ℤ)) (w : κ → MvPolynomial σ ℤ)
    (D M : ℕ) (hM : 1 ≤ M)
    (hD : ∀ i j, (A i j).totalDegree ≤ D)
    (hMass : ∀ i j, MvMass.mass (A i j) ≤ M)
    (hs : Function.Surjective (fun v => Matrix.vecMul v (A.map phi))) :
    ∃ d : MvPolynomial σ ℤ, d ≠ 0 ∧ d.totalDegree ≤ Fintype.card κ * D ∧
      MvMass.mass d ≤ (Fintype.card κ).factorial * M ^ Fintype.card κ ∧
      ∃ c : ι → MvPolynomial σ ℤ, Matrix.vecMul c A = d • w :=
  RowSpanEliminant.exists_bounded_certificate psi hi A w D M hM hD hMass
    (generic_surjective phi psi hi A hs (psi ∘ w))

end LeanCanny.Algebra.RowSpanSpecialization
