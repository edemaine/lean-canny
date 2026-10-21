/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayHigherDenominators

/-! # Permuting full Macaulay matrices and arbitrary maximal minors

Input and spatial permutations give explicit equivalences of the full
source and target index types. Transporting an arbitrary row selector
therefore preserves its maximal minor across universal orderings.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def activePermutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n)) :
    activeIndices (d ∘ ρ) W ≃ activeIndices d W :=
  Equiv.subtypeEquiv (FixedWidthPolynomial.permutation W ρ) (fun r => by
    rw [mem_activeIndices, mem_activeIndices, FixedWidthPolynomial.vector_permutation,
      KoszulWeighted.degree_equivMapDomain, MacaulayUniversal.level_comp_perm])

noncomputable def sourcePermutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n)) :
    MultiplierIndex (d ∘ ρ) W ≃ MultiplierIndex d W :=
  Equiv.sigmaCongr ρ (fun i => Equiv.subtypeEquiv (FixedWidthPolynomial.permutation W ρ) (fun r => by
    rw [mem_multiplierIndices, mem_multiplierIndices, FixedWidthPolynomial.vector_permutation,
      KoszulWeighted.degree_equivMapDomain, MacaulayUniversal.level_comp_perm]
    rfl))

theorem vector_activePermutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n)) (r : activeIndices (d ∘ ρ) W) :
    FixedWidthPolynomial.vector n W (activePermutation d W ρ r).val = Finsupp.equivMapDomain ρ (FixedWidthPolynomial.vector n W r.val) :=
  FixedWidthPolynomial.vector_permutation W ρ r.val

theorem sourcePermutation_fst (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n)) (a : MultiplierIndex (d ∘ ρ) W) :
    (sourcePermutation d W ρ a).1 = ρ a.1 := rfl

theorem vector_sourcePermutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n)) (a : MultiplierIndex (d ∘ ρ) W) :
    FixedWidthPolynomial.vector n W (sourcePermutation d W ρ a).2.val = Finsupp.equivMapDomain ρ (FixedWidthPolynomial.vector n W a.2.val) :=
  FixedWidthPolynomial.vector_permutation W ρ a.2.val

theorem sourceRow_permutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n))
    (p q : Fin n → MvPolynomial (Fin n) R) (hpq : ∀ i, MvPolynomial.rename ρ (p i) = q (ρ i))
    (a : MultiplierIndex (d ∘ ρ) W) :
    MvPolynomial.rename ρ (sourceRow p (d ∘ ρ) W a) = sourceRow q d W (sourcePermutation d W ρ a) := by
  simp only [sourceRow, map_mul, MvPolynomial.rename_monomial, sourcePermutation_fst, vector_sourcePermutation,
    Finsupp.equivMapDomain_eq_mapDomain, hpq]

theorem fullMatrix_permutation (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n))
    (p q : Fin n → MvPolynomial (Fin n) R) (hpq : ∀ i, MvPolynomial.rename ρ (p i) = q (ρ i)) :
    (fullMatrix q d W).submatrix (sourcePermutation d W ρ) (activePermutation d W ρ) = fullMatrix p (d ∘ ρ) W := by
  funext a r
  change (sourceRow q d W (sourcePermutation d W ρ a)).coeff
    (FixedWidthPolynomial.vector n W (activePermutation d W ρ r).val) = _
  rw [← sourceRow_permutation d W ρ p q hpq, vector_activePermutation, Finsupp.equivMapDomain_eq_mapDomain]
  exact MvPolynomial.coeff_rename_mapDomain ρ ρ.injective _ _

noncomputable def transportSelector (d : Fin n → ℕ) (W : ℕ) (ρ : Equiv.Perm (Fin n))
    (f : activeIndices d W → MultiplierIndex d W) : activeIndices (d ∘ ρ) W → MultiplierIndex (d ∘ ρ) W :=
  fun r => (sourcePermutation d W ρ).symm (f (activePermutation d W ρ r))

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem fullMatrix_ordering (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) :
    (Macaulay.fullMatrix (system (R := R) d W (Equiv.refl _)) d W).submatrix
      (Macaulay.sourcePermutation d W π) (Macaulay.activePermutation d W π) =
        Macaulay.fullMatrix (system (R := R) d W π) (d ∘ π) W :=
  Macaulay.fullMatrix_permutation d W π _ _ (system_rename d W π (Equiv.refl _) π (fun _ => rfl))

theorem fullMinor_ordering (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W) :
    ((Macaulay.fullMatrix (system (R := R) d W π) (d ∘ π) W).submatrix (Macaulay.transportSelector d W π f) id).det =
      ((Macaulay.fullMatrix (system (R := R) d W (Equiv.refl _)) d W).submatrix f id).det := by
  have hm : (Macaulay.fullMatrix (system (R := R) d W π) (d ∘ π) W).submatrix (Macaulay.transportSelector d W π f) id =
      ((Macaulay.fullMatrix (system (R := R) d W (Equiv.refl _)) d W).submatrix f id).submatrix
        (Macaulay.activePermutation d W π) (Macaulay.activePermutation d W π) := by
    rw [← fullMatrix_ordering]
    funext a b
    simp only [Matrix.submatrix_apply, Macaulay.transportSelector, Equiv.apply_symm_apply, id_eq]
  rw [hm, Matrix.det_submatrix_equiv_self]

end LeanCanny.Algebra.MacaulayUniversal
