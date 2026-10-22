/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulExteriorPermutation
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Simultaneous spatial and exterior coordinate permutations

Renaming polynomial variables and exterior indices gives a linear
equivalence over the original coefficient ring. Its action on every
monomial exterior word and its compatibility with the Koszul differential
are explicit.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def spatialRename (ρ : Equiv.Perm (Fin n)) : Total n R →ₗ[R] Total n R where
  toFun := polynomialMap (MvPolynomial.rename ρ).toRingHom
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    rw [← IsScalarTower.algebraMap_smul (Poly n R) r x, map_smulₛₗ]
    change MvPolynomial.rename ρ (MvPolynomial.C r) • _ = _
    rw [MvPolynomial.rename_C]
    exact IsScalarTower.algebraMap_smul (Poly n R) r _

noncomputable def coordinatePermutation (ρ : Equiv.Perm (Fin n)) : Total n R →ₗ[R] Total n R :=
  ((exteriorPermutation ρ).toLinearMap.restrictScalars R).comp (spatialRename ρ)

theorem coordinatePermutation_monomialBlade (ρ : Equiv.Perm (Fin n)) {k : ℕ}
    (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    coordinatePermutation (R := R) ρ (monomialBlade (R := R) v m) =
      monomialBlade (R := R) (ρ ∘ v) (Finsupp.equivMapDomain ρ m) := by
  change exteriorPermutation ρ (polynomialMap (MvPolynomial.rename ρ).toRingHom (monomialBlade (R := R) v m)) = _
  rw [polynomialMap_monomialBlade, map_smul, exteriorPermutation_blade]
  change MvPolynomial.rename ρ (MvPolynomial.monomial m (1 : R)) • _ = _
  rw [MvPolynomial.rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain]
  rfl

noncomputable def permutedSystem (ρ : Equiv.Perm (Fin n)) (p : Fin n → Poly n R) (i : Fin n) : Poly n R :=
  MvPolynomial.rename ρ (p (ρ.symm i))

theorem coordinatePermutation_differential (ρ : Equiv.Perm (Fin n)) (p : Fin n → Poly n R) (x : Total n R) :
    coordinatePermutation (R := R) ρ (KoszulExterior.differential p x) =
      KoszulExterior.differential (permutedSystem ρ p) (coordinatePermutation ρ x) := by
  change exteriorPermutation ρ (polynomialMap (MvPolynomial.rename ρ).toRingHom (KoszulExterior.differential p x)) = _
  rw [polynomialMap_differential, exteriorPermutation_differential]
  rfl

theorem coordinatePermutation_left_inverse (ρ : Equiv.Perm (Fin n)) (x : Total n R) :
    coordinatePermutation (R := R) ρ.symm (coordinatePermutation ρ x) = x := by
  have h : (coordinatePermutation (R := R) ρ.symm).comp (coordinatePermutation ρ) = LinearMap.id := by
    apply (ambientBasis (R := R)).ext
    rintro ⟨m, s⟩
    rw [ambientBasis_apply, exteriorBasis_as_blade s rfl]
    change coordinatePermutation ρ.symm (coordinatePermutation ρ (monomialBlade (R := R) _ m)) = monomialBlade (R := R) _ m
    rw [coordinatePermutation_monomialBlade, coordinatePermutation_monomialBlade]
    have hm : Finsupp.equivMapDomain ρ.symm (Finsupp.equivMapDomain ρ m) = m := by
      ext i
      simp only [Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    have hv : ρ.symm ∘ (ρ ∘ s.orderEmbOfFin rfl) = s.orderEmbOfFin rfl := by
      funext j
      exact ρ.symm_apply_apply _
    rw [hm, hv]
  exact LinearMap.congr_fun h x

noncomputable def coordinatePermutationEquiv (ρ : Equiv.Perm (Fin n)) : Total n R ≃ₗ[R] Total n R :=
  LinearEquiv.ofBijective (coordinatePermutation (R := R) ρ)
    ⟨by
      intro x y he
      have hi := congrArg (coordinatePermutation (R := R) ρ.symm) he
      simpa only [coordinatePermutation_left_inverse] using hi,
      fun x => ⟨coordinatePermutation (R := R) ρ.symm x, by
        have hi := coordinatePermutation_left_inverse (R := R) ρ.symm x
        simpa only [Equiv.symm_symm] using hi⟩⟩

end LeanCanny.Algebra.KoszulWeighted
