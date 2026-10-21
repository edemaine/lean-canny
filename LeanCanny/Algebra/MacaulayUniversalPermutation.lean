/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPermutation
public import LeanCanny.Algebra.KoszulWeightedPermutation
public import LeanCanny.Algebra.MacaulayUniversalExact

/-! # Spatial renaming of the actual universal input systems

Fixed-width exponent ranks permute bijectively. Reindexing the defining
finite sum proves that simultaneous input/spatial orderings describe the
same universal system in renamed coordinates, over the coefficient ring
and over its fraction field.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem system_rename (d : Fin n → ℕ) (W : ℕ) (π σ ρ : Equiv.Perm (Fin n))
    (h : ∀ i, σ (ρ i) = π i) (i : Fin n) :
    MvPolynomial.rename ρ (system (R := R) d W π i) = system (R := R) d W σ (ρ i) := by
  have he : ρ.trans σ = π := Equiv.ext h
  unfold system
  rw [map_sum]
  refine Fintype.sum_equiv (FixedWidthPolynomial.permutation W ρ) _ _ (fun r => ?_)
  rw [FixedWidthPolynomial.vector_permutation, KoszulWeighted.degree_equivMapDomain, h]
  split_ifs
  · rw [MvPolynomial.rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain,
      ← Finsupp.equivMapDomain_trans, he]
  · exact map_zero _

theorem fractionSystem_rename (d : Fin n → ℕ) (W : ℕ) (π σ ρ : Equiv.Perm (Fin n))
    (h : ∀ i, σ (ρ i) = π i) (i : Fin n) :
    MvPolynomial.rename ρ (fractionSystem (R := R) d W π i) = fractionSystem (R := R) d W σ (ρ i) := by
  unfold fractionSystem
  rw [← MvPolynomial.map_rename, system_rename d W π σ ρ h i]

end LeanCanny.Algebra.MacaulayUniversal
