/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoefficientMap

/-! # Polynomial-ring maps in exterior coordinates

An arbitrary polynomial-ring homomorphism acts semilinearly on the
polynomial exterior algebra. It fixes exterior words and intertwines the
Koszul differentials after applying the homomorphism to the inputs.
Unlike coefficient extension alone, this includes spatial renaming.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def polynomialMap (φ : Poly n R →+* Poly n S) : Total n R →ₛₗ[φ] Total n S :=
  (exteriorBasis (R := S)).repr.symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap φ.toSemilinearMap).comp (exteriorBasis (R := R)).repr.toLinearMap)

theorem polynomialMap_repr (φ : Poly n R →+* Poly n S) (x : Total n R) (s : Finset (Fin n)) :
    (exteriorBasis (R := S)).repr (polynomialMap φ x) s = φ ((exteriorBasis (R := R)).repr x s) := by
  change (exteriorBasis (R := S)).repr ((exteriorBasis (R := S)).repr.symm _) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem polynomialMap_exteriorBasis (φ : Poly n R →+* Poly n S) (s : Finset (Fin n)) :
    polynomialMap φ (exteriorBasis (R := R) s) = exteriorBasis (R := S) s := by
  apply (exteriorBasis (R := S)).repr.injective
  apply Finsupp.ext
  intro t
  rw [polynomialMap_repr, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem blade_perm_zsmul {k : ℕ} (v : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    blade (R := R) (v ∘ σ) = (σ.sign : ℤ) • blade (R := R) v := by
  simpa only [monomialBlade_zero_exponent] using monomialBlade_perm_zsmul (R := R) v 0 σ

theorem blade_sorted {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) :
    blade (R := R) (v ∘ sortPermutation v hv) = exteriorBasis (R := R) (Finset.univ.image v) := by
  rw [sortPermutation_order]
  exact (exteriorBasis_as_blade _ (image_card_of_injective v hv)).symm

theorem polynomialMap_blade (φ : Poly n R →+* Poly n S) {k : ℕ} (v : Fin k → Fin n) :
    polynomialMap φ (blade (R := R) v) = blade (R := S) v := by
  by_cases hv : Function.Injective v
  · apply (sortPermutation v hv).sign.isUnit.smul_left_cancel.mp
    rw [← map_zsmul, ← blade_perm_zsmul, blade_sorted, polynomialMap_exteriorBasis,
      ← blade_sorted v hv, blade_perm_zsmul]
  · rw [blade_eq_zero_of_not_injective v hv, map_zero, blade_eq_zero_of_not_injective v hv]

theorem polynomialMap_monomialBlade (φ : Poly n R →+* Poly n S) {k : ℕ}
    (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    polynomialMap φ (monomialBlade (R := R) v m) = φ (MvPolynomial.monomial m (1 : R)) • blade (R := S) v := by
  rw [monomialBlade, map_smulₛₗ, polynomialMap_blade]

theorem wedge_blade (i : Fin n) {k : ℕ} (v : Fin k → Fin n) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (blade (R := R) v) =
      blade (R := R) (Fin.cons i v) := (blade_cons i v).symm

theorem polynomialMap_wedge (φ : Poly n R →+* Poly n S) (i : Fin n) (x : Total n R) :
    polynomialMap φ (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S) (polynomialMap φ x) := by
  have h : (polynomialMap φ).comp (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)) =
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S)).comp (polynomialMap φ) := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change polynomialMap φ (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (exteriorBasis (R := R) s)) =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S) (polynomialMap φ (exteriorBasis (R := R) s))
    rw [exteriorBasis_as_blade s rfl, wedge_blade, polynomialMap_blade, polynomialMap_blade, wedge_blade]
  exact LinearMap.congr_fun h x

theorem differential_blade_succ (p : Fin n → Poly n R) {k : ℕ} (v : Fin (k + 1) → Fin n) :
    KoszulExterior.differential p (blade (R := R) v) = p (v 0) • blade (R := R) (Matrix.vecTail v) -
      KoszulExterior.wedge (Pi.single (v 0) 1 : Fin n → Poly n R)
        (KoszulExterior.differential p (blade (R := R) (Matrix.vecTail v))) := by
  simpa only [monomialBlade_zero_exponent] using differential_word_succ p v 0

theorem polynomialMap_differential_blade (φ : Poly n R →+* Poly n S) (p : Fin n → Poly n R)
    {k : ℕ} (v : Fin k → Fin n) :
    polynomialMap φ (KoszulExterior.differential p (blade (R := R) v)) =
      KoszulExterior.differential (fun i => φ (p i)) (blade (R := S) v) := by
  induction k with
  | zero =>
    simp only [blade_zero, KoszulExterior.differential, CliffordAlgebra.contractLeft_one, map_zero]
  | succ k ih =>
    rw [differential_blade_succ, map_sub, map_smulₛₗ, polynomialMap_blade, polynomialMap_wedge, ih,
      differential_blade_succ]

theorem polynomialMap_differential (φ : Poly n R →+* Poly n S) (p : Fin n → Poly n R) (x : Total n R) :
    polynomialMap φ (KoszulExterior.differential p x) =
      KoszulExterior.differential (fun i => φ (p i)) (polynomialMap φ x) := by
  have h : (polynomialMap φ).comp (KoszulExterior.differential p) =
      (KoszulExterior.differential (fun i => φ (p i))).comp (polynomialMap φ) := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change polynomialMap φ (KoszulExterior.differential p (exteriorBasis (R := R) s)) =
      KoszulExterior.differential (fun i => φ (p i)) (polynomialMap φ (exteriorBasis (R := R) s))
    rw [exteriorBasis_as_blade s rfl, polynomialMap_blade]
    exact polynomialMap_differential_blade φ p _
  exact LinearMap.congr_fun h x

theorem polynomialMap_left_inverse (φ : Poly n R →+* Poly n S) (ψ : Poly n S →+* Poly n R)
    (h : Function.LeftInverse ψ φ) (x : Total n R) : polynomialMap ψ (polynomialMap φ x) = x := by
  apply (exteriorBasis (R := R)).repr.injective
  apply Finsupp.ext
  intro s
  rw [polynomialMap_repr, polynomialMap_repr, h]

end LeanCanny.Algebra.KoszulWeighted
