/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoefficientDivision

/-! # Coefficient extension in canonical exterior coordinates

A coefficient homomorphism acts semilinearly on the polynomial exterior
algebra by applying it to every ordered exterior coordinate. It preserves
monomial exterior words and commutes with coordinate insertion and the
Koszul differential.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def coefficientMap (φ : R →+* S) :
    Total n R →ₛₗ[(MvPolynomial.map φ : Poly n R →+* Poly n S)] Total n S :=
  (exteriorBasis (R := S)).repr.symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (MvPolynomial.map φ : Poly n R →+* Poly n S).toSemilinearMap).comp
      (exteriorBasis (R := R)).repr.toLinearMap)

theorem coefficientMap_repr (φ : R →+* S) (x : Total n R) (s : Finset (Fin n)) :
    (exteriorBasis (R := S)).repr (coefficientMap φ x) s =
      ((exteriorBasis (R := R)).repr x s).map φ := by
  change (exteriorBasis (R := S)).repr ((exteriorBasis (R := S)).repr.symm _) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem coefficientMap_exteriorBasis (φ : R →+* S) (s : Finset (Fin n)) :
    coefficientMap φ (exteriorBasis (R := R) s) = exteriorBasis (R := S) s := by
  apply (exteriorBasis (R := S)).repr.injective
  apply Finsupp.ext
  intro t
  rw [coefficientMap_repr, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem coefficientMap_ambientBasis (φ : R →+* S) (a : AmbientIndex n) :
    coefficientMap φ (ambientBasis (R := R) a) = ambientBasis (R := S) a := by
  rcases a with ⟨m, s⟩
  rw [ambientBasis_apply, map_smulₛₗ, coefficientMap_exteriorBasis, MvPolynomial.map_monomial, map_one,
    ambientBasis_apply]

theorem monomialBlade_perm_zsmul {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin k)) :
    monomialBlade (R := R) (v ∘ σ) m = (σ.sign : ℤ) • monomialBlade (R := R) v m := by
  simpa only [Int.cast_smul_eq_zsmul] using monomialBlade_perm (R := R) v m σ

theorem coefficientMap_monomialBlade (φ : R →+* S) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    coefficientMap φ (monomialBlade (R := R) v m) = monomialBlade (R := S) v m := by
  by_cases hv : Function.Injective v
  · apply (sortPermutation v hv).sign.isUnit.smul_left_cancel.mp
    rw [← map_zsmul, ← monomialBlade_perm_zsmul, monomialBlade_sorted, coefficientMap_ambientBasis,
      ← monomialBlade_sorted v hv m, monomialBlade_perm_zsmul]
  · simp only [monomialBlade, blade_eq_zero_of_not_injective v hv, smul_zero, map_zero]

theorem monomialBlade_zero_exponent {k : ℕ} (v : Fin k → Fin n) :
    monomialBlade (R := R) v 0 = blade (R := R) v := by
  rw [monomialBlade, ← MvPolynomial.C_apply, map_one, one_smul]

theorem coefficientMap_wedge (φ : R →+* S) (i : Fin n) (x : Total n R) :
    coefficientMap φ (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S) (coefficientMap φ x) := by
  have h : (coefficientMap (n := n) φ).comp (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)) =
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S)).comp (coefficientMap φ) := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change coefficientMap φ (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (exteriorBasis (R := R) s)) =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n S) (coefficientMap φ (exteriorBasis (R := R) s))
    rw [exteriorBasis_as_blade s rfl, ← monomialBlade_zero_exponent, wedge_monomialBlade,
      coefficientMap_monomialBlade, coefficientMap_monomialBlade, wedge_monomialBlade]
  exact LinearMap.congr_fun h x

theorem differential_word_succ (p : Fin n → Poly n R) {k : ℕ} (v : Fin (k + 1) → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential p (monomialBlade (R := R) v m) =
      p (v 0) • monomialBlade (R := R) (Matrix.vecTail v) m -
      KoszulExterior.wedge (Pi.single (v 0) 1 : Fin n → Poly n R)
        (KoszulExterior.differential p (monomialBlade (R := R) (Matrix.vecTail v) m)) := by
  rw [differential_monomialBlade_succ]
  congr 1
  rw [monomialBlade, smul_smul, mul_comm]

theorem coefficientMap_differential_word (φ : R →+* S) (p : Fin n → Poly n R)
    {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    coefficientMap φ (KoszulExterior.differential p (monomialBlade (R := R) v m)) =
      KoszulExterior.differential (fun i => (p i).map φ) (monomialBlade (R := S) v m) := by
  induction k with
  | zero => rw [differential_monomialBlade_zero, map_zero, differential_monomialBlade_zero]
  | succ k ih =>
    rw [differential_word_succ, map_sub, map_smulₛₗ, coefficientMap_monomialBlade, coefficientMap_wedge, ih,
      differential_word_succ]

theorem coefficientMap_differential (φ : R →+* S) (p : Fin n → Poly n R) (x : Total n R) :
    coefficientMap φ (KoszulExterior.differential p x) =
      KoszulExterior.differential (fun i => (p i).map φ) (coefficientMap φ x) := by
  have h : (coefficientMap (n := n) φ).comp (KoszulExterior.differential p) =
      (KoszulExterior.differential (fun i => (p i).map φ)).comp (coefficientMap φ) := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change coefficientMap φ (KoszulExterior.differential p (exteriorBasis (R := R) s)) =
      KoszulExterior.differential (fun i => (p i).map φ) (coefficientMap φ (exteriorBasis (R := R) s))
    rw [exteriorBasis_as_blade s rfl, ← monomialBlade_zero_exponent, coefficientMap_monomialBlade]
    exact coefficientMap_differential_word φ p _ _
  exact LinearMap.congr_fun h x

end LeanCanny.Algebra.KoszulWeighted
