/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoefficientMap

/-! # Exterior support of monomial words and coordinate insertion

A monomial exterior word has no coordinate outside its underlying subset.
Insertion of coordinate `i` has zero coefficient on every subset omitting
`i`. These statements hold over any commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem exteriorBasis_repr_monomialBlade_eq_zero {k : ℕ} (v : Fin k → Fin n)
    (m : Fin n →₀ ℕ) (s : Finset (Fin n)) (hs : Finset.univ.image v ≠ s) :
    (exteriorBasis (R := R)).repr (monomialBlade (R := R) v m) s = 0 := by
  by_cases hv : Function.Injective v
  · apply (sortPermutation v hv).sign.isUnit.smul_left_cancel.mp
    have he := congrArg (fun x : Total n R => (exteriorBasis (R := R)).repr x s)
      (monomialBlade_sorted (R := R) v hv m)
    rw [monomialBlade_perm_zsmul, map_zsmul, Finsupp.smul_apply,
      ambientBasis_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply,
      ite_eq_right hs, smul_zero] at he
    exact he.trans (smul_zero _).symm
  · rw [monomialBlade, blade_eq_zero_of_not_injective v hv, smul_zero, map_zero, Finsupp.zero_apply]

theorem exteriorBasis_repr_wedge_eq_zero (i : Fin n) (x : Total n R) (s : Finset (Fin n))
    (hi : i ∉ s) :
    (exteriorBasis (R := R)).repr
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) s = 0 := by
  have he : (Finsupp.lapply s).comp ((exteriorBasis (R := R)).repr.toLinearMap.comp
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R))) = 0 := by
    apply (exteriorBasis (R := R)).ext
    intro t
    change (exteriorBasis (R := R)).repr
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (exteriorBasis (R := R) t)) s = 0
    rw [exteriorBasis_as_blade t rfl, ← monomialBlade_zero_exponent, wedge_monomialBlade]
    apply exteriorBasis_repr_monomialBlade_eq_zero
    intro ht
    apply hi
    rw [← ht]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  exact LinearMap.congr_fun he x

theorem exteriorBasis_repr_smul_basis (q : Poly n R) (s t : Finset (Fin n)) :
    (exteriorBasis (R := R)).repr (q • exteriorBasis (R := R) s) t = if s = t then q else 0 := by
  rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
  split_ifs <;> simp only [smul_eq_mul, mul_one, mul_zero]

end LeanCanny.Algebra.KoszulWeighted
