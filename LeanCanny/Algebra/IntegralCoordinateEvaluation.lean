/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinatePolynomial

/-! # Exact evaluation and uniqueness for canonical scalar coordinates

Evaluating a canonical representative commutes with every integer-algebra
homomorphism. The bounded coordinate generators therefore determine that
homomorphism uniquely, even for a nonreduced prefix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A K : Type*} [CommRing A] [CommRing K] {m N : ℕ}

theorem representative_basis (b : IntegralCoordinateBasis A m N) (e : Fin m → Fin N) :
    b.representative (b.basis e) = monomial (exponent e) 1 := by
  rw [representative, Module.Basis.repr_self, Finset.sum_eq_single e]
  · rw [Finsupp.single_eq_same]
  · intro f _ hfe
    rw [Finsupp.single_eq_of_ne hfe, map_zero]
  · simp

theorem representative_eval_algHom (b : IntegralCoordinateBasis A m N) (x : A) (φ : A →ₐ[ℤ] K) :
    (b.representative x).aeval (fun i => φ (b.generator i)) = φ x := by
  have HE := MvPolynomial.comp_aeval_apply (φ := φ) (p := b.representative x) (f := b.generator)
  rw [b.representative_eval] at HE
  exact HE.symm

theorem algHom_ext (b : IntegralCoordinateBasis A m N) (φ ψ : A →ₐ[ℤ] K)
    (h : ∀ i, φ (b.generator i) = ψ (b.generator i)) : φ = ψ := by
  ext x
  rw [← representative_eval_algHom b x φ, ← representative_eval_algHom b x ψ]
  congr 1
  congr 1
  exact funext h

end LeanCanny.Algebra.IntegralCoordinateBasis
