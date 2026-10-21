/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalQuotient

/-! # Permuting the normalized polynomial quotient

Simultaneously permuting the input forms and spatial coordinates preserves
the normalized universal polynomial value. The proof uses the already
proved common quotient for all universal orderings, before specializing.
It therefore does not require a nonzero specialized extraneous determinant.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def coefficientPermutation (π : Equiv.Perm (Fin n)) : CoefficientRing n ℤ →+* CoefficientRing n ℤ :=
  (MvPolynomial.rename (fun v : CoefficientIndex n => (π v.1, Finsupp.equivMapDomain π v.2))).toRingHom

theorem system_coefficientPermutation (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (system (R := ℤ) (d ∘ π) W (Equiv.refl _) i).map (coefficientPermutation π) = system d W π i := by
  rw [system, system, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Function.comp_apply, Equiv.refl_apply]
  by_cases h : (FixedWidthPolynomial.vector n W r).degree = d (π i)
  · simp [h, coefficientPermutation, Finsupp.equivMapDomain_refl]
  · simp [h]

theorem numerator_coefficientPermutation (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) :
    coefficientPermutation π (numerator (R := ℤ) (d ∘ π) W (Equiv.refl _)) = numerator d W π := by
  rw [numerator, Macaulay.det_activeMinor_map]
  have hs : (fun i => (system (R := ℤ) (d ∘ π) W (Equiv.refl _) i).map (coefficientPermutation π)) = system d W π :=
    funext (system_coefficientPermutation d W π)
  rw [hs]
  rfl

theorem denominator_coefficientPermutation (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) :
    coefficientPermutation π (denominator (R := ℤ) (d ∘ π) W (Equiv.refl _)) = denominator d W π := by
  rw [denominator, Macaulay.det_extraneousMinor_map]
  have hs : (fun i => (system (R := ℤ) (d ∘ π) W (Equiv.refl _) i).map (coefficientPermutation π)) = system d W π :=
    funext (system_coefficientPermutation d W π)
  rw [hs]
  rfl

theorem integerQuotient_permutation (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (π : Equiv.Perm (Fin (n + 1)))
    (hπ : Macaulay.level (d ∘ π) < 2 ^ W) :
    coefficientPermutation π (integerQuotient (d ∘ π) W (fun i => hdegree (π i)) hπ) = integerQuotient d W hdegree hW := by
  have he := congrArg (coefficientPermutation π)
    ((integerQuotient_spec (d ∘ π) W (fun i => hdegree (π i)) hπ).1 (Equiv.refl _))
  rw [numerator_coefficientPermutation, map_mul, denominator_coefficientPermutation] at he
  apply mul_left_cancel₀ (denominator_ne_zero (R := ℤ) d W hdegree π)
  exact he.symm.trans ((integerQuotient_spec d W hdegree hW).1 π)

theorem coeff_inverse_rename (π : Equiv.Perm (Fin n)) (p : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    p.coeff (Finsupp.equivMapDomain π m) = (MvPolynomial.rename π.symm p).coeff m := by
  have he := MvPolynomial.coeff_rename_mapDomain π π.injective (MvPolynomial.rename π.symm p) m
  rw [MvPolynomial.rename_rename, π.self_comp_symm, MvPolynomial.rename_id_apply] at he
  simpa only [← Finsupp.equivMapDomain_eq_mapDomain] using he

theorem coefficientSpecialization_permutation (π : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) :
    (coefficientSpecialization p).comp (coefficientPermutation π) =
      coefficientSpecialization (fun i => MvPolynomial.rename π.symm (p (π i))) := by
  apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
  intro v
  change coefficientSpecialization p (MvPolynomial.rename
      (fun v : CoefficientIndex (n + 1) => (π v.1, Finsupp.equivMapDomain π v.2)) (MvPolynomial.X v)) =
    coefficientSpecialization (fun i => MvPolynomial.rename π.symm (p (π i))) (MvPolynomial.X v)
  rw [MvPolynomial.rename_X]
  simp only [coefficientSpecialization, MvPolynomial.eval₂Hom_X']
  exact coeff_inverse_rename π (p (π v.1)) v.2

theorem polynomialValue_permutation (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (π : Equiv.Perm (Fin (n + 1)))
    (hπ : Macaulay.level (d ∘ π) < 2 ^ W) (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) :
    polynomialValue (d ∘ π) W (fun i => hdegree (π i)) hπ (fun i => MvPolynomial.rename π.symm (p (π i))) =
      polynomialValue d W hdegree hW p := by
  change coefficientSpecialization (fun i => MvPolynomial.rename π.symm (p (π i))) _ = _
  rw [← coefficientSpecialization_permutation, RingHom.comp_apply, integerQuotient_permutation]
  rfl

end LeanCanny.Algebra.MacaulayUniversal
