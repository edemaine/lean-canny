/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasis
public import LeanCanny.Algebra.PaddedIntegralNormalization

/-! # Canonical scalar equations in bounded prefix coordinates

Replace each coefficient by its canonical monomial-basis representative.
The resulting explicit polynomial specializes to the original equation.
Monic equations stay monic, with every coefficient bounded by the old basis
degree m*(N-1), independently of its original formula or algebra rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {m N : ℕ}

theorem representative_zero (b : IntegralCoordinateBasis A m N) : b.representative 0 = 0 := by
  simp [representative]

theorem representative_one (b : IntegralCoordinateBasis A m N) (hN : 0 < N) :
    b.representative 1 = 1 := by
  have HR : b.basis.repr 1 = Finsupp.single (zeroIndex m N hN) 1 := by
    rw [← b.basis_zero hN, Module.Basis.repr_self]
  rw [representative, HR, Finset.sum_eq_single (zeroIndex m N hN)]
  · have HZ : exponent (zeroIndex m N hN) = 0 := by ext i; rfl
    rw [Finsupp.single_eq_same, HZ, monomial_zero', map_one]
  · intro e _ he
    simp [Finsupp.single_eq_of_ne he]
  · simp

noncomputable def polynomial (b : IntegralCoordinateBasis A m N) (p : Polynomial A) :
    Polynomial (MvPolynomial (Fin m) ℤ) :=
  ∑ i ∈ p.support, Polynomial.monomial i (b.representative (p.coeff i))

theorem polynomial_coefficient (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (i : ℕ) :
    (b.polynomial p).coeff i = b.representative (p.coeff i) := by
  rw [polynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  by_cases hi : i ∈ p.support
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, Polynomial.notMem_support_iff.mp hi, representative_zero]

theorem polynomial_coefficient_degree (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (i : ℕ) :
    ((b.polynomial p).coeff i).totalDegree ≤ m * (N - 1) := by
  rw [polynomial_coefficient]
  exact b.representative_degree _

theorem polynomial_map (b : IntegralCoordinateBasis A m N) (p : Polynomial A) :
    (b.polynomial p).map (MvPolynomial.aeval b.generator).toRingHom = p := by
  ext i
  rw [Polynomial.coeff_map, polynomial_coefficient]
  exact b.representative_eval _

theorem polynomial_eval {K : Type*} [CommRing K] (b : IntegralCoordinateBasis A m N) (p : Polynomial A)
    (φ : A →ₐ[ℤ] K) (x : K) :
    (b.polynomial p).eval₂ (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom x = p.eval₂ φ.toRingHom x := by
  have HM : (b.polynomial p).map (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom = p.map φ.toRingHom := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, polynomial_coefficient]
    have HE := MvPolynomial.comp_aeval_apply (φ := φ) (p := b.representative (p.coeff i)) (f := b.generator)
    rw [b.representative_eval] at HE
    exact HE.symm
  have H := congrArg (fun q : Polynomial K => q.eval x) HM
  simpa only [Polynomial.eval_map] using H

theorem polynomial_monic [Nontrivial A] (b : IntegralCoordinateBasis A m N) (hN : 0 < N)
    (p : Polynomial A) (hp : p.Monic) : (b.polynomial p).Monic ∧ (b.polynomial p).natDegree = p.natDegree := by
  have HD : (b.polynomial p).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [polynomial_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt hi, representative_zero]
  have HT : (b.polynomial p).coeff p.natDegree = 1 := by
    rw [polynomial_coefficient, Polynomial.coeff_natDegree, hp.leadingCoeff, representative_one b hN]
  have HE : (b.polynomial p).natDegree = p.natDegree := Nat.le_antisymm HD (Polynomial.le_natDegree_of_ne_zero (by rw [HT]; exact one_ne_zero))
  refine ⟨?_, HE⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, HE, HT]

end LeanCanny.Algebra.IntegralCoordinateBasis
