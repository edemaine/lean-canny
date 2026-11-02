/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
public import LeanCanny.Algebra.MvCoefficientMass
/-! # A finite parameter lift preserves the original coefficient-mass budget -/
@[expose] public section
namespace LeanCanny.Algebra.SelectedMultivariatePolynomialLift
open Polynomial
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] {m : ℕ}

private theorem rename_tail (a : MvPolynomial (Fin m) ℤ) :
    MvPolynomial.finSuccEquiv ℤ m (MvPolynomial.rename Fin.succ a)=Polynomial.C a :=by
  have HE : (MvPolynomial.finSuccEquiv ℤ m).toRingEquiv.toRingHom.comp
      (MvPolynomial.rename (Fin.succ : Fin m→Fin (m+1))).toRingHom=Polynomial.C :=by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      simp [MvPolynomial.finSuccEquiv_apply]
  exact congrArg (fun f=>f a) HE

private theorem symm_monomial (a : MvPolynomial (Fin m) ℤ) (k : ℕ) :
    (MvPolynomial.finSuccEquiv ℤ m).symm (Polynomial.monomial k a)=
      MvPolynomial.rename Fin.succ a*(MvPolynomial.X (0:Fin (m+1)))^k :=by
  apply (MvPolynomial.finSuccEquiv ℤ m).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,map_pow,rename_tail,MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.C_mul_X_pow_eq_monomial]

private theorem symm_monomial_mass (a : MvPolynomial (Fin m) ℤ) (k : ℕ) :
    MvMass.mass ((MvPolynomial.finSuccEquiv ℤ m).symm (Polynomial.monomial k a))≤MvMass.mass a :=by
  rw [symm_monomial]
  have HX : MvMass.mass ((MvPolynomial.X (0:Fin (m+1)) : MvPolynomial (Fin (m+1)) ℤ)^k)≤1 :=by
    simpa only [MvMass.X,one_pow] using MvMass.pow_le (MvPolynomial.X (0:Fin (m+1)) : MvPolynomial (Fin (m+1)) ℤ) k
  exact (MvMass.mul_le _ _).trans ((Nat.mul_le_mul (MvMass.rename_le Fin.succ a) HX).trans_eq (Nat.mul_one _))

theorem coefficient_mass (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ)
    (d e H y : ℕ) (hG : ∀ k≤e,MvMass.mass (representative ((p.coeff y).coeff k))≤2^H) :
    MvMass.mass ((lift p representative d e).coeff y)≤(e+1)*2^H :=by
  unfold lift
  rw [Polynomial.coeff_map]
  change MvMass.mass ((MvPolynomial.finSuccEquiv ℤ m).symm
    ((SelectedParameterPolynomialLift.lift p representative d e).coeff y))≤_
  unfold SelectedParameterPolynomialLift.lift
  rw [SelectedPolynomialLift.coefficient]
  by_cases hy : y≤d
  · rw [ite_eq_left hy]
    unfold SelectedPolynomialLift.lift
    rw [map_sum]
    apply (MvMass.sum_le _ _).trans
    apply (Finset.sum_le_sum (fun k hk=>(symm_monomial_mass _ k).trans (hG k (by
      have HK:=Finset.mem_range.mp hk; omega)))).trans_eq
    simp
  · rw [ite_eq_right hy,map_zero,MvMass.zero]
    exact Nat.zero_le _

theorem coefficient_mass_pow (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ)
    (d e H y : ℕ) (hG : ∀ k≤e,MvMass.mass (representative ((p.coeff y).coeff k))≤2^H) :
    MvMass.mass ((lift p representative d e).coeff y)≤2^(H+(e+1).size) :=
  (coefficient_mass p representative d e H y hG).trans
    ((Nat.mul_le_mul_right _ (Nat.lt_size_self (e+1)).le).trans_eq (by rw [←pow_add,Nat.add_comm]))

end LeanCanny.Algebra.SelectedMultivariatePolynomialLift
