/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
/-! # Degree of a bounded parameter lift into the same raw joint variables -/
@[expose] public section
namespace LeanCanny.Algebra.SelectedMultivariatePolynomialLift
open Polynomial
open scoped Classical BigOperators
variable {A R : Type*} [CommRing A] [CommRing R] {m : ℕ}

theorem degree_of_coefficients (f : MvPolynomial (Fin (m+1)) R) (e G : ℕ)
    (he : (MvPolynomial.finSuccEquiv R m f).natDegree≤e)
    (hG : ∀ k,((MvPolynomial.finSuccEquiv R m f).coeff k).totalDegree≤G) :
    f.totalDegree≤e+G := by
  apply Finset.sup_le
  intro v hv
  have HC : ((MvPolynomial.finSuccEquiv R m f).coeff (v 0)).coeff v.tail≠0 :=by
    rw [MvPolynomial.finSuccEquiv_coeff_coeff,Finsupp.cons_tail]
    exact MvPolynomial.mem_support_iff.mp hv
  have HT : v.tail.sum (fun _ k=>k)≤G :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr HC)).trans (hG (v 0))
  have HK : v 0≤e :=
    (Polynomial.le_natDegree_of_ne_zero (fun H=>HC (by rw [H]; rfl))).trans he
  change v.sum (fun _ k=>k)≤e+G
  rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_succ]
  have HE : v.tail.sum (fun _ k=>k)=∑i : Fin m,v i.succ :=by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [HE] at HT
  exact Nat.add_le_add HK HT

theorem coefficient_degree (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ)
    (d e G : ℕ) (hG : ∀ a,(representative a).totalDegree≤G) (y : ℕ) :
    ((lift p representative d e).coeff y).totalDegree≤e+G := by
  have HE : MvPolynomial.finSuccEquiv ℤ m ((lift p representative d e).coeff y)=
      if y≤d then SelectedPolynomialLift.lift (p.coeff y) representative e else 0 :=by
    rw [lift,Polynomial.coeff_map]
    change (MvPolynomial.finSuccEquiv ℤ m) ((MvPolynomial.finSuccEquiv ℤ m).symm
      ((SelectedParameterPolynomialLift.lift p representative d e).coeff y))=_
    rw [AlgEquiv.apply_symm_apply]
    exact SelectedPolynomialLift.coefficient p (fun q=>SelectedPolynomialLift.lift q representative e) d y
  apply degree_of_coefficients _ e G
  · rw [HE]
    split_ifs
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [SelectedPolynomialLift.coefficient,ite_eq_right (by omega)]
    · simp
  · intro k
    rw [HE]
    split_ifs
    · rw [SelectedPolynomialLift.coefficient]
      split_ifs
      · exact hG _
      · simp
    · simp

end LeanCanny.Algebra.SelectedMultivariatePolynomialLift
