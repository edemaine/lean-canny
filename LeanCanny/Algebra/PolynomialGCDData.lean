/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantGCDGeneral
public import LeanCanny.Algebra.SubresultantBounds

/-! # An integer determinantal representative of the rational GCD

The selected coefficient form is associated to the rational GCD. Its integer
coefficients satisfy the existing Sylvester determinant height bound. Interior
orders use the existing subresultant polynomial; the terminal order is retained.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialGCDBits
open Polynomial PrincipalSubresultant
open scoped Classical

noncomputable def degree (p q : ℤ[X]) : ℕ :=
  (EuclideanDomain.gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))).natDegree

noncomputable def representative (p q : ℤ[X]) : ℤ[X] :=
  coefficientForm p q p.natDegree q.natDegree (degree p q)

theorem representative_associated (p q : ℤ[X]) (hq : q ≠ 0) (hlt : q.natDegree < p.natDegree) :
    Associated ((representative p q).map (Int.castRingHom ℚ))
      (EuclideanDomain.gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))) := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hq' : q.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hq
  have hlt' : (q.map (Int.castRingHom ℚ)).natDegree < (p.map (Int.castRingHom ℚ)).natDegree := by
    simpa only [natDegree_map_eq_of_injective hi] using hlt
  have h := (gcd_data _ _ hq' hlt').1
  simpa only [representative, coefficientForm_map, degree, natDegree_map_eq_of_injective hi] using h

theorem representative_ne_zero (p q : ℤ[X]) (hq : q ≠ 0) (hlt : q.natDegree < p.natDegree) :
    representative p q ≠ 0 := by
  have ha := representative_associated p q hq hlt
  have hn : EuclideanDomain.gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)) ≠ 0 := by
    intro hz
    have hq' := (EuclideanDomain.gcd_eq_zero_iff.mp hz).2
    exact hq ((Polynomial.map_eq_zero_iff Int.cast_injective).mp hq')
  intro hz
  exact (ha.ne_zero_iff.mpr hn) (by rw [hz, Polynomial.map_zero])

theorem representative_natDegree (p q : ℤ[X]) (hq : q ≠ 0) (hlt : q.natDegree < p.natDegree) :
    (representative p q).natDegree = degree p q := by
  have h := natDegree_eq_of_associated (representative_associated p q hq hlt)
  simpa only [degree, natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)] using h

theorem representative_interior (p q : ℤ[X]) (h : degree p q < p.natDegree ∧ degree p q < q.natDegree) :
    representative p q = Subresultant.polynomial p q p.natDegree q.natDegree (degree p q) :=
  coefficientForm_eq_subresultant _ _ _ _ _ h

theorem representative_terminal (p q : ℤ[X]) (hd : degree p q = q.natDegree)
    (hlt : q.natDegree < p.natDegree) :
    representative p q = C (q.leadingCoeff ^ (p.natDegree - q.natDegree - 1)) * q := by
  rw [representative, hd, coefficientForm_terminal p q _ _ le_rfl hlt, coeff_natDegree]

theorem representative_coeff_size (p q : ℤ[X]) (bp bq k : ℕ)
    (hp : ∀ i, (p.coeff i).natAbs ≤ 2 ^ bp) (hq : ∀ i, (q.coeff i).natAbs ≤ 2 ^ bq) :
    ((representative p q).coeff k).natAbs.size ≤
      (p.natDegree + q.natDegree).size * (p.natDegree + q.natDegree) +
        p.natDegree * bq + q.natDegree * bp + 1 := by
  rw [representative, coefficientForm_coeff]
  split_ifs
  · rw [subresultantCoeff_eq_minor_det]
    exact (Subresultant.minor_det_size_le p q _ _ _ _ bp bq hp hq).trans (Subresultant.budget_le_full _ _ _ _ _)
  · exact Nat.zero_le _

end LeanCanny.Algebra.PolynomialGCDBits
