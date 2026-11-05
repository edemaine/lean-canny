/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankTermQuery
public import LeanCanny.Algebra.CoefficientBankUnivariateQuery
/-! # Original univariate leaves cleared at their own physical bank column -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientBankLeafQuery
open Polynomial
open scoped Classical
variable {R S:Type*} [CommRing R] [CommRing S]

noncomputable def polynomial (A:CoefficientBankTermQuery.Arguments R) (p:Polynomial R) (D i:ℕ):
    MvPolynomial (Fin A.dimension) R:=
  if hi:i<A.birth then
    CoefficientBankUnivariateQuery.physical p D
      (UniformIntegralPowerSchedule.birth A.horizon (2^A.width) i)
      (A.cofactor (A.birth-1-i)) A.common (A.column ⟨A.birth-1-i,by omega⟩)
  else 0

theorem polynomial_map (φ:R→+*S) (A:CoefficientBankTermQuery.Arguments R) (p:Polynomial R) (D i:ℕ):
    MvPolynomial.map φ (polynomial A p D i)=polynomial (A.map φ) (p.map φ) D i:=by
  unfold polynomial CoefficientBankTermQuery.Arguments.map
  split_ifs
  · exact CoefficientBankUnivariateQuery.physical_map φ _ _ _ _ _ _
  · exact map_zero _

theorem polynomial_heq_of_eq (A B:CoefficientBankTermQuery.Arguments R) (h:A=B)
    (p:Polynomial R) (D i:ℕ):HEq (polynomial A p D i) (polynomial B p D i):=by
  cases h
  rfl

noncomputable def scalars (A:CoefficientBankTermQuery.Arguments ℤ) (i:ℕ):
    IntegerPolynomialRationalPointSource.Scalars where
  numerator _:=A.cofactor (A.birth-1-i)
  denominator _:=A.common
  mass _:=max (A.cofactor (A.birth-1-i)).natAbs.size A.common.natAbs.size
  numerator_bound _:= (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  denominator_bound _:= (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

/-- The advertised clearing degree is copied literally from the actual source. -/
theorem polynomial_native (A:CoefficientBankTermQuery.Arguments ℤ)
    (source:IntegerPolynomialRootQueriesBits.Source) (q:List Bool) (i:ℕ) (hi:i<A.birth):
    polynomial A (source.polynomial q) (2*source.degree q) i=
      ((IntegerPolynomialRationalPointSource.source source
        (scalars A i)
        (fun _=>UniformIntegralPowerSchedule.birth A.horizon (2^A.width) i)).polynomial q).toMvPolynomial
          (A.column ⟨A.birth-1-i,by omega⟩):=by
  simp only [polynomial,dite_eq_left hi]
  exact congrArg (fun p:ℤ[X]=>p.toMvPolynomial (A.column ⟨A.birth-1-i,by omega⟩))
    (CoefficientBankUnivariateQuery.polynomial_native source
      (scalars A i)
      (fun _=>UniformIntegralPowerSchedule.birth A.horizon (2^A.width) i) q)

end LeanCanny.Algebra.CoefficientBankLeafQuery
