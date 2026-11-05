/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientHeightBank
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSource
public import LeanCanny.Algebra.RelativeValueSystemMap

/-! # Fixed-degree univariate clearing at an actual common-bank monomial

The degree and creating power are explicit syntax. Coefficient maps may kill
leading coefficients; the fixed clearing recipe still commutes exactly.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientBankUnivariateQuery
open Polynomial
open scoped Classical BigOperators
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

noncomputable def polynomial (p : Polynomial R) (D w : ℕ) (a b : R) : Polynomial R :=
  Polynomial.expand R w (UnivariateRational.clear D p (C a * X) (C b))

noncomputable def physical {ι : Type*} (p : Polynomial R) (D w : ℕ) (a b : R) (column : ι) :
    MvPolynomial ι R := (polynomial p D w a b).toMvPolynomial column

theorem polynomial_map (φ : R →+* S) (p : Polynomial R) (D w : ℕ) (a b : R) :
    (polynomial p D w a b).map φ = polynomial (p.map φ) D w (φ a) (φ b) := by
  simp only [polynomial, Polynomial.map_expand, UnivariateRational.clear_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

theorem physical_map {ι : Type*} (φ : R →+* S) (p : Polynomial R) (D w : ℕ)
    (a b : R) (column : ι) :
    MvPolynomial.map φ (physical p D w a b column) =
      physical (p.map φ) D w (φ a) (φ b) column := by
  rw [physical, RelativeValueSystemMap.coordinate, polynomial_map]
  rfl

noncomputable def bankPolynomial {m : ℕ} (x : CoefficientHeightBank R A m) (i : Fin m)
    (p : Polynomial R) (D w : ℕ) : Polynomial R :=
  polynomial p D w (x.cofactor i) x.commonDenominator

noncomputable def bankPhysical {m : ℕ} {ι : Type*} (x : CoefficientHeightBank R A m) (i : Fin m)
    (p : Polynomial R) (D w : ℕ) (column : ι) : MvPolynomial ι R :=
  physical p D w (x.cofactor i) x.commonDenominator column

theorem bankPolynomial_map [Algebra R A] [Algebra S B] {m : ℕ}
    (φ : R →+* S) (ψ : A →+* B) {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank S B m}
    (H : x.Specializes φ ψ y) (i : Fin m) (p : Polynomial R) (D w : ℕ) :
    (bankPolynomial x i p D w).map φ = bankPolynomial y i (p.map φ) D w := by
  rw [bankPolynomial, polynomial_map, H.cofactor, H.commonDenominator]
  rfl

theorem bankPhysical_map [Algebra R A] [Algebra S B] {m : ℕ} {ι : Type*}
    (φ : R →+* S) (ψ : A →+* B) {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank S B m}
    (H : x.Specializes φ ψ y) (i : Fin m) (p : Polynomial R) (D w : ℕ) (column : ι) :
    MvPolynomial.map φ (bankPhysical x i p D w column) = bankPhysical y i (p.map φ) D w column := by
  rw [bankPhysical, physical_map, H.cofactor, H.commonDenominator]
  rfl

/-- The finite omitted-factor product is the native total-natural-index recipe. -/
theorem cofactor_ite {m : ℕ} (x : CoefficientHeightBank R A m) (i : Fin m) :
    x.cofactor i = ∏ j : Fin m, if j.val = i.val then 1 else x.denominator j := by
  unfold CoefficientHeightBank.cofactor
  simp only [Fin.val_inj]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact (ite_eq_right (Finset.mem_erase.mp hj).1).symm

/-- Exact installed native source, without replacing its advertised degree. -/
theorem polynomial_native (source : IntegerPolynomialRootQueriesBits.Source)
    (point : IntegerPolynomialRationalPointSource.Scalars) (w : List Bool → ℕ) (c : List Bool) :
    polynomial (source.polynomial c) (2 * source.degree c) (w c)
      (point.numerator c) (point.denominator c) =
      (IntegerPolynomialRationalPointSource.source source point w).polynomial c := rfl

end LeanCanny.Algebra.CoefficientBankUnivariateQuery
