/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientSelectedMultivariateLift
public import LeanCanny.Algebra.RationalMonomialBivariateShift
public import LeanCanny.Algebra.FixedWidthBivariateParameterPairSpace
public import LeanCanny.Algebra.FixedWidthTarskiPrincipalSpace
/-! # Coefficient-base constructors for literal eta and epsilon principal tests -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open Polynomial PrincipalSubresultant
open scoped Classical BigOperators
variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

theorem clear_map {σ τ : Type*} [Fintype σ] (φ : R →+* S) (D : ℕ) (q : R)
    (v : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    MvPolynomial.map φ (CommonDenominatorSpecialization.clear D q v p) =
      CommonDenominatorSpecialization.clear D (φ q) (fun i => MvPolynomial.map φ (v i)) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    simp only [CommonDenominatorSpecialization.monomial, MvPolynomial.map_monomial,
      CommonDenominatorSpecialization.factor, map_mul, map_prod, map_pow, MvPolynomial.map_C]
  | add p r hp hr => simp only [map_add, hp, hr]

noncomputable def monomial (index w : ℕ) (a : R) : MvPolynomial (Fin m) R :=
  if hi : index < m then MvPolynomial.monomial (Finsupp.single ⟨index, hi⟩ w) a else 0

theorem monomial_map (φ : R →+* S) (index w : ℕ) (a : R) :
    MvPolynomial.map φ (monomial (m := m) index w a) = monomial index w (φ a) := by
  unfold monomial
  split_ifs <;> simp only [MvPolynomial.map_monomial, map_zero]

noncomputable def parameterNumerator (q a : R) (index w : ℕ) (negative : Bool) :
    MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.rename Fin.succ (monomial index w a)+
    if negative then -(MvPolynomial.C q*MvPolynomial.X 0) else MvPolynomial.C q*MvPolynomial.X 0

noncomputable def numerators (q a : R) (index w : ℕ) (negative : Bool) :
    Fin (m+1) → MvPolynomial (Fin (m+1)) R :=
  Fin.cases (parameterNumerator q a index w negative) (fun i => MvPolynomial.C q*MvPolynomial.X i.succ)

theorem numerators_map (φ : R →+* S) (q a : R) (index w : ℕ) (negative : Bool) (i : Fin (m+1)) :
    MvPolynomial.map φ (numerators q a index w negative i) = numerators (φ q) (φ a) index w negative i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [numerators, Fin.cases_zero, parameterNumerator, map_add, MvPolynomial.map_rename,
      monomial_map]
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_neg, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_X]
  · simp only [numerators, Fin.cases_succ, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

noncomputable def shiftedHead (p : Polynomial (MvPolynomial (Fin (m+1)) R))
    (D : ℕ) (q a : R) (index w : ℕ) (negative : Bool) : Polynomial (MvPolynomial (Fin (m+1)) R) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.mapRange
    (CommonDenominatorSpecialization.clear (2*D) q (numerators q a index w negative)) (map_zero _)
    (AddMonoidAlgebra.coeff p.toFinsupp)))

theorem shifted_coefficient (p : Polynomial (MvPolynomial (Fin (m+1)) R))
    (D : ℕ) (q a : R) (index w : ℕ) (negative : Bool) (y : ℕ) :
    (shiftedHead p D q a index w negative).coeff y =
      CommonDenominatorSpecialization.clear (2*D) q (numerators q a index w negative) (p.coeff y) := rfl

theorem shiftedHead_map (φ : R →+* S) (p : Polynomial (MvPolynomial (Fin (m+1)) R))
    (D : ℕ) (q a : R) (index w : ℕ) (negative : Bool) :
    (shiftedHead p D q a index w negative).map (MvPolynomial.map φ) =
      shiftedHead (p.map (MvPolynomial.map φ)) D (φ q) (φ a) index w negative := by
  apply Polynomial.ext
  intro y
  rw [Polynomial.coeff_map, shifted_coefficient, shifted_coefficient, Polynomial.coeff_map, clear_map]
  have HN : (fun i : Fin (m+1) => MvPolynomial.map φ (numerators q a index w negative i)) =
      numerators (φ q) (φ a) index w negative := funext (numerators_map φ q a index w negative)
  rw [HN]

noncomputable def window (q a : R) (index w : ℕ) (negative : Bool) :
    Polynomial (MvPolynomial (Fin (m+1)) R) :=
  let eps := MvPolynomial.C (q^2)*MvPolynomial.X 0
  let raw := monomial (m := m) index w (q*a)
  Polynomial.C (MvPolynomial.C (q^2))*Polynomial.X+
    Polynomial.C ((if negative then -eps else eps)-MvPolynomial.rename Fin.succ raw)

theorem window_map (φ : R →+* S) (q a : R) (index w : ℕ) (negative : Bool) :
    (window (m := m) q a index w negative).map (MvPolynomial.map φ) =
      window (φ q) (φ a) index w negative := by
  unfold window
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C]
  cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    map_sub, map_neg, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.map_rename, monomial_map]

/-- Axis zero is eta, axis one is epsilon, with the literal installed embedding. -/
noncomputable def pairLift (keep : Bool) (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    Polynomial (MvPolynomial (Fin (1+(m+1))) R) :=
  p.map (MvPolynomial.rename (FixedWidthBivariateParameterPairBits.embedding keep m)).toRingHom

theorem pairLift_map (φ : R →+* S) (keep : Bool) (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    (pairLift keep p).map (MvPolynomial.map φ) = pairLift keep (p.map (MvPolynomial.map φ)) := by
  apply Polynomial.ext
  intro y
  simp only [pairLift, Polynomial.coeff_map]
  change MvPolynomial.map φ (MvPolynomial.rename _ (p.coeff y)) =
    MvPolynomial.rename _ (MvPolynomial.map φ (p.coeff y))
  exact MvPolynomial.map_rename _ _ _

noncomputable def principal {σ : Type*} (p q : Polynomial (MvPolynomial σ R)) (d s D j : ℕ) : MvPolynomial σ R :=
  signedPsc p (PseudoRemainder.seed p q d D) d s j

theorem principal_map {σ : Type*} (φ : R →+* S) (p q : Polynomial (MvPolynomial σ R)) (d s D j : ℕ) :
    MvPolynomial.map φ (principal p q d s D j) =
      principal (p.map (MvPolynomial.map φ)) (q.map (MvPolynomial.map φ)) d s D j := by
  rw [principal, ← signedPsc_map_map, ← PseudoRemainder.seed_map]
  rfl

theorem shiftedHead_int (F : RationalMonomialWindowQuery.Family) (negative : Bool) (W : List Bool → ℕ)
    (p : (c : List Bool) → Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) :
    shiftedHead (p c) (RationalMonomialParameterShift.sourceDegree F W c)
      (F.scalars.denominator c) (F.scalars.numerator c) (F.index c) (F.weight c) negative =
      RationalMonomialBivariateShift.head F negative W p c := rfl

theorem window_int (F : RationalMonomialWindowQuery.Family) (negative : Bool) (c : List Bool) :
    window (m := F.arity c) (F.scalars.denominator c) (F.scalars.numerator c) (F.index c) (F.weight c) negative =
      RationalMonomialWindowQuery.query F negative c := rfl

theorem principal_int (F : FixedWidthTarskiPrincipalBits.Family) (c : List Bool) (j : ℕ) :
    principal (F.head c) (F.query c) (F.degree c) (F.seedDegree c) (F.bound c) j =
      FixedWidthTarskiPrincipalBits.polynomial F c j := rfl

end LeanCanny.Algebra.CoefficientTarskiParameterQueries
