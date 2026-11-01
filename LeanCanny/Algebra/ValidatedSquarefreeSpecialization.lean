/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeSpecialization

/-! # Explicit squarefree preprocessing validated on one component

All polynomial arithmetic is over the original commutative coefficient
ring, which may have zero divisors. A finite principal-subresultant index
is validated only after specialization to a characteristic-zero field.
The constructed scaled quotient then preserves every specialized root and
is separable; no injectivity of the specialization is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.ValidatedSquarefreeSpecialization
open Polynomial PrincipalSubresultant
open scoped Classical
variable {R L : Type*} [CommRing R] [Field L] [CharZero L]

structure Valid (φ : R →+* L) (p : Polynomial R) (D k : ℕ) : Prop where
  index_lt : k < D
  leading : φ (p.coeff D) ≠ 0
  lower : ∀ j < k, φ (psc p p.derivative D (D - 1) j) = 0
  selected : φ (psc p p.derivative D (D - 1) k) ≠ 0

noncomputable def gcd (p : Polynomial R) (D k : ℕ) : Polynomial R :=
  coefficientForm p p.derivative D (D - 1) k

noncomputable def polynomial (p : Polynomial R) (D k : ℕ) : Polynomial R :=
  ScaledPolynomialQuotient.quotient (gcd p D k) p k (D - k)

omit [CharZero L] in
theorem mapped_degree (φ : R →+* L) (p : Polynomial R) (D k : ℕ)
    (hD : p.natDegree ≤ D) (v : Valid φ p D k) : (p.map φ).natDegree = D := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_map_le.trans hD)
  rw [Polynomial.coeff_map]
  exact v.leading

omit [CharZero L] in
theorem mapped_ne_zero (φ : R →+* L) (p : Polynomial R) (D k : ℕ) (v : Valid φ p D k) : p.map φ ≠ 0 := by
  intro HZ
  have H := congrArg (fun q : Polynomial L => q.coeff D) HZ
  rw [Polynomial.coeff_map, Polynomial.coeff_zero] at H
  exact v.leading H

theorem exists_valid (φ : R →+* L) (p : Polynomial R) (D : ℕ)
    (hD : (p.map φ).natDegree = D) (hpos : 0 < D) :
    ∃ k : Fin D, Valid φ p D k.val := by
  have HP : p.map φ ≠ 0 := by intro H; rw [H, Polynomial.natDegree_zero] at hD; omega
  have HD : (p.derivative.map φ).natDegree = D - 1 := by rw [← derivative_map, natDegree_derivative, hD]
  have HNZ : p.derivative.map φ ≠ 0 := by
    rw [← derivative_map]
    apply derivative_ne_zero.mpr
    rw [hD]
    omega
  have HLT : (p.derivative.map φ).natDegree < (p.map φ).natDegree := by rw [hD, HD]; omega
  have H := PrincipalSubresultant.gcd_data (p.map φ) (p.derivative.map φ) HNZ HLT
  let k := (EuclideanDomain.gcd (p.map φ) (p.derivative.map φ)).natDegree
  have HK : k < D := by
    have HE := Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (p.map φ) (p.derivative.map φ)) HNZ
    rw [HD] at HE
    omega
  refine ⟨⟨k, HK⟩, ⟨HK, ?_, ?_, ?_⟩⟩
  · have HE := Polynomial.leadingCoeff_ne_zero.mpr HP
    rw [Polynomial.leadingCoeff, hD, Polynomial.coeff_map] at HE
    exact HE
  · intro j hj
    have HE := H.2.2 j hj
    rw [hD, HD, psc_map_map] at HE
    exact HE
  · have HE := H.2.1
    rw [hD, HD, psc_map_map] at HE
    exact HE

theorem gcd_data (φ : R →+* L) (p : Polynomial R) (D k : ℕ)
    (hD : p.natDegree ≤ D) (v : Valid φ p D k) :
    Associated ((gcd p D k).map φ) (SquarefreePart.common (p.map φ)) ∧
      (SquarefreePart.common (p.map φ)).natDegree = k := by
  have HM := mapped_degree φ p D k hD v
  have HD : (p.derivative.map φ).natDegree = D - 1 := by rw [← derivative_map, natDegree_derivative, HM]
  have HNZ : p.derivative.map φ ≠ 0 := by
    rw [← derivative_map]
    apply derivative_ne_zero.mpr
    rw [HM]
    have H := v.index_lt
    omega
  have HLT : (p.derivative.map φ).natDegree < (p.map φ).natDegree := by
    rw [HM, HD]
    have H := v.index_lt
    omega
  have H := PrincipalSubresultant.gcd_data (p.map φ) (p.derivative.map φ) HNZ HLT
  have HK : (EuclideanDomain.gcd (p.map φ) (p.derivative.map φ)).natDegree = k := by
    apply Nat.le_antisymm
    · by_contra Hbad
      have HZ := H.2.2 k (by omega)
      rw [HM, HD, psc_map_map] at HZ
      exact v.selected HZ
    · by_contra Hbad
      have HZ := v.lower (EuclideanDomain.gcd (p.map φ) (p.derivative.map φ)).natDegree (by omega)
      have HNZ := H.2.1
      rw [HM, HD, psc_map_map] at HNZ
      exact HNZ HZ
  constructor
  · have HA := H.1
    rw [HM, HD, HK] at HA
    rw [gcd, coefficientForm_map]
    simpa only [SquarefreePart.common, derivative_map] using HA
  · simpa only [SquarefreePart.common, derivative_map] using HK

theorem associated_part (φ : R →+* L) (p : Polynomial R) (D k : ℕ)
    (hD : p.natDegree ≤ D) (v : Valid φ p D k) :
    Associated ((polynomial p D k).map φ) (SquarefreePart.part (p.map φ)) := by
  let P := p.map φ
  let G := (gcd p D k).map φ
  have HP : P ≠ 0 := mapped_ne_zero φ p D k v
  obtain ⟨HA, HK⟩ := gcd_data φ p D k hD v
  have HG : G ≠ 0 := HA.ne_zero_iff.mpr (SquarefreePart.common_ne_zero P HP)
  have Hdiv : G ∣ P := HA.dvd.trans (EuclideanDomain.gcd_dvd_left P P.derivative)
  have Hfact : G * (P / G) = P := EuclideanDomain.mul_div_cancel' HG Hdiv
  have Hquot : P / G ≠ 0 := by intro HZ; rw [HZ, mul_zero] at Hfact; exact HP Hfact.symm
  have HD : G.natDegree = k := (PrincipalSubresultant.natDegree_eq_of_associated HA).trans HK
  have HQ : (P / G).natDegree ≤ D - k := by
    have H := natDegree_mul HG Hquot
    rw [Hfact, HD] at H
    have HM : P.natDegree = D := mapped_degree φ p D k hD v
    omega
  have HAQ : Associated (P / G) (SquarefreePart.part P) :=
    Associated.of_mul_left (Associated.of_eq (Hfact.trans (SquarefreePart.factorization P HP).symm)) HA HG
  have HE : (polynomial p D k).map φ = C (G.coeff k ^ (D - k + 1)) * (P / G) := by
    rw [polynomial, ScaledPolynomialQuotient.quotient_map]
    change ScaledPolynomialQuotient.quotient G P _ _ = _
    have H := ScaledPolynomialQuotient.quotient_mul G (P / G) k (D - k) HD.le HQ
    rw [Hfact] at H
    exact H
  have HC : G.coeff k ≠ 0 := by rw [← HD, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr HG
  rw [HE]
  exact (associated_unit_mul_left (P / G) _
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ HC)))).trans HAQ

theorem separable (φ : R →+* L) (p : Polynomial R) (D k : ℕ)
    (hD : p.natDegree ≤ D) (v : Valid φ p D k) : ((polynomial p D k).map φ).Separable :=
  (associated_part φ p D k hD v).symm.separable
    (SquarefreePart.separable _ (mapped_ne_zero φ p D k v))

theorem roots_iff (φ : R →+* L) (p : Polynomial R) (D k : ℕ)
    (hD : p.natDegree ≤ D) (v : Valid φ p D k) (a : L) :
    (polynomial p D k).eval₂ φ a = 0 ↔ p.eval₂ φ a = 0 := by
  have HA := associated_part φ p D k hD v
  have HR : ((polynomial p D k).map φ).eval a = 0 ↔ (SquarefreePart.part (p.map φ)).eval a = 0 := by
    constructor
    · intro H
      obtain ⟨r, HE⟩ := HA.dvd
      rw [HE, eval_mul, H, zero_mul]
    · intro H
      obtain ⟨r, HE⟩ := HA.dvd'
      rw [HE, eval_mul, H, zero_mul]
  simpa only [Polynomial.eval_map, Polynomial.IsRoot] using
    HR.trans (SquarefreePart.roots_iff (p.map φ) (mapped_ne_zero φ p D k v) a)

end LeanCanny.Algebra.ValidatedSquarefreeSpecialization
