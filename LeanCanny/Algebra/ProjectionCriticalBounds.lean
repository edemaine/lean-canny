/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCriticalFamily
public import LeanCanny.Algebra.PartialDerivativeDegree
public import LeanCanny.Algebra.CoefficientMass

/-! # Degree and coefficient budgets for spatial critical slice equations -/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionCriticalBounds
open MvPolynomial
open scoped Classical

variable {ι : Type*} [DecidableEq ι]

def massExponent (b D U : ℕ) : ℕ := b + ((D + 1) * (U + 1)).size

omit [DecidableEq ι] in
theorem partial_parameter_degree (q : MvPolynomial ι (Polynomial ℤ)) (E : ℕ)
    (hq : ∀ e, (q.coeff e).natDegree ≤ E) (i : ι) (e : ι →₀ ℕ) :
    ((pderiv i q).coeff e).natDegree ≤ E := by
  rw [coeff_pderiv]
  have hs : (e i : Polynomial ℤ) + 1 = Polynomial.C ((e i + 1 : ℕ) : ℤ) := by simp
  rw [hs]
  exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, Nat.add_zero] using hq _)

omit [DecidableEq ι] in
theorem partial_coefficient_mass (q : MvPolynomial ι (Polynomial ℤ)) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b)
    (i : ι) (e : ι →₀ ℕ) : coefficientMass ((pderiv i q).coeff e) ≤ D * 2 ^ b := by
  rw [coeff_pderiv]
  have hs : (e i : Polynomial ℤ) + 1 = Polynomial.C ((e i + 1 : ℕ) : ℤ) := by simp
  rw [hs]
  by_cases hz : q.coeff (e + Finsupp.single i 1) = 0
  · simp [hz]
  have hmon := MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hz)
  have he : e i + 1 ≤ D := by
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
      hmon.trans ((MvPolynomial.degreeOf_le_totalDegree q i).trans hD)
  exact (coefficientMass_mul_le _ _).trans (by
    rw [coefficientMass_C, Int.natAbs_natCast]
    exact (Nat.mul_le_mul (hq _) he).trans_eq (Nat.mul_comm _ _))

theorem spatial_degree (q : MvPolynomial ι (Polynomial ℤ)) (base : ι) (v : ι → ℕ)
    (D : ℕ) (hD : q.totalDegree ≤ D) (i : ι) :
    (ProjectionCriticalFamily.spatialEquation q base (fun j => (v j : Polynomial ℤ)) i).totalDegree ≤ D := by
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · exact hD
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (PartialDerivativeDegree.degree_le q i).trans ((Nat.sub_le _ _).trans hD)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        simpa only [MvPolynomial.totalDegree_C, Nat.zero_add] using
          (PartialDerivativeDegree.degree_le q base).trans ((Nat.sub_le _ _).trans hD))

theorem spatial_parameter_degree (q : MvPolynomial ι (Polynomial ℤ)) (base : ι) (v : ι → ℕ)
    (E : ℕ) (hq : ∀ e, (q.coeff e).natDegree ≤ E) (i : ι) (e : ι →₀ ℕ) :
    ((ProjectionCriticalFamily.spatialEquation q base (fun j => (v j : Polynomial ℤ)) i).coeff e).natDegree ≤ E := by
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · exact hq e
  · rw [MvPolynomial.coeff_sub, coeff_C_mul]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact partial_parameter_degree q E hq i e
    · change (Polynomial.C ((v i : ℕ) : ℤ) * (pderiv base q).coeff e).natDegree ≤ E
      exact Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using partial_parameter_degree q E hq base e)

theorem spatial_coefficient_mass (q : MvPolynomial ι (Polynomial ℤ)) (base : ι) (v : ι → ℕ)
    (D U b : ℕ) (hD : q.totalDegree ≤ D) (hU : ∀ i, v i ≤ U)
    (hq : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b) (i : ι) (e : ι →₀ ℕ) :
    coefficientMass ((ProjectionCriticalFamily.spatialEquation q base (fun j => (v j : Polynomial ℤ)) i).coeff e) ≤
      2 ^ massExponent b D U := by
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · exact (hq e).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · rw [MvPolynomial.coeff_sub, coeff_C_mul]
    have hp := partial_coefficient_mass q D b hD hq
    apply (coefficientMass_sub_le _ _).trans
    calc
      _ ≤ D * 2 ^ b + U * (D * 2 ^ b) := Nat.add_le_add (hp i e)
        ((coefficientMass_mul_le _ _).trans (by
          change coefficientMass (Polynomial.C ((v i : ℕ) : ℤ)) * coefficientMass ((pderiv base q).coeff e) ≤ _
          rw [coefficientMass_C, Int.natAbs_natCast]
          exact Nat.mul_le_mul (hU i) (hp base e)))
      _ = (D * (U + 1)) * 2 ^ b := by ring
      _ ≤ ((D + 1) * (U + 1)) * 2 ^ b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ D))
      _ ≤ 2 ^ ((D + 1) * (U + 1)).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _ = 2 ^ massExponent b D U := by rw [← pow_add, Nat.add_comm]; rfl

end LeanCanny.Algebra.ProjectionCriticalBounds
