/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Euclidean
public import LeanCanny.Algebra.Subresultant

/-! # General GCD recovery from subresultant coefficient minors

The coefficient form retains the smaller terminal index, where it is a scalar
multiple of the smaller input. This terminal data is needed when the smaller
polynomial divides the larger one.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalSubresultant
open Polynomial
open scoped BigOperators
open scoped Classical

noncomputable def coefficientForm {R : Type*} [CommRing R]
    (p q : R[X]) (m n j : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (j + 1), monomial k (subresultantCoeff p q m n j k)

theorem coefficientForm_coeff {R : Type*} [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    (coefficientForm p q m n j).coeff k =
      if k ≤ j then subresultantCoeff p q m n j k else 0 := by
  classical
  simp [coefficientForm, coeff_monomial, Finset.mem_range]

theorem subresultantCoeff_eq_minor_det {R : Type*} [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k = (Subresultant.minor p q m n j k).det := by
  rw [subresultantCoeff_def]
  apply congrArg Matrix.det
  ext i l
  induction l using Fin.addCases <;>
    simp only [subresultantCoeffMatrix_castAdd, subresultantCoeffMatrix_natAdd, Subresultant.minor, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right, Subresultant.band, Subresultant.rowIndex, Nat.add_comm]

theorem coefficientForm_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n j : ℕ) :
    (coefficientForm p q m n j).map f = coefficientForm (p.map f) (q.map f) m n j := by
  ext k
  simp only [coeff_map, coefficientForm_coeff, subresultantCoeff_map_map]
  split_ifs <;> simp only [map_zero]

theorem coefficientForm_eq_subresultant {R : Type*} [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : j < m ∧ j < n) :
    coefficientForm p q m n j = Subresultant.polynomial p q m n j := by
  ext k
  rw [coefficientForm_coeff, Subresultant.coeff]
  by_cases hk : k ≤ j
  · rw [ite_eq_left hk, ite_eq_left ⟨hj.1, hj.2, hk⟩, subresultantCoeff_eq_minor_det]
  · rw [ite_eq_right hk, ite_eq_right (by omega)]

theorem coefficientForm_terminal {R : Type*} [CommRing R]
    (p q : R[X]) (m n : ℕ) (hqn : q.natDegree ≤ n) (hnm : n < m) :
    coefficientForm p q m n n = C (q.coeff n ^ (m - n - 1)) * q := by
  ext k
  rw [coefficientForm_coeff, coeff_C_mul]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, subresultantCoeff_right_bound p q hnm hk, mul_comm]
  · have hz : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [ite_eq_right hk, hz, mul_zero]

theorem psc_zero_left_of_lt {R : Type*} [CommRing R]
    (q : R[X]) (m n j : ℕ) (hj : j < n) : psc 0 q m n j = 0 := by
  have h := psc_C_mul_left (0 : R[X]) q 0 m n j
  simpa only [C_0, zero_mul, zero_pow (by omega : n - j ≠ 0)] using h

section Field
variable {K : Type*} [Field K]

theorem coefficientForm_euclidean (p q : K[X]) (m r j : ℕ)
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j < q.natDegree) :
    coefficientForm p q m q.natDegree j =
      C ((-1 : K) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) *
        coefficientForm q (p % q) q.natDegree r j := by
  ext k
  rw [coefficientForm_coeff, coeff_C_mul, coefficientForm_coeff]
  by_cases hk : k ≤ j
  · rw [ite_eq_left hk, ite_eq_left hk, ← subresultantCoeff_mod_left hp,
      subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hjr hjq k,
      subresultantCoeff_comm (p % q) q r q.natDegree j k, coeff_natDegree]
    have hgap : m - j = (m - r) + (r - j) := by omega
    rw [hgap, add_mul, pow_add]
    ring
  · rw [ite_eq_right hk, ite_eq_right hk, mul_zero]

variable [DecidableEq K]

theorem gcd_mod_associated (p q : K[X]) :
    Associated (EuclideanDomain.gcd p q) (EuclideanDomain.gcd q (p % q)) := by
  apply associated_of_dvd_dvd
  · exact EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right p q)
      ((EuclideanDomain.dvd_mod_iff (EuclideanDomain.gcd_dvd_right p q)).mpr (EuclideanDomain.gcd_dvd_left p q))
  · exact EuclideanDomain.dvd_gcd
      ((EuclideanDomain.dvd_mod_iff (EuclideanDomain.gcd_dvd_left q (p % q))).mp
        (EuclideanDomain.gcd_dvd_right q (p % q))) (EuclideanDomain.gcd_dvd_left q (p % q))

theorem natDegree_eq_of_associated {p q : K[X]} (h : Associated p q) : p.natDegree = q.natDegree := by
  by_cases hp : p = 0
  · have hq := h.eq_zero_iff.mp hp
    rw [hp, hq]
  · have hq : q ≠ 0 := h.ne_zero_iff.mp hp
    exact le_antisymm (natDegree_le_of_dvd h.dvd hq) (natDegree_le_of_dvd h.dvd' hp)

private theorem gcd_data_aux (n : ℕ) : ∀ p q : K[X], q ≠ 0 → q.natDegree = n →
    q.natDegree < p.natDegree →
    Associated (coefficientForm p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree)
      (EuclideanDomain.gcd p q) ∧
    psc p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree ≠ 0 ∧
    ∀ j < (EuclideanDomain.gcd p q).natDegree, psc p q p.natDegree q.natDegree j = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p q hq hn hlt
    have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    by_cases hr : p % q = 0
    · have hdiv : q ∣ p := EuclideanDomain.mod_eq_zero.mp hr
      have ha : Associated q (EuclideanDomain.gcd p q) := associated_of_dvd_dvd
        (EuclideanDomain.dvd_gcd hdiv dvd_rfl) (EuclideanDomain.gcd_dvd_right p q)
      have hd : (EuclideanDomain.gcd p q).natDegree = q.natDegree := (natDegree_eq_of_associated ha).symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hd, coefficientForm_terminal p q _ _ le_rfl hlt, coeff_natDegree]
        exact (associated_unit_mul_right q (C (q.leadingCoeff ^ (p.natDegree - q.natDegree - 1)))
          (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hlc)))).symm.trans ha
      · rw [hd, psc_right_bound, coeff_natDegree]
        exact pow_ne_zero _ hlc
      · intro j hj
        rw [← psc_mod_left (p := p) (q := q) le_rfl, hr]
        exact psc_zero_left_of_lt q _ _ j (by simpa only [hd] using hj)
    · have hrd : (p % q).natDegree < q.natDegree := natDegree_lt_natDegree hr (degree_mod_lt p hq)
      have hd := natDegree_eq_of_associated (gcd_mod_associated p q)
      have hgr : (EuclideanDomain.gcd q (p % q)).natDegree ≤ (p % q).natDegree :=
        natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right q (p % q)) hr
      obtain ⟨ha, hnonzero, hzero⟩ := ih (p % q).natDegree (by omega) q (p % q) hr rfl hrd
      have hunit (j : ℕ) : IsUnit (C ((-1 : K) ^ ((p.natDegree - j) * (q.natDegree - j)) *
          q.leadingCoeff ^ (p.natDegree - (p % q).natDegree))) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero (by simp) (pow_ne_zero _ hlc)))
      refine ⟨?_, ?_, ?_⟩
      · rw [hd, coefficientForm_euclidean p q p.natDegree (p % q).natDegree _ le_rfl le_rfl
          (by omega) hgr (by omega)]
        exact (associated_unit_mul_right _ _ (hunit _)).symm.trans (ha.trans (gcd_mod_associated p q).symm)
      · rw [hd, psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod le_rfl le_rfl (by omega) hgr (by omega)]
        exact mul_ne_zero (mul_ne_zero (by simp) (pow_ne_zero _ hlc)) hnonzero
      · intro j hj
        have hjr : j ≤ (p % q).natDegree := by rw [hd] at hj; omega
        rw [psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod le_rfl le_rfl (by omega) hjr (by omega),
          hzero j (by simpa only [hd] using hj), mul_zero]

/-- The first nonzero principal subresultant is the degree of the GCD. Its full
coefficient form is a nonzero scalar multiple of that GCD, including the terminal
case in which the smaller input divides the larger one. -/
theorem gcd_data (p q : K[X]) (hq : q ≠ 0) (hlt : q.natDegree < p.natDegree) :
    Associated (coefficientForm p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree)
      (EuclideanDomain.gcd p q) ∧
    psc p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree ≠ 0 ∧
    ∀ j < (EuclideanDomain.gcd p q).natDegree, psc p q p.natDegree q.natDegree j = 0 :=
  gcd_data_aux q.natDegree p q hq rfl hlt

end Field
end LeanCanny.Algebra.PrincipalSubresultant
