/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayLastParameter
public import LeanCanny.Algebra.MacaulayPivotCount

/-! # Degree in a parameter varying only the last input polynomial

Only rows whose pivot is the last coordinate depend on the parameter. There
are exactly the product of the other degrees such rows. A rowwise determinant
bound gives that count times the input coefficient degree. The nonzero
constant denominator leaves this bound unchanged for the quotient polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayLastParameter
open Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {K : Type*} [Field K]

theorem parameterMap_C_degree (a : Polynomial K) : (parameterMap (Polynomial.C a)).natDegree ≤ a.natDegree := by
  change ((Polynomial.Bivariate.swap (Polynomial.C a)).map (algebraMap (Polynomial K) (RatFunc K))).natDegree ≤ _
  rw [Polynomial.Bivariate.swap_C]
  exact Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le

theorem parameterMap_subtractive_entry_degree {ι : Type*} [DecidableEq ι]
    (A : Matrix ι ι (Polynomial K)) (r s : ι) :
    (parameterMap (AffineCharacteristic.subtractiveMatrix A r s)).natDegree ≤ (A r s).natDegree := by
  by_cases hrs : r = s
  · subst s
    simp only [AffineCharacteristic.subtractiveMatrix, Matrix.one_apply, ite_true, Polynomial.C_1, mul_one,
      map_sub, parameterMap_X]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (parameterMap_C_degree (A r r)) (by simp))
  · simp only [AffineCharacteristic.subtractiveMatrix, Matrix.one_apply, ite_eq_right hrs,
      Polynomial.C_0, mul_zero, sub_zero]
    exact parameterMap_C_degree (A r s)

theorem source_active_entry_degree (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (d : Fin n → ℕ) (W : ℕ) (D : Fin n → ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ D i) (r : activeIndices d W) (s : Index n W) :
    (matrix p d W r.val s).natDegree ≤ D (activePivot d W r) := by
  have hr := (mem_activeIndices d W r.val).mp r.property
  rw [entry_active p d W r.val s hr]
  split_ifs
  · exact hp _ _
  · simp

theorem activeMinor_system (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    activeMinor (system p d) d W =
      (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).map (parameterMap (K := K)) := by
  rw [← activeMinor_subtractiveSystem]
  exact (activeMinor_map (parameterMap (K := K)) (subtractiveSystem p d) d W).symm

theorem numerator_degree_le (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (W : ℕ) (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last)
    (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) (E : ℕ)
    (hE : ∀ e, ((p last).coeff e).natDegree ≤ E) :
    (numerator p d W).natDegree ≤ (∏ j ∈ Finset.univ.erase last, d j) * E := by
  have hp (i : Fin n) (e : Fin n →₀ ℕ) : ((p i).coeff e).natDegree ≤ if i = last then E else 0 := by
    by_cases hi : i = last
    · rw [ite_eq_left hi]
      subst i
      exact hE e
    · rw [ite_eq_right hi, hpq i hi, MvPolynomial.coeff_map]
      simp
  let A := (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).map (parameterMap (K := K))
  have hA (r s : activeIndices d W) : (A r s).natDegree ≤ if activePivot d W r = last then E else 0 :=
    (parameterMap_subtractive_entry_degree (activeMinor p d W) r s).trans
      (source_active_entry_degree p d W (fun i => if i = last then E else 0) hp r s.val)
  have hm := congrArg Matrix.det (activeMinor_system p d W)
  change numerator p d W = A.det at hm
  rw [hm]
  have hb := det_natDegree_le A.transpose (fun r => if activePivot d W r = last then E else 0)
    (fun r s => hA s r)
  rw [Matrix.det_transpose, sum_last_pivot_weights d hd W hW last hlast E] at hb
  exact hb

theorem polynomial_degree_eq_numerator (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) :
    (polynomial p q d W).natDegree = (numerator p d W).natDegree := by
  rw [polynomial, Polynomial.natDegree_mul
    (Polynomial.C_ne_zero.mpr (inv_ne_zero (denominatorValue_ne_zero q d W))) (numerator_ne_zero p d W)]
  simp only [Polynomial.natDegree_C, zero_add]

theorem polynomial_degree_le (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (W : ℕ) (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last)
    (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) (E : ℕ)
    (hE : ∀ e, ((p last).coeff e).natDegree ≤ E) :
    (polynomial p q d W).natDegree ≤ (∏ j ∈ Finset.univ.erase last, d j) * E := by
  rw [polynomial_degree_eq_numerator]
  exact numerator_degree_le p q d hd W hW last hlast hpq E hE

theorem exists_bounded_polynomial (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (W : ℕ) (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last)
    (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) (E : ℕ)
    (hE : ∀ e, ((p last).coeff e).natDegree ≤ E) :
    ∃ r : Polynomial (RatFunc K), r ≠ 0 ∧ r.natDegree ≤ (∏ j ∈ Finset.univ.erase last, d j) * E ∧
      swapExtension (RatFunc.mk (activeCharacteristic p d W)
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det) = algebraMap _ _ r := by
  refine ⟨polynomial p q d W, polynomial_ne_zero p q d W,
    polynomial_degree_le p q d hd W hW last hlast hpq E hE, ?_⟩
  rw [← value_eq_extension]
  exact value_eq_polynomial p q d W last hlast hpq

noncomputable def affineInput (q : Fin n → MvPolynomial (Fin n) K)
    (h : MvPolynomial (Fin n) K) (last : Fin n) : Fin n → MvPolynomial (Fin n) (Polynomial K) :=
  fun i => (q i).map Polynomial.C + if i = last then MvPolynomial.C Polynomial.X * h.map Polynomial.C else 0

theorem affineInput_off_last (q : Fin n → MvPolynomial (Fin n) K)
    (h : MvPolynomial (Fin n) K) (last i : Fin n) (hi : i ≠ last) :
    affineInput q h last i = (q i).map Polynomial.C := by
  simp only [affineInput, ite_eq_right hi, add_zero]

theorem affineInput_coefficient_degree (q : Fin n → MvPolynomial (Fin n) K)
    (h : MvPolynomial (Fin n) K) (last : Fin n) (e : Fin n →₀ ℕ) :
    ((affineInput q h last last).coeff e).natDegree ≤ 1 := by
  rw [affineInput, ite_eq_left rfl]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Nat.add_zero] using (Polynomial.natDegree_X_le (R := K)))

theorem affineInput_homogeneous (q : Fin n → MvPolynomial (Fin n) K)
    (h : MvPolynomial (Fin n) K) (d : Fin n → ℕ) (last : Fin n)
    (hq : ∀ i, (q i).IsHomogeneous (d i)) (hh : h.IsHomogeneous (d last)) (i : Fin n) :
    (affineInput q h last i).IsHomogeneous (d i) := by
  by_cases hi : i = last
  · subst i
    rw [affineInput, ite_eq_left rfl]
    exact ((hq last).map Polynomial.C).add ((hh.map Polynomial.C).C_mul Polynomial.X)
  · rw [affineInput_off_last q h last i hi]
    exact (hq i).map Polynomial.C

theorem affineInput_exists_bounded_polynomial (q : Fin n → MvPolynomial (Fin n) K)
    (h : MvPolynomial (Fin n) K) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (W : ℕ) (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last) :
    ∃ r : Polynomial (RatFunc K), r ≠ 0 ∧ r.natDegree ≤ (∏ j ∈ Finset.univ.erase last, d j) ∧
      swapExtension (RatFunc.mk (activeCharacteristic (affineInput q h last) d W)
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor (affineInput q h last) d W)).det) = algebraMap _ _ r := by
  have ht := exists_bounded_polynomial (affineInput q h last) q d hd W hW last hlast
    (fun i hi => affineInput_off_last q h last i hi) 1 (affineInput_coefficient_degree q h last)
  simpa only [mul_one] using ht

end LeanCanny.Algebra.MacaulayLastParameter
