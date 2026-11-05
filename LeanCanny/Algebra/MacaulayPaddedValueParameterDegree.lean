/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayPaddedPolynomialValue
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
/-! # Original coefficient-variable degree bounds for the normalized value

The Cramer formula bounds the entire retained-parameter polynomial before any
specialization. The bound does not require a nonzero extraneous determinant.
-/
@[expose] public section
namespace LeanCanny.Algebra.PolynomialMvCoefficientDegree
open Polynomial MvPolynomial
open scoped Classical BigOperators
variable {σ R : Type*} [CommRing R]

def Bound (p : Polynomial (MvPolynomial σ R)) (E : ℕ) : Prop := ∀ k, (p.coeff k).totalDegree ≤ E

theorem zero (E : ℕ) : Bound (0 : Polynomial (MvPolynomial σ R)) E := by intro k; simp
theorem one : Bound (1 : Polynomial (MvPolynomial σ R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs <;> simp

theorem mul {p q : Polynomial (MvPolynomial σ R)} {E F : ℕ} (hp : Bound p E) (hq : Bound q F) :
    Bound (p * q) (E + F) := MultivariateTarskiDegreeBounds.mul_coefficient p q E F hp hq

theorem sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R)) (E : ℕ)
    (hp : ∀ i ∈ s, Bound (p i) E) : Bound (∑ i ∈ s, p i) E := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i hi => hp i hi k))

theorem prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R)) (E : ι → ℕ)
    (hp : ∀ i ∈ s, Bound (p i) (E i)) : Bound (∏ i ∈ s, p i) (∑ i ∈ s, E i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one (σ := σ) (R := R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul (hp i (Finset.mem_insert_self _ _)) (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem unit_smul {p : Polynomial (MvPolynomial σ R)} {E : ℕ} (u : ℤˣ) (hp : Bound p E) :
    Bound (u • p) E := by
  rcases Int.units_eq_one_or u with H | H
  · simpa only [H, Units.smul_def, Units.val_one, one_smul] using hp
  · intro k
    simpa only [H, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul,
      Polynomial.coeff_neg, MvPolynomial.totalDegree_neg] using hp k

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (MvPolynomial σ R))) (E : ℕ)
    (hA : ∀ i j, Bound (A i j) E) : Bound A.det (Fintype.card ι * E) := by
  rw [Matrix.det_apply]
  apply sum
  intro π _
  apply unit_smul
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    prod Finset.univ (fun j => A (π j) j) (fun _ => E) (fun j _ => hA (π j) j)

theorem charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (E : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ E) :
    Bound A.charpoly (Fintype.card ι * E) := by
  apply det
  intro i j k
  by_cases HI : i = j
  · subst j
    rw [Matrix.charmatrix_apply_eq]
    cases k with
    | zero => simpa using hA i i
    | succ k =>
      cases k with
      | zero => simp
      | succ k => simp [Polynomial.coeff_X]
  · rw [Matrix.charmatrix_apply_ne A i j HI]
    cases k with
    | zero => simpa using hA i j
    | succ k => simp

theorem padding (r : ℕ) : Bound ((1 - Polynomial.X : Polynomial (MvPolynomial σ R)) ^ r) 0 := by
  have HM : (1 - Polynomial.X : Polynomial (MvPolynomial σ R)) ^ r =
      ((1 - Polynomial.X : Polynomial R) ^ r).map MvPolynomial.C := by simp
  intro k
  rw [HM, Polynomial.coeff_map, MvPolynomial.totalDegree_C]

theorem quotient (p q : Polynomial (MvPolynomial σ R)) (d L E : ℕ)
    (hp : Bound p E) (hq : Bound q E) (k : ℕ) :
    ((ScaledPolynomialQuotient.quotient p q d L).coeff k).totalDegree ≤ (L + 1) * E := by
  rw [ScaledPolynomialQuotient.quotient_coeff]
  split_ifs
  · apply (MultivariateTarskiDegreeBounds.determinant _ (fun _ => E) ?_).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])
    intro i j
    rw [ScaledPolynomialQuotient.selected_entry]
    split_ifs
    · exact hq _
    · exact hp _
    · simp
  · simp

end LeanCanny.Algebra.PolynomialMvCoefficientDegree

namespace LeanCanny.Algebra.MacaulayPaddedValueParameterDegree
open MvPolynomial PolynomialMvCoefficientDegree
open scoped Classical
variable {n : ℕ} {σ R : Type*} [CommRing R]

theorem matrix (p : Fin n → MvPolynomial (Fin n) (MvPolynomial σ R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).totalDegree ≤ E) (r s : Macaulay.Index n W) :
    (Macaulay.matrix p d W r s).totalDegree ≤ E := by
  by_cases HR : (FixedWidthPolynomial.vector n W r).degree = Macaulay.level d
  · rw [Macaulay.entry_active p d W r s HR]
    split_ifs
    · exact hp _ _
    · simp
  · simp only [Macaulay.matrix, HR, dite_false, Matrix.one_apply]
    split_ifs <;> simp

theorem normalized_value [IsDomain R]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial σ R))
    (d : Fin (n + 1) → ℕ) (W E : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (hhom : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hp : ∀ i e, ((p i).coeff e).totalDegree ≤ E) :
    (MacaulayUniversal.polynomialValue d W hdegree hW p).totalDegree ≤
      (MacaulayPaddedPolynomialValue.reduced d + 1) * (FixedWidthPolynomial.count (n + 1) W * E) := by
  rw [MacaulayPaddedPolynomialValue.value_eq_coefficient_zero d W hdegree hW p hhom hd]
  have HE : ∀ i j, (Macaulay.extraneousPadded p d W i j).totalDegree ≤ E := by
    intro i j
    simp only [Macaulay.extraneousPadded, PrincipalPadding.matrix]
    split_ifs
    · exact matrix p d W E hp i j
    · rw [Matrix.one_apply]
      split_ifs <;> simp
  apply PolynomialMvCoefficientDegree.quotient
  · simpa only [MacaulayPaddedPolynomialValue.divisor, Fintype.card_fin] using
      charpoly (Macaulay.extraneousPadded p d W) E HE
  · simpa only [MacaulayPaddedPolynomialValue.dividend, Fintype.card_fin, Nat.add_zero] using
      mul (charpoly _ E (matrix p d W E hp)) (padding (MacaulayPaddedPolynomialValue.reduced d))

end LeanCanny.Algebra.MacaulayPaddedValueParameterDegree
