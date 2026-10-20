/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalPadding
public import LeanCanny.Algebra.PolynomialAffineDeformation

/-! # Polynomial bounds for padded principal deformations

Identity row padding preserves uniform entry degree and mass allowances.
An additional radix encoding bounds every scalar coefficient of the affine
determinant, without enumerating the selected principal index subtype.
-/

@[expose] public section

namespace LeanCanny.Algebra
open scoped BigOperators Classical

namespace PrincipalPadding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem entry_degree {R : Type*} [CommRing R] (A : Matrix ι ι (Polynomial R)) (s : Finset ι) (E : ℕ)
    (hA : ∀ r t, (A r t).natDegree ≤ E) (r t : ι) : (matrix A s r t).natDegree ≤ E := by
  rw [matrix]
  split_ifs
  · exact hA r t
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

omit [Fintype ι] in
theorem entry_mass (A : Matrix ι ι (Polynomial ℤ)) (s : Finset ι) (b : ℕ)
    (hA : ∀ r t, coefficientMass (A r t) ≤ 2 ^ b) (r t : ι) : coefficientMass (matrix A s r t) ≤ 2 ^ b := by
  rw [matrix]
  split_ifs
  · exact hA r t
  · simp only [Matrix.one_apply]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ b
      rw [coefficientMass_C]
      exact Nat.one_le_two_pow
    · simp

end PrincipalPadding

namespace AffineCharacteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem polynomial_entry (A : Matrix ι ι (Polynomial ℤ)) (r t : ι) :
    affineMatrix A r t = PolynomialAffineDeformation.affine (A r t) (if r = t then 1 else 0) := by
  by_cases hrt : r = t <;>
    simp [affineMatrix, PolynomialAffineDeformation.affine, Matrix.one_apply, hrt]
  ring

theorem polynomial_inner_degree (A : Matrix ι ι (Polynomial ℤ)) (E : ℕ)
    (hA : ∀ r t, (A r t).natDegree ≤ E) (j : ℕ) :
    ((affineMatrix A).det.coeff j).natDegree ≤ Fintype.card ι * E := by
  have h := PolynomialKronecker.determinant_inner_degree (affineMatrix A) (fun _ => E)
    (fun r t k => by
      rw [polynomial_entry]
      exact PolynomialAffineDeformation.inner_degree_le _ _ E (hA r t) k) j
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h

theorem polynomial_coefficient_size (A : Matrix ι ι (Polynomial ℤ)) (E b : ℕ)
    (hdeg : ∀ r t, (A r t).natDegree ≤ E) (hmass : ∀ r t, coefficientMass (A r t) ≤ 2 ^ b) (k l : ℕ) :
    (((affineMatrix A).det.coeff l).coeff k).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + Fintype.card ι * (b + 2) + 1 := by
  let B := Fintype.card ι * E + 1
  by_cases hk : k < B
  · have hc := PolynomialKronecker.coefficient B (affineMatrix A).det
      (fun j => (polynomial_inner_degree A E hdeg j).trans_lt (Nat.lt_succ_self _)) k l hk
    have hm : PolynomialKronecker.encode B (affineMatrix A).det =
        ((affineMatrix A).map (PolynomialKronecker.encode B)).det := (PolynomialKronecker.encode B).map_det _
    rw [hm] at hc
    rw [← hc]
    have h := det_coeff_size_le ((affineMatrix A).map (PolynomialKronecker.encode B)) (fun _ => b + 2)
      (fun r t => by
        change coefficientMass (PolynomialKronecker.encode B (affineMatrix A r t)) ≤ _
        rw [polynomial_entry]
        apply PolynomialAffineDeformation.encoded_mass_le _ _ B b (hmass r t)
        split_ifs <;> decide) (k + B * l)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h
  · have hz : ((affineMatrix A).det.coeff l).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd := polynomial_inner_degree A E hdeg l
      dsimp only [B] at hk
      omega
    rw [hz]
    simp

end AffineCharacteristic
end LeanCanny.Algebra
