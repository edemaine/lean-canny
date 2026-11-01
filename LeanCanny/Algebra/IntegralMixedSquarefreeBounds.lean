/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
public import LeanCanny.Algebra.PrincipalParameterDegree

/-! # Fixed spatial degree ceilings for the selected squarefree factor

The relative principal determinant, its exceptional factor and the scaled
squarefree quotient have explicit sweep-parameter bounds. Their dimensions
are the original spatial coordinate dimension, independent of all old scalar
algebra ranks and absolute norm degrees.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeBounds
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCoordinateSquarefree Polynomial PrincipalSubresultant
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

private theorem derivative_bound {R : Type*} [CommRing R] (p : Polynomial (Polynomial R)) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (k : ℕ) : (p.derivative.coeff k).natDegree ≤ E := by
  rw [Polynomial.coeff_derivative, ← Nat.cast_add_one]
  change (p.coeff (k + 1) * C ((k + 1 : ℕ) : R)).natDegree ≤ E
  exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, Nat.add_zero] using hE (k + 1))

theorem principal_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : ℕ) :
    (principal x hm r j i).natDegree ≤ 2 * coordinateDegree P r * parameterDegree P.degree r := by
  unfold principal
  rw [psc_eq_minor]
  apply (Subresultant.minor_natDegree_le _ _ _ _ i i _ _
    (coordinate_coefficient_degree x hm r j) (derivative_bound _ _ (coordinate_coefficient_degree x hm r j))).trans
  have HK : (coordinateDegree P r - i) + (coordinateDegree P r - 1 - i) ≤ 2 * coordinateDegree P r := by omega
  simpa only [← Nat.add_mul] using Nat.mul_le_mul_right (parameterDegree P.degree r) HK

theorem exceptional_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :
    (exceptional x hm r j i).natDegree ≤ (2 * coordinateDegree P r + 1) * parameterDegree P.degree r := by
  apply Polynomial.natDegree_mul_le.trans
  exact (Nat.add_le_add (coordinate_coefficient_degree x hm r j _) (principal_degree x hm r j i.val)).trans_eq (by ring)

private theorem gcd_coefficient_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i k : ℕ) :
    ((ValidatedSquarefreeSpecialization.gcd (coordinate x hm r j) (coordinateDegree P r) i).coeff k).natDegree ≤
      2 * coordinateDegree P r * parameterDegree P.degree r := by
  rw [ValidatedSquarefreeSpecialization.gcd, coefficientForm_coeff]
  split_ifs
  · rw [subresultantCoeff_eq_minor_det]
    apply (Subresultant.minor_natDegree_le _ _ _ _ i k _ _
      (coordinate_coefficient_degree x hm r j) (derivative_bound _ _ (coordinate_coefficient_degree x hm r j))).trans
    have HK : (coordinateDegree P r - i) + (coordinateDegree P r - 1 - i) ≤ 2 * coordinateDegree P r := by omega
    simpa only [← Nat.add_mul] using Nat.mul_le_mul_right (parameterDegree P.degree r) HK
  · simp only [Polynomial.natDegree_zero, Nat.zero_le]

theorem auxiliary_coefficient_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) (k : ℕ) :
    ((auxiliary x hm r j i).coeff k).natDegree ≤
      (coordinateDegree P r + 1) * ((2 * coordinateDegree P r + 1) * parameterDegree P.degree r) := by
  unfold auxiliary ValidatedSquarefreeSpecialization.polynomial
  rw [ScaledPolynomialQuotient.quotient_coeff]
  split_ifs with hk
  · let N := coordinateDegree P r - i.val + 1
    let E := (2 * coordinateDegree P r + 1) * parameterDegree P.degree r
    have HP (v : ℕ) : ((coordinate x hm r j).coeff v).natDegree ≤ E :=
      (coordinate_coefficient_degree x hm r j v).trans (by dsimp only [E]; nlinarith)
    have HG (v : ℕ) : ((ValidatedSquarefreeSpecialization.gcd (coordinate x hm r j) (coordinateDegree P r) i.val).coeff v).natDegree ≤ E :=
      (gcd_coefficient_degree x hm r j i.val v).trans (by dsimp only [E]; nlinarith)
    have HM (a b : Fin N) :
        (((ScaledPolynomialQuotient.matrix
          (ValidatedSquarefreeSpecialization.gcd (coordinate x hm r j) (coordinateDegree P r) i.val) i.val (coordinateDegree P r - i.val)).updateCol
          ⟨k, hk⟩ (ScaledPolynomialQuotient.input (coordinate x hm r j) i.val (coordinateDegree P r - i.val))) a b).natDegree ≤ E := by
      rw [ScaledPolynomialQuotient.selected_entry]
      split_ifs
      · exact HP _
      · exact HG _
      · simp
    have H := det_natDegree_le _ (fun _ : Fin N => E) HM
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at H
    exact H.trans (Nat.mul_le_mul_right E (by dsimp only [N]; omega))
  · simp only [Polynomial.natDegree_zero, Nat.zero_le]

end LeanCanny.Algebra.IntegralMixedSquarefreeBounds
