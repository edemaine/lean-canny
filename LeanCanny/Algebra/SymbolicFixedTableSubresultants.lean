/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableBounds

/-! # Uniform specialization of every squarefree-preparation test

The same source bound covers every principal subresultant index. Consequently
one ordinary small evaluation preserves the selected GCD order, as well as
unsuccessful PSC tests, without assuming the selected order as metadata.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair PrincipalSubresultant
open scoped Classical
attribute [local irreducible] Matrix.det

theorem subresultant_coefficient_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (j k : ℕ) :
    coefficientMass (subresultantCoeff p p.derivative p.natDegree p.derivative.natDegree j k) ≤
      2 ^ gcdMassExponent p.natDegree b := by
  rw [subresultantCoeff_eq_minor_det]
  have hp (i : ℕ) : coefficientMass (p.coeff i) ≤ 2 ^ (b + p.natDegree.size) :=
    (hb i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have he (i l : Fin ((p.natDegree - j) + (p.derivative.natDegree - j))) :
      coefficientMass (Subresultant.minor p p.derivative p.natDegree p.derivative.natDegree j k i l) ≤
        2 ^ (b + p.natDegree.size) := by
    induction l using Fin.addCases <;>
      simp only [Subresultant.minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Subresultant.band]
    all_goals split_ifs
    all_goals first | exact hp _ | exact derivative_coefficient_mass p b hb _ | simp
  have h := det_coefficientMass_le_pow _ (b + p.natDegree.size) he
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  have hn := natDegree_derivative_le p
  have hN : (p.natDegree - j) + (p.derivative.natDegree - j) ≤ 2 * p.natDegree := by omega
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right _ hN)

theorem subresultant_inner_degree (p : Polynomial Coefficient) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (j k : ℕ) :
    (subresultantCoeff p p.derivative p.natDegree p.derivative.natDegree j k).natDegree ≤
      2 * p.natDegree * E := by
  rw [subresultantCoeff_eq_minor_det]
  apply (Subresultant.minor_natDegree_le p p.derivative p.natDegree
    p.derivative.natDegree j k E E hE (derivative_inner_degree p E hE)).trans
  have hn := natDegree_derivative_le p
  have hs : (p.natDegree - j) + (p.derivative.natDegree - j) ≤ 2 * p.natDegree := by omega
  simpa only [← Nat.add_mul] using Nat.mul_le_mul_right E hs

theorem Budget.psc_zero_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) (j : ℕ) :
    scalarEvaluation beta (psc p p.derivative p.natDegree p.derivative.natDegree j) = 0 ↔
      psc p p.derivative p.natDegree p.derivative.natDegree j = 0 := by
  apply zero_iff_of_mass _ (gcdMassExponent B.degree B.massExponent) B.testExponent
    _ (by unfold Budget.testExponent; omega) beta hb he
  rw [← subresultantCoeff_self]
  exact (subresultant_coefficient_mass p _ hp.2.2 j j).trans
    (Nat.pow_le_pow_right (by decide) (gcdMassExponent_mono hp.1 le_rfl))

theorem Budget.psc_map_zero_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) (j : ℕ) :
    psc (p.map (scalarEvaluation beta)) (p.map (scalarEvaluation beta)).derivative
        (p.map (scalarEvaluation beta)).natDegree (p.map (scalarEvaluation beta)).derivative.natDegree j = 0 ↔
      psc p p.derivative p.natDegree p.derivative.natDegree j = 0 := by
  have hd := B.degree_map p hp beta hb he
  rw [derivative_map, hd]
  have hdd : (p.derivative.map (scalarEvaluation beta)).natDegree = p.derivative.natDegree := by
    rw [← derivative_map, natDegree_derivative, hd, natDegree_derivative]
  rw [hdd, psc_map_map]
  exact B.psc_zero_iff p hp beta hb he j

theorem Budget.gcd_degree (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p) (hn : p ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) :
    (SquarefreePart.common (p.map (scalarEvaluation beta))).natDegree = SymbolicScaledSquarefree.degree p := by
  apply small_gcd_degree p hn B.massExponent hp.2.2 beta hb
  exact he.trans (dyadic_antitone (by
    unfold SymbolicScaledSquarefree.smallExponent Budget.testExponent
    exact Nat.add_le_add_right (Nat.add_le_add_left (gcdMassExponent_mono hp.1 le_rfl) _) _))

end LeanCanny.Algebra.SymbolicFixedTable
