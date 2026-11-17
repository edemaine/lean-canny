/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalPolynomial
public import LeanCanny.CountingHierarchy.ParameterDegree

/-! # Spatial and parameter degrees of the coercive deformation -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ}

theorem potentialPolynomial_totalDegree_le {S : Type*} [CommRing S] [Nontrivial S] (ell : ℕ)
    (a : Fin n → S) : (potentialPolynomial ell a).totalDegree ≤ ell + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_add _ _).trans
  apply max_le _ (by simp only [totalDegree_C]; omega)
  apply (totalDegree_sub _ _).trans
  apply max_le
  · rw [totalDegree_X_pow]
  · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X, Nat.zero_add]; omega)

theorem parameterObjective_totalDegree_le (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (parameterObjective d F).totalDegree ≤ d + 2 := by
  rw [parameterObjective, deformedPolynomial]
  apply (totalDegree_add _ _).trans
  apply max_le (potentialPolynomial_totalDegree_le _ _) _
  exact (totalDegree_mul _ _).trans (by
    simp only [totalDegree_C, Nat.zero_add]
    exact (PurePowerResidue.map_degree_le Polynomial.C F).trans (hF.trans (by omega)))

theorem parameterLower_hasParameterDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    HasParameterDegree (parameterLower d F i) 1 := by
  have hc : HasParameterDegree
      (MvPolynomial.C (parameterCenters d i ^ (d + 1)) : MvPolynomial (Fin n) (Polynomial ℤ)) 0 := by
    apply HasParameterDegree.C
    rw [parameterCenters, ← Polynomial.C_pow, Polynomial.natDegree_C]
  have hx : HasParameterDegree
      (MvPolynomial.C Polynomial.X : MvPolynomial (Fin n) (Polynomial ℤ)) 1 :=
    HasParameterDegree.C _ (by simp)
  simpa only [parameterLower, criticalLower, Nat.add_zero, Nat.max_eq_right (Nat.zero_le 1)] using
    hc.sub (hx.mul ((HasParameterDegree.map_C F).pderiv i))

theorem parameterObjective_hasParameterDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ) :
    HasParameterDegree (parameterObjective d F) 1 := by
  have hp : HasParameterDegree (potentialPolynomial (d + 1) (parameterCenters (n := n) d)) 0 := by
    have h := HasParameterDegree.map_C
      (potentialPolynomial (d + 1) (fun i : Fin n => (separatedCenters (d + 1) i : ℤ)))
    rw [potentialPolynomial_map] at h
    exact h
  have hx : HasParameterDegree
      (MvPolynomial.C (((d + 1 + 1 : ℕ) : Polynomial ℤ) * Polynomial.X) : MvPolynomial (Fin n) (Polynomial ℤ)) 1 := by
    apply HasParameterDegree.C
    exact Polynomial.natDegree_mul_le.trans (by simp)
  simpa only [parameterObjective, deformedPolynomial, Nat.add_zero,
    Nat.max_eq_right (Nat.zero_le 1)] using hp.add (hx.mul (HasParameterDegree.map_C F))

end LeanCanny.CountingHierarchy
