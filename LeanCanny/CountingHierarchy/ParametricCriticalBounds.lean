/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedPotentialMass
public import LeanCanny.CountingHierarchy.SeparatedPotentialDegree
public import LeanCanny.CountingHierarchy.QuotientMassBounds
public import LeanCanny.CountingHierarchy.QuotientParameterDegree

/-! # Explicit degree and log-mass bounds for the integer critical polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial PurePowerResidue LeanCanny.Algebra

/-- A short log-mass bound, specified entirely by source arity, degree and mass. -/
@[expose] def criticalValueMassExponent (n d b : ℕ) : ℕ :=
  let D := (d + 1) ^ n
  let br := criticalLowerMassExponent n d b
  let bv := criticalObjectiveMassExponent n d b
  let bJ := n.size * n + n * ((d + 1).size + br + 1)
  traceMassExponent n (D * (d + 2) + n * d) D bv br bJ * D + (D + 1).size

/-- A short bound on the degree in the independent deformation parameter. -/
@[expose] def criticalValueParameterDegreeBound (n d : ℕ) : ℕ :=
  let D := (d + 1) ^ n
  D * (D + n + n * (D * (d + 2) + n * d))

theorem parametricCriticalValue_mass_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b) :
    NestedMass.mass (parametricCriticalValue d F hF) ≤ 2 ^ criticalValueMassExponent n d b := by
  have hr (i : Fin n) : (parameterLower d F i).totalDegree ≤ d := by
    have := parameterLower_degree d F hF i
    omega
  exact multiplicationMatrix_charpoly_nestedMass_le d hd (parameterLower d F) hr
    (parameterObjective d F) (d + 2)
    (criticalObjectiveMassExponent n d b) (criticalLowerMassExponent n d b)
    (parameterObjective_totalDegree_le d F hF) (parameterObjective_mass_le d b F hM)
    (parameterLower_mass_le d b F hF hM)

theorem parametricCriticalValue_parameterDegree_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (k : ℕ) :
    ((parametricCriticalValue d F hF).coeff k).natDegree ≤ criticalValueParameterDegreeBound n d := by
  have hr (i : Fin n) : (parameterLower d F i).totalDegree ≤ d := by
    have := parameterLower_degree d F hF i
    omega
  simpa only [parametricCriticalValue, criticalValueParameterDegreeBound, Nat.mul_one] using
    multiplicationMatrix_charpoly_parameterDegree_le d hd (parameterLower d F) hr
      (parameterObjective d F) (d + 2) 1 1 (parameterObjective_totalDegree_le d F hF)
      (parameterLower_hasParameterDegree d F) (parameterObjective_hasParameterDegree d F) k

end LeanCanny.CountingHierarchy
