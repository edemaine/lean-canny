/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.IntegerCriticalSpecialization
public import LeanCanny.CountingHierarchy.QuotientRootLabelCriterion
public import LeanCanny.CountingHierarchy.RootLabelPolynomialBounds

/-! # Source-derived data for the finite critical determinant test -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra

@[expose] def criticalSpecializationExponent (n d b : ℕ) : ℕ :=
  criticalParameterExponent ((d + 1) ^ n) (criticalValueMassExponent n d b)

@[expose] def criticalSpecializedMassExponent (n d b : ℕ) : ℕ :=
  criticalValueMassExponent n d b + criticalSpecializationExponent n d b * criticalValueParameterDegreeBound n d

@[expose] def criticalLabelInputMassExponent (n d b : ℕ) : ℕ :=
  criticalSpecializedMassExponent n d b + criticalValueCutoffExponent (criticalValueMassExponent n d b) + 2

@[expose] def criticalRootLabelLength (n d : ℕ) : ℕ := n * (d + 1).size

@[expose] def criticalIntegerParameter (n d b : ℕ) : ℤ := (2 : ℤ) ^ criticalSpecializationExponent n d b

@[expose] def criticalIntegerCutoff (n d b : ℕ) : ℤ :=
  (2 : ℤ) ^ criticalValueCutoffExponent (criticalValueMassExponent n d b)

@[expose] noncomputable def finiteCriticalPolynomial {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) : Polynomial ℤ :=
  powerCriticalValue d F hF (criticalSpecializationExponent n d b)

@[expose] noncomputable def finiteCriticalRelations {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) : Fin n → MvPolynomial (Fin n) ℤ :=
  criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) (criticalIntegerParameter n d b) F

@[expose] noncomputable def finiteCriticalObjective {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin n) ℤ :=
  deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) (criticalIntegerParameter n d b) F

theorem finiteCriticalRelations_degree {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) :
    (finiteCriticalRelations d b F i).totalDegree ≤ d := by
  exact Nat.le_of_lt_succ (criticalLower_degree (d + 1) (by omega)
    (fun j => (separatedCenters (d + 1) j : ℤ)) (criticalIntegerParameter n d b) F hF i)

theorem finiteCriticalPolynomial_eq_charpoly {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) :
    finiteCriticalPolynomial d b F hF =
      (multiplicationMatrix (by omega : 1 ≤ d + 1) (finiteCriticalRelations d b F)
        (fun i => (finiteCriticalRelations_degree d b F hF i).trans_lt (Nat.lt_succ_self d))
        (finiteCriticalObjective d b F)).charpoly :=
  parametricCriticalValue_map_integer d hd F hF (criticalIntegerParameter n d b)

theorem criticalRootLabelLength_suffices (n d : ℕ) : (d + 1) ^ n ≤ 2 ^ criticalRootLabelLength n d := by
  apply (Nat.pow_le_pow_left (Nat.lt_size_self (d + 1)).le n).trans_eq
  rw [criticalRootLabelLength, ← pow_mul, Nat.mul_comm]

theorem finiteCriticalPolynomial_mass_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) :
    coefficientMass (finiteCriticalPolynomial d b F hF) ≤ 2 ^ criticalLabelInputMassExponent n d b :=
  (powerCriticalValue_mass_le d hd b F hF hM _).trans
    (Nat.pow_le_pow_right (by decide) (by unfold criticalLabelInputMassExponent criticalSpecializedMassExponent; omega))

theorem criticalCutoff_test_mass_le (n d b : ℕ) :
    coefficientMass (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X) ≤
      2 ^ criticalLabelInputMassExponent n d b := by
  have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
    rw [coefficientMass_monomial]
    rfl
  apply (coefficientMass_sub_le _ _).trans
  rw [coefficientMass_C, hx, criticalIntegerCutoff, Int.natAbs_pow]
  change 2 ^ criticalValueCutoffExponent (criticalValueMassExponent n d b) + 1 ≤ _
  apply le_trans _ (Nat.pow_le_pow_right (by decide)
    (show criticalValueCutoffExponent (criticalValueMassExponent n d b) + 1 ≤
      criticalLabelInputMassExponent n d b by unfold criticalLabelInputMassExponent; omega))
  have := Nat.one_le_two_pow (n := criticalValueCutoffExponent (criticalValueMassExponent n d b))
  rw [pow_succ]
  omega

end LeanCanny.CountingHierarchy
