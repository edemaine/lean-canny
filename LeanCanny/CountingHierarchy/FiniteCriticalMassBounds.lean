/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteCriticalData
public import LeanCanny.CountingHierarchy.ParameterSpecializationMass
public import LeanCanny.CountingHierarchy.ShiftedIntegerLabelBounds
public import LeanCanny.CountingHierarchy.PolynomialMultivariateCompositionBounds
public import LeanCanny.CountingHierarchy.IntegerQuotientMassBounds

/-! # Source-derived degree and log-mass bounds for the final quotient norm -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra

@[expose] def criticalSpecializedRelationMassExponent (n d b : ℕ) : ℕ :=
  criticalLowerMassExponent n d b + criticalSpecializationExponent n d b

@[expose] def criticalSpecializedObjectiveMassExponent (n d b : ℕ) : ℕ :=
  criticalObjectiveMassExponent n d b + criticalSpecializationExponent n d b

@[expose] def criticalShiftedLabelDegreeBound (n d b : ℕ) : ℕ :=
  sparseRootLabelDegreeBound ((d + 1) ^ n) (criticalRootLabelLength n d)
    (criticalLabelInputMassExponent n d b)

@[expose] def criticalShiftedLabelMassExponent (n d b : ℕ) : ℕ :=
  sparseRootLabelMassExponent ((d + 1) ^ n) (criticalRootLabelLength n d)
    (criticalLabelInputMassExponent n d b) + ((d + 1) ^ n).size + 3

@[expose] def criticalNormObjectiveDegreeBound (n d b : ℕ) : ℕ :=
  criticalShiftedLabelDegreeBound n d b * (d + 2)

@[expose] def criticalNormObjectiveMassExponent (n d b : ℕ) : ℕ :=
  criticalShiftedLabelMassExponent n d b +
    criticalShiftedLabelDegreeBound n d b * criticalSpecializedObjectiveMassExponent n d b

@[expose] def criticalNormMassExponent (n d b : ℕ) : ℕ :=
  quotientCharMassExponent n d (criticalNormObjectiveDegreeBound n d b)
    (criticalNormObjectiveMassExponent n d b) (criticalSpecializedRelationMassExponent n d b)

lemma parameterEvaluation_integer (u : ℤ) : parameterEvaluation u = Polynomial.evalRingHom u := by
  ext <;> simp [parameterEvaluation]

lemma parameterLower_map_integer {n : ℕ} (d : ℕ) (F : MvPolynomial (Fin n) ℤ) (u : ℤ) (i : Fin n) :
    (parameterLower d F i).map (Polynomial.evalRingHom u) =
      criticalLower (d + 1) (fun j => (separatedCenters (d + 1) j : ℤ)) u F i := by
  have hInt : Int.castRingHom ℤ = RingHom.id ℤ := by ext z; rfl
  simpa only [parameterEvaluation_integer, hInt, MvPolynomial.map_id, Int.cast_id] using
    parameterLower_map d u F i

lemma parameterObjective_map_integer {n : ℕ} (d : ℕ) (F : MvPolynomial (Fin n) ℤ) (u : ℤ) :
    (parameterObjective d F).map (Polynomial.evalRingHom u) =
      deformedPolynomial (d + 1) (fun j => (separatedCenters (d + 1) j : ℤ)) u F := by
  have hInt : Int.castRingHom ℤ = RingHom.id ℤ := by ext z; rfl
  simpa only [parameterEvaluation_integer, hInt, MvPolynomial.map_id, Int.cast_id] using
    parameterObjective_map d u F

theorem finiteCriticalRelations_mass_le {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b)
    (i : Fin n) :
    MvMass.mass (finiteCriticalRelations d b F i) ≤ 2 ^ criticalSpecializedRelationMassExponent n d b := by
  simpa only [parameterLower_map_integer, mul_one, finiteCriticalRelations,
    criticalIntegerParameter, criticalSpecializedRelationMassExponent] using
    parameterSpecialization_mass_le_pow (parameterLower d F i) 1 _
      (criticalSpecializationExponent n d b) (parameterLower_hasParameterDegree d F i)
      (parameterLower_mass_le d b F hF hM i)

theorem finiteCriticalObjective_mass_le {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hM : MvMass.mass F ≤ 2 ^ b) :
    MvMass.mass (finiteCriticalObjective d b F) ≤ 2 ^ criticalSpecializedObjectiveMassExponent n d b := by
  simpa only [parameterObjective_map_integer, mul_one, finiteCriticalObjective,
    criticalIntegerParameter, criticalSpecializedObjectiveMassExponent] using
    parameterSpecialization_mass_le_pow (parameterObjective d F) 1 _
      (criticalSpecializationExponent n d b) (parameterObjective_hasParameterDegree d F)
      (parameterObjective_mass_le d b F hM)

theorem finiteCriticalObjective_degree_le {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) :
    (finiteCriticalObjective d b F).totalDegree ≤ d + 2 := by
  have h := (map_degree_le (Polynomial.evalRingHom (criticalIntegerParameter n d b))
    (parameterObjective d F)).trans (parameterObjective_totalDegree_le d F hF)
  simpa only [parameterObjective_map_integer, finiteCriticalObjective] using h

end LeanCanny.CountingHierarchy
