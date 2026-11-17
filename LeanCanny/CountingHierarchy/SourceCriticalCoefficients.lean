/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceCriticalEvaluation
public import LeanCanny.CountingHierarchy.FiniteCriticalMassBounds

/-! # Correct coefficient access to the source-bounded critical-value polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

/-- The `F_(a+9)` algorithm computes coefficients of the actual integer
specialization used by the finite feasibility theorem. All geometric cutoffs
are computed from the source, rather than supplied as polynomial oracles. -/
theorem criticalCoefficientValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b m : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hcut : criticalCoefficientPrimeCutoff n d < p)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    (criticalCoefficientValue p n d b m value : ZMod p) =
      ((finiteCriticalPolynomial d b F hF).coeff m : ZMod p) := by
  have hr := finiteCriticalRelations_degree d b F hF
  have hdeg (k : ℕ) (hk : k ≤ (d + 1) ^ n) :
      ((finiteCriticalObjective d b F) ^ k * jacobian (d + 1) (finiteCriticalRelations d b F)).totalDegree ≤
        criticalTraceDegreeBound n d :=
    quotient_trace_numerator_degree d (finiteCriticalRelations d b F) hr
      (finiteCriticalObjective d b F) (d + 2) ((d + 1) ^ n) k
      (finiteCriticalObjective_degree_le d b F hF) hk
  have hgrid := sourceCriticalEvaluation_cast d b F hF hcut
  have hprime : (d + 1) * (criticalTraceDegreeBound n d + 1) + 1 < p := by
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  have hdim : (d + 1) ^ n < p - 1 := by
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  have hsquare : (d + 1) ^ n * (d + 1) ^ n < p - 1 := by
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  have hcoeff := quotientCharacteristicValue_eq_specialization (m := m) (Int.castRingHom (ZMod p))
    d hd (finiteCriticalRelations d b F) hr (finiteCriticalObjective d b F)
    hdeg hprime hdim hsquare
    (fun z => criticalObjectiveValue p n (d + 1) (criticalParameterResidue p n d b) z value)
    (fun z => criticalJacobianValue p n (d + 1) (criticalParameterResidue p n d b) z value)
    (fun i z => criticalLowerValue p n (d + 1) (criticalParameterResidue p n d b) i z value)
    (fun s _ => (hgrid (gridPoint p n s) value hv).1)
    (fun s _ => (hgrid (gridPoint p n s) value hv).2.1)
    (fun i s _ => (hgrid (gridPoint p n s) value hv).2.2 i)
  rw [← finiteCriticalPolynomial_eq_charpoly d hd b F hF] at hcoeff
  simpa only [criticalCoefficientValue, criticalTraceDegreeBound, ZMod.natCast_zmod_val,
    Int.coe_castRingHom] using congrArg (fun r : ℕ => (r : ZMod p)) hcoeff

end LeanCanny.CountingHierarchy
