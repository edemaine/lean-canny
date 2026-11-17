/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceNormDeterminantEvaluation

/-! # Correct residues and magnitude bounds for the coded feasibility determinant -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

/-- Truncating labels and reducing the shift gives a uniform magnitude bound
on every input code, including overlong lists and oversized natural shifts. -/
theorem codedFiniteCriticalDeterminant_natAbs_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : LeanCanny.Algebra.MvMass.mass F ≤ 2 ^ b)
    (data : List (ℕ × ℕ)) (e : ℕ) :
    (codedFiniteCriticalDeterminant d b F hF data e).natAbs ≤ 2 ^ criticalNormMassExponent n d b :=
  finiteCriticalDeterminant_natAbs_le d hd b F hF hM _ _ (sourceNormShift_le n d e)

/-- The twenty-one-level evaluator computes the actual source integer norm.
All prime cutoffs, degrees and integer-size bounds come from the original
arity, degree and logarithmic coefficient-mass allowance. -/
theorem sourceNormDeterminantValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b e : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hM : LeanCanny.Algebra.MvMass.mass F ≤ 2 ^ b)
    (hcut : sourceNormPrimeCutoff n d b < p) (data : List (ℕ × ℕ)) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    (sourceNormDeterminantValue p n d b e data value : ZMod p) =
      (codedFiniteCriticalDeterminant d b F hF data e : ZMod p) := by
  have hsource : criticalCoefficientPrimeCutoff n d < p := by
    unfold sourceNormPrimeCutoff at hcut
    omega
  have hr := finiteCriticalRelations_degree d b F hF
  have hobj := finiteCriticalNormObjective_bounds d hd b F hF hM
    (sourceCodedLabel n d data) (sourceNormShift n d e) (sourceNormShift_le n d e)
  have hdeg (k : ℕ) (hk : k ≤ (d + 1) ^ n) :
      ((codedCriticalNormObjective d b F hF data e) ^ k *
        jacobian (d + 1) (finiteCriticalRelations d b F)).totalDegree ≤ sourceNormTraceDegreeBound n d b :=
    quotient_trace_numerator_degree d (finiteCriticalRelations d b F) hr
      (codedCriticalNormObjective d b F hF data e) (criticalNormObjectiveDegreeBound n d b)
      ((d + 1) ^ n) k hobj.1 hk
  have hgrid := sourceCriticalEvaluation_cast d b F hF hsource
  have hprime : (d + 1) * (sourceNormTraceDegreeBound n d b + 1) + 1 < p := by
    unfold sourceNormPrimeCutoff at hcut
    omega
  have hdim : (d + 1) ^ n < p - 1 := by unfold sourceNormPrimeCutoff at hcut; omega
  have hsquare : (d + 1) ^ n * (d + 1) ^ n < p - 1 := by unfold sourceNormPrimeCutoff at hcut; omega
  have hdet := quotientDeterminantValue_cast (Int.castRingHom (ZMod p)) d hd
    (finiteCriticalRelations d b F) hr (codedCriticalNormObjective d b F hF data e)
    hdeg hprime hdim hsquare
    (fun z => sourceNormObjectiveValue p n d b e z data value)
    (fun z => criticalJacobianValue p n (d + 1) (criticalParameterResidue p n d b) z value)
    (fun i z => criticalLowerValue p n (d + 1) (criticalParameterResidue p n d b) i z value)
    (fun s _ => sourceNormObjectiveValue_cast d hd b e F hF hsource (gridPoint p n s) data value hv)
    (fun s _ => (hgrid (gridPoint p n s) value hv).2.1)
    (fun i s _ => (hgrid (gridPoint p n s) value hv).2.2 i)
  simpa only [sourceNormDeterminantValue, codedFiniteCriticalDeterminant, codedCriticalNormObjective,
    finiteCriticalDeterminant, finiteCriticalNormObjective, finiteCriticalShiftedLabel,
    Int.coe_castRingHom] using hdet

end LeanCanny.CountingHierarchy
