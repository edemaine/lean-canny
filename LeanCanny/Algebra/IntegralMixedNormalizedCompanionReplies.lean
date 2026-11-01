/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionChildren
/-! # Exact current normalized coefficients supply the actual companion calculation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false

theorem scalarDegree_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    (scalarFamily P F).scalarDegree q ≤ numericCap P (RankedHistoryTask.root q) := by
  change 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ≤ _
  rw [g.width]
  exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem coefficientTask_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    normalizedValue P F (coefficientTask P F q) = residueBits
      ((scalarFamily P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
        ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q)) := by
  have HK : IntegralScalarGeneratorBits.index (scalarFamily P F) q ≤ numericCap P (RankedHistoryTask.root q) :=
    (Nat.sub_le _ _).trans (((scalarFamily P F).row q).isLt.le.trans (scalarDegree_cap P F g q))
  change normalizedValue P F (coefficientTask P F q) = residueBits
    ((family P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
      ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q))
  rw [coefficient_entry]
  exact writer_value P F g q hv _ HK _ _

theorem coefficient_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : NormalizationMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
    answer (coefficientTask P F q) = residueBits
      ((scalarFamily P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
        ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q)) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P (coefficientTask P F q) := by
    unfold IntegralMixedVirtualCaps.valid coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_birth,
      IntegralMixedCoefficientQueryBits.writer_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (coefficientTask P F q) = 5 :=
    IntegralMixedCoefficientQueryBits.writer_routine P .normalization .eulerSum _
  have HC : isPhase .eulerSum (coefficientTask P F q) :=
    IntegralMixedCoefficientQueryBits.writer_phase P .normalization .eulerSum _
  exact (hm _ HV HR HC).trans (coefficientTask_value P F g q hv)

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
