/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindHeight
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight
/-! # An original radius bound for every query kind at an actual saved rule -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordQueryKindProfile
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data factor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- Guard probes may change tag, coordinate and choice at the same actual critical rule. -/
theorem coefficient_bound (R : List Bool → ℕ) (key : List Bool)
    (K : IntegralMixedRelativeCuts.Kind ((actualFamily hn ht ha R).spatial key) ((actualFamily hn ht ha R).rule key))
    (tau : ℕ) (i j : Fin (FixedWidthPolynomial.count
      ((actualFamily hn ht ha R).birth key) ((actualFamily hn ht ha R).width key))) :
    (IntegralMixedCutMatrix.coefficientMatrix ((actualFamily hn ht ha R).state key)
      ((actualFamily hn ht ha R).birth_bound key) ((actualFamily hn ht ha R).rule key) K tau i j).natAbs ≤
      2 ^ (rawSlope hn ht ha (pairFst key) * R (pairFst key) + rawOffset hn ht ha (pairFst key)) := by
  let P := parameters hn ht ha
  let D := plan hn ht ha R
  let H := data hn ht ha R
  let G := actualFamily hn ht ha R
  let HB := IntegralMixedFramedOriginalBounds.originalBounds P D H (fun _ => 3) (factor hn ht ha)
    (seed hn ht ha R) (familyInputs hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha) (fallback_bounds hn ht ha R)
  have HC := IntegralMixedRawKindHeight.coefficient_height_at G (IntegralMixedCutStepHeight.indices G) HB key K tau i j
  have HL := IntegralMixedFramedRawHeight.allRaw_height_le P D H (fun _ => 3) (factor hn ht ha)
    (seed hn ht ha R) (familyInputs hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha) (fallback_bounds hn ht ha R) key
  have HT := HC.trans (Nat.pow_le_pow_right (by decide) (HL.trans
    (IntegralMixedFramedRawHeight.local_le_root P (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key)))
  rw [raw_ceiling_affine] at HT
  exact HT

end LeanCanny.Encoding.CoefficientMarkedRecordQueryKindProfile
