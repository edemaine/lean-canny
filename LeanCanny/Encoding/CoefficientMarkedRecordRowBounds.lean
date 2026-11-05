/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRows
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedHeight
/-! # Original parameter coefficient bounds for the actual full sampler -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open CoefficientMarkedRecordRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def samplerData (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool):CoefficientMarkedRecordRows.Data ℤ:=
  let sampler:=IntegralFramedPhysicalSquare.sampler P D H key
  ⟨IntegralFramedPhysicalSquare.count P D key,(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,
    sampler.rows,sampler.scalar⟩

private theorem samplerData_planned (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C:List Bool→ℕ) (key:List Bool):
    samplerData (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key=samplerData P D H key:=rfl

private theorem indexed_eq_samplerData (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    indexed hn ht ha ctx R k aux=
      samplerData (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux):=rfl

noncomputable def certifiedIndexed (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R)
    (k:ℕ) (aux:List Bool):CoefficientMarkedRecordRows.Data ℤ:=
  samplerData (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)

/-- Planning changes query clipping, but not the sampler at this explicit key. -/
theorem certifiedIndexed_eq (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ) (aux:List Bool):
    certifiedIndexed hn ht ha ctx hR k aux=indexed hn ht ha ctx R k aux:=
  (samplerData_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (fun _=>3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).trans (indexed_eq_samplerData hn ht ha ctx R k aux).symm

attribute [local irreducible] samplerData certifiedIndexed IntegralMixedSourceIntegerRecordAppend.plan

theorem map_certified (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    map (evalRingHom ((2:ℤ)^R ctx)) (symbolic hn ht ha ctx k hk)=certifiedIndexed hn ht ha ctx hR k aux:=
  (map_indexed hn ht ha ctx R k hk aux hlarge).trans (certifiedIndexed_eq hn ht ha ctx hR k aux).symm

private def MassBound (D:CoefficientMarkedRecordRows.Data ℤ) (M:ℕ):Prop:=
  ∀i,MvMass.mass (D.rows i)≤M

private theorem sampler_mass_bound (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (M:ℕ)
    (h:∀i,MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.rows i)≤M):
    MassBound (samplerData P D H key) M:=by
  unfold MassBound samplerData
  intro i
  change MvMass.mass (MvPolynomial.rename
    (IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands P D key))
    (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.rows
      ((IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands P D key)).symm i)))≤M
  exact (MvMass.rename_le _ _).trans (h _)

private theorem certified_mass_bound (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ) (aux:List Bool):
    MassBound (certifiedIndexed hn ht ha ctx hR k aux)
      (2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx*R ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx)):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  have HB:=sampler_mass_bound P D H key _
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_full_row_mass hn ht ha hR key)
  unfold certifiedIndexed
  change MassBound (samplerData P D H key) _
  simpa only [key,CoefficientMarkedRecordRowLayout.key_root] using HB

theorem certified_row_mass (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ) (aux:List Bool)
    (i:Fin (certifiedIndexed hn ht ha ctx hR k aux).count):
    MvMass.mass ((certifiedIndexed hn ht ha ctx hR k aux).rows i)≤
      2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx*R ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx):=
  certified_mass_bound hn ht ha ctx hR k aux i

private def CoefficientBound (D:CoefficientMarkedRecordRows.Data ℤ) (M:ℕ):Prop:=
  ∀i e,((D.rows i).coeff e).natAbs≤M

private theorem certified_coefficient_bound (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R)
    (k:ℕ) (aux:List Bool):
    CoefficientBound (certifiedIndexed hn ht ha ctx hR k aux)
      (2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx*R ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx)):=by
  intro i e
  exact (MvMass.coeff_le _ _).trans (certified_row_mass hn ht ha ctx hR k aux i)

noncomputable def coefficientBudget (ctx:List Bool):ℕ:=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx)

theorem coefficientBudget_binary:BinaryFn (coefficientBudget hn ht ha):=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset_binary hn ht ha)

/-- Every spatial coefficient is one fixed integer polynomial in the radius parameter. -/
theorem coefficient_degree_mass (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx)
    (i:Fin (symbolic hn ht ha ctx k hk).count) (e:Fin (symbolic hn ht ha ctx k hk).count→₀ ℕ):
    (((symbolic hn ht ha ctx k hk).rows i).coeff e).natDegree≤
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx ∧
    coefficientMass (((symbolic hn ht ha ctx k hk).rows i).coeff e)≤2^coefficientBudget hn ht ha ctx:=by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HH:=certified_coefficient_bound hn ht ha ctx (BinaryFn.const r) k []
  have HE:=map_certified hn ht ha ctx (BinaryFn.const r) k hk [] hr
  have HM:CoefficientBound
      (map (evalRingHom ((2:ℤ)^r)) (symbolic hn ht ha ctx k hk))
      (2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx*r+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx)):=HE.symm ▸ HH
  exact HM i e

end LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
