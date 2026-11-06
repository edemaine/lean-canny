/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowBad
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperOrder
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointMembership
/-! # Native Base excludes the genuine selected bad roots of every ordinary row -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderProper.OriginalBadFree FormulaSignSlotRadialProviderProper.Base

theorem no_bad_of_base (z :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (HB :FormulaSignSlotRadialProviderProper.Base (atomic z))
    (hr :FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (φ :((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :QuotientsAt G (parentKey false z) φ (originalValue (atomic z) hv))
    (c :IntegralMixedRelativeCuts.Choices ((G).state (parentKey false z)) ((G).birth_bound _)
      ((G).rule (parentKey false z)) φ) :
    ∀a,a∈Set.Ioo (originalValue (atomic z) hv (oldProducer false z))
      (originalValue (atomic z) hv (oldProducer true z))→
      a∉IntegralMixedSelectedCriticalCuts.bad ((G).state (parentKey false z)) ((G).birth_bound _)
        ((G).rule (parentKey false z)) φ c:=by
  have HOrder:=FormulaSignSlotRadialProviderProper.order_of_base (atomic z) hv HB
  have HBase:=HB
  unfold FormulaSignSlotRadialProviderProper.Base at HBase
  have HNo:=(FormulaSignSlotRadialProviderProper.noBad_iff_original_bad_free (atomic z) hv HBase.1 HOrder).mp HBase.2.2.2.1
  unfold FormulaSignSlotRadialProviderProper.OriginalBadFree at HNo
  have HL:=before_probe_field z hv _ hr.2.2.1
  have HR:=before_probe_field z hv _ hr.2.2.2.1
  intro a ha hbad
  rw [HL,HR] at ha
  apply HNo a (by simpa only [oldProducer] using ha)
  simpa only [labels] using (ordinary_bad_iff_original z hv hr φ hφ c a).mpr hbad

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
