/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphDepthCompleteness
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPairGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedAtPoint
/-! # Actual native association is geometric association of the entire current points -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "V" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.levels
  FormulaSignSlotRadialProviderAtomicGeometry.source

theorem language_joined_iff (a ext : List Bool) (ha : A a) (he : A ext)
    (hda : depth a=0) (hde : depth ext=0)
    (hp : V a=FormulaSignSlotRadialProviderPair.oldOf (V ext))
    (hx : FormulaSignSlotRadialExternalContext.external (V ext)) :
    LeanCanny.pair a ext∈language ↔
      JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet (V a)) (pointAt (V a) a ha rfl)
        (FormulaSignSlotRadialProviderPairGeometry.externalPoint a ext hp he) := by
  rw [language_packet_iff a ext ha he hda hde hp hx]
  constructor
  · rintro ⟨r,HR,HC⟩
    have HE := (FormulaSignSlotRadialProviderPairGeometry.crossPoint_iff a ext he hp r HR.2.1 HR.2.2.2.1).mp HC
    simpa only [HE] using raw_reachable_joined (V a) a r HR
  · intro HJ
    let p := FormulaSignSlotRadialProviderPairGeometry.externalPoint a ext hp he
    have HO : @IntegralMixedAtomicOccurrence.Occurrence (num (V a)+3)
        (FormulaSignSlotRadialProviderAtomicGeometry.source (V a)) 0
        (FormulaSignSlotRadialProviderAtomic.levels ext he) p := by
      simpa only [hde] using FormulaSignSlotRadialProviderPairGeometry.external_occurrence a ext hp he
    obtain ⟨r,hr,hprovider,hdepth,hpoint,_⟩ := FormulaSignSlotRadialProviderFirstSeed.exists_at_occurrence a ha p HO
    have HE : pointAt (V a) r hr hprovider=p :=
      eq_of_heq ((native_pointAt_heq (V a) r hr hprovider).symm.trans hpoint)
    have HPath : JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet (V a))
        (pointAt (V a) a ha rfl) (pointAt (V a) r hr hprovider) := by rw [HE];exact HJ
    have HR := (depth_zero_raw_reachable_iff_joined (V a) a r ha hr rfl hprovider hda hdepth).mpr HPath
    exact ⟨r,HR,(FormulaSignSlotRadialProviderPairGeometry.crossPoint_iff a ext he hp r hr hprovider).mpr HE⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
