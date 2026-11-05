/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedPrelude
/-! # Provider replay identifies the actual original prelude fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.ReplayFields
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialProviderAtomic
open FormulaSignSlotRadialExternalPrelude (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables

theorem grid_point_env (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input b) c w)
    (i : ℕ) (hi : i<(IntegralMixedFramedHistoryFamilyBits.family b.parameters b.plan b.data).birth (b.key c)) :
    IntegralFramedPhysicalGridReplay.point b c w hw (4*i)=IntegralFramedPhysicalBankTerm.env b tab hr c w hw i := by
  rw [IntegralFramedPhysicalBankTerm.env_coordinate b tab hr c w hw i hi]
  unfold IntegralFramedPhysicalGridReplay.point
  apply congrArg (IntegralFramedPhysicalSquare.point b.parameters b.plan b.data b.nodes b.factor b.seed b.bounds b.key b.positive c w hw)
  apply Fin.ext
  rw [IntegralFramedPhysicalGridReplay.coordinate_packet,IntegralFramedPhysicalIntegerLeaves.coordinate_packet]
  change IntegralFramedPhysicalGridReplay.count b c-1-(4*i)/4=
    IntegralFramedPhysicalGridReplay.count b c-1-i
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.ReplayFields
