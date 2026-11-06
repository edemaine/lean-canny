/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalIntervalEndpoints
public import LeanCanny.Encoding.IntegralFramedPhysicalBankNaturalPoint
/-! # The native old-bank scan reads carrier-free observations of one joint tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

theorem bank_point_observation (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input child) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key child q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key child) (positive child) q w hv j=z j.val)
    (i : ℕ) (hi : i<birth false q) :
    FormulaSignSlotRadialProviderCriticalBankEquality.point child q w hv i=
      (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key child q)).point
        z (i+if child then 1 else 0) :=by
  have HE:=IntegralFramedPhysicalSquare.bank_observation_of_joint (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (key child) (positive child)
    q w hv z hz (FormulaSignSlotRadialProviderCriticalBankEquality.coordinate child q
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)))
  exact HE.symm.trans (congrArg (fun j=>(IntegralMixedFullBankObservation.atFamily
    (B).parameters (B).plan (B).data (key child q)).point z j)
      (FormulaSignSlotRadialProviderCriticalBankEquality.coordinate_val child q i 0 hi))

theorem newest_observation (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key true q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key true) (positive true) q w hv j=z j.val) :
    newestPoint q w hv=
      (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key true q)).point z 0 :=
  (IntegralFramedPhysicalSquare.bank_observation_of_joint (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (key true) (positive true)
    q w hv z hz ⟨0,positive true q⟩).symm

theorem agrees_iff_observations (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key true q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key true) (positive true) q w hv j=z j.val) :
    FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w) ↔
      ∀i<birth false q,
        FormulaSignSlotRadialProviderCriticalBankEquality.point false q
          (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
        (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key true q)).point z (i+1) :=by
  rw [FormulaSignSlotRadialProviderCriticalBankEquality.agrees_iff q w hp hv]
  constructor
  · intro HE i hi
    exact (HE i hi).trans (bank_point_observation true q w hv z hz i hi)
  · intro HE i hi
    exact (HE i hi).trans (bank_point_observation true q w hv z hz i hi).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
