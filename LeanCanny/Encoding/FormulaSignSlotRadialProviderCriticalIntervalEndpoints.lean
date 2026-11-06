/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalIntervalReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankReadback
/-! # Interval endpoints belong to the same fixed parent word

The all-old-bank equality scan transports the two chronological endpoint
labels to the child. The appended chronological label reads newest index0.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "hr" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable def newestPoint (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) : ℝ :=
  IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (key true) (positive true) q v hv ⟨0,positive true q⟩

theorem env_old (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (i : ℕ) (hi : i<birth false q) :
    IntegralFramedPhysicalBankTerm.env (childBank) T hr q v hv i=
      FormulaSignSlotRadialProviderCriticalBankEquality.point true q v hv
        (birth false q-1-i) :=by
  have HA : i<(IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (key true q)).count :=by
    change i<(IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth (key true q)
    rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth,
      FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
    omega
  have HP:=IntegralFramedPhysicalBankTerm.env_coordinate (childBank) T
    hr q v hv i HA
  refine HP.trans ?_
  unfold FormulaSignSlotRadialProviderCriticalBankEquality.point
  apply congrArg (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (key true) (positive true) q v hv)
  apply Fin.ext
  rw [IntegralFramedPhysicalIntegerLeaves.coordinate_packet,
    FormulaSignSlotRadialProviderCriticalBankEquality.coordinate_val true q _ 0 (by omega)]
  change (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth
    (key true q)-1-i=birth false q-1-i+1
  rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth,
    FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
  omega

theorem env_newest (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) :
    IntegralFramedPhysicalBankTerm.env (childBank) T hr q v hv
      (birth false q)=newestPoint q v hv :=by
  have HA : birth false q<
      (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (key true q)).count :=by
    change _<(IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth (key true q)
    rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth,
      FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
    omega
  have HP:=IntegralFramedPhysicalBankTerm.env_coordinate (childBank) T
    hr q v hv (birth false q) HA
  refine HP.trans ?_
  unfold newestPoint
  apply congrArg (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (key true) (positive true) q v hv)
  apply Fin.ext
  rw [IntegralFramedPhysicalIntegerLeaves.coordinate_packet]
  change (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth
    (key true q)-1-birth false q=0
  rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth,
    FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
  omega

noncomputable def endpointValue (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (i : ℕ) : ℝ :=
  FormulaSignSlotRadialProviderCriticalBankEquality.point false q
    (IntegralMixedPhysicalCriticalQuery.parentWord q) hp (birth false q-1-i)

theorem interval_iff_parent (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (hg : Guard q) (haq : FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q v)) :
    (value false (pair q v)=InfinitesimalSign.encode 1 ∧
      value true (pair q v)=InfinitesimalSign.encode 1) ↔
    endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q))<
        newestPoint q v hv ∧
      newestPoint q v hv<
        endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q)) :=by
  have HB:=FormulaSignSlotRadialProviderCriticalPrefixes.birth_pos false q
  have HE:=(FormulaSignSlotRadialProviderCriticalBankEquality.agrees_iff q v hp hv).mp haq
  rw [interval_iff q v hv hg]
  dsimp only
  rw [env_old q v hv _ hg.2.1,env_old q v hv _ hg.2.2,
    env_newest q v hv,←HE _ (by omega),←HE _ (by omega)]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
