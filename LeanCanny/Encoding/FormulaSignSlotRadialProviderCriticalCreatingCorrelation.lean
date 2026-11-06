/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalIntervalEndpoints
/-! # Actual appended-command provenance removes the correlation active guard -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "NB" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "NT" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

variable (q : List Bool)
  (r : IntegralMixedHistory.CriticalRule ((NB).parameters.ambient
    (pairFst (key true q))))
  (hc : (IntegralMixedFramedRootPullback.instructionAt (NB).parameters
    (NB).plan (pairFst (key true q)) (birth false q)).command=.critical r)

include hc in
theorem correlation_active :
    IntegralMixedFramedCriticalGuardBits.Active (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q []) :=by
  constructor
  · simp only [stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
    have HB:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth true q
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HB
    rw [HB,FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
    omega
  · rw [IntegralMixedFramedCriticalGuardBits.header_actual _ _ _ _ NR]
    have HH : (IntegralMixedCommandHeaderBits.command
        (IntegralMixedFramedRootPullback.instructionAt (NB).parameters
          (NB).plan (pairFst (key true q)) (birth false q)).command).context=1 :=by
      rw [hc]
      rfl
    simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,stage] using
      (congrArg (fun z=>(IntegralMixedCommandHeaderBits.command
        (IntegralMixedFramedRootPullback.instructionAt (NB).parameters
          (NB).plan (pairFst (key true z)) (birth false z)).command).context)
        (pairFst_pair q [])).trans HH

include hc in
theorem correlation_creating_column :
    IntegralMixedFramedCriticalGuardBits.physical (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q [])=
    IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (NB).parameters
        (NB).plan (pairFst (key true q)))
      ((NB).plan.rules (pairFst (key true q))) (birth false q))+
        r.offset.val+r.coordinate%((NB).parameters.ambient
          (pairFst (key true q))-r.offset.val+1) :=by
  have HE : IntegralMixedFramedCriticalGuardBits.physical (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q [])=
    IntegralMixedFramedCriticalGuardBits.physical (NB).parameters
      NT (key true) (birth false) q :=by
    simp only [IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralMixedFramedCriticalGuardBits.header,stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
  rw [HE]
  exact IntegralMixedFramedCriticalGuardBits.physical_at_critical _ _ _ _ NR
    (key true) (birth false) q r hc

noncomputable def creatingSelected (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) : ℝ :=
  IntegralMixedFramedBankObservation.extend
    (IntegralFramedPhysicalSquare.joint (NB).parameters
      (NB).plan (NB).data
      (NB).nodes (NB).factor
      (NB).seed (NB).bounds
      (key true) (positive true) q v hv)
    (IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (NB).parameters
        (NB).plan (pairFst (key true q)))
      ((NB).plan.rules (pairFst (key true q))) (birth false q))+
        r.offset.val+r.coordinate%((NB).parameters.ambient
          (pairFst (key true q))-r.offset.val+1))^
    UniformIntegralPowerSchedule.physical ((NB).parameters.cap
      (pairFst (key true q))+1)
      (2^(NB).parameters.width (pairFst (key true q))) (birth false q)

include hc in
theorem correlation_iff_creating (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) :
    correlation (pair q v)=InfinitesimalSign.encode 0 ↔
      newestPoint q v hv=creatingSelected q r v hv :=by
  have HA:=correlation_active q r hc
  rw [correlation_iff_newest q v hv HA]
  change newestPoint q v hv=_ ↔ _
  apply Iff.of_eq
  apply congrArg (fun z : ℝ=>newestPoint q v hv=z)
  unfold creatingSelected IntegralMixedFramedBankObservation.extend
  rw [←correlation_creating_column q r hc]
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt (NB).parameters
    (NB).plan (NB).data NT
    NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
    (stage) (pair q []) HA
  have HL':=HL
  rw [guard_count q []] at HL'
  change _<IntegralFramedPhysicalSquare.count (NB).parameters
    (NB).plan (key true q) at HL'
  rw [dite_eq_left HL']
  simp only [IntegralMixedFramedCriticalGuardBits.physicalPower,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,stage,pairFst_pair]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
