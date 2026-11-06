/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalCreatingCorrelation
public import LeanCanny.Geometry.IntegralMixedPrefixPointReadback
public import LeanCanny.Geometry.IntegralMixedAtomicFrameRecord
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalStageMetadata
/-! # Literal metadata of the appended point-rule probe

Header and column equalities take values in source-independent types. This
retains the actual parent source without casting its algebra or frame.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key)
open IntegralMixedFramedHistoryFamilyBits (family commands instruction prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

theorem stage_parent (q : List Bool) : stage (pair q [])=
    prefixLength (B).parameters (key false q) :=by
  have HE:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  simpa only [stage,pairFst_pair] using HE.symm

theorem root_parent (q : List Bool) :
    pairFst (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true) (pair q []))=
      pairFst (key false q) :=by
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,key,
    IntegralMixedFramedHistoryFamilyBits.keyAt,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]

private noncomputable def headerAt (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (root : List Bool) (j : ℕ) : IntegralMixedCommandHeaderBits.Header :=
  IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D root j).command

theorem header_parent (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.header T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q [])=
    IntegralMixedCommandHeaderBits.command (instruction (B).parameters (B).plan (key false q)).command :=by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual _ _ _ _ NR]
  exact congrArg₂ (headerAt (B).parameters (B).plan)
    (root_parent q) (stage_parent q)

private noncomputable def arityAt (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (root : List Bool) (j : ℕ) : ℕ :=
  IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) j)

theorem prefix_arity_parent (q : List Bool) :
    IntegralMixedFramedPhysicalIndex.prefixArity (B).parameters T
      (IntegralMixedFramedCriticalGuardBits.packet
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []))=
      IntegralMixedFramedPhysicalIndex.arity (commands (B).parameters (B).plan (key false q)) :=by
  unfold IntegralMixedFramedCriticalGuardBits.packet
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet _ _ _ _ NR]
  exact congrArg₂ (arityAt (B).parameters (B).plan)
    (root_parent q) (stage_parent q)

theorem power_parent (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q [])=
      UniformIntegralPowerSchedule.physical ((family (B).parameters (B).plan (B).data).cap (key false q))
        (2^(family (B).parameters (B).plan (B).data).width (key false q))
        ((family (B).parameters (B).plan (B).data).birth (key false q)) :=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [root_parent q,stage_parent q,
    IntegralMixedFramedHistoryFamilyBits.family_birth]
  rfl

theorem child_key (q : List Bool) : key true q=
    IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key false q))
      (prefixLength (B).parameters (key false q)+1) q :=by
  have HE:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  rw [HE,←FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
  simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem parent_room (q : List Bool) : prefixLength (B).parameters (key false q)≤
    (B).parameters.cap (pairFst (key false q)) :=by
  have HE:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  rw [HE]
  have HR:=FormulaSignSlotRadialProviderCriticalPrefixes.below_cap false q
  simpa only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair] using HR.le

theorem active_parent (q : List Bool)
    (r : IntegralMixedHistory.CriticalRule ((B).parameters.ambient (pairFst (key false q))))
    (hc : (instruction (B).parameters (B).plan (key false q)).command=.critical r) :
    IntegralMixedFramedCriticalGuardBits.Active (B).parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []) :=by
  constructor
  · simp only [stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
    have HE:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth true q
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
    rw [HE,FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
    omega
  · rw [header_parent q,hc]
    rfl

theorem physical_pointRule (q : List Bool)
    (F : IntegralMixedFrozenFrame.Frame ((B).parameters.ambient (pairFst (key false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (B).parameters (B).plan (B).data).birth (key false q)))
    (h : Fin ((B).parameters.ambient (pairFst (key false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (B).parameters (B).plan (key false q)).command=.critical (HA.pointData h h hh hh).rule) :
    IntegralMixedFramedCriticalGuardBits.physical (B).parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q [])=
      IntegralMixedFramedPhysicalIndex.arity (commands (B).parameters (B).plan (key false q))+h.val :=by
  unfold IntegralMixedFramedCriticalGuardBits.physical
  rw [prefix_arity_parent q,header_parent q,hc]
  change _+(HA.pointData h h hh hh).rule.offset.val+
    (HA.pointData h h hh hh).rule.coordinate%(_-(HA.pointData h h hh hh).rule.offset.val+1)=_
  rw [Nat.add_assoc,HP.pointData_selected F HA h hh]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
