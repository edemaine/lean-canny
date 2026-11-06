/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalStageMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalObservation
/-! # The native guard selects the actual geometric point-rule coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "K" => FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

theorem correlation_iff_pointRule_at (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key true q)),
      IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (key true)
        (positive true) q v hv j=z j.val)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (key false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (key false q)))
    (h : Fin ((BK).parameters.ambient (pairFst (key false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (key false q)).command=.critical (HA.pointData h h hh hh).rule) :
    correlation (pair q v)=InfinitesimalSign.encode 0 ↔
    newestPoint q v hv=
      IntegralMixedCriticalReadback.point
        (S:=(family (BK).parameters (BK).plan (BK).data).cap (key false q))
        (B:=(family (BK).parameters (BK).plan (BK).data).width (key false q))
        (m:=(family (BK).parameters (BK).plan (BK).data).birth (key false q))
        (IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (key false q)
          (HA.pointData h h hh hh).rule
          z) h :=by
  have HA':=active_parent q (HA.pointData h h hh hh).rule hc
  rw [correlation_iff_newest q v hv HA',
    IntegralMixedPhysicalCriticalObservation.point_ambient]
  apply Iff.of_eq
  apply congrArg (fun u : ℝ=>newestPoint q v hv=u)
  rw [power_parent q]
  apply congrArg (fun u : ℝ=>u^UniformIntegralPowerSchedule.physical
    ((family (BK).parameters (BK).plan (BK).data).cap (key false q))
    (2^(family (BK).parameters (BK).plan (BK).data).width (key false q))
    ((family (BK).parameters (BK).plan (BK).data).birth (key false q)))
  let j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key true q)) :=
    Fin.cast (guard_count q [])
      ⟨IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (BK).parameters (BK).plan (BK).data T
          NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
          (stage) (pair q []) HA'⟩
  have HE:=hz j
  have HE' : correlationTuple q v hv
      ⟨IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (BK).parameters (BK).plan (BK).data T
          NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
          (stage) (pair q []) HA'⟩=
      z (IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
          (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q [])) :=by
    exact HE
  rw [HE',physical_pointRule q F HP HA h hh hc]

theorem correlation_iff_pointRule (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (key false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (key false q)))
    (h : Fin ((BK).parameters.ambient (pairFst (key false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (key false q)).command=.critical (HA.pointData h h hh hh).rule) :
    correlation (pair q v)=InfinitesimalSign.encode 0 ↔
    newestPoint q v hv=
      IntegralMixedCriticalReadback.point
        (S:=(family (BK).parameters (BK).plan (BK).data).cap (key false q))
        (B:=(family (BK).parameters (BK).plan (BK).data).width (key false q))
        (m:=(family (BK).parameters (BK).plan (BK).data).birth (key false q))
        (IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (key false q)
          (HA.pointData h h hh hh).rule
          (IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data (BK).nodes (BK).factor (BK).seed (BK).bounds
            (key true) (positive true) q v hv)) h :=by
  exact correlation_iff_pointRule_at q v hv
    (IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key true)
      (positive true) q v hv)
    (fun j=>(IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key true)
      (positive true) q v hv j).symm) F HP HA h hh hc

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
