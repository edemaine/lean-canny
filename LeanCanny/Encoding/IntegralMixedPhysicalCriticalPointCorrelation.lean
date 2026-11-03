/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalStageMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalObservation
/-! # The native guard selects the actual geometric point-rule coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalCriticalPrefixes (key input positive)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank tables
local notation "BK" => bank hn ht ha hR outer
local notation "T" => tables hn ht ha hR outer

theorem correlation_iff_pointRule_at (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key n outer true q)),
      IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true)
        (positive hn ht ha hR outer true) q v hv j=z j.val)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (key n outer false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (key n outer false q)))
    (h : Fin ((BK).parameters.ambient (pairFst (key n outer false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (key n outer false q)).command=.critical (HA.pointData h h hh hh).rule) :
    correlation hn ht ha hR outer (pair q v)=InfinitesimalSign.encode 0 ↔
    newestPoint hn ht ha hR outer q v hv=
      IntegralMixedCriticalReadback.point
        (S:=(family (BK).parameters (BK).plan (BK).data).cap (key n outer false q))
        (B:=(family (BK).parameters (BK).plan (BK).data).width (key n outer false q))
        (m:=(family (BK).parameters (BK).plan (BK).data).birth (key n outer false q))
        (IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (key n outer false q)
          (HA.pointData h h hh hh).rule
          z) h :=by
  have HA':=active_parent hn ht ha hR outer q (HA.pointData h h hh hh).rule hc
  rw [correlation_iff_newest hn ht ha hR outer q v hv HA',
    IntegralMixedPhysicalCriticalObservation.point_ambient]
  apply Iff.of_eq
  apply congrArg (fun u : ℝ=>newestPoint hn ht ha hR outer q v hv=u)
  rw [power_parent hn ht ha hR outer q]
  apply congrArg (fun u : ℝ=>u^UniformIntegralPowerSchedule.physical
    ((family (BK).parameters (BK).plan (BK).data).cap (key n outer false q))
    (2^(family (BK).parameters (BK).plan (BK).data).width (key n outer false q))
    ((family (BK).parameters (BK).plan (BK).data).birth (key n outer false q)))
  let j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key n outer true q)) :=
    Fin.cast (guard_count hn ht ha hR outer q [])
      ⟨IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (BK).parameters (BK).plan (BK).data T
          (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
          (stage n outer) (pair q []) HA'⟩
  have HE:=hz j
  have HE' : correlationTuple hn ht ha hR outer q v hv
      ⟨IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (BK).parameters (BK).plan (BK).data T
          (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
          (stage n outer) (pair q []) HA'⟩=
      z (IntegralMixedFramedCriticalGuardBits.physical (BK).parameters T
          (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q [])) :=by
    exact HE
  rw [HE',physical_pointRule hn ht ha hR outer q F HP HA h hh hc]

theorem correlation_iff_pointRule (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (key n outer false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (key n outer false q)))
    (h : Fin ((BK).parameters.ambient (pairFst (key n outer false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (key n outer false q)).command=.critical (HA.pointData h h hh hh).rule) :
    correlation hn ht ha hR outer (pair q v)=InfinitesimalSign.encode 0 ↔
    newestPoint hn ht ha hR outer q v hv=
      IntegralMixedCriticalReadback.point
        (S:=(family (BK).parameters (BK).plan (BK).data).cap (key n outer false q))
        (B:=(family (BK).parameters (BK).plan (BK).data).width (key n outer false q))
        (m:=(family (BK).parameters (BK).plan (BK).data).birth (key n outer false q))
        (IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (key n outer false q)
          (HA.pointData h h hh hh).rule
          (IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data (BK).nodes (BK).factor (BK).seed (BK).bounds
            (key n outer true) (positive hn ht ha hR outer true) q v hv)) h :=by
  exact correlation_iff_pointRule_at hn ht ha hR outer q v hv
    (IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true)
      (positive hn ht ha hR outer true) q v hv)
    (fun j=>(IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true)
      (positive hn ht ha hR outer true) q v hv j).symm) F HP HA h hh hc

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
