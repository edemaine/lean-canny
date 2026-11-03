/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalNaturalPoint
public import LeanCanny.Algebra.IntegralMixedFullBankObservation
/-! # The full bank observation reads exactly the complete vertex's quotients

The natural array is a view of one joint tuple. No scalar root is allocated
separately, and all denominator and coordinate powers come from that state.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)

theorem bank_observation_of_joint (z : ℕ→ℝ)
    (hz : ∀j : Fin (count P D (key c)),joint P D H L F C hs key hpos c w hv j=z j.val)
    (i : Fin ((family P D H).birth (key c))) :
    (IntegralMixedFullBankObservation.atFamily P D H (key c)).point z i.val=
      point P D H L F C hs key hpos c w hv i :=by
  rw [IntegralMixedFullBankObservation.atFamily,IntegralMixedFullBankObservation.point_ofState]
  change IntegralMixedCanonicalBankPoint.point _ _ i=IntegralMixedCanonicalBankPoint.point _ _ i
  apply congrArg (fun f=>IntegralMixedCanonicalBankPoint.point ((family P D H).state (key c)) f i)
  funext j
  exact (hz (enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar j))).symm

theorem bank_naturalPoint (i : Fin ((family P D H).birth (key c))) :
    (IntegralMixedFullBankObservation.atFamily P D H (key c)).point
      (naturalPoint P D H L F C hs key hpos c w hv) i.val=point P D H L F C hs key hpos c w hv i :=
  bank_observation_of_joint P D H L F C hs key hpos c w hv _
    (fun j=>(naturalPoint_at P D H L F C hs key hpos c w hv j).symm) i

end LeanCanny.Encoding.IntegralFramedPhysicalSquare

namespace LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
open LeanCanny.Algebra IntegralMixedHistory

theorem critical_step_succ {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (z : ((ι⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ) (i : Fin m) :
    point (criticalStep x hm r) (fun j=>z ((criticalStep x hm r).sampler.scalar j)) i.succ=
      point x (fun j=>z (Sum.inl (Sum.inl (x.sampler.scalar j)))) i :=by
  change z (Sum.inl (Sum.inl (x.sampler.scalar i)))^
    UniformIntegralPowerSchedule.weights S (2^B) (m+1) i.succ/(x.bank.denominator i:ℝ)=_
  rw [UniformIntegralPowerSchedule.old]
  rfl

end LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
