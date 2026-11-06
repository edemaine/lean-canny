/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalPoints
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalRetainedSweep
/-! # Actual accepted critical heights belong to the canonical endpoint set -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "r" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd E he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
noncomputable local instance providerCriticalEndpointIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

theorem canonical_height_mem_jointEndpointSet (q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hp : FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old)
    (ht : FormulaSignSlotRadialProviderAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth old)
    (HS : pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp∈
      frozenSlice (FormulaSignSlotRadialProviderAtomic.provider old) (FormulaSignSlotRadialProviderAtomic.depth old)
        (FormulaSignSlotRadialProviderAtomic.levels old hv)) :
    parentPoint old (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp) h∈
      jointEndpointSet x hm phi (d).frame h g hg V choices :=
  Or.inr (canonical_height_mem_realCriticalValues old hv hd q hq hp ht HS)

theorem canonical_point_eq (q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hp : FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old)
    (p : Fin ((P).ambient r+1)→ℝ)
    (HE : providerPoint old p=pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp) :
    p=parentPoint old (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp) := by
  simpa only [parentPoint_providerPoint] using congrArg (parentPoint old) HE

theorem canonical_point_height_mem_jointEndpointSet (q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hp : FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old)
    (ht : FormulaSignSlotRadialProviderAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth old)
    (p : Fin ((P).ambient r+1)→ℝ)
    (HE : providerPoint old p=pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp)
    (HS : p∈slice (Q r) (d).frame V) :
    p h∈jointEndpointSet x hm phi (d).frame h g hg V choices := by
  have HC := (providerPoint_slice_iff old hv hd p).mpr HS
  rw [HE] at HC
  rw [canonical_point_eq old q hq hp p HE]
  exact canonical_height_mem_jointEndpointSet old hv hd q hq hp ht HC

theorem canonical_point_child_partials (q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hp : FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old)
    (ht : FormulaSignSlotRadialProviderAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth old)
    (p : Fin ((P).ambient r+1)→ℝ)
    (HE : providerPoint old p=pointAt (FormulaSignSlotRadialProviderAtomic.provider old) q hq hp) :
    ∀i,i∉(line (d).frame h).frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0 := by
  rw [canonical_point_eq old q hq hp p HE]
  intro i hi _
  exact canonical_child_partials old hv hd q hq hp ht i hi

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
