/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphChildFiber
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperEqualPreservingChild
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalRetainedSweep
/-! # Next-depth completeness simulates actual allowed endpoint fibers -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
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
noncomputable local instance providerEndpointFiberIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

open FormulaSignSlotRadialProviderGraph

theorem point_reachable_of_endpoint_fiber (endpoint : ParentEndpoint old hv hd)
    (HAllowed : endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p q : Fin ((P).ambient r+1)→ℝ)
    (HP : p∈slice (Q r) (d).frame V) (HQ : q∈slice (Q r) (d).frame V)
    (Hph : p h=endpoint.value V) (Hqh : q h=endpoint.value V)
    (HGp : ∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq : ∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ : JoinedIn (slice (Q r) (d).frame V∩{y |y h=endpoint.value V}) p q)
    (IH : DepthComplete (FormulaSignSlotRadialProviderAtomic.provider old) (FormulaSignSlotRadialProviderAtomic.depth old+1)) :
    PointReachable (FormulaSignSlotRadialProviderAtomic.provider old) (providerPoint old p) (providerPoint old q) := by
  obtain ⟨qp,hVp,hcp,hdp,hPp,_⟩ := exists_equal_preserving_child old hv hd endpoint HAllowed p HP Hph HGp
  obtain ⟨qq,hVq,hcq,hdq,hPq,_⟩ := exists_equal_preserving_child old hv hd endpoint HAllowed q HQ Hqh HGq
  have HPointp := providerPoint_eq_pointAt_of_native_heq old qp hVp hcp p hPp
  have HPointq := providerPoint_eq_pointAt_of_native_heq old qq hVq hcq q hPq
  let coord := childCoordinate (FormulaSignSlotRadialProviderAtomic.provider old) old hv rfl
  have Hcoord : Fin.cast (parent_point_dimension old).symm coord=h := by
    apply Fin.ext
    simp only [Fin.val_cast,coord,childCoordinate_val,IntegralMixedChronologicalSweepFrame.next]
    exact (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd E he).symm
  have HOld : pointAt (FormulaSignSlotRadialProviderAtomic.provider old) qp hVp hcp∈
      frozenSlice (FormulaSignSlotRadialProviderAtomic.provider old) (FormulaSignSlotRadialProviderAtomic.depth old)
        (FormulaSignSlotRadialProviderAtomic.levels old hv) := by
    rw [←HPointp]
    exact (providerPoint_slice_iff old hv hd p).mpr HP
  have Hheight : pointAt (FormulaSignSlotRadialProviderAtomic.provider old) qp hVp hcp coord=endpoint.value V := by
    rw [←HPointp]
    change p (Fin.cast _ coord)=endpoint.value V
    rw [Hcoord]
    exact Hph
  have HSlice := child_frozenSlice_eq (FormulaSignSlotRadialProviderAtomic.provider old) old qp hv hVp rfl hcp hdp
    HOld (endpoint.value V) Hheight
  have HNative : JoinedIn (frozenSlice (FormulaSignSlotRadialProviderAtomic.provider old)
      (FormulaSignSlotRadialProviderAtomic.depth qp) (FormulaSignSlotRadialProviderAtomic.levels qp hVp))
      (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) qp hVp hcp)
      (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) qq hVq hcq) := by
    rw [HSlice,←HPointp,←HPointq]
    apply (HJ.map (providerPoint_continuous old).continuousOn).mono
    rintro _ ⟨sample,hSample,rfl⟩
    refine ⟨(providerPoint_slice_iff old hv hd sample).mpr hSample.1,?_⟩
    change sample (Fin.cast _ coord)=endpoint.value V
    rw [Hcoord]
    exact hSample.2
  have HR := IH qp qq hVp hVq hcp hcq hdp hdq (by simpa only [hdp] using HNative)
  rw [HPointp,HPointq]
  exact (point_reachable_iff_raw _ qp qq hVp hVq hcp hcq).mpr HR

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
