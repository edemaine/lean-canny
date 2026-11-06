/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMatchedSlabSimulation
public import LeanCanny.Geometry.IntegralMixedMatchedFiniteSweep
public import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths
/-! # Actual native graph simulation includes artificial empty-cut slabs -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedRelativeCuts IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep Set
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
noncomputable local instance providerSweepSlabIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

open FormulaSignSlotRadialProviderGraph

private theorem endpoint_reach_of_empty_branches {X J :Type*} [TopologicalSpace X] [IsEmpty J]
    {f :X→ℝ} {a b :ℝ} (D :ComponentSlabCover.InteriorData f a b J)
    (hab :a<b) {u v :X} (hu :f u=a∨f u=b) (H :D.EndpointReach u v):D.FiberLink u v:=by
  induction H with
  | refl=>exact D.fiberLink_refl hu
  | @tail y z _ HStep IH=>
    apply D.fiberLink_trans hab IH
    cases HStep with
    | left H=>exact Or.inl H
    | right H=>exact Or.inr H
    | forward j=>exact isEmptyElim j
    | backward j=>exact isEmptyElim j

private theorem sweep_subtype_fiber_path {X :Type*} [TopologicalSpace X] (K :Set X)
    (f :K→ℝ) (height :X→ℝ) (HF :∀y,f y=height y.val)
    (heightValue :ℝ) {u v :K} (H :JoinedIn (f ⁻¹' {heightValue}) u v):
    JoinedIn (K∩{y |height y=heightValue}) u.val v.val:=by
  apply (H.map continuous_subtype_val.continuousOn).mono
  rintro y ⟨w,hw,rfl⟩
  exact ⟨w.property,(HF w).symm.trans hw⟩

/-- Artificial empty cut fibers need no endpoint origin certificate. -/
theorem point_reachable_of_sweep_slab
    (W :MatchedFiniteSweep x hm phi (d).frame h g hg V
      (prefixInputChoices x hm (d).frame h g hg
        (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi choices))
    (i :Fin (W.slabs+1))
    (p q :Fin ((P).ambient r+1)→ℝ)
    (HP :p∈slice (Q r) (d).frame V) (HQ :q∈slice (Q r) (d).frame V)
    (Hph :p h=W.cut i.val∨p h=W.cut (i.val+1))
    (Hqh :q h=W.cut i.val∨q h=W.cut (i.val+1))
    (HGp :∀j,j∉insert h (d).frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀j,j∉insert h (d).frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice (Q r) (d).frame V∩{y |y h∈Icc (W.cut i.val) (W.cut (i.val+1))}) p q)
    (IH :DepthComplete (FormulaSignSlotRadialProviderAtomic.provider old)
      (FormulaSignSlotRadialProviderAtomic.depth old+1)):
    PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
      (providerPoint old p)
      (providerPoint old q):=by
  let a:=W.cut i.val
  let b:=W.cut (i.val+1)
  let M:=W.matched i
  have hab :a<b:=W.strict (Fin.castSucc_lt_succ (i:=i))
  have Hset:=prefixInputChoices_badset x hm (d).frame h g hg
    (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi V choices
  have Hgap :∀v∈Ioo a b,v∉jointEndpointSet x hm phi (d).frame h g hg V choices:=by
    intro v hv
    rw [←Hset]
    exact W.gap i v hv
  by_cases HBoth :a∈jointEndpointSet x hm phi (d).frame h g hg V choices ∧
      b∈jointEndpointSet x hm phi (d).frame h g hg V choices
  · exact point_reachable_of_matched_slab old hv hd (.fresh a) (.fresh b)
      HBoth.1 HBoth.2 hab
      (fun v hv hbad=>Hgap v hv (Or.inl hbad))
      (Set.disjoint_left.mpr (fun v hv hbad=>Hgap v hv (Or.inr hbad))) M
      p q HP HQ Hph Hqh HGp HGq HJ IH
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  let K:=slice (Q r) (coarse (line (d).frame h) h) V
  let u :K:=⟨p,by simpa only [K,coarse_line (d).frame h hh] using HP⟩
  let v :K:=⟨q,by simpa only [K,coarse_line (d).frame h hh] using HQ⟩
  have HProjection (y :K):coarseProjection (Q r) (line (d).frame h) V h y=y.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V y.val
  have HUsed (j :Fin (W.slabs+2)) (y :K)
      (HY :coarseProjection (Q r) (line (d).frame h) V h y=W.cut j.val):
      W.cut j.val∈jointEndpointSet x hm phi (d).frame h g hg V choices:=by
    rcases W.origin j with Hbad|Hempty
    · rwa [Hset] at Hbad
    · have HFiber :y∈(coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' {W.cut j.val}:=HY
      rw [Hempty] at HFiber
      exact False.elim HFiber
  let J:=IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
    (cutRule x (d).frame h g hg) phi (consecutiveMidpoint W.cut W.strict i).val
  let :IsEmpty J:=⟨fun j=>HBoth ⟨HUsed i.castSucc (M.interior.arc j a) (M.interior.level_left j),
    HUsed i.succ (M.interior.arc j b) (M.interior.level_right j)⟩⟩
  let :=M.finite_index
  let :=W.finite_endpoint i.castSucc
  let :=W.finite_endpoint i.succ
  have HU :coarseProjection (Q r) (line (d).frame h) V h u=a∨
      coarseProjection (Q r) (line (d).frame h) V h u=b:=by rw [HProjection];exact Hph
  have HV :coarseProjection (Q r) (line (d).frame h) V h v=a∨
      coarseProjection (Q r) (line (d).frame h) V h v=b:=by rw [HProjection];exact Hqh
  have HUcc :u∈(coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' Icc a b:=by
    rcases HU with HE|HE <;> change _∈Icc a b <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HVcc :v∈(coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' Icc a b:=by
    rcases HV with HE|HE <;> change _∈Icc a b <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HSub :JoinedIn ((coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' Icc a b) u v:=by
    have HI:=Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image HUcc HVcc
    rw [closed_slab_image (Q r) (d).frame V h hh (d).free_normal a b] at HI
    exact HI.mp HJ
  have HWalk:=(M.interior.endpoint_joined_iff_reach (W.endpointCover i.castSucc) (W.endpointCover i.succ)
    (coarseProjection_continuous (Q r) (line (d).frame h) V h) hab
    (consecutiveMidpoint W.cut W.strict i) M.clopen HU HV).mp HSub
  have HFiber:=endpoint_reach_of_empty_branches (J:=J) M.interior hab HU HWalk
  have HReach (height :ℝ) (j :Fin (W.slabs+2)) (HC :W.cut j.val=height)
      (HF :JoinedIn ((coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' {height}) u v):
      PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
        (providerPoint old p)
        (providerPoint old q):=by
    have HAllowed :height∈jointEndpointSet x hm phi (d).frame h g hg V choices:=by
      rw [←HC]
      exact HUsed j u (HF.source_mem.trans HC.symm)
    exact point_reachable_of_endpoint_fiber old hv hd (.fresh height) HAllowed p q HP HQ
      ((HProjection u).symm.trans HF.source_mem) ((HProjection v).symm.trans HF.target_mem) HGp HGq
      (by simpa only [K,u,v,IntegralMixedOptionalEndpoints.Endpoint.value,coarse_line (d).frame h hh] using
        sweep_subtype_fiber_path K _ (fun y=>y h) HProjection height HF) IH
  rcases HFiber with HF|HF
  · exact HReach a i.castSucc rfl HF
  · exact HReach b i.succ rfl HF

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
