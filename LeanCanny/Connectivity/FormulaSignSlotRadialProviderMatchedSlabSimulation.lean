/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderEndpointFiber
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderProperBranchReachability
public import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths
/-! # Actual provider graph simulation of genuine matched closed-slab paths -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedRelativeCuts IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem atomic_walk_simulation {X J :Type*} [TopologicalSpace X] {f :X→ℝ} {a b :ℝ}
    (D :ComponentSlabCover.InteriorData f a b J) (K :Set X) (R :X→X→Prop)
    (HTrans :∀{x y z},R x y→R y z→R x z)
    (HRefl :∀x∈K,R x x)
    (HStep :∀x∈K,∀y∈K,ComponentSlabCover.InteriorData.EndpointStep D x y→R x y)
    {x y :K} (H :D.AtomicEndpointReach K x y):R x.val y.val:=by
  induction H with
  | refl=>exact HRefl _ x.property
  | @tail y z _ h IH=>exact HTrans IH (HStep _ y.property _ z.property h)

private theorem subtype_fiber_path {X :Type*} [TopologicalSpace X] (S :Set X)
    (f :S→ℝ) (height :X→ℝ) (HF :∀y,f y=height y.val)
    (t :ℝ) {u v :S} (H :JoinedIn (f ⁻¹' {t}) u v):
    JoinedIn (S∩{y |height y=t}) u.val v.val:=by
  apply (H.map continuous_subtype_val.continuousOn).mono
  rintro y ⟨w,hw,rfl⟩
  exact ⟨w.property,(HF w).symm.trans hw⟩

private theorem branch_endpoint_data {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (hm :m≤S) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F :Frame a) (h :Fin (a+1)) (hh :h∉F.frozen) (HF :FreeNormal F)
    (g :Fin (a+1)) (hg :g∉(line F h).frozen) (values :Fin m→ℝ)
    (HV :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (lo hi :ℝ) (center :Ioo lo hi)
    (M :MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self _ _) g hg values lo hi center)
    (j :IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ center.val)
    (t :ℝ) (ht :t∈Icc lo hi):
    (M.interior.arc j t).val∈slice P F values ∧ (M.interior.arc j t).val h=t ∧
      ∀i,i∉insert h F.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) (M.interior.arc j t).val=0:=by
  rw [M.readback j t ht]
  exact selected_point_endpoint x hm φ F h hh HF g hg values HV t _ (M.physical j t ht)

open FormulaSignSlotRadialProviderGraph
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
noncomputable local instance providerMatchedSlabIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

variable (left right :ParentEndpoint old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

/-- A genuine closed-slab path between critical boundary points is simulated
by the actual native graph, using only the next-depth recursive statement. -/
theorem point_reachable_of_matched_slab
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab :a<b)
    (havoid :∀v,v∈Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm
      (cutRule x (d).frame h g hg) phi choices)
    (hheight :Disjoint (Ioo a b) (realCriticalValues (Q r) (line (d).frame h) V h))
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (p q :Fin ((P).ambient r+1)→ℝ)
    (HP :p∈slice (Q r) (d).frame V) (HQ :q∈slice (Q r) (d).frame V)
    (Hph :p h=a∨p h=b) (Hqh :q h=a∨q h=b)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice (Q r) (d).frame V∩{y |y h∈Icc a b}) p q)
    (IH :DepthComplete (FormulaSignSlotRadialProviderAtomic.provider old)
      (FormulaSignSlotRadialProviderAtomic.depth old+1)):
    PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
      (providerPoint old p)
      (providerPoint old q):=by
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst :(h).val=(d).frame.frozen.card:=(d).frozen_card.symm
  obtain ⟨R,_⟩:=FormulaSignSlotRadialProviderProperParent.exists_guarded_pair old hv hd left right HL HR
  have HRoom :(cs).length+R.result.commands.length+((P).ambient r-(d).frame.frozen.card)≤(P).cap r+2:=by
    have HB:=FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he
    have HC:=R.result.count
    rw [(d).frozen_card]
    omega
  have HProper := FormulaSignSlotRadialProviderGraph.parent_source_proper old hv
  let S:=slice (Q r) (coarse (line (d).frame h) h) V
  let u :S:=⟨p,by simpa only [S,coarse_line (d).frame h hh] using HP⟩
  let v :S:=⟨q,by simpa only [S,coarse_line (d).frame h hh] using HQ⟩
  have HProjection (y :S):coarseProjection (Q r) (line (d).frame h) V h y=y.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V y.val
  have HU :coarseProjection (Q r) (line (d).frame h) V h u=a∨
      coarseProjection (Q r) (line (d).frame h) V h u=b:=by rw [HProjection];exact Hph
  have HV :coarseProjection (Q r) (line (d).frame h) V h v=a∨
      coarseProjection (Q r) (line (d).frame h) V h v=b:=by rw [HProjection];exact Hqh
  have HWalk:=(R.result.matched_atomic_paths hm h hh hfirst (d).free_normal g hg
    (FormulaSignSlotRadialProviderRetainedAppend.charge old)
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E) HProper HRoom hab
    ⟨(a+b)/2,by constructor <;> linarith⟩ M u v HU HV).mp HJ
  let K:=M.interior.endpointSupport u v
  let Good (y :S):Prop:=(y.val h=a∨y.val h=b) ∧ ∀i,i∉insert h (d).frame.frozen→i≠g→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
      (Int.castRingHom ℝ) y.val=0
  have HSupport :∀y∈K,Good y:=by
    intro y hy
    simp only [K,ComponentSlabCover.InteriorData.endpointSupport,mem_insert_iff,mem_union,mem_range] at hy
    rcases hy with rfl|rfl|⟨j,rfl⟩|⟨j,rfl⟩
    · exact ⟨Hph,HGp⟩
    · exact ⟨Hqh,HGq⟩
    · have H:=branch_endpoint_data x hm phi (d).frame h hh (d).free_normal g hg V
        (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he) a b _ M j a ⟨le_rfl,hab.le⟩
      exact ⟨Or.inl H.2.1,H.2.2⟩
    · have H:=branch_endpoint_data x hm phi (d).frame h hh (d).free_normal g hg V
        (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he) a b _ M j b ⟨hab.le,le_rfl⟩
      exact ⟨Or.inr H.2.1,H.2.2⟩
  let Reach (y z :S):Prop:=PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
    (providerPoint old y.val)
    (providerPoint old z.val)
  have HFiber (endpoint :ParentEndpoint old hv hd)
      (HA :endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
      (y z :S) (hy :y∈K) (hz :z∈K)
      (H :JoinedIn ((coarseProjection (Q r) (line (d).frame h) V h) ⁻¹' {endpoint.value V}) y z):Reach y z:=by
    exact point_reachable_of_endpoint_fiber old hv hd endpoint HA y.val z.val
      (by simpa only [S,coarse_line (d).frame h hh] using y.property)
      (by simpa only [S,coarse_line (d).frame h hh] using z.property)
      ((HProjection y).symm.trans H.source_mem) ((HProjection z).symm.trans H.target_mem)
      (HSupport y hy).2 (HSupport z hz).2
      (by simpa only [S,coarse_line (d).frame h hh] using
        subtype_fiber_path S _ (fun p=>p h) HProjection (endpoint.value V) H) IH
  have HRefl (y :S) (hy :y∈K):Reach y y:=by
    rcases (HSupport y hy).1 with HE|HE
    · exact HFiber left HL y y hy hy (JoinedIn.refl ((HProjection y).trans HE))
    · exact HFiber right HR y y hy hy (JoinedIn.refl ((HProjection y).trans HE))
  have HStep (y :S) (hy :y∈K) (z :S) (hz :z∈K)
      (H :ComponentSlabCover.InteriorData.EndpointStep M.interior y z):Reach y z:=by
    cases H with
    | left H=>exact HFiber left HL _ _ hy hz H
    | right H=>exact HFiber right HR _ _ hy hz H
    | forward j=>
      have HR:=FormulaSignSlotRadialProviderGraph.proper_branch_point_reachable old hv hd left right
        HL HR hab havoid hheight M j
      exact (congrArg₂ (fun p q=>PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
        (providerPoint old p)
        (providerPoint old q))
        (M.readback j a ⟨le_rfl,hab.le⟩) (M.readback j b ⟨hab.le,le_rfl⟩)).mpr HR
    | backward j=>
      have HR:=FormulaSignSlotRadialProviderGraph.proper_branch_point_reachable old hv hd left right
        HL HR hab havoid hheight M j
      exact (congrArg₂ (fun p q=>PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
        (providerPoint old p)
        (providerPoint old q))
        (M.readback j b ⟨hab.le,le_rfl⟩) (M.readback j a ⟨le_rfl,hab.le⟩)).mpr HR.symm
  exact atomic_walk_simulation M.interior K Reach
    (fun H K=>FormulaSignSlotRadialProviderGraph.PointReachable.trans H K) HRefl HStep HWalk

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
