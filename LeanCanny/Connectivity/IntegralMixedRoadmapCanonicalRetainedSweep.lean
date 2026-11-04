/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalFiniteSweep
/-! # Actual finite matched sweeps retaining a prescribed old bank value -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open IntegralMixedOptionalEndpoints IntegralMixedFullHistoryScript
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type}

/-- Cut origins may be existing bank values, in addition to genuine bad values.
The prescribed retained value is included without declaring it a bad root. -/
structure RetainedMatchedFiniteSweep (x :State P S B m ι) (hm :m≤S)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F :Frame n)
    (h g :Fin (n+1)) (hg :g∉(line F h).frozen) (values :Fin m→ℝ)
    (old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) (target :Fin m) where
  slabs :ℕ
  cut :ℕ→ℝ
  strict :StrictMono (fun i :Fin (slabs+2)=>cut i.val)
  includes_bad :∀t∈jointEndpointSet x hm φ F h g hg values old,∃j :Fin (slabs+2),cut j.val=t
  includes_target :∃j :Fin (slabs+2),cut j.val=values target
  range_bound :∀y :slice P (coarse (line F h) h) values,
    coarseProjection P (line F h) values h y∈Icc (cut 0) (cut (slabs+1))
  gap :∀i :Fin (slabs+1),∀t∈Ioo (cut i.val) (cut (i.val+1)),
    t∉jointEndpointSet x hm φ F h g hg values old
  gap_target :∀i :Fin (slabs+1),∀t∈Ioo (cut i.val) (cut (i.val+1)),t≠values target
  origin :∀j :Fin (slabs+2),
    (∃endpoint :Endpoint m,endpoint.Allowed (jointEndpointSet x hm φ F h g hg values old) ∧
      endpoint.value values=cut j.val) ∨
    (coarseProjection P (line F h) values h) ⁻¹' {cut j.val}=∅
  endpointIndex :Fin (slabs+2)→Type
  finite_endpoint :∀j,Finite (endpointIndex j)
  endpointCover :∀j,ClopenPathCover
    ((coarseProjection P (line F h) values h) ⁻¹' {cut j.val}) (endpointIndex j)
  matched :∀i :Fin (slabs+1),MatchedSlabInterior x hm φ (line F h) h
    (Finset.mem_insert_self _ _) g hg values (cut i.val) (cut (i.val+1))
    (consecutiveMidpoint cut strict i)
  leftOf :∀i,IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
    (cutRule x F h g hg) φ (consecutiveMidpoint cut strict i).val→endpointIndex i.castSucc
  rightOf :∀i,IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
    (cutRule x F h g hg) φ (consecutiveMidpoint cut strict i).val→endpointIndex i.succ
  selected :∀i j,ComponentSlabCover.Valid (matched i).interior
    (endpointCover i.castSucc) (endpointCover i.succ) j (leftOf i j) (rightOf i j)

namespace RetainedMatchedFiniteSweep
variable {x :State P S B m ι} {hm :m≤S} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
  {F :Frame n} {h g :Fin (n+1)} {hg :g∉(line F h).frozen} {values :Fin m→ℝ}
  {old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ} {target :Fin m}
  (W :RetainedMatchedFiniteSweep x hm φ F h g hg values old target)

abbrev Index (i :Fin (W.slabs+1)):=ComponentSlabCover.SelectedIndex
  (IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
    (cutRule x F h g hg) φ (consecutiveMidpoint W.cut W.strict i).val)
  (W.endpointIndex i.castSucc) (W.endpointIndex i.succ)

theorem finite_index (i :Fin (W.slabs+1)) :Finite (W.Index i):=by
  let :=W.finite_endpoint i.castSucc
  let :=W.finite_endpoint i.succ
  let :Finite (IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
    (cutRule x F h g hg) φ (consecutiveMidpoint W.cut W.strict i).val):=(W.matched i).finite_index
  exact inferInstance

theorem finite_cover_index :Finite (Σi,W.Index i):=by
  let :∀i,Finite (W.Index i):=W.finite_index
  exact inferInstance

noncomputable def slabCover (i :Fin (W.slabs+1)) :ClopenPathCover
    ((coarseProjection P (line F h) values h) ⁻¹' Icc (W.cut i.val) (W.cut (i.val+1))) (W.Index i):=by
  letI:=W.finite_index i
  exact ClopenPathCover.ofClosed
    (ComponentSlabCover.selectedPiece (W.matched i).interior
      (W.endpointCover i.castSucc) (W.endpointCover i.succ) (W.leftOf i) (W.rightOf i))
    (ComponentSlabCover.selected_closed _ _ _ _ _ (coarseProjection_continuous P (line F h) values h))
    (ComponentSlabCover.selected_cover _ _ _ _ _ (W.selected i))
    (ComponentSlabCover.selected_paths _ _ _ _ _ (coarseProjection_continuous P (line F h) values h)
      ((consecutiveMidpoint W.cut W.strict i).property.1.trans
        (consecutiveMidpoint W.cut W.strict i).property.2)
      (consecutiveMidpoint W.cut W.strict i))

noncomputable def cover (hh :h∉F.frozen) :ClopenPathCover (slice P F values) (Σi,W.Index i):=by
  letI:∀i,Finite (W.Index i):=W.finite_index
  exact (FiniteSlabCover.componentCover (coarseProjection P (line F h) values h) W.cut W.slabCover
    (coarseProjection_continuous P (line F h) values h) W.range_bound).comap
    (coarseLineHomeomorph P F values h hh)

end RetainedMatchedFiniteSweep

/-- The retained cut receives its existing producer. Other nonempty cut fibers
are constructed from actual fresh bad/critical values, not assumed covers. -/
theorem exists_retained_matched_finite_sweep [Fintype ι] (x :State P S B m ι) (hm :m≤S)
    (hn :0<n) (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F :Frame n) (HF :FreeNormal F) (HA :AtomicRows F m) (HP :PrefixFrozen F)
    (h :Fin (n+1)) (hh :h∉F.frozen) (hfirst :h.val=F.frozen.card)
    (g :Fin (n+1)) (hg :g∉(line F h).frozen)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) (target :Fin m)
    (room :m+2+(n-F.frozen.card)≤S+1)
    (hp :IsProperMap (fun y :Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    Nonempty (RetainedMatchedFiniteSweep x hm φ F h g hg values old target):=by
  have hcard :F.frozen.card<n+1:=by rw [←hfirst];exact h.isLt
  have hfree :firstFree F hcard=h:=Fin.ext hfirst.symm
  have HPline :PrefixFrozen (line F h):=by
    have HL:=HP.line_first hcard
    rwa [hfree] at HL
  let choices:=prefixInputChoices x hm F h g hg HPline φ old
  let p:=coarseProjection P (line F h) values h
  let forbidden:=jointEndpointSet x hm φ F h g hg values old∪{values target}
  have HFinite :(jointEndpointSet x hm φ F h g hg values old).Finite:=by
    have HB:=sweepBadReal_finite x hm φ F h g hg values H
      (prefixInputChoices x hm F h g hg HPline φ old)
    exact (congrArg Set.Finite (prefixInputChoices_badset x hm F h g hg HPline φ values old)).mp HB
  let :CompactSpace (slice P (coarse (line F h) h) values):=
    isCompact_iff_compactSpace.mp (coarse_compact P (line F h) values h hp)
  obtain ⟨N,cut,HM,HC,HB,HG,HO⟩:=FiniteCriticalSweepOrigins.exists_cuts p
    (coarseProjection_continuous P (line F h) values h) forbidden (HFinite.union (finite_singleton _))
  let seq :ℕ→ℝ:=fun j=>cut ⟨min j (N+1),by omega⟩
  have Hread (j :Fin (N+2)):seq j.val=cut j:=by
    apply congrArg cut
    apply Fin.ext
    have HJ:=j.isLt
    change min j.val (N+1)=j.val
    omega
  have HS :StrictMono (fun i :Fin (N+2)=>seq i.val):=by
    intro i j hij
    change seq i.val<seq j.val
    rw [Hread i,Hread j]
    exact HM hij
  have Hgap (i :Fin (N+1)):∀t∈Ioo (seq i.val) (seq (i.val+1)),t∉forbidden:=by
    change ∀t∈Ioo (seq i.castSucc.val) (seq i.succ.val),_
    rw [Hread i.castSucc,Hread i.succ]
    exact HG i
  have Horigin (j :Fin (N+2)):
      (∃endpoint :Endpoint m,endpoint.Allowed (jointEndpointSet x hm φ F h g hg values old) ∧
        endpoint.value values=seq j.val) ∨ p ⁻¹' {seq j.val}=∅:=by
    rw [Hread j]
    rcases HO j with HBad|HEmpty
    · by_cases HT :cut j=values target
      · exact Or.inl ⟨.retained target,True.intro,HT.symm⟩
      · have HJoint :cut j∈jointEndpointSet x hm φ F h g hg values old:=by
          rcases HBad with HJoint|HTarget
          · exact HJoint
          · exact False.elim (HT (mem_singleton_iff.mp HTarget))
        exact Or.inl ⟨.fresh (cut j),HJoint,rfl⟩
    · exact Or.inr HEmpty
  have Hends (j :Fin (N+2)):∃I :Type,Finite I∧Nonempty (ClopenPathCover (p ⁻¹' {seq j.val}) I):=by
    rcases Horigin j with ⟨endpoint,HE,HValue⟩|HEmpty
    · obtain ⟨R,_⟩:=realize_pair x hm (by omega) hn charge hdegree hcap F HF HA HP h hh g hg
        z hz φ hφ values H old endpoint endpoint HE HE
      have Hroom :m+R.commands.length+(n-F.frozen.card)≤S+1:=by have :=R.count;omega
      have HC:=R.exists_endpoint_cover h hh hfirst HF charge hdegree hp Hroom false
      have HHeight :(if false then endpoint.value values else endpoint.value values)=seq j.val:=by
        exact HValue
      exact Eq.mp (congrArg (fun t :ℝ=>∃I :Type,Finite I∧Nonempty (ClopenPathCover (p ⁻¹' {t}) I)) HHeight) HC
    · let :IsEmpty (p ⁻¹' {seq j.val}):=⟨fun y=>(Set.ext_iff.mp HEmpty y.val).mp y.property⟩
      exact ⟨Unit,inferInstance,⟨emptyCover _⟩⟩
  choose E HE CE using Hends
  let EC (j :Fin (N+2)):ClopenPathCover (p ⁻¹' {seq j.val}) (E j):=(CE j).some
  have HMexists (i :Fin (N+1)):Nonempty (MatchedSlabInterior x hm φ (line F h) h
      (Finset.mem_insert_self _ _) g hg values (seq i.val) (seq (i.val+1))
      (consecutiveMidpoint seq HS i)):=by
    apply exists_matched_slab_interior x hm φ (line F h) h (Finset.mem_insert_self _ _) g hg values H choices
      (seq i.val) (seq (i.val+1)) (consecutiveMidpoint seq HS i)
    · intro t ht HBad
      apply Hgap i t ht
      apply Or.inl
      rw [←prefixInputChoices_badset x hm F h g hg HPline φ values old]
      exact Or.inl HBad
    · intro t ht HBad
      exact Hgap i t ht (Or.inl (Or.inr HBad))
    · exact hp
  let M (i :Fin (N+1)):=(HMexists i).some
  have Hselect (i :Fin (N+1)):=ComponentSlabCover.exists_selection (M i).interior (EC i.castSucc) (EC i.succ)
  choose leftOf rightOf Hselected using Hselect
  refine ⟨{
    slabs:=N
    cut:=seq
    strict:=HS
    includes_bad:=?_
    includes_target:=?_
    range_bound:=?_
    gap:=fun i t ht HBad=>Hgap i t ht (Or.inl HBad)
    gap_target:=fun i t ht HT=>Hgap i t ht (Or.inr (mem_singleton_iff.mpr HT))
    origin:=Horigin
    endpointIndex:=E
    finite_endpoint:=HE
    endpointCover:=EC
    matched:=M
    leftOf:=leftOf
    rightOf:=rightOf
    selected:=Hselected}⟩
  · intro t ht
    obtain ⟨j,Hj⟩:=HC t (Or.inl ht)
    exact ⟨j,(Hread j).trans Hj⟩
  · obtain ⟨j,Hj⟩:=HC (values target) (Or.inr (mem_singleton _))
    exact ⟨j,(Hread j).trans Hj⟩
  · intro y
    change p y∈Icc (seq (0:Fin (N+2)).val) (seq (Fin.last (N+1)).val)
    rw [Hread 0,Hread (Fin.last (N+1))]
    exact HB y

end LeanCanny.Geometry.IntegralMixedFrozenFrame

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "ho"=>IntegralMixedRoadmapRetainedAppend.parent_room hn ht ha hR0 old hv hd E he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd E he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices"=>IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd
noncomputable local instance canonicalRetainedSweepIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.metadata IntegralMixedRoadmapChain.rawStart
  IntegralMixedRoadmapRetainedAppend.start IntegralMixedRoadmapChain.depth
  IntegralMixedRoadmapChain.prefixCount IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentTuple
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
  IntegralMixedFramedHistoryFamilyBits.initial IntegralMixedRoadmapProperParent.hom
  IntegralMixedRoadmapProperParent.choices IntegralMixedRoadmapRetainedAppend.parentState

/-- An actual accepted parent constructs the sweep including its prescribed
existing bank value. No new hom, cover, model or radius/budget premise is given. -/
theorem exists_canonical_retained_sweep (targetRef :Fin (cs).length):
    Nonempty (RetainedMatchedFiniteSweep x hm phi (d).frame h g hg V choices targetRef):=by
  have HRoom :(cs).length+2+((P).ambient c-(d).frame.frozen.card)≤(P).cap c+2:=by
    have HB:=canonical_level_horizon hn ht ha hR0 old hv hd
    rw [(d).frozen_card]
    omega
  have HProper :IsProperMap (fun y :Fin ((P).ambient c+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree).eval₂
        (Int.castRingHom ℝ) y):=
    regular_source_proper (BoundedRegularLowCoefficient.readers (IntegralMixedAuxiliaryMarkedIntegerSource.number n)
      (t∘IntegralMixedAuxiliaryMarkedIntegerSource.original) (radius R0)) c
  exact exists_retained_matched_finite_sweep x hm
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c)
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original c)).toData.size
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) c)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
    (d).frame (d).free_normal (d).atomic (d).prefix_frozen h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    (IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd E he)
    (IntegralMixedRoadmapRetainedAppend.parent_roots hn ht ha hR0 old hv hd E he)
    phi (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd)
    V (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) choices targetRef HRoom HProper

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
