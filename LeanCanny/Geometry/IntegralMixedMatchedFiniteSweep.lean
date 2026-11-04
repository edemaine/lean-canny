/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedSlabEndpointPaths
public import LeanCanny.Geometry.IntegralMixedJointSlabEndpointSet
/-! # A finite sweep retaining the actual matched family in every closed slab -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open IntegralMixedOptionalEndpoints IntegralMixedFullHistoryScript
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type}

noncomputable def consecutiveMidpoint {N :ℕ} (cut :ℕ→ℝ)
    (hs :StrictMono (fun i :Fin (N+2)=>cut i.val)) (i :Fin (N+1)) :
    Ioo (cut i.val) (cut (i.val+1)):=
  ⟨(cut i.val+cut (i.val+1))/2,by
    have H:=hs (Fin.castSucc_lt_succ (i:=i))
    change cut i.val<cut (i.val+1) at H
    constructor <;> linarith⟩

structure MatchedFiniteSweep (x :State P S B m ι) (hm :m≤S)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F :Frame n)
    (h g :Fin (n+1)) (hg :g∉(line F h).frozen) (values :Fin m→ℝ)
    (choices :IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ) where
  slabs :ℕ
  cut :ℕ→ℝ
  strict :StrictMono (fun i :Fin (slabs+2)=>cut i.val)
  includes_bad :∀t∈sweepBadReal x hm φ F h g hg values choices,∃j :Fin (slabs+2),cut j.val=t
  range_bound :∀y :slice P (coarse (line F h) h) values,
    coarseProjection P (line F h) values h y∈Icc (cut 0) (cut (slabs+1))
  gap :∀i :Fin (slabs+1),∀t∈Ioo (cut i.val) (cut (i.val+1)),
    t∉sweepBadReal x hm φ F h g hg values choices
  origin :∀j :Fin (slabs+2),cut j.val∈sweepBadReal x hm φ F h g hg values choices ∨
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

namespace MatchedFiniteSweep
variable {x :State P S B m ι} {hm :m≤S} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
  {F :Frame n} {h g :Fin (n+1)} {hg :g∉(line F h).frozen} {values :Fin m→ℝ}
  {choices :IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ}
  (W :MatchedFiniteSweep x hm φ F h g hg values choices)

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

end MatchedFiniteSweep

/-- Endpoint covers are an internal intermediate here. The full parent factory
below constructs them from actual optional endpoint births. -/
theorem exists_matched_finite_sweep_from_endpoint_covers (x :State P S B m ι) (hm :m≤S)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F :Frame n) (h :Fin (n+1))
    (g :Fin (n+1)) (hg :g∉(line F h).frozen) (values :Fin m→ℝ)
    (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (choices :IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp :IsProperMap (fun y :Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (ends :∀a∈sweepBadReal x hm φ F h g hg values choices,
      ∃I :Type,Finite I∧Nonempty (ClopenPathCover
        ((coarseProjection P (line F h) values h) ⁻¹' {a}) I)) :
    Nonempty (MatchedFiniteSweep x hm φ F h g hg values choices):=by
  let p:=coarseProjection P (line F h) values h
  let :CompactSpace (slice P (coarse (line F h) h) values):=
    isCompact_iff_compactSpace.mp (coarse_compact P (line F h) values h hp)
  obtain ⟨N,cut,HM,HC,HB,HA,HO⟩:=FiniteCriticalSweepOrigins.exists_cuts p
    (coarseProjection_continuous P (line F h) values h) _
    (sweepBadReal_finite x hm φ F h g hg values H choices)
  let seq :ℕ→ℝ:=fun j=>cut ⟨min j (N+1),by omega⟩
  have Hread (j :Fin (N+2)) :seq j.val=cut j:=by
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
  have Hends (j :Fin (N+2)) :∃I :Type,Finite I∧Nonempty (ClopenPathCover (p ⁻¹' {seq j.val}) I):=by
    rw [Hread j]
    rcases HO j with Hbad|Hempty
    · exact ends _ Hbad
    · let :IsEmpty (p ⁻¹' {cut j}):=⟨fun y=>(Set.ext_iff.mp Hempty y.val).mp y.property⟩
      exact ⟨Unit,inferInstance,⟨emptyCover _⟩⟩
  choose E HE CE using Hends
  let EC (j :Fin (N+2)):ClopenPathCover (p ⁻¹' {seq j.val}) (E j):=(CE j).some
  have Hgap (i :Fin (N+1)) :∀t∈Ioo (seq i.val) (seq (i.val+1)),
      t∉sweepBadReal x hm φ F h g hg values choices:=by
    change ∀t∈Ioo (seq i.castSucc.val) (seq i.succ.val),_
    rw [Hread i.castSucc,Hread i.succ]
    exact HA i
  have HMexists (i :Fin (N+1)) :Nonempty (MatchedSlabInterior x hm φ (line F h) h
      (Finset.mem_insert_self _ _) g hg values (seq i.val) (seq (i.val+1))
      (consecutiveMidpoint seq HS i)):=by
    exact exists_matched_slab_interior x hm φ (line F h) h (Finset.mem_insert_self _ _) g hg values H choices
      (seq i.val) (seq (i.val+1)) (consecutiveMidpoint seq HS i)
      (fun t ht htbad=>Hgap i t ht (Or.inl htbad))
      (fun t ht htbad=>Hgap i t ht (Or.inr htbad)) hp
  let M (i :Fin (N+1)):=(HMexists i).some
  have Hselect (i :Fin (N+1)):=ComponentSlabCover.exists_selection
    (M i).interior (EC i.castSucc) (EC i.succ)
  choose leftOf rightOf Hselected using Hselect
  refine ⟨{
    slabs:=N
    cut:=seq
    strict:=HS
    includes_bad:=?_
    range_bound:=?_
    gap:=Hgap
    origin:=?_
    endpointIndex:=E
    finite_endpoint:=HE
    endpointCover:=EC
    matched:=M
    leftOf:=leftOf
    rightOf:=rightOf
    selected:=Hselected}⟩
  · intro t ht
    obtain ⟨j,Hj⟩:=HC t ht
    exact ⟨j,(Hread j).trans Hj⟩
  · intro y
    change p y∈Icc (seq (0:Fin (N+2)).val) (seq (Fin.last (N+1)).val)
    rw [Hread 0,Hread (Fin.last (N+1))]
    exact HB y
  · intro j
    rw [Hread j]
    exact HO j


noncomputable def reframeInputChoices {Q :SpatialSource n} (x :State P S B m ι) (hm :m≤S)
    (hc :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (hQ :Q=P)
    (r :Rule n) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old :IntegralMixedRelativeCuts.Choices x hm r φ) :
    IntegralMixedRelativeCuts.Choices (reframe x Q hc) hm r φ:=by
  subst Q
  cases x
  exact old

private theorem reframeInputChoices_cancel {Q :SpatialSource n} (x :State P S B m ι) (hm :m≤S)
    (hc :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (hQ :Q=P)
    (r :Rule n) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old :IntegralMixedRelativeCuts.Choices x hm r φ) :
    IntegralMixedCutSourceCast.choices x hm hc hQ r φ (reframeInputChoices x hm hc hQ r φ old)=old:=by
  subst Q
  cases x
  rfl

/-- Transport the supplied choices, rather than choosing new factor data. -/
noncomputable def prefixInputChoices (x :State P S B m ι) (hm :m≤S)
    (F :Frame n) (h g :Fin (n+1)) (hg :g∉(line F h).frozen)
    (HP :PrefixFrozen (line F h)) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) :
    IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ:=
  reframeInputChoices (Q:=IntegralMixedCoordinateRename.spatial P
    (FrozenCoordinateOrdering.permutation (line F h).frozen)) x hm x.critical_cap (HP.spatial P) _ φ old

theorem prefixInputChoices_badset (x :State P S B m ι) (hm :m≤S)
    (F :Frame n) (h g :Fin (n+1)) (hg :g∉(line F h).frozen)
    (HP :PrefixFrozen (line F h)) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values :Fin m→ℝ) (old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) :
    sweepBadReal x hm φ F h g hg values (prefixInputChoices x hm F h g hg HP φ old)=
      jointEndpointSet x hm φ F h g hg values old:=by
  rw [HP.sweepBadReal_eq]
  unfold prefixInputChoices
  rw [reframeInputChoices_cancel]

/-- All endpoint covers and all matched closed-slab covers come from this
honest full parent and its exact supplied cut choices. -/
theorem exists_matched_finite_sweep [Fintype ι] (x :State P S B m ι) (hm :m≤S)
    (hn :0<n) (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F :Frame n) (HF :FreeNormal F) (HA :AtomicRows F m) (HP :PrefixFrozen F)
    (h :Fin (n+1)) (hh :h∉F.frozen) (hfirst :h.val=F.frozen.card)
    (g :Fin (n+1)) (hg :g∉(line F h).frozen)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old :IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (room :m+2+(n-F.frozen.card)≤S+1)
    (hp :IsProperMap (fun y :Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∃HPline :PrefixFrozen (line F h),
      Nonempty (MatchedFiniteSweep x hm φ F h g hg values
        (prefixInputChoices x hm F h g hg HPline φ old)):=by
  have hcard :F.frozen.card<n+1:=by rw [←hfirst];exact h.isLt
  have hfree :firstFree F hcard=h:=Fin.ext hfirst.symm
  have HPline :PrefixFrozen (line F h):=by
    have HL:=HP.line_first hcard
    rwa [hfree] at HL
  refine ⟨HPline,?_⟩
  apply exists_matched_finite_sweep_from_endpoint_covers x hm φ F h g hg values H
    (prefixInputChoices x hm F h g hg HPline φ old) hp
  intro a ha
  have HAset :a∈jointEndpointSet x hm φ F h g hg values old:=by
    rwa [prefixInputChoices_badset] at ha
  obtain ⟨R,HR⟩:=realize_pair x hm (by omega) hn charge hdegree hcap F HF HA HP h hh g hg
    z hz φ hφ values H old (.fresh a) (.fresh a) HAset HAset
  have Hlen :R.commands.length=2:=by simpa only [Endpoint.freshCount] using HR
  have Hroom :m+R.commands.length+(n-F.frozen.card)≤S+1:=by omega
  exact R.exists_endpoint_cover h hh hfirst HF charge hdegree hp Hroom false

end LeanCanny.Geometry.IntegralMixedFrozenFrame
