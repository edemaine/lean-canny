/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapPointGlue
public import LeanCanny.Geometry.IntegralMixedFrozenFrameTerminal
public import LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource

/-! # Terminal original-source frozen fibers glue by native identity -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralCriticalHistoryTask Set
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem finite_reference_fiber {dim sched bits born :ℕ} {Q :SpatialSource dim}
    {ι :Type} (x :State Q sched bits born ι) (hm :born≤sched)
    (phi :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin born→ℝ)
    (HV :∀i,phi (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (refs :Fin dim→Fin born) (levels :ℕ→ℝ) (HL :∀i,values (refs i)=levels i.val) :
    Set.Finite {y :Fin (dim+1)→ℝ |
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (dim+1),i.val<dim→y i=levels i.val}:=by
  let frame :Frame dim:={
    frozen:=Finset.univ.filter (fun i=>i.val<dim)
    scales:=fun _=>1
    scales_ne_zero:=fun _=>by norm_num
    heights:=fun i=>if hi :i.val<dim then .reference (refs ⟨i.val,hi⟩).val else .constant 0 }
  have HH :Fin.last dim∉frame.frozen:=by simp [frame]
  have HF (i :Fin (dim+1)) (hi :i≠Fin.last dim) :i∈frame.frozen:=by
    have HE :i.val≠dim:=by intro h;apply hi;exact Fin.ext h
    simp only [frame,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  let :Finite (slice Q frame values):=(last_free_finite_card x hm phi frame (Fin.last dim) HH HF values HV).1
  apply (Set.toFinite (slice Q frame values)).subset
  intro y hy
  refine ⟨hy.1,?_⟩
  intro i hi
  have HI :i.val<dim:=by simpa only [frame,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have HE :(frame.heights i).evaluate values=values (refs ⟨i.val,HI⟩):=by
    simp only [frame,dite_eq_left HI,AffineExpr.evaluate,dite_eq_left (refs ⟨i.val,HI⟩).isLt]
  have HS :(frame.scales i:ℝ)=1:=by simp only [frame,Int.cast_one]
  rw [HS,one_mul,HE]
  exact (hy.2 i HI).trans (HL ⟨i.val,HI⟩).symm

private theorem finite_fiber_source_transport {a b :ℕ} (Q :SpatialSource a) (P :SpatialSource b)
    (HD :a=b) (HS :HEq Q P) (levels :ℕ→ℝ)
    (HF :Set.Finite {y :Fin (a+1)→ℝ |
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (a+1),i.val<a→y i=levels i.val}) :
    Set.Finite {y :Fin (b+1)→ℝ |
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (b+1),i.val<b→y i=levels i.val}:=by
  cases HD
  have HE :Q=P:=eq_of_heq HS
  cases HE
  exact HF

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.root
  IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.point

private theorem terminal_label_bound (c a :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a) (hc :IntegralMixedRoadmapAtomic.candidate a=c)
    (hterminal :IntegralMixedRoadmapAtomic.depth a=n (pairFst c)+3)
    (i :Fin ((P).ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context a))))) :
    Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen a) i.val)<
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (IntegralMixedRoadmapAtomic.context a)):=by
  have HD:=ambient_eq hn ht ha hR0 c a hc
  have HI :i.val<WordListRecords.count (IntegralMixedRoadmapAtomic.frozen a):=by
    rw [IntegralMixedRoadmapAtomic.frozen_count]
    have :=i.isLt
    omega
  have HB:=(IntegralMixedRoadmapAtomic.own_frame_good hn ht ha hR0 a hA).2 i.val HI
  have HA:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context a) (IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 a)
    (IntegralMixedRoadmapAtomic.own_active hn ht ha hR0 a hA)).1
  change IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 a<_ at HA
  change Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen a) i.val)<
    IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 a at HB
  exact HB.trans HA

/-- Acceptance supplies the exact bank references and an interpretation of
the actual full state. The terminal original frozen slice is finite. -/
theorem terminal_frozenSlice_finite (c a :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a) (hc :IntegralMixedRoadmapAtomic.candidate a=c)
    (hterminal :IntegralMixedRoadmapAtomic.depth a=n (pairFst c)+3) :
    Set.Finite (frozenSlice (n:=n) (t:=t) (R0:=R0) c (n (pairFst c)+3)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA)):=by
  let ctx:=IntegralMixedRoadmapAtomic.context a
  let key:=(B).key ctx
  let word:=IntegralMixedRoadmapAtomic.word a
  have hw:=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA
  let values:=IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed
    (B).bounds (B).key (B).positive ctx word hw
  have HInterpret:=IntegralFramedPhysicalSquare.exists_interpretation P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive ctx word hw
  let phi:=HInterpret.choose
  have HV:=HInterpret.choose_spec.2
  let refs :Fin ((P).ambient (pairFst key))→Fin ((G).birth key):=fun i=>
    ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P key-1-
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen a) i.val),by
        rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
        have HL:=terminal_label_bound hn ht ha hR0 c a hA hc hterminal i
        change Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen a) i.val)<
          IntegralMixedFramedHistoryFamilyBits.prefixLength P key at HL
        omega⟩
  have HL (i :Fin ((P).ambient (pairFst key))) :
      values (refs i)=IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA i.val:=by
    have H:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) ctx word hw
      (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen a) i.val))
      (terminal_label_bound hn ht ha hR0 c a hA hc hterminal i)
    simpa only [IntegralMixedRoadmapAtomic.levels,values,refs,ctx,word] using H.symm
  have HF:=finite_reference_fiber ((G).state key) ((G).birth_bound key)
    phi values HV refs (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA) HL
  have HD:=ambient_eq hn ht ha hR0 c a hc
  have HS:=IntegralMixedPhysicalOriginalSource.family_source hn ht ha hR0 false key
  have HO :IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst key)=pairFst c:=by
    rw [IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 a]
    simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      IntegralMixedRoadmapAtomic.root,pairFst_pair] using congrArg pairFst hc
  rw [HO] at HS
  exact finite_fiber_source_transport ((G).spatial key) (originalSource (n:=n) (t:=t) (R0:=R0) c)
    HD HS (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA) HF

/-- A path in the terminal fiber identifies the entire original-source
point. Only the first accepted vertex must have terminal depth. -/
theorem terminal_pointAt_eq (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (hterminal :IntegralMixedRoadmapAtomic.depth a=n (pairFst c)+3)
    (HP :JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) c (n (pairFst c)+3)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA))
        (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd)) :
    pointAt hn ht ha hR0 c a hA hc=pointAt hn ht ha hR0 c b hB hd:=by
  let fiber:=frozenSlice (n:=n) (t:=t) (R0:=R0) c (n (pairFst c)+3)
    (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA)
  have HF:=terminal_frozenSlice_finite hn ht ha hR0 c a hA hc hterminal
  let :Finite fiber:=HF.to_subtype
  let :TotallyDisconnectedSpace fiber:=inferInstance
  have HE :(⟨pointAt hn ht ha hR0 c a hA hc,HP.source_mem⟩ :fiber)=
      ⟨pointAt hn ht ha hR0 c b hB hd,HP.target_mem⟩:=
    isPreconnected_connectedComponent.subsingleton mem_connectedComponent
      (pathComponent_subset_component _ HP.joined_subtype)
  exact congrArg Subtype.val HE

/-- The terminal geometric fiber simulation lands in the actual native
identity language and in the fixed-candidate raw graph. -/
theorem terminal_fiber_glue (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (hterminal :IntegralMixedRoadmapAtomic.depth a=n (pairFst c)+3)
    (HP :JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) c (n (pairFst c)+3)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA))
        (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd)) :
    pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0 ∧RawReachable hn ht ha hR0 c a b:=by
  have HE:=terminal_pointAt_eq hn ht ha hR0 c a b hA hB hc hd hterminal HP
  exact ⟨(identity_language_iff_pointAt_eq hn ht ha hR0 c a b hA hB hc hd).mpr HE,
    raw_reachable_of_pointAt_eq hn ht ha hR0 c a b hA hB hc hd HE⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
