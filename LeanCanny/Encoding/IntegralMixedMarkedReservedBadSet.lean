/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotBad
public import LeanCanny.Encoding.IntegralMixedMarkedReservedPoint
/-! # The actual canonical parent bad set is fixed by one full native word

Every older interpretation and every classical factor choice is constructed
internally from that word's literal prefix realization.  Different reserved
probes use their own full words; only the actual old bank quotients are
compared between them.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedMarkedPrefixRun (reservedRoot)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
 (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool)

noncomputable def snapshot :=IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0
 (reservedRoot old codes probe aux) codes.length (IntegralMixedMarkedReservedParent.codes_good old codes probe aux)

theorem canonical :Canonical (snapshot hn ht ha hR0 old codes probe aux).state:=
 IntegralMixedMarkedPrefixSnapshot.canonical hn ht ha hR0 _ _ _

theorem birth : (snapshot hn ht ha hR0 old codes probe aux).birth=
    number n (reservedRoot old codes probe aux)+8+codes.length:=
 IntegralMixedMarkedPrefixSnapshot.birth hn ht ha hR0 _ _ _

variable (w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w)

theorem realizes : IntegralMixedIntegerRealization.Realizes (snapshot hn ht ha hR0 old codes probe aux).state
    (IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv):=
 IntegralMixedMarkedPrefixSnapshot.realizes_at hn ht ha hR0 _ _ _ _
   (IntegralMixedMarkedReservedParent.prepared_realizes hn ht ha hR0 old codes probe aux w hv probe aux)

attribute [local irreducible] snapshot IntegralMixedMarkedReservedParent.bank

noncomputable def bad (labels : List Bool):Set ℝ:=
 (snapshot hn ht ha hR0 old codes probe aux).bad labels
   (IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv)

theorem exists_interpretation :
    ∃φ : (snapshot hn ht ha hR0 old codes probe aux).state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ ((snapshot hn ht ha hR0 old codes probe aux).state.bank.numerator i)/
        ((snapshot hn ht ha hR0 old codes probe aux).state.bank.denominator i:ℝ)=
          IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv i.val:=by
 obtain ⟨_,φ,_,_,Hφ⟩:=realizes hn ht ha hR0 old codes probe aux w hv
 exact ⟨φ,Hφ⟩

noncomputable def interpretation :=Classical.choose (exists_interpretation hn ht ha hR0 old codes probe aux w hv)

theorem interpretation_values :
    ∀i,interpretation hn ht ha hR0 old codes probe aux w hv
        ((snapshot hn ht ha hR0 old codes probe aux).state.bank.numerator i)/
      ((snapshot hn ht ha hR0 old codes probe aux).state.bank.denominator i:ℝ)=
        IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv i.val:=
 Classical.choose_spec (exists_interpretation hn ht ha hR0 old codes probe aux w hv)

variable (labels : List Bool) (hr : (snapshot hn ht ha hR0 old codes probe aux).Ready labels)

noncomputable def choices :Choices (snapshot hn ht ha hR0 old codes probe aux).state hr.1
    ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr)
    (interpretation hn ht ha hR0 old codes probe aux w hv):=
 Classical.choice (exists_choices _ _ _ _)

theorem mem_bad_iff_selected (a : ℝ) :
    a∈bad hn ht ha hR0 old codes probe aux w hv labels ↔
      a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad
        (snapshot hn ht ha hR0 old codes probe aux).state hr.1
        ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr)
        (interpretation hn ht ha hR0 old codes probe aux w hv)
        (choices hn ht ha hR0 old codes probe aux w hv labels hr):=
 IntegralMixedPrefixSnapshot.Data.mem_bad_iff _ _ _ hr (canonical hn ht ha hR0 old codes probe aux)
   _ (interpretation_values hn ht ha hR0 old codes probe aux w hv) _ a

theorem mem_bad_factor_iff (a : ℝ) :
    a∈bad hn ht ha hR0 old codes probe aux w hv labels ↔
      ∃k : Kind (snapshot hn ht ha hR0 old codes probe aux).source
          ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr),
        Valid (snapshot hn ht ha hR0 old codes probe aux).state hr.1
          ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr)
          (interpretation hn ht ha hR0 old codes probe aux w hv) k ∧
        IntegralMixedSelectedBadMembership.Ordinary ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr) k ∧
        (factor (snapshot hn ht ha hR0 old codes probe aux).state hr.1
          ((snapshot hn ht ha hR0 old codes probe aux).rule labels hr) k).eval₂
          (interpretation hn ht ha hR0 old codes probe aux w hv).toRingHom a=0:=
 IntegralMixedPrefixSnapshot.Data.mem_bad_factor_iff _ _ _ hr (canonical hn ht ha hR0 old codes probe aux)
   _ (interpretation_values hn ht ha hR0 old codes probe aux w hv) a

theorem snapshot_eq (nextProbe nextAux : List Bool) :
    snapshot hn ht ha hR0 old codes probe aux=snapshot hn ht ha hR0 old codes nextProbe nextAux:=by
 unfold snapshot
 exact IntegralMixedMarkedPrefixSnapshot.reserved_eq hn ht ha hR0 old codes probe nextProbe aux nextAux

theorem bad_eq_of_values (nextProbe nextAux nextWord : List Bool)
    (hv' : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (reservedRoot old codes nextProbe nextAux)) nextWord)
    (he : ∀i<(snapshot hn ht ha hR0 old codes probe aux).birth,
      IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv i=
        IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes nextProbe nextAux nextWord hv' i) :
    bad hn ht ha hR0 old codes probe aux w hv labels=
      bad hn ht ha hR0 old codes nextProbe nextAux nextWord hv' labels:=
 IntegralMixedPrefixSnapshot.Data.bad_transport _ _ (snapshot_eq hn ht ha hR0 old codes probe aux nextProbe nextAux)
   labels _ _ he

theorem bad_eq_of_parent_fields (nextProbe nextAux nextWord : List Bool)
    (hv' : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (reservedRoot old codes nextProbe nextAux)) nextWord)
    (he : ∀i<(snapshot hn ht ha hR0 old codes probe aux).birth,
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (reservedRoot old codes probe aux) w
        (IntegralMixedMarkedReservedPoint.native_valid hn ht ha hR0 old codes probe aux w hv) i=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (reservedRoot old codes nextProbe nextAux) nextWord
        (IntegralMixedMarkedReservedPoint.native_valid hn ht ha hR0 old codes nextProbe nextAux nextWord hv') i) :
    bad hn ht ha hR0 old codes probe aux w hv labels=
      bad hn ht ha hR0 old codes nextProbe nextAux nextWord hv' labels:=by
 apply bad_eq_of_values hn ht ha hR0 old codes probe aux w hv labels nextProbe nextAux nextWord hv'
 intro i hi
 exact (congrFun (IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0 old codes probe aux w hv) i).trans
   ((he i hi).trans (congrFun (IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0 old codes nextProbe nextAux nextWord hv') i).symm)

end LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
