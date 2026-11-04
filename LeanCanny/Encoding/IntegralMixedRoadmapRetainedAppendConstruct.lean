/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendWord
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendAcceptance
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPoint
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendFieldScalar
public import LeanCanny.Connectivity.IntegralMixedRoadmapRetainedAppendSeed
/-! # A geometric retained child gives a fresh accepted atomic vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def JointNatural (K :IntegralFramedBankQuery.Bank) (c w :List Bool) (u :ℕ→ℝ):Prop:=
  ∀hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w,
  ∀i :Fin (IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c)),
    IntegralFramedPhysicalSquare.joint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hw i=u i.val

private theorem natural_of_joint (K :IntegralFramedBankQuery.Bank) (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (u :ℕ→ℝ) (H :JointNatural K c w u) (i :ℕ)
    (hi :i<IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c)):
    IntegralFramedPhysicalSquare.naturalPoint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hw i=u i:=
  (IntegralFramedPhysicalSquare.naturalPoint_at K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
    K.key K.positive c w hw ⟨i,hi⟩).trans (H hw ⟨i,hi⟩)

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "DIM"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (e :ℕ)
  (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "localCs"=>localInstructions hn ht ha hR0 old hv hd e he
local notation "CTX"=>context hn ht ha hR0 old e

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot parentCommands localInstructions
  IntegralMixedMarkedPrefixFieldReadback.fullObservation


private theorem parent_arity_le_full :arity older≤
    (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).arity:=by
  unfold IntegralMixedMarkedPrefixFieldReadback.fullObservation
  change arity older≤arity ((PLAN).rules r)
  have HL:=local_arity hn ht ha hR0 old hv hd e he
  have HA :arity older≤arity localCs:=by omega
  have HB :arity localCs≤arity ((PLAN).rules r):=by
    rw [full_local_commands hn ht ha hR0 old hv hd e he]
    exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _
  exact HA.trans HB


theorem receipt_raw_retention (p p0 :Fin ((P).ambient r+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd e he p p0):
    ∀i,i<arity older→IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid i=
      oldNatural hn ht ha hR0 old hv i:=by
  have HReserved :JointNatural BP CTX W.word W.tuple:=by
    intro hw i
    exact W.joint i
  have HE :B=BP:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
    rfl
  have HNative :JointNatural B CTX W.word W.tuple:=
    (congrArg (fun K=>JointNatural K CTX W.word W.tuple) HE).mpr HReserved
  have HC :IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key CTX)=
      (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).arity:=by
    exact congrArg IntegralMixedFramedRunObservation.Data.arity
      (IntegralMixedMarkedPrefixFieldReadback.terminal_bank_data hn ht ha hR0 r)
  intro i hi
  have HFull :i<IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key CTX):=by
    rw [HC]
    exact hi.trans_le (parent_arity_le_full hn ht ha hR0 old hv hd e he)
  have HN:=natural_of_joint B CTX W.word W.valid W.tuple HNative i HFull
  have HLocal :i<arity localCs:=by
    have HL:=local_arity hn ht ha hR0 old hv hd e he
    omega
  exact HN.trans ((W.preserved i HLocal).trans (W.old_raw i hi))

theorem receipt_word_bound (p p0 :Fin ((P).ambient r+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd e he p p0):
    W.word.length≤IntegralMixedRoadmapAtomic.wordBudget hn ht ha hR0 (packet (DIM old) old e W.word):=by
  have HW :SquareSampleCompleteVertices.Valid S
      (IntegralMixedRoadmapAtomic.context (packet (DIM old) old e W.word)) W.word:=
    Eq.mpr (congrArg (fun c=>SquareSampleCompleteVertices.Valid S c W.word)
      (packet_context hn ht ha hR0 old e W.word)) W.valid
  have HG:=grammar hn ht ha hR0 old hv hd e he W.word HW
  simpa only [word_packet] using HG.2.2

local notation "d"=>parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "F"=>IntegralMixedChronologicalMidpoint.frame d hk a a
local notation "g"=>midpointObjective hn ht ha hR0 old hv hd e he

/-- A prescribed critical point in the retained child slice is accepted at
its own new complete word. Padding roots and every native guard are derived. -/
theorem exists_valid_at (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈IntegralMixedFrozenFrame.slice (Q r) (d).frame
      (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))
    (hg :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃w,∃hNew :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet (DIM old) old e w),
      w.length=SquareSampleCompleteVertices.width S CTX ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 (packet (DIM old) old e w) hNew) p:=by
  obtain ⟨p0,hp0,hg0⟩:=exists_padding_critical hn ht ha hR0 old hv e
  have HG0 :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p0=0:=by
    intro i hi
    apply hg0 i
    intro HE
    exact hi (Fin.ext HE)
  obtain ⟨W⟩:=exists_word_receipt hn ht ha hR0 old hv hd e he p hp hheight hg p0 hp0 HG0
  have HR :FreshReadback hn ht ha hR0 old e W.word W.valid
      (nativePoint hn ht ha hR0 old e p) (nativePoint hn ht ha hR0 old e p0):=
    ⟨physical_of_word_receipt hn ht ha hR0 old hv hd e he p p0 W,
      scalar_of_word_receipt hn ht ha hR0 old hv hd e he p p0 W⟩
  have HNew:=valid_of_retained_readback hn ht ha hR0 old hv hd e he W.word W.valid
    (nativePoint hn ht ha hR0 old e p) (nativePoint hn ht ha hR0 old e p0) HR
    (receipt_raw_retention hn ht ha hR0 old hv hd e he p p0 W)
  refine ⟨W.word,HNew,W.word_length,?_⟩
  exact (point_of_fresh_readback hn ht ha hR0 old hv hd e he W.word W.valid
    (nativePoint hn ht ha hR0 old e p) (nativePoint hn ht ha hR0 old e p0) HR HNew).trans
      (nativePoint_heq hn ht ha hR0 old e p)

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
