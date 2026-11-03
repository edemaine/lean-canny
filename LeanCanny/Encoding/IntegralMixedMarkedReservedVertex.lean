/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
/-! # One base full word gives a fresh actual replacement-probe vertex

The raw table has the same chronological prefix and a literal typed last cut.
The old natural tuple supplies its parent realization.  The zero-padded cut
is sampled anew in the actual completed prepared-root sampler; no word or
ordinal is transferred between different roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedVertex
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedCausalRecordBits
open IntegralMixedMarkedPrefixRun (reservedRoot reserved_count)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "V"=>IntegralMixedMarkedReservedCutView.plan hn ht ha hR0

noncomputable def parent (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool):=
 keyAt (reservedRoot old codes probe aux) (number n (reservedRoot old codes probe aux)+8+codes.length) []

theorem parent_root (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    pairFst (parent (n:=n) old codes probe aux)=reservedRoot old codes probe aux:=by
 simp only [parent,keyAt,pairFst_pair]

theorem parent_prefix (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    prefixLength P (parent (n:=n) old codes probe aux)=number n (pairFst (parent (n:=n) old codes probe aux))+8+codes.length:=by
 rw [parent_root]
 exact keyAt_prefix P _ _ [] (IntegralMixedMarkedReservedParent.bound hn ht ha hR0 _ codes.length
   (IntegralMixedMarkedReservedParent.codes_good old codes probe aux))

attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
 IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedSourceIntegerRecordAppend.plan

variable (old : List Bool) (codes : List (List Bool)) (oldProbe oldAux probe aux : List Bool)
 (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes oldProbe oldAux)) w)
variable (d : IntegralMixedCutRecordConstructor.Data ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient (pairFst (parent (n:=n) old codes probe aux)))
 ((number n (pairFst (parent (n:=n) old codes probe aux))+8)+codes.length)) (tag : Tag) (choice degree : ℕ)
 (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient (pairFst (parent (n:=n) old codes probe aux))+1)
   (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 (pairFst (parent (n:=n) old codes probe aux))).degree)
 (hcode : probe=d.code tag choice degree)

include hcode in
theorem table_at_parent : IntegralMixedCausalRecordPlanBits.records (pairFst (parent (n:=n) old codes probe aux))=
    WordList.encode (codes++[d.code tag choice degree]):=by
 have HE:=congrArg IntegralMixedCausalRecordPlanBits.records (parent_root (n:=n) old codes probe aux)
 have HT : IntegralMixedCausalRecordPlanBits.records (reservedRoot old codes probe aux)=WordList.encode (codes++[probe]):=by
   simp only [reservedRoot,IntegralMixedCausalRecordPlanBits.records,pairFst_pair,pairSnd_pair]
 exact HE.trans (HT.trans (congrArg (fun q : List Bool=>WordList.encode (codes++[q])) hcode))

include hdegree hcode in
 theorem exists_vertex : ∃w',∃hw : SquareSampleCompleteVertices.Valid
    (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
    (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w',
    w'.length=SquareSampleCompleteVertices.width (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) ∧
    ∀i : Fin ((family P (B).plan (B).data).birth ((B).key
      (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)))),
      IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w' hw i=
      IntegralFramedPaddedCutVertex.values (IntegralMixedMarkedReservedParent.values hn ht ha hR0
        old codes oldProbe oldAux w hv) i.val:=by
 let c:=IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)
 let v:=IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes oldProbe oldAux w hv
 have HT:=table_at_parent hn ht ha hR0 old codes probe aux d tag choice degree hcode
 have HK:=parent_prefix hn ht ha hR0 old codes probe aux
 have HR : pairFst ((B).key c)=pairFst (parent (n:=n) old codes probe aux):=by
   rw [IntegralMixedMarkedReservedParent.key_root,parent_root]
 have HL:=IntegralMixedSourceIntegerLastCode.rules_length_last P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.room hn ht ha hR0) (pairFst (parent (n:=n) old codes probe aux)) codes (d.code tag choice degree) HT
 change ((V).rules (pairFst (parent (n:=n) old codes probe aux))).length=
   number n (pairFst (parent (n:=n) old codes probe aux))+8+codes.length+1 at HL
 have HC : prefixLength P ((B).key c)=((V).rules (pairFst (parent (n:=n) old codes probe aux))).length:=by
   rw [IntegralMixedMarkedReservedParent.full_prefix,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,
     reserved_count,HL,parent_root]
   omega
 have HV:=IntegralMixedMarkedReservedCutView.state_realizes hn ht ha hR0 (parent (n:=n) old codes probe aux) v
   (IntegralMixedMarkedReservedParent.prepared_canonical_realizes hn ht ha hR0 old codes oldProbe oldAux w hv probe aux [])
 have HW:=IntegralMixedReservedCutActualVertex.run_realizes P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) (parent (n:=n) old codes probe aux) codes d tag choice degree hdegree HT HK
   (IntegralMixedMarkedReservedCutView.strict_margin hn ht ha hR0 (pairFst (parent (n:=n) old codes probe aux))) v HV
 have HF:=IntegralMixedMarkedReservedCutView.full_realizes hn ht ha hR0
   (pairFst (parent (n:=n) old codes probe aux)) (IntegralFramedPaddedCutVertex.values v) HW
 have HC' : prefixLength P ((B).key c)=((B).plan.rules (pairFst (parent (n:=n) old codes probe aux))).length:=
   HC.trans (congrArg (fun D : Plan P=>(D.rules (pairFst (parent (n:=n) old codes probe aux))).length)
     (IntegralMixedMarkedReservedCutView.plan_eq hn ht ha hR0))
 exact IntegralMixedReservedCutActualVertex.vertex_from_full_run P (B).plan (B).data
   (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c
   (pairFst (parent (n:=n) old codes probe aux)) HR HC' _ HF

end LeanCanny.Encoding.IntegralMixedMarkedReservedVertex
