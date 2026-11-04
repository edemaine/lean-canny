/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedVertex
public import LeanCanny.Encoding.IntegralMixedMarkedReservedPoint
/-! # A freshly sampled zero probe preserves every old native parent field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedFieldVertex
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedCausalRecordBits
open IntegralMixedMarkedPrefixRun (reservedRoot)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def Observed (B : IntegralFramedBankQuery.Bank) (c : List Bool) (values : ℕ→ℝ) :Prop:=
 ∃w,∃hv:SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w,
 ∀i:Fin ((family B.parameters B.plan B.data).birth (B.key c)),
   IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv i=values i.val

private theorem observed_of_width (B : IntegralFramedBankQuery.Bank) (c : List Bool) (values : ℕ→ℝ)
    (h : ∃w,∃hv:SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w,
      w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input B) c ∧
      ∀i:Fin ((family B.parameters B.plan B.data).birth (B.key c)),
        IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv i=values i.val) :
    Observed B c values:=by
 obtain ⟨w,hv,_,hp⟩:=h
 exact ⟨w,hv,hp⟩

private theorem padded_succ (v : ℕ→ℝ) (i : ℕ) :IntegralFramedPaddedCutVertex.values v (i+1)=v i:=by
 simp only [IntegralFramedPaddedCutVertex.values,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]

private theorem point_clamp (A : Parameters) (E : Plan A) (J : IntegralMixedFramedHistoryFamilyBits.Data A E)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs A E L F C)
    (key : List Bool→List Bool) (hp : ∀c,0<(family A E J).birth (key c))
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input A E J L F C hs key hp) c w)
    (i : Fin ((family A E J).birth (key c))) :
    IntegralFramedPhysicalSquare.point A E J L F C hs key hp c w hv
      ⟨min i.val ((family A E J).birth (key c)-1),by have:=i.isLt;omega⟩=
    IntegralFramedPhysicalSquare.point A E J L F C hs key hp c w hv i:=by
 apply congrArg _
 apply Fin.ext
 exact min_eq_left (by have:=i.isLt;omega)

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "M"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
private theorem banks_equal : (B)=(M):=rfl
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank IntegralMixedPhysicalMarkedPlan.bank
 IntegralFramedPhysicalSquare.point IntegralFramedPhysicalSquare.input
 IntegralMixedFramedHistoryFamilyBits.family
private theorem newest_eq_point (c v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) c v)
    (i : Fin (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) c)) :
    IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0) c v hv i.val=
      IntegralFramedPhysicalSquare.point (M).parameters (M).plan (M).data (M).nodes (M).factor (M).seed (M).bounds
        (M).key (M).positive c v hv i:=by
 unfold IntegralMixedPhysicalFieldEquality.pointNewest
 exact point_clamp (M).parameters (M).plan (M).data (M).nodes (M).factor (M).seed (M).bounds
   (M).key (M).positive c v hv i

variable (old : List Bool) (codes : List (List Bool)) (oldProbe oldAux probe aux w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes oldProbe oldAux)) w)
 (d : IntegralMixedCutRecordConstructor.Data
   ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient
     (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux)))
   (number n (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))+8+codes.length))
 (tag : Tag) (choice degree : ℕ)
 (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap
   ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient
     (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))+1)
   (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0
     (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))).degree)
 (hcode : probe=d.code tag choice degree)

include hdegree hcode in
theorem exists_parent_fields :∃w',∃hv':SquareSampleCompleteVertices.Valid
    (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
    (IntegralMixedMarkedPrefixFieldReadback.context (reservedRoot old codes probe aux)) w',
    ∀i<number n (reservedRoot old codes probe aux)+8+codes.length,
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (reservedRoot old codes probe aux) w' hv' i=
        IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes oldProbe oldAux w hv i:=by
 let c:=IntegralMixedMarkedPrefixFieldReadback.context (reservedRoot old codes probe aux)
 let v:=IntegralFramedPaddedCutVertex.values
   (IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes oldProbe oldAux w hv)
 have H0 :Observed B c v:=observed_of_width B c v
   (IntegralMixedMarkedReservedVertex.exists_vertex hn ht ha hR0
     old codes oldProbe oldAux probe aux w hv d tag choice degree hdegree hcode)
 have H1 :Observed M c v:=(congrArg (fun bankData=>Observed bankData c v) (banks_equal hn ht ha hR0)).mp H0
 obtain ⟨w',hv',HP⟩:=H1
 refine ⟨w',hv',?_⟩
 have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) c=
     number n (reservedRoot old codes probe aux)+8+codes.length+1:=by
   rw [IntegralMixedPhysicalFieldEquality.count_eq]
   simp only [c,IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair,
     IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,IntegralMixedMarkedPrefixRun.reserved_count]
   omega
 intro i hi
 have HI :i<IntegralMixedMarkedPrefixFieldReadback.parent n (reservedRoot old codes probe aux):=by
   unfold IntegralMixedMarkedPrefixFieldReadback.parent
   rw [IntegralMixedMarkedPrefixRun.reserved_count]
   omega
 have HE:=IntegralMixedMarkedPrefixFieldReadback.parent_value hn ht ha hR0 (reservedRoot old codes probe aux) w' hv'
   (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega) i HI
 have HJ :i+1<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) c:=by rw [HC];omega
 have HV :IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0) c w' hv' (i+1)=v (i+1):=
   (newest_eq_point hn ht ha hR0 c w' hv' ⟨i+1,HJ⟩).trans (HP ⟨i+1,HJ⟩)
 exact HE.trans (HV.trans (padded_succ _ i))

end LeanCanny.Encoding.IntegralMixedMarkedReservedFieldVertex
