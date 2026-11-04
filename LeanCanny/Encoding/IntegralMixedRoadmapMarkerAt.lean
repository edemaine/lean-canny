/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
public import LeanCanny.Encoding.IntegralMixedRoadmapIdentityReadback
/-! # Native terminal markers compare the entire point to its marked prelude -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapMarkerAt
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def initialSignature (d :ℕ):=WordList.encode ((List.range (d+1)).map BinaryNatCode.encode)
theorem initialSignature_FP {d :List Bool→ℕ} (hd :UnaryFn d):
    (fun q=>initialSignature (d q))∈FP:=by
  apply mem_FP_of_eq (flatMap_range_mem_FP
    (mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP (constFn_mem_FP []))
    ((hd.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [initialSignature,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    pairSnd_pair,List.length_replicate]

theorem initialSignature_lookup (d :ℕ) (i :Fin (d+1)):
    WordList.get (initialSignature d) i.val=BinaryNatCode.encode i.val:=by
  simp only [initialSignature,WordList.get_encode,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry
  IntegralMixedRoadmapChain.frozen

noncomputable def table (q :List Bool):=IntegralMixedPhysicalPointSignatureComparison.pairs (D q)
  (IntegralMixedRoadmapIdentity.ownSignature hn ht ha hR0 q) (initialSignature (D q))
noncomputable def query (q :List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
  (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) (table hn ht ha hR0 q)

theorem table_FP :table hn ht ha hR0∈FP:=IntegralMixedPhysicalPointSignatureComparison.pairs_FP
  (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)
  (IntegralMixedRoadmapAtomic.native_signature hn ht ha hR0)
  (initialSignature_FP (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0))
theorem query_FP :query hn ht ha hR0∈FP:=mem_FP_pair
  (mem_FP_pair IntegralMixedRoadmapAtomic.context_FP IntegralMixedRoadmapAtomic.word_FP)
  (mem_FP_pair (mem_FP_pair IntegralMixedRoadmapAtomic.context_FP IntegralMixedRoadmapAtomic.word_FP)
    (table_FP hn ht ha hR0))

noncomputable def language :Language:={q|IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q ∧
  IntegralMixedRoadmapAtomic.depth q=D q ∧ IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q ∧
  query hn ht ha hR0 q∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)}

theorem decider :SpaceDecider (language hn ht ha hR0):=by
  have EV:=IntegralMixedRoadmapAtomic.evaluator hn ht ha hR0
  have ET:=SpaceFunction.ofFP _ ((BinaryFn.ofUnary IntegralMixedRoadmapAtomic.depth_unary).eq
    (BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0))).flag_mem_FP
  have ER:=(IntegralMixedRoadmapMarkedPrelude.decider hn ht ha hR0).flagEvaluator
  have EQ:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose _
    (query_FP hn ht ha hR0)).flagEvaluator
  apply (EV.andFlags (ET.andFlags (ER.andFlags EQ))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,IntegralMixedRoadmapMarkedPrelude.language,Set.mem_ofPred_eq,Set.mem_preimage,
    List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE :language hn ht ha hR0∈PSPACE:=(decider hn ht ha hR0).mem_PSPACE

noncomputable def target (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    Fin (D q+1)→ℝ:=fun i=>IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 q hv i.val

theorem prelude_bound (q :List Bool) (i :Fin (D q+1)):
    i.val<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q):=by
  have HC:=IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root q)
  simp only [IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,Bool.false_eq_true,ite_false] at HC
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8≤
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q) at HC
  have HD:=IntegralMixedRoadmapMarkedPrelude.point_dimension hn ht ha hR0 q
  have HI:=i.isLt
  omega

theorem table_count (q :List Bool):WordListRecords.count (table hn ht ha hR0 q)=D q+1:=
  IntegralMixedPhysicalPointSignatureComparison.pairs_count _ _ _
theorem table_lookup (q :List Bool) (i :Fin (D q+1)):
    WordList.get (table hn ht ha hR0 q) i.val=
      pair (WordList.get (IntegralMixedRoadmapIdentity.ownSignature hn ht ha hR0 q) i.val)
        (BinaryNatCode.encode i.val):=by
  unfold table
  rw [IntegralMixedPhysicalPointSignatureComparison.pairs_lookup,initialSignature_lookup]

attribute [local irreducible] IntegralMixedPhysicalFieldEquality.count IntegralMixedPhysicalFieldEquality.point
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapIdentity.point
  IntegralMixedRoadmapMarkedPrelude.value table query target

theorem query_iff (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    query hn ht ha hR0 q∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ↔
      IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv=target hn ht ha hR0 q hv:=by
  have HB:∀i<WordListRecords.count (table hn ht ha hR0 q),
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (table hn ht ha hR0 q) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q) ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (table hn ht ha hR0 q) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q):=by
    intro i hi
    rw [table_count] at hi
    rw [table_lookup hn ht ha hR0 q ⟨i,hi⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact ⟨IntegralMixedRoadmapIdentity.signature_bound hn ht ha hR0 q hv ⟨i,hi⟩,
      prelude_bound hn ht ha hR0 q ⟨i,hi⟩⟩
  unfold query
  rw [IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0) _ _ _ _ _
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) HB]
  constructor
  · intro H
    funext i
    have HE:=H i.val (by rw [table_count];exact i.isLt)
    rw [table_lookup hn ht ha hR0 q i] at HE
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HE
    unfold target IntegralMixedRoadmapMarkedPrelude.value
    exact (IntegralMixedRoadmapIdentity.signature_point hn ht ha hR0 q hv i).symm.trans HE
  · intro H i hi
    rw [table_count] at hi
    rw [table_lookup hn ht ha hR0 q ⟨i,hi⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have HE:=congrFun H ⟨i,hi⟩
    unfold target IntegralMixedRoadmapMarkedPrelude.value at HE
    exact (IntegralMixedRoadmapIdentity.signature_point hn ht ha hR0 q hv ⟨i,hi⟩).trans HE

private theorem cast_point_heq {a b :ℕ} (h :a=b) (p :Fin b→ℝ):
    HEq (fun i:Fin a=>p (Fin.cast h i)) p:=by cases h;rfl
private theorem restriction_heq {a b :ℕ} (h :a=b) (v :ℕ→ℝ):
    HEq (fun i:Fin a=>v i.val) (fun i:Fin b=>v i.val):=by cases h;rfl

theorem language_iff (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    q∈language hn ht ha hR0 ↔IntegralMixedRoadmapAtomic.depth q=D q ∧
      IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
        (IntegralMixedRoadmapMarkedPrelude.point hn ht ha hR0 q hv):=by
  have HI:HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapIdentity.point
    exact cast_point_heq _ _
  have HT:HEq (target hn ht ha hR0 q hv) (IntegralMixedRoadmapMarkedPrelude.point hn ht ha hR0 q hv):=by
    unfold target IntegralMixedRoadmapMarkedPrelude.point
    exact restriction_heq (IntegralMixedRoadmapMarkedPrelude.point_dimension hn ht ha hR0 q).symm _
  simp only [language,Set.mem_ofPred_eq,hv,true_and,query_iff hn ht ha hR0 q hv]
  constructor
  · rintro ⟨HD,HR,HE⟩
    exact ⟨HD,HR,HI.symm.trans ((heq_of_eq HE).trans HT)⟩
  · rintro ⟨HD,HR,HE⟩
    exact ⟨HD,HR,eq_of_heq (HI.trans (HE.trans HT.symm))⟩

end LeanCanny.Encoding.IntegralMixedRoadmapMarkerAt
