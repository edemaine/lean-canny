/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEdge
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignatureBounds
/-! # Actual native roadmap edges can be traversed in either direction -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.Valid
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem language_of_values (a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (HC :Compatible hn ht ha hR0 (pair a b))
    (HV :∀i, i < D a+2→
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context a) (IntegralMixedRoadmapAtomic.word a)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA)
        (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 a) i))=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context b) (IntegralMixedRoadmapAtomic.word b)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 b hB)
        (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 b) i))) :
    pair a b∈language hn ht ha hR0:=by
  have HD :D a=D b ∧ IntegralMixedRoadmapAtomic.depth a=IntegralMixedRoadmapAtomic.depth b ∧
      0<IntegralMixedRoadmapAtomic.depth a:=by
    simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using HC
  have HB :∀i<WordListRecords.count (table hn ht ha hR0 (pair a b)),
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (table hn ht ha hR0 (pair a b)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context a) ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (table hn ht ha hR0 (pair a b)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context b):=by
    intro i hi
    rw [table_pair_count] at hi
    rw [table_pair_lookup hn ht ha hR0 a b ⟨i,hi⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair]
    exact ⟨signature_bounded_full hn ht ha hR0 a hA HD.2.2 i hi,
      signature_bounded_full hn ht ha hR0 b hB (HD.2.1 ▸ HD.2.2) i (by omega)⟩
  refine ⟨HC,?_⟩
  unfold query
  simp only [left,right,pairFst_pair,pairSnd_pair]
  apply (IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0)
    _ _ _ _ _ (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 b hB) HB).mpr
  intro i hi
  rw [table_pair_count] at hi
  rw [table_pair_lookup hn ht ha hR0 a b ⟨i,hi⟩]
  simpa only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair] using HV i hi

theorem language_symm (a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (H :pair a b∈language hn ht ha hR0) :pair b a∈language hn ht ha hR0:=by
  have HC :D a=D b ∧ IntegralMixedRoadmapAtomic.depth a=IntegralMixedRoadmapAtomic.depth b ∧
      0<IntegralMixedRoadmapAtomic.depth a:=by
    simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using H.1
  apply language_of_values hn ht ha hR0 b a hB hA
  · simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using
      And.intro HC.1.symm (And.intro HC.2.1.symm (HC.2.1 ▸ HC.2.2))
  · intro i hi
    exact (language_values hn ht ha hR0 a b hA hB H i (by omega)).symm
end LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature

namespace LeanCanny.Encoding.IntegralMixedRoadmapEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem symm {a b :List Bool} (H :Adjacent hn ht ha hR0 a b) :Adjacent hn ht ha hR0 b a:=by
  obtain ⟨hA,hB⟩:=valid hn ht ha hR0 a b H
  have HC:=candidate_eq hn ht ha hR0 a b H
  rcases H with HI|HP
  · exact Or.inl ((IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 b a hB hA HC.symm).mpr
      (((IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 a b hA hB HC).mp HI).symm))
  · have HL :IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 a:=by
      simpa only [pairFst_pair] using HP.2.1
    have HR :IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 b:=by
      simpa only [pairSnd_pair] using HP.2.2.1
    refine Or.inr ⟨?_,?_,?_,IntegralMixedRoadmapProperMidSignature.language_symm hn ht ha hR0 a b hA hB HP.2.2.2⟩
    · simpa only [IntegralMixedRoadmapIdentity.SameCandidate,IntegralMixedRoadmapIdentity.left,
        IntegralMixedRoadmapIdentity.right,pairFst_pair,pairSnd_pair] using HC.symm
    · simpa only [pairFst_pair] using HR
    · simpa only [pairSnd_pair] using HL
end LeanCanny.Encoding.IntegralMixedRoadmapEdge
