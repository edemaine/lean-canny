/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
/-! # Marked replay persists with the actual prelude coordinate values -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
  IntegralMixedPhysicalFieldEquality.point IntegralMixedAuxiliaryCandidate.point
  value point

theorem original_value (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i :Fin (number n (IntegralMixedRoadmapAtomic.root q))):
    value hn ht ha hR0 q hv i.val=IntegralMixedPhysicalReplayNew.point hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
      (full_valid hn ht ha hR0 q hv) i:=by
  have HP:=congrFun (point_eq_native hn ht ha hR0 q hv) (i.castAdd 4)
  unfold point at HP
  exact HP.trans (IntegralMixedPhysicalReplayRelation.point_original hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q) (full_valid hn ht ha hR0 q hv) i)

private theorem candidate_values_congr (a b :List Bool) (h :a=b) (v :ℕ→ℝ):
    (∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha a,
      ∀i :Fin (n (pairFst a)),IntegralMixedAuxiliaryCandidate.point hn ht ha a hp i=v i.val) ↔
    (∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha b,
      ∀i :Fin (n (pairFst b)),IntegralMixedAuxiliaryCandidate.point hn ht ha b hp i=v i.val):=by
  cases h
  rfl

theorem original_coordinates (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hr :Replay hn ht ha hR0 q):
    ∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedRoadmapAtomic.candidate q),
      ∀i :Fin (n (pairFst (IntegralMixedRoadmapAtomic.candidate q))),
        IntegralMixedAuxiliaryCandidate.point hn ht ha (IntegralMixedRoadmapAtomic.candidate q) hp i=
          value hn ht ha hR0 q hv i.val:=by
  obtain ⟨hp,_,HE⟩:=(IntegralMixedPhysicalReplayRelation.thom_packet hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)).mp hr.1
  have HO:∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root q)),
      ∀i :Fin (number n (IntegralMixedRoadmapAtomic.root q)),
        IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root q)) hp i=
          value hn ht ha hR0 q hv i.val:=
    ⟨hp,fun i=>(HE i).trans (original_value hn ht ha hR0 q hv i).symm⟩
  exact (candidate_values_congr hn ht ha _ _ (candidate_root q) _).mp HO

/-- This receipt compares physical values, not word ordinals or sample labels. -/
theorem replay_of_values (a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b)
    (hr :Replay hn ht ha hR0 a)
    (he :∀i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a,
      value hn ht ha hR0 a hA i=value hn ht ha hR0 b hB i):
    Replay hn ht ha hR0 b:=by
  have HO:=original_coordinates hn ht ha hR0 a hA hr
  rw [hc] at HO
  have HN:∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root b)),
      ∀i :Fin (number n (IntegralMixedRoadmapAtomic.root b)),
        IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root b)) hp i=
          value hn ht ha hR0 a hA i.val:=by
    exact (candidate_values_congr hn ht ha _ _ (candidate_root b) _).mpr HO
  obtain ⟨hp,HE⟩:=HN
  refine ⟨?_,hB.2.2.2.2.2.2⟩
  apply (IntegralMixedPhysicalReplayRelation.thom_packet hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root b) (IntegralMixedRoadmapAtomic.word b)).mpr
  refine ⟨hp,full_valid hn ht ha hR0 b hB,fun i=>?_⟩
  have HD:=IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 a
  have HC :n (pairFst (IntegralMixedRoadmapAtomic.candidate b))=
      n (IntegralMixedRoadmapAtomic.original a):=by
    rw [←hc]
    rfl
  have HI:i.val≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a:=by
    have HI0:i.val<n (pairFst (IntegralMixedRoadmapAtomic.candidate b)):=by
      simpa only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
        IntegralMixedAuxiliaryMarkedIntegerSource.candidate,candidate_root] using i.isLt
    omega
  exact (HE i).trans ((he i.val HI).trans (original_value hn ht ha hR0 b hB i))

private theorem fin_point_heq {a b :ℕ} (h :a=b) (p :Fin a→ℝ) (q :Fin b→ℝ)
    (he :∀i,p i=q (Fin.cast h i)):HEq p q:=by
  cases h
  exact heq_of_eq (funext he)

theorem point_heq_of_values (a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b)
    (he :∀i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a,
      value hn ht ha hR0 a hA i=value hn ht ha hR0 b hB i):
    HEq (point hn ht ha hR0 a hA) (point hn ht ha hR0 b hB):=by
  have HD :number n (IntegralMixedRoadmapAtomic.root a)=number n (IntegralMixedRoadmapAtomic.root b):=by
    rw [number_root,number_root]
    exact congrArg (fun c=>n (pairFst c)) hc
  apply fin_point_heq (congrArg (·+4) HD)
  intro i
  unfold point
  apply he i.val
  have HI:=i.isLt
  have HH:=point_dimension hn ht ha hR0 a
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
