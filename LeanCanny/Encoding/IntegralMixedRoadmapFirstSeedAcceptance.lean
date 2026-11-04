/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedWord
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVectorPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedValidity
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedGeometry
/-! # First fully accepted native seeds from original bounded candidates -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" old=>IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapSeedResampling.preparedRoot IntegralMixedRoadmapSeedResampling.seedOlder
  IntegralMixedRoadmapSeedResampling.seedSelections IntegralMixedRoadmapSeedResampling.seedTail
  IntegralMixedRoadmapSeedResampling.seedObservation IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.point
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private theorem reverse_selection (d m tail a :ℕ)
    (ha0 :a<(IntegralMixedChronologicalSeedProgram.selections d m tail).length) :
    ((IntegralMixedChronologicalSeedProgram.selections d m tail).get
      ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩).val.val=
      IntegralMixedRoadmapSeedMetadata.selected d a:=by
  have H:=IntegralMixedChronologicalSeedProgram.selection_coordinate d m tail
    ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩
  have HL:=IntegralMixedChronologicalSeedProgram.selections_length d m tail
  simp only [List.get_eq_getElem]
  rw [H]
  simp only [HL]
  unfold IntegralMixedRoadmapSeedMetadata.selected
  split_ifs <;> omega

private theorem field_values (u label w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX (base u label)) w)
    (v :ℕ→ℝ) (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+1)→ℝ) (old :ℕ→ℝ)
    (HJ :IntegralMixedRoadmapSeedResampling.FieldJoint hn ht ha hR0 (base u label) w hw v)
    (HV :∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
      (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
        IntegralMixedPointCompanion.values p
          (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>old j.val)
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i)
    (c :ℕ) (hc :c<(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX (base u label)) w hw c=
      IntegralMixedPointCompanion.values p
        (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>old j.val)
        (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label))
        ⟨(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-c,by omega⟩:=
  (IntegralMixedRoadmapSeedResampling.seed_field_observation hn ht ha hR0 (base u label) w hw v HJ c hc).trans
    (HV ⟨_,by omega⟩)

private theorem initial_field (u label w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX (base u label)) w)
    (v :ℕ→ℝ) (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+1)→ℝ) (old :ℕ→ℝ)
    (HJ :IntegralMixedRoadmapSeedResampling.FieldJoint hn ht ha hR0 (base u label) w hw v)
    (HV :∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
      (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
        IntegralMixedPointCompanion.values p
          (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>old j.val)
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i)
    (c :ℕ) (hc :c<(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX (base u label)) w hw c=
      old ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length-1-c):=by
  let N:=(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length
  let js:=IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)
  have HH:=field_values hn ht ha hR0 u label w hw v p old HJ HV c (by omega)
  let i :Fin N:=⟨N-1-c,by omega⟩
  have HE :(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-c=
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length+i.val:=by
    dsimp only [i,N];omega
  simp only [HE] at HH
  exact HH.trans (IntegralMixedPointCompanion.values_old p (fun j :Fin N=>old j.val) js i)

private theorem native_readback (u label w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX (base u label)) w)
    (v :ℕ→ℝ) (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+1)→ℝ) (old :ℕ→ℝ)
    (HJ :IntegralMixedRoadmapSeedResampling.FieldJoint hn ht ha hR0 (base u label) w hw v)
    (HB :∀k :Fin (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length,∀i,
      v (arity (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label))+
        (2*(P).ambient (root hn ht ha hR0 u label)+4)*
          ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (root hn ht ha hR0 u label)+1)
          (2^(P).width (root hn ht ha hR0 u label))
          ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
            ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val))=p i)
    (HV :∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
      (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
        IntegralMixedPointCompanion.values p
          (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>old j.val)
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i) :
    IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 (base u label) w hw
      (IntegralMixedRoadmapSeedResampling.seedNativePoint hn ht ha hR0 (base u label) p):=by
  constructor
  · intro b hb
    exact IntegralMixedRoadmapSeedResampling.geometricPoint_of_columns hn ht ha hR0 (base u label) w hw p v
      (IntegralMixedRoadmapSeedResampling.seed_candidates hn ht ha hR0 _ w hw v HJ) HB b hb
  · intro b hb
    let N:=(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length
    let js:=IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)
    have HL:=IntegralMixedRoadmapSeedResampling.seed_length hn ht ha hR0 (base u label)
    have HN:=IntegralMixedRoadmapSeedResampling.seed_older_length hn ht ha hR0 (base u label)
    have HF :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX (base u label)) w hw
        (number n (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+8+b)=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX (base u label)) w hw (N+b):=by
      exact congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX (base u label)) w hw)
        (by dsimp only [N];omega)
    have HH:=field_values hn ht ha hR0 u label w hw v p old HJ HV (N+b) (by dsimp only [N];omega)
    have HE :(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
        (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-(N+b)=
        (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-b:=by
      dsimp only [N];omega
    simp only [HE] at HH
    let k :Fin js.length:=⟨js.length-1-b,by dsimp only [js];omega⟩
    have HG:=IntegralMixedPointCompanion.values_get p (fun j :Fin N=>old j.val) js k
    refine HF.trans (HH.trans (HG.trans ?_))
    unfold IntegralMixedRoadmapSeedResampling.seedNativePoint
    apply congrArg p
    apply Fin.ext
    have HR :((js.get k).val).val=IntegralMixedRoadmapSeedMetadata.selected
        ((P).ambient (root hn ht ha hR0 u label)) b:=by
      dsimp only [js,k]
      unfold IntegralMixedRoadmapSeedResampling.seedSelections
      exact reverse_selection _ _ _ b (by
        rw [←IntegralMixedRoadmapSeedResampling.seed_length hn ht ha hR0 (base u label)] at hb
        simpa only [IntegralMixedRoadmapSeedResampling.seedSelections] using hb)
    have HS:=IntegralMixedRoadmapSeedMetadata.critical_selected hn ht ha hR0 (base u label) b hb
    rw [←IntegralMixedRoadmapSeedResampling.prepared_dimension hn ht ha hR0 (base u label)] at HS
    exact HR.trans HS.symm

private noncomputable def chronological (r :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate r))
    (q :MvPolynomial (Fin (number n r)) ℤ) (a :BoundedZeroSource.Bounded q (radius R0 r)) :ℕ→ℝ:=
  IntegralMixedAuxiliaryMarkedIntegerSource.values n t (radius R0) r
    (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha r hq)
    (BoundedRegularSource.sphereSlack q (radius R0 r) a)
    (BoundedRegularSource.regularSlack q
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original r))
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)) (radius R0 r) a).re

private theorem prescribed_reverse (r :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate r))
    (q :MvPolynomial (Fin (number n r)) ℤ) (a :BoundedZeroSource.Bounded q (radius R0 r))
    (i :ℕ) (hi :i<number n r+8) :
    prescribed hn ht ha (R0:=R0) r hq q a (number n r+8-1-i)=chronological hn ht ha (R0:=R0) r hq q a i:=by
  unfold prescribed chronological
  have HE :number n r+8-1-(number n r+8-1-i)=i:=by omega
  rw [HE]

private theorem marked_of_values (u label :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)))
    (a :BoundedZeroSource.Bounded
      (IntegralMixedAuxiliaryMarkedCandidateAtRadius.polynomial n t (root hn ht ha hR0 u label))
      (radius R0 (root hn ht ha hR0 u label)))
    (ha0 :∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)) hq i)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX (base u label)) w)
    (v :ℕ→ℝ)
    (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+1)→ℝ)
    (HJ :IntegralMixedRoadmapSeedResampling.FieldJoint hn ht ha hR0 (base u label) w hw v)
    (HV :∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
      (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
        IntegralMixedPointCompanion.values p
          (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>
            prescribed hn ht ha (R0:=R0) (root hn ht ha hR0 u label) hq
              (IntegralMixedAuxiliaryMarkedCandidateAtRadius.polynomial n t (root hn ht ha hR0 u label)) a j.val)
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i) :
    pair (root hn ht ha hR0 u label) w∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
  let r:=root hn ht ha hR0 u label
  let q:=IntegralMixedAuxiliaryMarkedCandidateAtRadius.polynomial n t r
  let V:=chronological hn ht ha (R0:=R0) r hq q a
  have hwR :SquareSampleCompleteVertices.Valid S (IntegralMixedPhysicalMarkedTest.sampleContext r) w:=by
    simpa only [IntegralMixedPhysicalMarkedTest.sampleContext,IntegralMixedRoadmapSeedMetadata.context,r,root] using hw
  have HE :∀i<number n r+8,
      IntegralMixedPhysicalMarkedSemantics.env hn ht ha (radius_binary hR0) false r w hwR i=V i:=by
    intro i hi
    have HN:=IntegralMixedRoadmapSeedResampling.seed_older_length hn ht ha hR0 (base u label)
    have HF:=initial_field hn ht ha hR0 u label w hw v p
      (prescribed hn ht ha (R0:=R0) r hq q a) HJ HV i (by dsimp only [r,root] at hi;omega)
    have HT :(IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length-1-i=
        number n r+8-1-i:=by dsimp only [r,root];omega
    have HX:=IntegralMixedPhysicalMarkedRetention.env_field hn ht ha hR0 r w hwR i hi
    refine HX.trans (HF.trans ?_)
    rw [HT]
    exact prescribed_reverse hn ht ha (R0:=R0) r hq q a i hi
  apply (IntegralMixedPhysicalMarkedValidity.accepted_iff hn ht ha (radius_binary hR0) false r w).mpr
  refine ⟨hwR,?_,?_⟩
  · intro i hi
    simp only [Bool.false_eq_true,ite_false] at hi
    rw [HE i hi]
    have HS:=IntegralMixedAuxiliaryMarkedSlackRoots.roots hn ht ha (radius R0) r hq q a ha0
    have HRoots:=IntegralMixedAuxiliaryMarkedIntegerSource.roots hn ht ha (radius R0) r
      (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha r hq)
      (BoundedRegularSource.sphereSlack q (radius R0 r) a)
      (BoundedRegularSource.regularSlack q
        (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original r))
        (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)) (radius R0 r) a).re
      (IntegralMixedAuxiliaryMarkedCandidateRealization.coordinate_root hn ht ha r hq) HS.1 HS.2 i
    simpa only [IntegralMixedPhysicalMarkedPlan.originalSource,Bool.false_eq_true,ite_false,V,chronological] using HRoots
  · let D0:=AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)
    let z:=BoundedRegularSource.markedLift q D0 D0 (radius R0 r) a
    refine ⟨z,?_⟩
    have HP :IntegralMixedPhysicalMarkedSemantics.point hn ht ha (radius_binary hR0) false r w hwR=
        (fun i :Fin (number n r+4)=>V i.val):=by
      funext i
      exact HE i.val (by have H:=i.isLt;omega)
    have HM:=IntegralMixedAuxiliaryMarkedIntegerSource.values_markedLift n t (radius R0) r q D0 D0 a
      (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha r hq) (by
        intro i hi
        unfold IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues
        rw [dite_eq_left hi]
        exact (ha0 ⟨i,hi⟩).symm)
    exact (HP.trans HM).symm

private theorem full_query_packet (u label w :List Bool) :
    IntegralMixedRoadmapAtomic.fullQuery (IntegralMixedRoadmapSeedResampling.packet
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w)=
      pair (root hn ht ha hR0 u label) w:=by
  simp only [IntegralMixedRoadmapAtomic.fullQuery,IntegralMixedRoadmapAtomic.root,root,
    IntegralMixedRoadmapSeedResampling.preparedRoot,IntegralMixedRoadmapSeedResampling.candidate_packet,
    IntegralMixedRoadmapSeedResampling.payload_packet,IntegralMixedRoadmapSeedResampling.word_packet]

/-- Initialize at any chosen genuine critical point while retaining every
new physical block and scalar capture on the same fresh complete word. -/
theorem exists_at (u label :List Bool)
    (hg :LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hLower :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u)
    (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label))+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).degree).eval₂
        (Int.castRingHom ℝ) p=0)
    (hcrit :∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root hn ht ha hR0 u label)).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid S (CTX (base u label)) w,
      IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label)
        (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w) ∧
      IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 (base u label) w hw
        (IntegralMixedRoadmapSeedResampling.seedNativePoint hn ht ha hR0 (base u label) p):=by
  obtain ⟨hq,a,ha0⟩:=bounded_witness hn ht ha hR0 u label hg hLower
  obtain ⟨v,w,hw,HJ,HB,HV⟩:=exists_word hn ht ha hR0 u label hq _ a ha0 p hp hcrit
  have HR:=native_readback hn ht ha hR0 u label w hw v p
    (prescribed hn ht ha (R0:=R0) (root hn ht ha hR0 u label) hq _ a) HJ HB HV
  have HM:=marked_of_values hn ht ha hR0 u label hq a ha0 w hw v p HJ HV
  have HC :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label):=Classical.choose hg
  have hwA :SquareSampleCompleteVertices.Valid S
      (IntegralMixedRoadmapAtomic.context (IntegralMixedRoadmapSeedResampling.packet
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w)) w:=
    Eq.mpr (congrArg (fun c=>SquareSampleCompleteVertices.Valid S c w)
      (IntegralMixedRoadmapSeedMetadata.packet_context hn ht ha hR0 (base u label) w)) hw
  have HG:=grammar hn ht ha hR0 u label w HC hwA
  have HCA :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedRoadmapAtomic.candidate
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label))
        (base u label) w)):=by
    rw [IntegralMixedRoadmapSeedResampling.candidate_packet,candidate_base]
    exact HC
  have HCut :pair (root hn ht ha hR0 u label) w∈IntegralMixedPhysicalTraceBeforeProbe.language
      hn ht ha (radius_binary hR0) false:=by
    refine ⟨?_,IntegralMixedRoadmapSeedMetadata.before_probe_holds hn ht ha hR0 (base u label) w⟩
    simpa only [root,IntegralMixedRoadmapSeedMetadata.context,IntegralMixedPhysicalMarkedTest.sampleContext,
      pairFst_pair,pairSnd_pair] using hw
  have HAll:=IntegralMixedRoadmapSeedMetadata.all_critical_of_readback hn ht ha hR0 (base u label) w hw _ HR
  have HComp:=IntegralMixedRoadmapSeedMetadata.atomic_companion_of_readback hn ht ha hR0 (base u label) w hw _ HR
  have HValid :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w):=by
    unfold IntegralMixedRoadmapAtomic.Valid
    refine ⟨HG,HCA,?_,?_,?_,HComp,?_⟩
    · simpa only [IntegralMixedRoadmapSeedResampling.word_packet] using hwA
    · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false)
        (full_query_packet hn ht ha hR0 u label w)) HCut
    · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false)
        (full_query_packet hn ht ha hR0 u label w)) HAll
    · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false)
        (full_query_packet hn ht ha hR0 u label w)) HM
  exact ⟨w,hw,Eq.mp (congrArg (IntegralMixedRoadmapAtomic.Valid hn ht ha hR0) (packet_eq hn ht ha hR0 u label w)) HValid,HR⟩

/-- A filtered original candidate inside the chosen original radius produces
the first fully accepted canonical seed, with no previous roadmap word. -/
theorem exists_valid (u label :List Bool)
    (hg :LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hLower :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃w,IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w):=by
  obtain ⟨p,hp,hcrit⟩:=LeanCanny.Connectivity.IntegralMixedRoadmapGraph.exists_first_critical
    hn ht ha hR0 u label hg hLower
  obtain ⟨w,_,hw,_⟩:=exists_at hn ht ha hR0 u label hg hLower p hp hcrit
  exact ⟨w,hw⟩

end LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
