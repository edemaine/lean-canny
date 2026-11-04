/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedPrelude
/-! # Fresh full seed words from the prescribed marked prelude -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  base IntegralMixedRoadmapSeedResampling.preparedRoot
  IntegralMixedRoadmapSeedResampling.seedTail IntegralMixedRoadmapSeedResampling.seedState
  IntegralMixedMarkedRecordContinuation.oldCommands IntegralMixedMarkedRecordContinuation.records_before
  IntegralMixedCausalRecordPlanBits.count IntegralMixedCausalRecordPlanBits.records
  IntegralMixedChronologicalSeedProgram.selections IntegralMixedChronologicalSeedProgram.descriptor
  IntegralMixedPointCompanion.commands IntegralMixedPointCompanion.values IntegralMixedFramedHistoryScript.Index

private theorem observation_commands {a S B :ℕ} {V :SpatialSource a}
    (x :State V S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd:=by cases he;rfl

theorem exists_tuple (u label :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)))
    (q :MvPolynomial (Fin (number n (root hn ht ha hR0 u label))) ℤ)
    (a :BoundedZeroSource.Bounded q (radius R0 (root hn ht ha hR0 u label)))
    (ha0 :∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)) hq i)
    (p :Fin ((P).ambient (root hn ht ha hR0 u label)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (root hn ht ha hR0 u label)).low
      (Q (root hn ht ha hR0 u label)).leading (Q (root hn ht ha hR0 u label)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (root hn ht ha hR0 u label)).low
        (Q (root hn ht ha hR0 u label)).leading (Q (root hn ht ha hR0 u label)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃v :ℕ→ℝ,(IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).Roots v ∧
      (∀k :Fin (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length,∀i,
        v (arity (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label))+
          (2*(P).ambient (root hn ht ha hR0 u label)+4)*
            ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val)+i.val)^
          UniformIntegralPowerSchedule.physical ((P).cap (root hn ht ha hR0 u label)+1)
            (2^(P).width (root hn ht ha hR0 u label))
            ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
              ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val))=p i) ∧
      ∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
        (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
        (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
          IntegralMixedPointCompanion.values p
            (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>
              prescribed hn ht ha (R0:=R0) (root hn ht ha hR0 u label) hq q a j.val)
            (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i:=by
  let r:=IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label)
  let older :List (Instruction ((P).ambient r) ((P).width r)):=IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)
  let js:=IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)
  let d:=IntegralMixedChronologicalSeedProgram.descriptor ((P).ambient r) older.length
  let g:=IntegralMixedChronologicalSeedProgram.zero ((P).ambient r) older.length
  let x:=preludeState hn ht ha hR0 r
  let old :Fin older.length→ℝ:=fun j=>prescribed hn ht ha (R0:=R0) r hq q a j.val
  have HI:=prelude_realizes hn ht ha hR0 r hq q a ha0
  unfold preludeState at HI
  obtain ⟨z,φ,hz,hφ,HV⟩:=HI
  have HD :(Q r).degree=BoundedZeroSource.powerDegree (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  have HR :older.length+js.length≤(P).cap r+1+1:=IntegralMixedRoadmapSeedResampling.seed_room hn ht ha hR0 (base u label)
  have HRoomG :older.length+(IntegralMixedChronologicalSeedProgram.selections
      ((P).ambient r) older.length (IntegralMixedRoadmapSeedResampling.seedTail hn ht ha hR0 (base u label))).length≤(P).cap r+1+1:=by
    simpa only [js,IntegralMixedRoadmapSeedResampling.seedSelections,r,older,root] using HR
  have HC:=@IntegralMixedChronologicalSeedProgram.exists_realized_seed
    ((P).ambient r) ((P).cap r+1) ((P).width r) older.length (Q r)
    (Index (Fin 0) older) (indexFintype (Fin 0) older) x
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r)
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size HD
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r) z hz φ hφ old HV p hp hg
    (IntegralMixedRoadmapSeedResampling.seedTail hn ht ha hR0 (base u label)) HRoomG
  obtain ⟨⟨R⟩,_⟩:=HC
  let cs :List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)):=
    IntegralMixedPointCompanion.commands d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g js
  have HE :((D).rules r)=(cs.map (IntegralMixedFramedFixedContinuation.wrap (Q r)
      (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))) :
      List (Instruction ((P).ambient r) ((P).width r)))++older:=
    IntegralMixedRoadmapSeedResampling.seed_full_commands hn ht ha hR0 (base u label)
  obtain ⟨v,hv,_,hblocks,hpoint⟩:=@IntegralMixedFramedFixedContinuation.companion_observation
    ((P).ambient r) ((P).width r) (Q r)
    ((P).ambient r) ((P).cap r+1) ((P).width r) ((D).initialSource r)
    (initial P D r) (Q r)
    (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))
    older ((Nat.le_add_right _ _).trans HR) d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g
    z φ old p js HR R
  have HO :ofCommands (initial P D r) ((D).rules r)
      (IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 r)=
    ofCommands (initial P D r) ((cs.map (IntegralMixedFramedFixedContinuation.wrap (Q r)
      (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))) :
      List (Instruction ((P).ambient r) ((P).width r)))++older)
      (by dsimp only [cs];simp only [List.length_append,List.length_map,IntegralMixedPointCompanion.commands_length];omega):=
    observation_commands _ _ _ _ _ HE
  refine ⟨v,?_,hblocks,?_⟩
  · unfold IntegralMixedRoadmapSeedResampling.seedObservation
    exact Eq.mpr (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>O.Roots v) HO) hv
  · intro i
    unfold IntegralMixedRoadmapSeedResampling.seedObservation
    exact (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>O.point v i.val) HO).trans (hpoint i)

noncomputable def WordReceipt (u label :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)))
    (q :MvPolynomial (Fin (number n (root hn ht ha hR0 u label))) ℤ)
    (a :BoundedZeroSource.Bounded q (radius R0 (root hn ht ha hR0 u label)))
    (p :Fin ((P).ambient (root hn ht ha hR0 u label)+1)→ℝ) :Prop:=
  ∃v :ℕ→ℝ,∃w,∃hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 (base u label)) w,
    IntegralMixedRoadmapSeedResampling.FieldJoint hn ht ha hR0 (base u label) w hw v ∧
    (∀k :Fin (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length,∀i,
      v (arity (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label))+
        (2*(P).ambient (root hn ht ha hR0 u label)+4)*
          ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (root hn ht ha hR0 u label)+1)
          (2^(P).width (root hn ht ha hR0 u label))
          ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
            ((IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length-1-k.val))=p i) ∧
    ∀i :Fin ((IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length+
      (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)).length),
      (IntegralMixedRoadmapSeedResampling.seedObservation hn ht ha hR0 (base u label)).point v i.val=
        IntegralMixedPointCompanion.values p
          (fun j :Fin (IntegralMixedRoadmapSeedResampling.seedOlder hn ht ha hR0 (base u label)).length=>
            prescribed hn ht ha (R0:=R0) (root hn ht ha hR0 u label) hq q a j.val)
          (IntegralMixedRoadmapSeedResampling.seedSelections hn ht ha hR0 (base u label)) i

theorem exists_word (u label :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)))
    (q :MvPolynomial (Fin (number n (root hn ht ha hR0 u label))) ℤ)
    (a :BoundedZeroSource.Bounded q (radius R0 (root hn ht ha hR0 u label)))
    (ha0 :∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (root hn ht ha hR0 u label)) hq i)
    (p :Fin ((P).ambient (root hn ht ha hR0 u label)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (root hn ht ha hR0 u label)).low
      (Q (root hn ht ha hR0 u label)).leading (Q (root hn ht ha hR0 u label)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (root hn ht ha hR0 u label)).low
        (Q (root hn ht ha hR0 u label)).leading (Q (root hn ht ha hR0 u label)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    WordReceipt hn ht ha hR0 u label hq q a p:=by
  obtain ⟨v,hv,HB,HV⟩:=exists_tuple hn ht ha hR0 u label hq q a ha0 p hp hg
  obtain ⟨w,hw,_,HJ⟩:=IntegralMixedRoadmapSeedResampling.sample_seed hn ht ha hR0 (base u label) v hv
  have hwS :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 (base u label)) w:=
    Eq.mp (congrArg (fun I=>SquareSampleCompleteVertices.Valid I
      (IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 (base u label)) w)
      (IntegralMixedRoadmapSeedResampling.seed_input_eq hn ht ha hR0)) hw
  exact ⟨v,w,hwS,HJ,HB,HV⟩

end LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
