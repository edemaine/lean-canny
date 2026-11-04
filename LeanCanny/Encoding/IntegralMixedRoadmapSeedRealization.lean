/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedTuple
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
/-! # Actual full seed rows from one old accepted vertex and one critical point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_commands {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd:=by cases he;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot seedTail
  IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.oldCommands
  IntegralMixedMarkedRecordContinuation.start preludeTuple oldTuple
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedAuxiliaryMarkedRecordPlan.factor
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedCausalRecordPlanBits.count IntegralMixedCausalRecordPlanBits.records
  IntegralMixedMarkedRecordContinuation.records_before IntegralMixedStaticRecordPrefix.records
  IntegralMixedStaticRecordPrefix.later IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.candidate
  IntegralMixedRoadmapAtomic.packet packet pair delimit pairFst pairSnd
  IntegralMixedChronologicalSeedProgram.selections IntegralMixedChronologicalSeedProgram.descriptor
  IntegralMixedChronologicalFrame.Descriptor.frame IntegralMixedChronologicalFrame.Descriptor.orderedFree
  IntegralMixedPointCompanion.commands IntegralMixedPointCompanion.codes IntegralMixedPointCompanion.values
  Turing.MultiTapeTM.ComputableTidilyInPolyTime IntegralMixedFramedHistoryScript.Index

noncomputable def seedState (old :List Bool):=
  reframe (run (initial P D (preparedRoot hn ht ha hR0 old)) (seedOlder hn ht ha hR0 old)
    ((Nat.le_add_right (seedOlder hn ht ha hR0 old).length (seedSelections hn ht ha hR0 old).length).trans
      (seed_room hn ht ha hR0 old))) (Q (preparedRoot hn ht ha hR0 old))
        (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot hn ht ha hR0 old))
          (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 (preparedRoot hn ht ha hR0 old)))
noncomputable def seedPoint (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    Fin (seedOlder hn ht ha hR0 old).length→ℝ:=
  IntegralMixedFullBankPoint.point (seedState hn ht ha hR0 old)
    (preludeTuple hn ht ha hR0 (preparedRoot hn ht ha hR0 old) (oldTuple hn ht ha hR0 old hv))

theorem seedState_start (old :List Bool) :seedState hn ht ha hR0 old=
    IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 (preparedRoot hn ht ha hR0 old) 0 (Nat.zero_le _):=by
  unfold seedState IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
    IntegralMixedCausalUnitContinuation.start seedOlder IntegralMixedMarkedRecordContinuation.oldCommands
  rfl
noncomputable def seedObservation (old :List Bool):=
  ofCommands (initial P D (preparedRoot hn ht ha hR0 old)) ((D).rules (preparedRoot hn ht ha hR0 old))
    (IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 (preparedRoot hn ht ha hR0 old))

attribute [local irreducible] seedState seedPoint seedObservation

theorem seed_interpretation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∃φ :(seedState hn ht ha hR0 old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((seedState hn ht ha hR0 old).sampler.scalarPrefix.basis.generator i)=
        preludeTuple hn ht ha hR0 (preparedRoot hn ht ha hR0 old) (oldTuple hn ht ha hR0 old hv)
          ((seedState hn ht ha hR0 old).sampler.scalar i)^
          weights ((P).cap (preparedRoot hn ht ha hR0 old)+1)
            (2^(P).width (preparedRoot hn ht ha hR0 old)) (seedOlder hn ht ha hR0 old).length i) ∧
      ∀i,φ ((seedState hn ht ha hR0 old).bank.numerator i)/
        ((seedState hn ht ha hR0 old).bank.denominator i:ℝ)=seedPoint hn ht ha hR0 old hv i:=by
  let root:=preparedRoot hn ht ha hR0 old
  let older:=seedOlder hn ht ha hR0 old
  let x:=seedState hn ht ha hR0 old
  let z:=preludeTuple hn ht ha hR0 root (oldTuple hn ht ha hR0 old hv)
  have HZ :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0:=by
    have H:=start_roots hn ht ha hR0 old hv
    unfold IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
      IntegralMixedCausalUnitContinuation.start IntegralMixedMarkedRecordContinuation.oldCommands at H
    unfold x seedState z root seedOlder IntegralMixedMarkedRecordContinuation.oldCommands
    exact H
  have HO :older.length≤(P).cap root+1+1:=by
    have HL:=seed_older_length hn ht ha hR0 old
    have HB:=seed_room hn ht ha hR0 old
    dsimp only [older,root]
    omega
  have HZ' :∀i,((run (initial P D root) older HO).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0:=by
    unfold x seedState at HZ
    simpa only [older,root,reframe] using HZ
  have HI:=IntegralMixedFramedFixedContinuation.before_interprets (initial P D root) (Q root)
    (IntegralMixedStaticRecordPrefix.cap (Q root) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root))
    older HO z HZ'
  have HI' :∃φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        z (x.sampler.scalar i)^weights ((P).cap root+1) (2^(P).width root) older.length i) ∧
      ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=IntegralMixedFullBankPoint.point x z i:=by
    unfold x seedState
    simpa only [older,root] using HI
  unfold seedPoint
  exact HI'

noncomputable def seedCommands (old :List Bool) :
    List (IntegralMixedFullHistoryScript.Command (Q (preparedRoot hn ht ha hR0 old))
      ((P).width (preparedRoot hn ht ha hR0 old))):=
  let d:=IntegralMixedChronologicalSeedProgram.descriptor ((P).ambient (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old).length
  IntegralMixedPointCompanion.commands d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i))
    (IntegralMixedChronologicalSeedProgram.zero ((P).ambient (preparedRoot hn ht ha hR0 old))
      (seedOlder hn ht ha hR0 old).length) (seedSelections hn ht ha hR0 old)

noncomputable def seedCodes (old :List Bool):=
  let d:=IntegralMixedChronologicalSeedProgram.descriptor ((P).ambient (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old).length
  IntegralMixedPointCompanion.codes d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i))
    (IntegralMixedChronologicalSeedProgram.zero ((P).ambient (preparedRoot hn ht ha hR0 old))
      (seedOlder hn ht ha hR0 old).length) (seedSelections hn ht ha hR0 old)

theorem seed_commands_length (old :List Bool) :
    (seedCommands hn ht ha hR0 old).length=(seedSelections hn ht ha hR0 old).length:=by
  unfold seedCommands
  rw [IntegralMixedPointCompanion.commands_length]

theorem seed_codes_length (old :List Bool) :
    (seedCodes hn ht ha hR0 old).length=IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old):=by
  unfold seedCodes
  rw [IntegralMixedPointCompanion.codes_length,seed_length]

theorem seed_records_codes (old :List Bool) :
    IntegralMixedCausalRecordPlanBits.records (preparedRoot hn ht ha hR0 old)=
      WordList.encode (seedCodes hn ht ha hR0 old).reverse:=by
  unfold seedCodes seedSelections
  rw [IntegralMixedChronologicalSeedProgram.codes_exact]
  simpa only [seedTail] using prepared_records hn ht ha hR0 old

theorem seed_decodes (old :List Bool) :
    IntegralMixedOptionalEndpoints.Decodes (seedState hn ht ha hR0 old)
      (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha (preparedRoot hn ht ha hR0 old))
      (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 (preparedRoot hn ht ha hR0 old))
      (seedCommands hn ht ha hR0 old)
      (by rw [seed_commands_length];exact seed_room hn ht ha hR0 old)
      (seedCodes hn ht ha hR0 old):=by
  unfold seedCommands seedCodes
  let d:=IntegralMixedChronologicalSeedProgram.descriptor ((P).ambient (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old).length
  have HR:=seed_room hn ht ha hR0 old
  have HT :(seedOlder hn ht ha hR0 old).length≤(P).cap (preparedRoot hn ht ha hR0 old)+1+1:=
    (Nat.le_add_right _ _).trans HR
  have HD:=IntegralMixedPointCompanion.decodes_append (seedState hn ht ha hR0 old)
    d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i))
    (IntegralMixedChronologicalSeedProgram.zero ((P).ambient (preparedRoot hn ht ha hR0 old))
      (seedOlder hn ht ha hR0 old).length)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha (preparedRoot hn ht ha hR0 old))
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 (preparedRoot hn ht ha hR0 old))
    [] HT [] rfl (Nat.add_zero _).symm (seedSelections hn ht ha hR0 old)
    (by simp only [List.append_nil,IntegralMixedPointCompanion.commands_length];exact HR)
  simp only [List.append_nil] at HD
  dsimp only [d] at HD
  exact HD

theorem seed_full_commands (old :List Bool) :
    ((D).rules (preparedRoot hn ht ha hR0 old))=((seedCommands hn ht ha hR0 old).map
      (IntegralMixedFramedFixedContinuation.wrap (Q (preparedRoot hn ht ha hR0 old))
        (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot hn ht ha hR0 old))
          (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 (preparedRoot hn ht ha hR0 old)))) :
            List (Instruction ((P).ambient (preparedRoot hn ht ha hR0 old))
              ((P).width (preparedRoot hn ht ha hR0 old))))++
        seedOlder hn ht ha hR0 old:=by
  let root:=preparedRoot hn ht ha hR0 old
  let cs:=seedCommands hn ht ha hR0 old
  let codes:=seedCodes hn ht ha hR0 old
  have HL :codes.length=IntegralMixedCausalRecordPlanBits.count root:=seed_codes_length hn ht ha hR0 old
  have HRE :IntegralMixedCausalRecordPlanBits.records root=WordList.encode codes.reverse:=
    seed_records_codes hn ht ha hR0 old
  have HDEC:=seed_decodes hn ht ha hR0 old
  rw [seedState_start] at HDEC
  have HC:=IntegralMixedMarkedConstructedPrefix.compiled_commands hn ht ha hR0 root 0 (Nat.zero_le _) codes
    (by omega) (by intro i hi;simp only [IntegralMixedCausalRecordPlanBits.code,HRE,
      WordList.get_encode,Nat.zero_add])
    cs (by rw [seed_commands_length];exact seed_room hn ht ha hR0 old) HDEC
  have HF :((D).rules root).length=number n root+8+codes.length:=by
    rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root,HL]
    rfl
  simp only [Nat.add_zero,←HF,IntegralMixedFramedHistoryScript.paddedPast_full] at HC
  unfold root cs at HC
  unfold seedOlder
  exact HC

noncomputable def seedDescriptor (old :List Bool):=
  IntegralMixedChronologicalSeedProgram.descriptor ((P).ambient (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old).length

noncomputable def RealizedSeed (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) :Prop:=
  ∃hom :(seedState hn ht ha hR0 old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  Nonempty (IntegralMixedPointCompanion.Realized (seedState hn ht ha hR0 old)
    (seedDescriptor hn ht ha hR0 old).frame.frozen (fun _=>false)
    (fun i=>.single ((seedDescriptor hn ht ha hR0 old).atom i))
    (IntegralMixedChronologicalSeedProgram.zero ((P).ambient (preparedRoot hn ht ha hR0 old))
      (seedOlder hn ht ha hR0 old).length)
    (preludeTuple hn ht ha hR0 (preparedRoot hn ht ha hR0 old) (oldTuple hn ht ha hR0 old hv))
    hom (seedPoint hn ht ha hR0 old hv) p (seedSelections hn ht ha hR0 old) (seed_room hn ht ha hR0 old))

set_option backward.isDefEq.respectTransparency true in
theorem exists_realized (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
      (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree).eval₂
        (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
        (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree)).eval₂
          (Int.castRingHom ℝ) p=0) :RealizedSeed hn ht ha hR0 old hv p:=by
  let root:=preparedRoot hn ht ha hR0 old
  let older:=seedOlder hn ht ha hR0 old
  let x:=seedState hn ht ha hR0 old
  let z:=preludeTuple hn ht ha hR0 root (oldTuple hn ht ha hR0 old hv)
  let js:=seedSelections hn ht ha hR0 old
  have HZ :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0:=by
    have H:=start_roots hn ht ha hR0 old hv
    unfold IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
      IntegralMixedCausalUnitContinuation.start IntegralMixedMarkedRecordContinuation.oldCommands at H
    unfold x seedState z root seedOlder IntegralMixedMarkedRecordContinuation.oldCommands
    exact H
  obtain ⟨φ,hφ,HV⟩:=seed_interpretation hn ht ha hR0 old hv
  have HG :(Q root).degree=BoundedZeroSource.powerDegree (t (IntegralMixedAuxiliaryMarkedIntegerSource.original root)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) root
  have HR :older.length+js.length≤(P).cap root+1+1:=seed_room hn ht ha hR0 old
  let F0:=@IntegralMixedChronologicalSeedProgram.exists_realized_seed
    ((P).ambient root) ((P).cap root+1) ((P).width root) older.length
    (Q root) (Index (Fin 0) older) (indexFintype (Fin 0) older)
  let F1:=F0 x
  let F2:=F1 (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original root)).toData.size HG
  let F3:=F2 (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root)
  let F4:=F3 z HZ φ hφ
  let F5:=F4 (seedPoint hn ht ha hR0 old hv) HV p hp hg
  have HRoomG :older.length+(IntegralMixedChronologicalSeedProgram.selections
      ((P).ambient root) older.length (seedTail hn ht ha hR0 old)).length≤(P).cap root+1+1:=by
    simpa only [js,seedSelections,root,older] using HR
  have HSeed:=F5 (seedTail hn ht ha hR0 old) HRoomG
  obtain ⟨⟨R⟩,_⟩:=HSeed
  exact ⟨φ,⟨R⟩⟩

theorem realized_observation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (receipt :RealizedSeed hn ht ha hR0 old hv p) :
    ∃u :ℕ→ℝ,(seedObservation hn ht ha hR0 old).Roots u ∧
      (∀i :Index (Fin 0) (seedOlder hn ht ha hR0 old),
        u (enumerate (seedOlder hn ht ha hR0 old) i).val=
          oldTuple hn ht ha hR0 old hv (enumerate (seedOlder hn ht ha hR0 old) i).val) ∧
      (∀k :Fin (seedSelections hn ht ha hR0 old).length,∀i,
        u (arity (seedOlder hn ht ha hR0 old)+
          (2*(P).ambient (preparedRoot hn ht ha hR0 old)+4)*
            ((seedSelections hn ht ha hR0 old).length-1-k.val)+i.val)^
          physical ((P).cap (preparedRoot hn ht ha hR0 old)+1)
            (2^(P).width (preparedRoot hn ht ha hR0 old))
            ((seedOlder hn ht ha hR0 old).length+((seedSelections hn ht ha hR0 old).length-1-k.val))=p i) ∧
      ∀i :Fin ((seedOlder hn ht ha hR0 old).length+(seedSelections hn ht ha hR0 old).length),
        (seedObservation hn ht ha hR0 old).point u i.val=
          IntegralMixedPointCompanion.values p (seedPoint hn ht ha hR0 old hv)
            (seedSelections hn ht ha hR0 old) i:=by
  let root:=preparedRoot hn ht ha hR0 old
  let older:=seedOlder hn ht ha hR0 old
  let x:=seedState hn ht ha hR0 old
  let z:=preludeTuple hn ht ha hR0 root (oldTuple hn ht ha hR0 old hv)
  let dim:=(P).ambient root
  let d:=IntegralMixedChronologicalSeedProgram.descriptor dim older.length
  let g:=IntegralMixedChronologicalSeedProgram.zero dim older.length
  let js:=seedSelections hn ht ha hR0 old
  unfold RealizedSeed seedState at receipt
  obtain ⟨φ,⟨R⟩⟩:=receipt
  have HR :older.length+js.length≤(P).cap root+1+1:=seed_room hn ht ha hR0 old
  let cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)):=
    IntegralMixedPointCompanion.commands d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g js
  have HE :((D).rules root)=(cs.map
      (IntegralMixedFramedFixedContinuation.wrap (Q root)
        (IntegralMixedStaticRecordPrefix.cap (Q root) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root))) :
          List (Instruction ((P).ambient root) ((P).width root)))++older:=
    seed_full_commands hn ht ha hR0 old
  obtain ⟨u,hu,hold,hblocks,hpoint⟩:=@IntegralMixedFramedFixedContinuation.companion_observation
    ((P).ambient root) ((P).width root) (Q root)
    ((P).ambient root) ((P).cap root+1) ((P).width root) ((D).initialSource root)
    (initial P D root) (Q root)
    (IntegralMixedStaticRecordPrefix.cap (Q root) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root))
    older ((Nat.le_add_right _ _).trans HR)
    d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g z φ
    (seedPoint hn ht ha hR0 old hv) p js HR R
  have HO:=observation_commands (initial P D root) ((D).rules root) _
    (IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 root)
    (by simp only [List.length_append,List.length_map,cs,IntegralMixedPointCompanion.commands_length];omega) HE
  refine ⟨u,?_,?_,?_,?_⟩
  · unfold seedObservation
    exact (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots u) HO).mpr hu
  · intro i
    unfold seedOlder at i ⊢
    unfold older seedOlder at hold
    simpa only [z,preludeTuple,root] using hold i
  · exact hblocks
  · intro i
    unfold seedObservation
    exact (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point u i.val) HO).trans (hpoint i)


theorem exists_seed_tuple (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
      (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree).eval₂
        (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
        (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree)).eval₂
          (Int.castRingHom ℝ) p=0) :
    ∃u :ℕ→ℝ,(seedObservation hn ht ha hR0 old).Roots u ∧
      (∀i :Index (Fin 0) (seedOlder hn ht ha hR0 old),
        u (enumerate (seedOlder hn ht ha hR0 old) i).val=
          oldTuple hn ht ha hR0 old hv (enumerate (seedOlder hn ht ha hR0 old) i).val) ∧
      (∀k :Fin (seedSelections hn ht ha hR0 old).length,∀i,
        u (arity (seedOlder hn ht ha hR0 old)+
          (2*(P).ambient (preparedRoot hn ht ha hR0 old)+4)*
            ((seedSelections hn ht ha hR0 old).length-1-k.val)+i.val)^
          physical ((P).cap (preparedRoot hn ht ha hR0 old)+1)
            (2^(P).width (preparedRoot hn ht ha hR0 old))
            ((seedOlder hn ht ha hR0 old).length+((seedSelections hn ht ha hR0 old).length-1-k.val))=p i) ∧
      ∀i :Fin ((seedOlder hn ht ha hR0 old).length+(seedSelections hn ht ha hR0 old).length),
        (seedObservation hn ht ha hR0 old).point u i.val=
          IntegralMixedPointCompanion.values p (seedPoint hn ht ha hR0 old hv)
            (seedSelections hn ht ha hR0 old) i:=by
  have receipt:=exists_realized hn ht ha hR0 old hv p hp hg
  exact realized_observation hn ht ha hR0 old hv p receipt

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
