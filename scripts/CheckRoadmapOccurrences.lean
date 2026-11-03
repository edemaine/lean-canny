import Lean.Util.CollectAxioms
import LeanCanny.Connectivity
import LeanCanny.Encoding.IntegralFramedPhysicalPrefixRealization
import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
import LeanCanny.Encoding.IntegralMixedMarkedPrefixObservation
import LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
import LeanCanny.Encoding.IntegralMixedMarkedReservedVertex
import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeHints
import LeanCanny.Encoding.IntegralMixedRoadmapCaptureRecords
import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
import LeanCanny.Encoding.IntegralMixedRoadmapProperAllRows
import LeanCanny.Encoding.IntegralMixedRoadmapProperBaseReadback
import LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCritical
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowReadback
import LeanCanny.Geometry.IntegralMixedChronologicalDegenerateLevel
import LeanCanny.Geometry.IntegralMixedChronologicalLevelRecord
import LeanCanny.Geometry.IntegralMixedChronologicalProperLevel
import LeanCanny.Geometry.IntegralMixedFrozenFrameRetainedSweep
import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths

/-! Checked history prefixes, native occurrences and branch path normalization.
The complete bounded graph/path equivalence remains a separate obligation. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapInternalPrefixCongruence
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedMarkedPrefixRun
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace MarkedPrefixCongruenceRegression

example (old p q a b : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (reservedRoot old [] p a)=
      IntegralMixedCausalRecordPlanBits.count (reservedRoot old [] q b) :=by
  rw [reserved_count,reserved_count]
example (old : List Bool) (codes : List (List Bool)) (p a : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (reservedRoot old codes p a)=codes.length+1 :=
  reserved_count old codes p a
example (old : List Bool) (codes : List (List Bool)) (p q a b : List Bool)
    (i : ℕ) (hi : i<codes.length) :
    IntegralMixedCausalRecordPlanBits.code (reservedRoot old codes p a) i=
      IntegralMixedCausalRecordPlanBits.code (reservedRoot old codes q b) i :=
  reserved_prefix old codes p q a b i hi

-- The common first malformed record is retained; the changed probe is not equated.
example : IntegralMixedCausalRecordPlanBits.code
    (reservedRoot [] [[false,false,true]] [true] []) 0=[false,false,true] :=by decide
example : IntegralMixedCausalRecordPlanBits.code
    (reservedRoot [] [[false,false,true]] [] [true]) 0=[false,false,true] :=by decide
example : IntegralMixedCausalRecordPlanBits.code (reservedRoot [] [[]] [true] []) 1≠
    IntegralMixedCausalRecordPlanBits.code (reservedRoot [] [[]] [] []) 1 :=by decide
example : IntegralMixedCausalRecordPlanBits.count (reservedRoot [] [[]] [] [])≠
    IntegralMixedCausalRecordPlanBits.count (reservedRoot [] [[],[]] [] []) :=by decide

private noncomputable def Q : SpatialSource 1 where
  low:=0
  leading:=1
  degree:=2
  degree_two:=le_rfl
  low_degree:=by simp
  leading_ne_zero:=one_ne_zero
private noncomputable def seed : State Q 3 32 0 (Fin 0) :=
  IntegralMixedHistory.base Q (IntegralHistorySampler.base 3 (2^32)) (by decide)
private noncomputable def p : Polynomial ℤ :=-(Polynomial.C (-2)*Polynomial.X+Polynomial.C 3)^2
private theorem pn :p≠0 :=by
  intro h
  have H:=congrArg (fun a : Polynomial ℤ=>a.eval 0) h
  norm_num [p] at H
private theorem pd :p.natDegree≤2^32 :=by
  have hd :(Polynomial.C (-2)*Polynomial.X+Polynomial.C (3:ℤ)).natDegree≤1 :=by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  rw [p,Polynomial.natDegree_neg,Polynomial.natDegree_pow]
  exact (Nat.mul_le_mul_left 2 hd).trans (by decide)
private noncomputable def integer :IntegralMixedCausalRecordBits.Record 1 32 :=
  ⟨Q,by decide,.integer p pn pd⟩
private noncomputable def cut :IntegralMixedCausalRecordBits.Record 1 32 where
  source:=Q
  source_cap:=by decide
  template:=.cut {
    critical:={offset:=⟨1,by decide⟩,objective:=0,coordinate:=0,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
    height:=⟨0,by decide⟩
    frozen:=by decide
    tag:=.coordinate
    coordinate:=0
    choice:=0
    degree:=1
    source_cap:=by decide
    degree_cap:=by decide
    current:=true}
private noncomputable def fallback :Instruction 1 32 :=
  IntegralMixedCausalRecordBits.instantiate seed integer

-- A repeated-root polynomial with negative, nonunit leading coefficient is allowed.
example :p.eval₂ (Int.castRingHom ℝ) (3/2)=0 :=by
  simp only [p,Polynomial.eval₂_neg,Polynomial.eval₂_pow,Polynomial.eval₂_add,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X]
  norm_num
example :p.leadingCoeff=-4 :=by
  have H :(Polynomial.C (-2)*Polynomial.X+Polynomial.C (3:ℤ)).leadingCoeff=-2 :=by
    rw [Polynomial.leadingCoeff_add_of_degree_lt']
    · exact Polynomial.leadingCoeff_C_mul_X (-2)
    · rw [Polynomial.degree_C (by decide : (3:ℤ)≠0),
        Polynomial.degree_C_mul_X (by decide : (-2:ℤ)≠0)]
      decide
  rw [p,Polynomial.leadingCoeff_neg,Polynomial.leadingCoeff_pow,H]
  norm_num
example :HEq
    (IntegralMixedCausalPrefixCongruence.prefixRun seed [cut,integer] (by decide) fallback 1 (by decide))
    (IntegralMixedCausalPrefixCongruence.prefixRun seed [integer,integer] (by decide) fallback 1 (by decide)) :=by
  unfold IntegralMixedCausalPrefixCongruence.prefixRun
  exact IntegralMixedCausalPrefixCongruence.run_prefix seed [cut,integer] [integer,integer]
    (by decide) (by decide) fallback fallback 1 (by decide) (by decide) rfl
example (z : ℕ→ℝ) :
    (IntegralMixedFramedRunObservation.ofCommands seed [fallback] (by decide)).Roots z↔
      ∀i,((run seed [fallback] (by decide)).sampler.rows i).eval₂ (Int.castRingHom ℝ)
        (fun j=>z (IntegralMixedFramedPhysicalIndex.enumerate [fallback] j).val)=0 :=
  IntegralMixedFramedRunObservation.roots_actual seed [fallback] (by decide) z
example (z : ℕ→ℝ) :
    (IntegralMixedFramedRunObservation.ofCommands seed [fallback] (by decide)).point z 0=
      Geometry.IntegralMixedCanonicalBankPoint.point (run seed [fallback] (by decide))
        (fun j=>z (IntegralMixedFramedPhysicalIndex.enumerate [fallback]
          ((run seed [fallback] (by decide)).sampler.scalar j)).val) ⟨0,by decide⟩ :=
  IntegralMixedFramedRunObservation.point_actual seed [fallback] (by decide) z ⟨0,by decide⟩

private noncomputable def observation :IntegralMixedFramedRunObservation.Data :=
  ⟨⟨4,2,1,fun _=>-6⟩,1,fun i=>if i=0 then MvPolynomial.X 7-1 else 0,fun _=>7⟩
example :observation.point (fun _=>1) 0=-(1/6:ℝ) :=by
  dsimp only [observation,IntegralMixedFramedRunObservation.Data.point,
    IntegralMixedFramedBankObservation.Data.point]
  norm_num
example :observation.point (fun _=>1) 99=0 :=by
  norm_num [observation,IntegralMixedFramedRunObservation.Data.point,
    IntegralMixedFramedBankObservation.Data.point]
example :observation.Roots (fun _=>1) :=by
  intro i
  by_cases hi :i=0 <;> simp [observation,hi]

section Actual
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR0)

example (old :List Bool) (codes :List (List Bool)) (p q a b :List Bool) (i :ℕ) :
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (IntegralMixedOriginalRegularSource.radius R0)).polynomial
        (pair (reservedRoot old codes p a) (BinaryNatCode.encode i))=
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (IntegralMixedOriginalRegularSource.radius R0)).polynomial
        (pair (reservedRoot old codes q b) (BinaryNatCode.encode i)) :=by
  apply IntegralMixedMarkedPreludeCongruence.polynomial hn ht ha R0
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,reservedRoot,pairFst_pair]
example (old :List Bool) (codes :List (List Bool)) (p q a b :List Bool) :
    (P).width (reservedRoot old codes p a)=(P).width (reservedRoot old codes q b) :=by
  apply IntegralMixedMarkedPrefixParameters.width hn ht ha hR0
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,reservedRoot,pairFst_pair]
example (old :List Bool) (codes :List (List Bool)) (p q a b :List Bool) :
    (P).cap (reservedRoot old codes p a)=(P).cap (reservedRoot old codes q b) :=by
  apply IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0
  · simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,reservedRoot,pairFst_pair]
  · rw [reserved_count,reserved_count]
example (old p q a b :List Bool) :
    HEq (IntegralMixedFramedFamilyRunView.familyRun P D
      (IntegralMixedFramedHistoryFamilyBits.keyAt (reservedRoot old [] p a)
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n (reservedRoot old [] p a)+8) []))
      (IntegralMixedFramedFamilyRunView.familyRun P D
        (IntegralMixedFramedHistoryFamilyBits.keyAt (reservedRoot old [] q b)
          (IntegralMixedAuxiliaryMarkedIntegerSource.number n (reservedRoot old [] q b)+8) [true])) :=by
  simpa only [List.length_nil,Nat.add_zero] using reserved_run hn ht ha hR0 old [] p q a b [] [true]
example (old :List Bool) (codes :List (List Bool)) (p q a b :List Bool) (z :ℕ→ℝ) (i :ℕ) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (reservedRoot old codes p a) codes.length
      (by rw [reserved_count];omega)).point z i=
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (reservedRoot old codes q b) codes.length
      (by rw [reserved_count];omega)).point z i :=by
  rw [IntegralMixedMarkedPrefixObservation.reserved_eq hn ht ha hR0 old codes p q a b]
end Actual

#print axioms IntegralMixedFramedSlackSibling.common_eq
#print axioms IntegralMixedFramedSlackSibling.matrix_heq
#print axioms IntegralMixedFramedSlackSibling.sphere_polynomial
#print axioms IntegralMixedFramedSlackSibling.regular_polynomial
#print axioms IntegralMixedMarkedPreludeCongruence.polynomial
#print axioms IntegralMixedMarkedPreludeCongruence.degree_bound
#print axioms IntegralMixedMarkedPrefixParameters.width
#print axioms IntegralMixedMarkedPrefixParameters.cap
#print axioms IntegralMixedCausalPrefixCongruence.commands_prefix
#print axioms IntegralMixedCausalPrefixCongruence.run_prefix
#print axioms IntegralMixedStaticRecordPrefix.prefix_heq
#print axioms IntegralMixedStaticRecordPrefix.run_heq
#print axioms IntegralMixedMarkedPrefixRecords.rules
#print axioms IntegralMixedMarkedPrefixRecords.initial_heq
#print axioms IntegralMixedMarkedPrefixRecords.prefix_heq
#print axioms IntegralMixedMarkedPrefixRun.runAt_heq
#print axioms IntegralMixedMarkedPrefixRun.familyRun_heq
#print axioms IntegralMixedMarkedPrefixRun.reserved_run
#print axioms IntegralMixedFramedRunObservation.point_actual
#print axioms IntegralMixedFramedRunObservation.roots_actual
#print axioms IntegralMixedMarkedPrefixObservation.eq
#print axioms IntegralMixedMarkedPrefixObservation.roots_iff
#print axioms IntegralMixedMarkedPrefixObservation.point_eq
#print axioms IntegralMixedMarkedPrefixObservation.reserved_eq
end MarkedPrefixCongruenceRegression
end RoadmapInternalPrefixCongruence

namespace RoadmapInternalFullPrefix
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength keyAt)
open IntegralMixedFramedPhysicalIndex (enumerate arity scalarSlot)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FullPrefixRestrictionRegression
private def Q : SpatialSource 1 where
 low:=-1
 leading:=1
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
private def width:=(PurePowerReductionBounds.dimension 2 Q.degree).size
private theorem cap : PurePowerReductionBounds.dimension 2 Q.degree≤2^width:=Nat.le_of_lt (Nat.lt_size_self _)
private def integer : Instruction 1 width:=⟨Q,cap,.integer Polynomial.X (by simp) (by simpa only [Polynomial.natDegree_X] using (show 1≤2^width from Nat.one_le_two_pow))⟩
private def critical : Instruction 1 width:=IntegralMixedCanonicalPaddingSeed.instruction Q cap
private def r : IntegralMixedCriticalSweep.Rule 1 where
 critical:={
  offset:=⟨1,by decide⟩
  objective:=0
  coordinate:=0
  scales _:=1
  scales_ne_zero _:=one_ne_zero
  heights _:=.constant 0}
 height:=⟨0,by decide⟩
 height_frozen:=by decide
 slope:=1
 slope_ne_zero:=one_ne_zero
private def cut : Instruction 1 width:=⟨Q,cap,.cut r (.coordinate ⟨0,by decide⟩ ⟨0,by decide⟩)
  0 (Nat.zero_le _) (Nat.zero_le _)⟩
private def cs:=[cut,critical,integer]
example : arity cs=8:=rfl
example : arity (cs.drop 1)=7:=rfl
example : arity (cs.drop 2)=1:=rfl
example : (enumerate cs (IntegralMixedFramedPhysicalDrop.embedding cs 2 (Sum.inr ()))).val=0:=rfl
example : (enumerate cs (IntegralMixedFramedPhysicalDrop.embedding cs 1
 (Sum.inl (Sum.inr (Sum.inl (0 : Fin 2)))))).val=1:=rfl
example : (enumerate cs (IntegralMixedFramedPhysicalDrop.embedding cs 1 (Sum.inr ()))).val=6:=rfl
example : (enumerate cs (Sum.inr ())).val=7:=rfl
example (i : Index (Fin 0) cs) : IntegralMixedFramedPhysicalDrop.embedding cs 0 i=i:=rfl
example (i : Index (Fin 0) (cs.drop 2)) :
 (enumerate cs (IntegralMixedFramedPhysicalDrop.embedding cs 2 i)).val=(enumerate (cs.drop 2) i).val:=
 IntegralMixedFramedPhysicalDrop.enumerate_embedding cs 2 i
example : UniformIntegralPowerSchedule.weights 6 8 3 ⟨2,by decide⟩=
 UniformIntegralPowerSchedule.weights 6 8 1 ⟨0,by decide⟩:=by decide
variable (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
 (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c))
 (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w)
 (m : ℕ) (hm : m≤prefixLength P (key c))
example : IntegralMixedIntegerRealization.Realizes (IntegralFramedPhysicalPrefixRealization.state P D key c m hm)
 (IntegralFramedPhysicalPrefixRealization.values P D H L F C hs key hp c w hv m hm):=
 IntegralFramedPhysicalPrefixRealization.realizes P D H L F C hs key hp c w hv m hm
example (aux : List Bool) : IntegralMixedIntegerRealization.Realizes
 (IntegralMixedFramedFamilyRunView.stateView P D H (keyAt (pairFst (key c)) m aux))
 (IntegralFramedPhysicalPrefixRealization.values P D H L F C hs key hp c w hv m hm):=
 IntegralFramedPhysicalPrefixRealization.canonical_realizes P D H L F C hs key hp c w hv m hm aux
example (aux : List Bool) : IntegralMixedIntegerRealization.Realizes
 (IntegralMixedFramedFamilyRunView.stateView P D H (keyAt (pairFst (key c)) (prefixLength P (key c)-1) aux))
 (IntegralFramedPhysicalPrefixRealization.values P D H L F C hs key hp c w hv
   (prefixLength P (key c)-1) (Nat.sub_le _ _)):=
 IntegralFramedPhysicalPrefixRealization.canonical_realizes P D H L F C hs key hp c w hv _ (Nat.sub_le _ _) aux
#print axioms IntegralMixedFramedPhysicalDrop.enumerate_embedding
#print axioms IntegralMixedFramedPhysicalDrop.rows_embedding
#print axioms IntegralMixedFramedPhysicalDrop.roots
#print axioms IntegralFramedPhysicalPrefixRealization.drop_eq
#print axioms IntegralFramedPhysicalPrefixRealization.column
#print axioms IntegralFramedPhysicalPrefixRealization.raw_column
#print axioms IntegralFramedPhysicalPrefixRealization.raw_roots
#print axioms IntegralFramedPhysicalPrefixRealization.values_at
#print axioms IntegralFramedPhysicalPrefixRealization.exists_interpretation
#print axioms IntegralFramedPhysicalPrefixRealization.realizes
#print axioms IntegralFramedPhysicalPrefixRealization.canonical_realizes
end FullPrefixRestrictionRegression
end
end RoadmapInternalFullPrefix

namespace RoadmapInternalBadProbe
open LeanCanny LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

example (c r w labels a b : List Bool) :
    IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapBadProbePacket.packet c r w labels a b)=pair c (pair r []) :=by
  simp only [IntegralMixedRoadmapBadProbePacket.root,IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapBadProbePacket.raw,pairFst_pair,pairSnd_pair]
example (q : List Bool) (n i : ℕ) (hi : i<IntegralMixedRoadmapBadProbePacket.count (pairFst q)-1) :
    WordList.get (IntegralMixedRoadmapBadProbePacket.preparedRaw n q) i=
      WordList.get (IntegralMixedRoadmapBadProbePacket.raw (pairFst q)) i :=
  IntegralMixedRoadmapBadProbePacket.prepared_lookup n q i hi
example (q : List Bool) (n : ℕ) :
    WordList.get (IntegralMixedRoadmapBadProbePacket.preparedRaw n q)
      (IntegralMixedRoadmapBadProbePacket.count (pairFst q)-1)=IntegralMixedRoadmapBadProbePacket.probe n q :=
  IntegralMixedRoadmapBadProbePacket.prepared_last n q
example (q : List Bool) (i : ℕ) (hi : i<IntegralMixedRoadmapBadProbePacket.creating 8 q) :
    WordList.get (IntegralMixedRoadmapBadProbePacket.matchTable 8 q) i=
      pair (BinaryNatCode.encode i) (BinaryNatCode.encode i) :=
  IntegralMixedRoadmapBadProbePacket.matchTable_lookup 8 q i hi
example (q : List Bool) :
    WordListRecords.count (IntegralMixedRoadmapBadProbePacket.matchTable 8 q)=
      IntegralMixedRoadmapBadProbePacket.creating 8 q :=IntegralMixedRoadmapBadProbePacket.matchTable_count 8 q

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
example : IntegralMixedRoadmapBadProbeTest.language hn ht ha hR∈PSPACE:=
  IntegralMixedRoadmapBadProbeTest.mem_PSPACE hn ht ha hR
example (q : List Bool) : IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hR q ↔
    ∃w : List Bool,IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair q w) :=
  IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha hR q
example : IntegralMixedRoadmapBadProbeSearch.language hn ht ha hR∈PSPACE:=
  IntegralMixedRoadmapBadProbeSearch.mem_PSPACE hn ht ha hR
example (base : List Bool) (e : ℕ→ℕ)
    (he : ∀i<4,e i<2^IntegralMixedRoadmapBadProbeSearch.blockWidth hn ht ha hR base) :
    Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field 3
      (IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha hR (pair base
        (FixedWidthNatVector.encode 4 (IntegralMixedRoadmapBadProbeSearch.blockWidth hn ht ha hR base) e))))=e 3 :=
  IntegralMixedRoadmapBadProbeSearch.encode_fields hn ht ha hR base e he 3 (by decide)

#print axioms IntegralMixedRoadmapBadProbePacket.prepared_count
#print axioms IntegralMixedRoadmapBadProbePacket.prepared_lookup
#print axioms IntegralMixedRoadmapBadProbePacket.prepared_last
#print axioms IntegralMixedRoadmapBadProbePacket.matchTable_lookup
#print axioms IntegralMixedRoadmapBadProbePacket.hintGood_FP
#print axioms IntegralMixedRoadmapBadProbeTest.mem_PSPACE
#print axioms IntegralMixedRoadmapBadProbeTest.witness_word_length
#print axioms IntegralMixedRoadmapBadProbeTest.hasWitness_iff
#print axioms IntegralMixedRoadmapBadProbeTest.hasWitness_evaluator
#print axioms IntegralMixedRoadmapBadProbeSearch.encode_fields
#print axioms IntegralMixedRoadmapBadProbeSearch.ordinary_fields_fit
#print axioms IntegralMixedRoadmapBadProbeSearch.mem_PSPACE

example (base : List Bool) : IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha hR base ↔
    ∀hint w : List Bool,¬IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (pair base hint) w) :=
  IntegralMixedRoadmapBadProbeSearch.noBadProbe_iff hn ht ha hR base
#print axioms IntegralMixedRoadmapBadProbeSearch.witness_hint_iff
#print axioms IntegralMixedRoadmapBadProbeSearch.hasBadProbe_iff
#print axioms IntegralMixedRoadmapBadProbeSearch.noBadProbe_iff
end RoadmapInternalBadProbe

namespace RoadmapInternalOldFields
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
namespace BadProbeFieldRegression
open IntegralMixedRoadmapBadProbePacket (packet matchTable creating)
private def base :List Bool:=packet (pair [] []) (WordList.encode [[false],[true,false]])
  [false,true] [] (BinaryNatCode.encode 0) (BinaryNatCode.encode 1)
example :IntegralMixedRoadmapBadProbePacket.count base=2 :=by decide
example :creating 8 base=9 :=by decide
example :WordListRecords.count (matchTable 8 base)=9 :=
  IntegralMixedRoadmapBadProbePacket.matchTable_count 8 base
example :WordList.get (matchTable 8 base) 0=pair (BinaryNatCode.encode 0) (BinaryNatCode.encode 0) :=
  IntegralMixedRoadmapBadProbePacket.matchTable_lookup 8 base 0 (by decide)
example :WordList.get (matchTable 8 base) 8=pair (BinaryNatCode.encode 8) (BinaryNatCode.encode 8) :=
  IntegralMixedRoadmapBadProbePacket.matchTable_lookup 8 base 8 (by decide)
example :(9:ℕ)∉List.range (creating 8 base) :=by decide
example :IntegralMixedPhysicalFieldEquality.newest 10 0=9 ∧
    IntegralMixedPhysicalFieldEquality.newest 10 8=1 :=by decide
example :IntegralMixedPhysicalFieldEquality.newest 9 0=8 ∧
    IntegralMixedPhysicalFieldEquality.newest 9 8=0 :=by decide
example (hint :List Bool) :IntegralMixedCausalRecordPlanBits.count
    (IntegralMixedRoadmapBadProbePacket.preparedRoot 3 (pair base hint))=2 :=by
  simpa only [pairFst_pair,show IntegralMixedRoadmapBadProbePacket.count base=2 by decide] using
    IntegralMixedRoadmapBadProbePacket.prepared_count 3 (pair base hint) (by rw [pairFst_pair];decide)
example (hint :List Bool) :WordList.get
    (IntegralMixedRoadmapBadProbePacket.preparedRaw 3 (pair base hint)) 0=[false] :=by
  rw [IntegralMixedRoadmapBadProbePacket.prepared_lookup 3 (pair base hint) 0 (by rw [pairFst_pair];decide),pairFst_pair]
  decide

private def number (_ :List Bool):ℕ:=0
private def term (_ :List Bool):Term:=.const 0
private def radius (_ :List Bool):ℕ:=0
private theorem hn :UnaryFn number:=UnaryFn.const 0
private theorem ht :(fun q=>(term q).toData.toBits)∈FP:=by
  simpa only [term] using constFn_mem_FP (Term.const (0:ℤ)).toData.toBits
private theorem ha :∀q,(term q).arity≤number q:=by intro q;change 0≤0;omega
private theorem hR :BinaryFn radius:=BinaryFn.const 0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

example :SpaceDecider (IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR):=
  IntegralMixedPhysicalFieldEqualityList.decider hn ht ha hR
example (z :List Bool) (hc :0<IntegralMixedRoadmapBadProbePacket.count (pairFst z)) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha hR
      (IntegralMixedRoadmapBadProbeFields.rightContext 3 z)=
        IntegralMixedAuxiliaryMarkedIntegerSource.number number (IntegralMixedRoadmapBadProbePacket.root (pairFst z))+
          8+IntegralMixedRoadmapBadProbePacket.count (pairFst z) :=
  IntegralMixedRoadmapBadProbeFields.right_count hn ht ha hR 3 z hc
example (q :List Bool) :IntegralMixedAuxiliaryMarkedIntegerSource.number number
    (IntegralMixedRoadmapBadProbePacket.root q)+8=8 :=rfl

section General
variable {n :List Bool→ℕ} {t :List Bool→Term} (hN :UnaryFn n)
  (hT :(fun q=>(t q).toData.toBits)∈FP) (hA :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hRadius :BinaryFn R)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hN hT hA hRadius false
example (root a b w :List Bool) (hv :SquareSampleCompleteVertices.Valid S (pair root a) w) :
    SquareSampleCompleteVertices.Valid S (pair root b) w :=
  (IntegralMixedPhysicalMarkedContext.valid_iff hN hT hA hRadius _ _ w
    (by rw [pairFst_pair,pairFst_pair])).mp hv
example (root a b w :List Bool)
    (hv :SquareSampleCompleteVertices.Valid S (pair root a) w)
    (hd :SquareSampleCompleteVertices.Valid S (pair root b) w) (i :ℕ) :
    IntegralMixedPhysicalFieldEquality.point hN hT hA hRadius (pair root a) w hv i=
      IntegralMixedPhysicalFieldEquality.point hN hT hA hRadius (pair root b) w hd i :=
  IntegralMixedPhysicalMarkedContext.point_eq hN hT hA hRadius _ _ w
    (by rw [pairFst_pair,pairFst_pair]) hv hd i
example (c d w :List Bool) (hc :pairFst c=pairFst d)
    (hv :SquareSampleCompleteVertices.Valid S c w) (hd :SquareSampleCompleteVertices.Valid S d w) :
    IntegralFramedPhysicalSquareContext.naturalValue S c w hv=
      IntegralFramedPhysicalSquareContext.naturalValue S d w hd :=by
  have HE:=IntegralMixedPhysicalMarkedContext.natural_eq hN hT hA hRadius c d w hc hv hd
  exact HE
example (d initial :ℕ) (z w :List Bool) (hc :0<IntegralMixedRoadmapBadProbePacket.count (pairFst z))
    (hi :initial=(IntegralMixedPhysicalMarkedPlan.bank hN hT hA hRadius false).parameters.ambient
      (IntegralMixedRoadmapBadProbePacket.root (pairFst z))+5)
    (hL :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapBadProbeFields.leftContext (pairFst z))
      (IntegralMixedRoadmapBadProbePacket.word (pairFst z)))
    (hR' :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapBadProbeFields.rightContext d z) w) :
    IntegralMixedRoadmapBadProbeFields.packet d initial z w∈
        IntegralMixedPhysicalFieldEqualityList.language hN hT hA hRadius ↔
      ∀i<creating initial (pairFst z),IntegralMixedPhysicalFieldEquality.point hN hT hA hRadius
        (IntegralMixedRoadmapBadProbeFields.leftContext (pairFst z))
        (IntegralMixedRoadmapBadProbePacket.word (pairFst z)) hL i=
      IntegralMixedPhysicalFieldEquality.point hN hT hA hRadius
        (IntegralMixedRoadmapBadProbeFields.rightContext d z) w hR' i :=
  IntegralMixedRoadmapBadProbeFields.packet_iff hN hT hA hRadius d initial z w hc hi hL hR'
end General

-- The list comparison retains signed, nonunit quotients; no modular division.
example :((-12:ℝ)/(-6))=2 ∧ ((18:ℝ)/(-6))=-3 :=by norm_num
example :((-6:ℤ):ZMod 6)=0 ∧ ((-4:ℤ):ZMod 6)=2 :=by decide
private noncomputable def p :Polynomial ℝ:=Polynomial.C (-6)*(Polynomial.X-Polynomial.C 2)^2*
  (Polynomial.X+Polynomial.C 1)^2
example :p.eval 2=0 ∧ p.eval (-1)=0 :=by norm_num [p]
example :ThomEncoding.sign p 2 0=ThomEncoding.sign p (-1) 0 :=by norm_num [ThomEncoding.sign,p]
example :ThomEncoding.sign p 2 3≠ThomEncoding.sign p (-1) 3 :=by
  norm_num [ThomEncoding.sign,p,Function.iterate_succ_apply,Polynomial.derivative_mul,Polynomial.derivative_pow]

#print axioms IntegralMixedRoadmapBadProbeFields.counts
#print axioms IntegralMixedRoadmapBadProbeFields.packet_iff
#print axioms IntegralFramedPhysicalPrefixPoint.point_cons
#print axioms IntegralFramedPhysicalPrefixPoint.point_drop_one
#print axioms IntegralFramedPhysicalPrefixPoint.full_point
#print axioms IntegralMixedPhysicalMarkedContext.input_factor
#print axioms IntegralMixedPhysicalMarkedContext.valid_iff
#print axioms IntegralMixedPhysicalMarkedContext.natural_eq
#print axioms IntegralMixedPhysicalMarkedContext.pointNewest_eq
#print axioms IntegralMixedPhysicalMarkedContext.point_eq
#print axioms IntegralMixedMarkedPrefixFieldReadback.terminal_commands
#print axioms IntegralMixedMarkedPrefixFieldReadback.full_value
#print axioms IntegralMixedMarkedPrefixFieldReadback.parent_value
#print axioms IntegralMixedMarkedPrefixFieldReadback.parent_chronological
#print axioms IntegralMixedMarkedPrefixFieldReadback.packet_parent_iff
end BadProbeFieldRegression
end RoadmapInternalOldFields

namespace RoadmapInternalProperLevel
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFullHistoryScript Set
open scoped Classical
noncomputable section
namespace ChronologicalOneLevelRegression
private def d : Descriptor 4 5:=⟨[0,3],by decide⟩
private theorem hk : d.labels.length<5:=by decide
private def g : Fin 5:=3
private theorem hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen:=by
  exact (IntegralMixedChronologicalSweepFrame.free_iff d hk g).mpr (by decide)
private def u : Fin 5:=4
private def v : Fin 5:=1

-- The native capture words are chronological coordinate4 then3, without an alias.
example (a b : ℕ) : IntegralMixedChronologicalMidpointCompanionCode.codes 4
    (IntegralMixedChronologicalFrameCode.labels d) a b 3=
      [IntegralMixedChronologicalMidpointCode.code 4 (IntegralMixedChronologicalFrameCode.labels d) a b 3 4,
       IntegralMixedChronologicalMidpointCode.code 4 (IntegralMixedChronologicalFrameCode.labels d) a b 3 3]:=by
  unfold IntegralMixedChronologicalMidpointCompanionCode.codes
  rw [IntegralMixedChronologicalFrameCode.labels_count]
  rfl
example (a : ℕ) : IntegralMixedChronologicalCompanionCode.codes 4
    (IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d) a) 3=
      [IntegralMixedChronologicalFrameCode.code 4
        (IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d) a) 3 4,
       IntegralMixedChronologicalFrameCode.code 4
        (IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d) a) 3 3]:=by
  unfold IntegralMixedChronologicalCompanionCode.codes
  rw [IntegralMixedChronologicalEndpointCode.append_count,IntegralMixedChronologicalFrameCode.labels_count]
  rfl

section ActualLevel
variable {S B : ℕ} {P : SpatialSource 4} {ι : Type} [Fintype ι]
variable {x : State P S B 5 ι} {z : ι→ℝ} {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
  {values : Fin 5→ℝ} {left right : Endpoint 5}
  {hn : 0<4} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap 5 P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap)

example : (R.orderedFree hk).length=2:=R.orderedFree_length hk
example : ((R.orderedFree hk).get ⟨0,by rw [R.orderedFree_length];decide⟩).val.val=3:=
  R.orderedFree_get hk _
example : ((R.orderedFree hk).get ⟨1,by rw [R.orderedFree_length];decide⟩).val.val=4:=
  R.orderedFree_get hk _
example (side : Bool) : IntegralMixedChronologicalFrameCode.labels (R.childFrameDescriptor hk 2 side)=
    IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1):=
  R.childFrameDescriptor_labels hk 2 side
example (side : Bool) : R.result.endpointFrame (IntegralMixedChronologicalSweepFrame.next d hk) 2 side=
    (R.childFrameDescriptor hk 2 side).frame:=R.endpointFrame_eq hk 2 side
example (side : Bool) :
    WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled 4 (R.levelPacket side):=
  R.levelWord_compiled hk g hg (by rfl) side
example (side : Bool) : IntegralMixedRoadmapLevel.Checked 4 B
    (IntegralMixedExceptionalBounds.auxiliaryCap 5 P.degree) 5 (R.levelRecord side):=
  R.levelRecord_checked side (by decide)
example (side : Bool) : WordList.encode (R.levelCodes hk g hg side).reverse=
    IntegralMixedRoadmapLevel.slice (R.levelRecord side):=R.levelRecord_word hk g hg (by rfl) side
example (side : Bool) (room : 5+(R.levelCommands hk g hg side).length≤S+1) :
    Decodes x hn hcap (R.levelCommands hk g hg side) room (R.levelCodes hk g hg side):=
  R.level_decodes hk g hg side room
example (side : Bool) : (R.levelCommands hk g hg side).length=
    IntegralMixedRoadmapLevel.emittedCount 4 (R.levelPacket side):=R.levelCount_native hk g hg side

example (RR : NativePair x d z φ values (.retained u) (.retained v) hn hcap) (side : Bool) :
    (RR.levelCommands hk g hg side).length=6:=RR.level_length_original hk g hg side
example (b : ℝ) (RR : NativePair x d z φ values (.retained u) (.fresh b) hn hcap) (side : Bool) :
    (RR.levelCommands hk g hg side).length=7:=RR.level_length_original hk g hg side
example (a b : ℝ) (RR : NativePair x d z φ values (.fresh a) (.fresh b) hn hcap) (side : Bool) :
    (RR.levelCommands hk g hg side).length=8:=RR.level_length_original hk g hg side
example (RR : NativePair x d z φ values (.retained u) (.retained v) hn hcap) :
    (RR.result.endpointIndex 2 true).val=4:=by
  have HC : RR.result.commands.length=0:=RR.count
  have HI:=RR.result.endpointIndex_val 2 true
  have HR:=RR.right_reference
  have HP:=RR.right_producer
  change IntegralMixedRoadmapEndpointSyntax.field RR.rightSpec 1=3 at HP
  simp only [ite_true] at HI
  omega

end ActualLevel

#print axioms atom_value_injective
#print axioms atomic_atom
#print axioms midpoint_rows
#print axioms midpoint_data_code
#print axioms captured_frame
#print axioms freeze_atom
#print axioms endpoint_rows
#print axioms endpoint_data_code
#print axioms endpoint_frame
#print axioms index_append
#print axioms IntegralMixedOptionalEndpoints.step_heq
#print axioms continueRun_append
#print axioms Decodes.append
#print axioms Decodes.prepend_critical
#print axioms Decodes.congr_start
#print axioms continueRun_heq
#print axioms continueRun_list_heq
#print axioms IntegralMixedPointCompanion.original_code_of_rows
#print axioms IntegralMixedPointCompanion.codes_shift
#print axioms IntegralMixedPointCompanion.ordered_codes
#print axioms IntegralMixedPointCompanion.decoded_decodes
#print axioms IntegralMixedPointCompanion.decodes_append
#print axioms NativePair.childFrameDescriptor_labels
#print axioms NativePair.endpointFrame_eq
#print axioms NativePair.orderedFree_get
#print axioms NativePair.levelCodes_compiled
#print axioms NativePair.levelWord_compiled
#print axioms NativePair.exists_matched_level_captures
#print axioms NativePair.levelCommands_length
#print axioms NativePair.levelCount_native
#print axioms NativePair.level_decodes
#print axioms NativePair.level_run_heq
#print axioms NativePair.exists_proper_level
#print axioms NativePair.levelRecord_checked
end ChronologicalOneLevelRegression
end
end RoadmapInternalProperLevel

namespace RoadmapInternalSlabPaths
open LeanCanny LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Geometry Set
open ComponentSlabCover ComponentSlabCover.InteriorData
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedOptionalEndpoints
open scoped Classical
noncomputable section
namespace MatchedEndpointPathsRegression
private def projection (i : Fin 2) : ℝ:=i.val
private def noBranches : InteriorData projection 0 1 Empty where
  piece j:=nomatch j
  closed j:=nomatch j
  cover x:=by
    rcases x with ⟨i,hi⟩
    fin_cases i <;> norm_num [projection] at hi
  paths j:=nomatch j
  arc j:=nomatch j
  continuous_arc j:=nomatch j
  arc_mem j:=nomatch j
  level_left j:=nomatch j
  level_right j:=nomatch j
  limit_left j:=nomatch j
  limit_right j:=nomatch j

private theorem step_eq {i j : Fin 2} (H : noBranches.EndpointStep i j) : i=j:=by
  cases H with
  | left H=>
    have hi:=H.source_mem
    have hj:=H.target_mem
    fin_cases i <;> fin_cases j <;> norm_num [projection] at *
  | right H=>
    have hi:=H.source_mem
    have hj:=H.target_mem
    fin_cases i <;> fin_cases j <;> norm_num [projection] at *
  | forward j=>nomatch j
  | backward j=>nomatch j

private theorem reach_eq {i j : Fin 2} (H : noBranches.EndpointReach i j) : i=j:=by
  induction H with
  | refl=>rfl
  | tail H h IH=>exact IH.trans (step_eq h)

example : ¬noBranches.EndpointReach 0 1:=by
  intro H
  exact (by decide : (0 : Fin 2)≠1) (reach_eq H)

example : noBranches.EndpointReach 0 0:=.refl
example : noBranches.EndpointReach 1 1:=.refl

section Branch
variable {X J : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}
  (D : InteriorData p a b J) (hab : a<b) (j : J)
example : D.EndpointReach (D.arc j a) (D.arc j b):=.single (.forward j)
example : D.EndpointReach (D.arc j b) (D.arc j a):=.single (.backward j)
example : JoinedIn (p ⁻¹' Icc a b) (D.arc j a) (D.arc j b):=
  D.endpointStep_joined hab (.forward j)
example {u v : X} (H : JoinedIn (p ⁻¹' {a}) u v) : D.EndpointReach u v:=.single (.left H)
example {u v : X} (H : JoinedIn (p ⁻¹' {b}) u v) : D.EndpointReach u v:=.single (.right H)
example {u v : X} (H : D.EndpointReach u v) : D.EndpointReach v u:=D.endpointReach_symm H
end Branch

example : noBranches.endpointSupport 0 1=univ:=by
  ext i
  fin_cases i <;> simp [endpointSupport]
example : (noBranches.endpointSupport 0 1).Finite:=
  noBranches.endpointSupport_finite 0 1
example : ¬noBranches.AtomicEndpointReach (noBranches.endpointSupport 0 1)
    ⟨0,mem_insert _ _⟩ ⟨1,mem_insert_of_mem _ (mem_insert _ _)⟩:=by
  intro H
  have HE:=H.lift Subtype.val (fun _ _ h=>h)
  exact (by decide : (0 : Fin 2)≠1) (reach_eq HE)

section Normalization
variable {X J : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}
  (D : InteriorData p a b J) (hab : a<b) (j : J)
example : D.AtomicEndpointReach (D.endpointSupport (D.arc j a) (D.arc j b))
    ⟨D.arc j a,mem_insert _ _⟩ ⟨D.arc j b,mem_insert_of_mem _ (mem_insert _ _)⟩:=by
  exact (D.endpointReach_support hab (Or.inr (D.level_right j))).mp (.single (.forward j))
example [Finite J] (u v : X) : (D.endpointSupport u v).Finite:=D.endpointSupport_finite u v
example {K : Set X} {u v w : K} (H : D.FiberLink u.val v.val) (G : D.FiberLink v.val w.val) :
    D.AtomicEndpointReach K u w:=D.atomicEndpointReach_of_fiberLink (D.fiberLink_trans hab H G)
end Normalization

#print axioms endpointStep_symm
#print axioms endpointReach_symm
#print axioms endpointStep_joined
#print axioms endpointReach_joined
#print axioms endpoint_joined_iff_reach
#print axioms PairResult.exists_endpoint_cover
#print axioms PairResult.matched_endpoint_paths
#print axioms closed_slab_image
#print axioms PairResult.matched_endpoint_paths_raw
#print axioms fiberLink_trans
#print axioms endpointReach_atomic
#print axioms atomicEndpointReach_iff
#print axioms endpointSupport_finite
#print axioms endpointReach_support
#print axioms PairResult.matched_atomic_paths
end MatchedEndpointPathsRegression
end
end RoadmapInternalSlabPaths

namespace RoadmapInternalDegenerateLevel
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints Set
open scoped Classical
noncomputable section
namespace ChronologicalDegenerateLevelRegression
private def d : Descriptor 2 1:=⟨[],by decide⟩
private theorem hk : d.labels.length<3:=by decide
private def h : Fin 3:=IntegralMixedChronologicalSweepFrame.next d hk
private def g : Fin 3:=1
private theorem hg : g∉(line d.frame h).frozen:=by
  exact (IntegralMixedChronologicalSweepFrame.free_iff d hk g).mpr (by decide)
private def sphere : SpatialSource 2 where
  low:=MvPolynomial.C (-(2^18))
  leading:=1
  degree:=BoundedZeroSource.powerDegree 0
  degree_two:=by decide
  low_degree:=by rw [MvPolynomial.totalDegree_C];decide
  leading_ne_zero:=by decide
private def point (i : Fin 3) : ℝ:=if i=0 then 2 else 0
private def old : Fin 1→ℝ:=fun _=>2
private theorem source_root :
    (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree).eval₂
      (Int.castRingHom ℝ) point=0:=by
  norm_num [sphere,BoundedZeroSource.powerDegree,BoundedZeroSource.powerHalfDegree,BoundedZeroSource.degreeAllowance,
    point,FermatCriticalHomogenization.polynomial,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
private theorem source_member : point∈slice sphere d.frame old:=by
  apply (d.slice_iff sphere old point).mpr
  exact ⟨source_root,fun i=>Fin.elim0 i⟩
private theorem gradient_eval (i : Fin 3) :
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=18*point i^17:=by
  change ((MvPolynomial.pderiv i) (FermatCriticalHomogenization.polynomial (MvPolynomial.C (-(2^18))) 1 18)).eval₂
    (Int.castRingHom ℝ) point=18*point i^17
  rw [FermatCriticalHomogenization.pderiv_polynomial,MvPolynomial.pderiv_C]
  norm_num [MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
private theorem parent_critical : ∀i,i∉d.frame.frozen→i≠h→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0:=by
  intro i _ hi
  fin_cases i
  · exact (hi rfl).elim
  · exact (gradient_eval 1).trans (by norm_num [point])
  · exact (gradient_eval 2).trans (by norm_num [point])

example : Ioo (old 0) (old 0)=∅:=Ioo_self _
example : point h=(.retained (0 : Fin 1) : Endpoint 1).value old:=rfl
example :
    (MvPolynomial.pderiv (1 : Fin 3) (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0:= (gradient_eval 1).trans (by norm_num [point])

variable {S B : ℕ} {ι : Type} [Fintype ι] {x : State sphere S B 1 ι} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {hn : 0<2}
  {hcap : IntegralMixedExceptionalBounds.auxiliaryCap 3 sphere.degree≤2^B}
variable (R : NativePair x d z φ old (.retained 0) (.retained 0) hn hcap)

-- SAME actual singular boundary point, with no M or Near input.
example (room : 1+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1) :=
  R.exists_degenerate_level hk g hg 0 rfl (by rfl) point source_member rfl parent_critical room
example (side : Bool) : (R.levelCommands hk g hg side).length=6:=R.level_length_original hk g hg side
example (side : Bool) : IntegralMixedChronologicalFrameCode.labels (R.childFrameDescriptor hk 2 side)=
    IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1):=
  R.childFrameDescriptor_labels hk 2 side

#print axioms NativePair.exists_degenerate_level
#print axioms critical_after_freezing
#print axioms NativePair.level_decodes
#print axioms NativePair.level_run_heq
#print axioms NativePair.levelWord_compiled
end ChronologicalDegenerateLevelRegression
end
end RoadmapInternalDegenerateLevel

namespace RoadmapInternalRetainedSweep
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame Set
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
variable (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice P F values).Nonempty)

-- Distinct retained values force a genuine ordered sweep, even when neither
-- value is a member of the original bad/critical set.
example (i j : Fin m) (hij : values i≠values j) :
    ∃N : ℕ,∃cut : Fin (N+2)→ℝ,StrictMono cut ∧
      (∀r,∃a,cut a=values r) ∧
      ∀y∈slice P F values,∃a : Fin (N+1),y h∈Icc (cut a.castSucc) (cut a.succ) :=by
  rcases retained_sweep_cases x hm φ F h hh HF g hg values H c hp hne with
    ⟨a,_,HV,_⟩|⟨N,cut,HM,_,HV,HC,_⟩
  · exact False.elim (hij ((HV i).trans (HV j).symm))
  · exact ⟨N,cut,HM,HV,HC⟩

-- Every proper subslab avoids each old value, not just the exceptional set.
example : (∃a,∀r,values r=a) ∨
    ∃N : ℕ,∃cut : Fin (N+2)→ℝ,StrictMono cut ∧
      ∀a : Fin (N+1),∀t∈Ioo (cut a.castSucc) (cut a.succ),∀r,t≠values r :=by
  rcases retained_sweep_cases x hm φ F h hh HF g hg values H c hp hne with
    ⟨a,_,HV,_⟩|⟨N,cut,HM,_,_,_,HA⟩
  · exact Or.inl ⟨a,HV⟩
  · exact Or.inr ⟨N,cut,HM,fun a t ht=>(HA a t ht).2.2⟩

#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.retained_sweep_cases
end RoadmapInternalRetainedSweep

namespace RoadmapInternalPreparedProbe
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open IntegralMixedMarkedPrefixRun (reservedRoot)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PreparedProbeRegression
private def Q : SpatialSource 1 where
 low:=-1
 leading:=-2
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
private def width:=(PurePowerReductionBounds.dimension 2 Q.degree).size
private theorem cap : PurePowerReductionBounds.dimension 2 Q.degree≤2^width:=Nat.le_of_lt (Nat.lt_size_self _)
private def integer : Instruction 1 width:=⟨Q,cap,.integer Polynomial.X (by simp)
 (by simpa only [Polynomial.natDegree_X] using (show 1≤2^width from Nat.one_le_two_pow))⟩
private def critical : Instruction 1 width:=IntegralMixedCanonicalPaddingSeed.instruction Q cap
private def r : IntegralMixedCriticalSweep.Rule 1 where
 critical:={
  offset:=⟨1,by decide⟩
  objective:=0
  coordinate:=0
  scales _:=1
  scales_ne_zero _:=one_ne_zero
  heights _:=.constant 0}
 height:=⟨0,by decide⟩
 height_frozen:=by decide
 slope:=1
 slope_ne_zero:=one_ne_zero
private def cut : Instruction 1 width:=⟨Q,cap,.cut r (.coordinate ⟨0,by decide⟩ ⟨0,by decide⟩)
 0 (Nat.zero_le _) (Nat.zero_le _)⟩
-- The replaced last record can change the full physical arity.
example : IntegralMixedFramedPhysicalIndex.arity [critical,integer]=7:=rfl
example : IntegralMixedFramedPhysicalIndex.arity [cut,integer]=2:=rfl
example : IntegralMixedFramedPhysicalIndex.arity ([critical,integer].drop 1)=
 IntegralMixedFramedPhysicalIndex.arity ([cut,integer].drop 1):=rfl
example (v : ℕ→ℝ) : IntegralFramedPaddedCutVertex.values v 0=0:=rfl
example (v : ℕ→ℝ) : IntegralFramedPaddedCutVertex.values v 5=v 4:=rfl
private def observation :IntegralMixedFramedRunObservation.Data:=
 ⟨⟨4,2,1,fun _=>-6⟩,1,fun i=>if i=0 then MvPolynomial.X 7-1 else 0,fun _=>7⟩
example : observation.Roots (fun _=>1):=by intro i;by_cases hi:i=0 <;>simp [observation,hi]
example : observation.point (fun _=>1) 0=-(1/6:ℝ):=by
 dsimp only [observation,IntegralMixedFramedRunObservation.Data.point,IntegralMixedFramedBankObservation.Data.point]
 norm_num
example : observation.point (fun _=>1) 9=0:=by
 norm_num [observation,IntegralMixedFramedRunObservation.Data.point,IntegralMixedFramedBankObservation.Data.point]
example : (-6:ℤ)%6=0:=by decide
example (old probe aux :List Bool) (codes :List (List Bool)) :
 IntegralMixedCausalRecordPlanBits.count (reservedRoot old codes probe aux)=codes.length+1:=
 IntegralMixedMarkedPrefixRun.reserved_count old codes probe aux
example (old probe aux :List Bool) (codes :List (List Bool)) :
 pairFst (IntegralMixedMarkedReservedVertex.parent (n:=fun _=>2) old codes probe aux)=reservedRoot old codes probe aux:=
 IntegralMixedMarkedReservedVertex.parent_root old codes probe aux
section Generic
variable (P :Parameters) (D :Plan P) (root :List Bool) (m :ℕ) (hb:m≤P.cap root+1) (z:ℕ→ℝ)
 (hz:(IntegralFramedPhysicalPrefixObservation.atRoot P D root m hb).Roots z)
example :IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.runAt P D root m hb)
 ((IntegralFramedPhysicalPrefixObservation.atRoot P D root m hb).point z):=
 IntegralFramedPhysicalPrefixObservation.at_realizes P D root m hb z hz
end Generic
section Actual
variable {n:List Bool→ℕ} {t:List Bool→ETR.Term} (hn:UnaryFn n)
 (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q) {R0:List Bool→ℕ} (hR0:BinaryFn R0)
 (old:List Bool) (codes:List (List Bool)) (oldProbe oldAux probe aux w:List Bool)
 (hv:SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes oldProbe oldAux)) w)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
 IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point
 IntegralMixedFramedHistoryFamilyBits.family
example :IntegralMixedIntegerRealization.Realizes
 (IntegralMixedFramedFamilyRunView.stateView (B).parameters (B).plan (B).data
   (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))
 (IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes oldProbe oldAux w hv):=
 IntegralMixedMarkedReservedParent.prepared_canonical_realizes hn ht ha hR0 old codes oldProbe oldAux w hv probe aux []
variable (d:IntegralMixedCutRecordConstructor.Data
 ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient
   (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux)))
 (number n (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))+8+codes.length))
 (tag:IntegralMixedCausalRecordBits.Tag) (choice degree:ℕ)
 (hd:degree≤IntegralMixedExceptionalBounds.auxiliaryCap
   ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient
     (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))+1)
   (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0
     (pairFst (IntegralMixedMarkedReservedVertex.parent (n:=n) old codes probe aux))).degree)
 (hc:probe=d.code tag choice degree)
include hv hd hc in
example :∃w',SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
 (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w':=by
 have H:=IntegralMixedMarkedReservedVertex.exists_vertex hn ht ha hR0
   old codes oldProbe oldAux probe aux w hv d tag choice degree hd hc
 exact Exists.elim H (fun word Hword=>Exists.elim Hword (fun hword _=>⟨word,hword⟩))
end Actual
#print axioms IntegralFramedPhysicalPrefixObservation.at_congr
#print axioms IntegralFramedPhysicalPrefixObservation.at_roots
#print axioms IntegralFramedPhysicalPrefixObservation.at_realizes
#print axioms IntegralFramedPhysicalPrefixObservation.raw_tuple
#print axioms IntegralFramedPhysicalPrefixObservation.roots
#print axioms IntegralMixedMarkedReservedParent.base_roots
#print axioms IntegralMixedMarkedReservedParent.prepared_realizes
#print axioms IntegralMixedMarkedReservedParent.prepared_canonical_realizes
#print axioms IntegralMixedReservedCutActualVertex.vertex_from_full_run
#print axioms IntegralMixedReservedCutActualVertex.run_realizes
#print axioms IntegralMixedReservedCutActualVertex.exists_vertex
#print axioms IntegralMixedMarkedReservedCutView.plan_eq
#print axioms IntegralMixedMarkedReservedCutView.state_realizes
#print axioms IntegralMixedMarkedReservedCutView.full_realizes
#print axioms IntegralMixedMarkedReservedCutView.strict_margin
#print axioms IntegralMixedMarkedReservedVertex.parent_prefix
#print axioms IntegralMixedMarkedReservedVertex.table_at_parent
#print axioms IntegralMixedMarkedReservedVertex.exists_vertex
end PreparedProbeRegression
end
end RoadmapInternalPreparedProbe

namespace RoadmapInternalChainConstruction
open LeanCanny LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedRoadmapChain
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

example : Checked 2 4 8 8 5 (completePayload 2 [] (seedCode 2)) :=
  complete_seed_checked 2 4 8 8 5 (by decide) (by decide)
example : WordListRecords.count (raw (completePayload 2 [] (seedCode 2)))=23 :=by
  have H:=(complete_seed_checked 2 4 8 8 5 (by decide) (by decide)).2.2.2.2.2.2.1
  simpa only [IntegralMixedRoadmapRecordChain.probedRecordBound,IntegralMixedRoadmapRecordChain.recordBound] using H
example (n : ℕ) (q : List Bool) (i : ℕ) (hi : i<depth q) :
    IntegralMixedRoadmapLevel.rawSlice (compiled n q) (rawStart n q i) (blockCount n q i)=
      IntegralMixedRoadmapLevel.compiled n (template q i) :=compiled_level_slice n q i hi
example (n : ℕ) (q : List Bool) (i : ℕ) (hi : i<depth q) :
    rawStart n q i+blockCount n q i≤WordListRecords.count (compiled n q) :=compiled_level_fits n q i hi
example (n : ℕ) (m p : List Bool) : raw (completePayload n m p)=compiled n (completePayload n m p) :=
  completePayload_raw n m p
example (n : ℕ) (m p : List Bool) : metadata (completePayload n m p)=m :=completePayload_metadata n m p
example (n : ℕ) (m p : List Bool) : probe (completePayload n m p)=p :=completePayload_probe n m p

#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.compiledCodes_split
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.compiled_level_slice
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.compiled_level_fits
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.checked_of_compiled
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.completePayload_checked
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.complete_seed_checked

example (n : ℕ) (q l r : List Bool) (s : Bool) (p : List Bool) :
    depth (appendPayload n q l r s p)=depth q+1 :=append_depth n q l r s p
example (n : ℕ) (q l r : List Bool) (s : Bool) (p : List Bool) :
    frozen (appendPayload n q l r s p) (depth q)=frozen q (depth q) :=
  append_frozen_before n q l r s p (depth q) (Nat.le_refl _)
example {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (l r : List Bool) (s : Bool) (p : List Bool)
    (hd : depth q<n)
    (hnew : IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial q (depth q))
      (IntegralMixedRoadmapLevel.packet (frozen q (depth q)) l r s []))
    (hp : p.length≤IntegralMixedRoadmapRecordChain.codeBound n initial C) :
    Checked n B sourceCap initial C (appendPayload n q l r s p) :=append_checked hq l r s p hd hnew hp
example {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (l r : List Bool) (s : Bool) (p : List Bool)
    (i : ℕ) (hi : i<rawStart n q (depth q)) :
    WordList.get (raw (appendPayload n q l r s p)) i=WordList.get (raw q) i :=
  append_raw_before hq l r s p i hi
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.append_depth
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.append_frozen_before
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.append_template_last
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.append_checked
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.compiled_prefix_lookup
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.append_raw_before
end RoadmapInternalChainConstruction

namespace RoadmapInternalAtomicVertex
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapAtomic
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace AtomicVertexRegression
private def retained (i :ℕ):=IntegralMixedRoadmapEndpointSyntax.spec 0 i 0 0 0 0
private def fresh :=IntegralMixedRoadmapEndpointSyntax.spec 1 12 0 0 0 0
private def history (l r :List Bool):=IntegralMixedRoadmapChain.packet
  (WordList.encode [WordList.encode [l,r,[]]]) [] []
private def vertex (l r :List Bool):=packet (pair [] []) (history l r) []
private def seed :=packet (pair [] []) (IntegralMixedRoadmapChain.packet [] [] []) []
private theorem count_nil :WordListRecords.count ([]:List Bool)=0:=WordListRecords.count_encode []
private theorem zero_bits :Nat.fromBitsLE []=0:=rfl
private theorem one_bits :Nat.fromBitsLE [true]=1:=rfl

macro "read_atomic" : tactic => `(tactic| norm_num [seed,vertex,history,retained,fresh,anchor,endBirth,first,free,depth,frozen,signature,
  IntegralMixedRoadmapChain.rawStart,IntegralMixedRoadmapChain.prefixCount,IntegralMixedRoadmapChain.blockCount,
  IntegralMixedRoadmapChain.freshCount,IntegralMixedRoadmapChain.depth,IntegralMixedRoadmapChain.metadata,
  IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,IntegralMixedRoadmapChain.entry,IntegralMixedRoadmapChain.sideWord,
  IntegralMixedRoadmapChain.chosen,IntegralMixedRoadmapChain.frozen,IntegralMixedRoadmapChain.packet,
  IntegralMixedRoadmapEndpointSyntax.fresh,IntegralMixedRoadmapEndpointSyntax.field,IntegralMixedRoadmapEndpointSyntax.spec,
  IntegralMixedChronologicalPointSignatureCode.code,IntegralMixedChronologicalPointSignatureCode.producer,
  payload,packet,pairFst_pair,pairSnd_pair,WordList.get_encode,WordListRecords.count_encode,
  BinaryNatCode.encode,Nat.fromBitsLE_bits,zero_bits,one_bits,count_nil])

private theorem not_canonical_nil :¬Canonical ([]:List Bool) :=by
  intro h
  have HE:=congrArg List.length h.1
  simp only [List.length_nil,packet,pair_length] at HE
  omega

example :depth seed=0 :=by read_atomic
example :anchor 2 8 seed=8 ∧ first 2 8 seed=9 ∧ free 2 seed=3 :=by read_atomic
example :depth (vertex (retained 0) (retained 1))=1 :=by read_atomic
example :anchor 2 8 (vertex (retained 0) (retained 1))=15 ∧
    first 2 8 (vertex (retained 0) (retained 1))=16 ∧ free 2 (vertex (retained 0) (retained 1))=2 :=by read_atomic
example :endBirth 2 8 (vertex (retained 0) (retained 1))=18 :=by read_atomic
example :anchor 2 8 (vertex fresh (retained 1))=16 ∧
    endBirth 2 8 (vertex fresh (retained 1))=19 :=by read_atomic
example :anchor 2 8 (vertex fresh fresh)=17 ∧ endBirth 2 8 (vertex fresh fresh)=20 :=by read_atomic
example :frozen (vertex (retained 0) (retained 1))=WordList.encode [BinaryNatCode.encode 0] :=by read_atomic
example :Nat.fromBitsLE (WordList.get (signature 2 8 (vertex (retained 0) (retained 1))) 0)=0 :=by read_atomic
example :Nat.fromBitsLE (WordList.get (signature 2 8 (vertex (retained 0) (retained 1))) 1)=17 :=by read_atomic
example :Nat.fromBitsLE (WordList.get (signature 2 8 (vertex (retained 0) (retained 1))) 2)=16 :=by read_atomic
example :WordListRecords.count (signature 2 8 (vertex fresh fresh))=3:=signature_count _ _ _
example :¬Canonical ([]:List Bool) :=not_canonical_nil
example (c h w :List Bool) :
    candidate (packet c h w)=c ∧ payload (packet c h w)=h ∧ word (packet c h w)=w :=by
  simp only [candidate,payload,word,packet,pairFst_pair,pairSnd_pair,and_self]
example (n m :ℕ) (q :List Bool) (hd :depth q=0) :anchor n m q=m:=seed_anchor n m q hd
example (n m :ℕ) (q :List Bool) (hd :depth q≤n) :first n m q+free n q=endBirth n m q:=block_end n m q hd

private def number (_ :List Bool):ℕ:=0
private def term (_ :List Bool):Term:=.const 0
private def radius (_ :List Bool):ℕ:=0
private theorem hn :UnaryFn number:=UnaryFn.const 0
private theorem ht :(fun q=>(term q).toData.toBits)∈FP:=by
  simpa only [term] using constFn_mem_FP (Term.const (0:ℤ)).toData.toBits
private theorem ha :∀q,(term q).arity≤number q:=by intro q;change 0≤0;omega
private theorem hR :BinaryFn radius:=BinaryFn.const 0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

example :SpaceDecider (language hn ht ha hR):=decider hn ht ha hR
example :FPPred (Grammar hn ht ha hR):=grammar_FP hn ht ha hR
example :(fun q=>signature (dimension hn ht ha hR q) (initial hn ht ha hR q) q)∈FP:=native_signature hn ht ha hR
example :(fun q=>companionQuery (dimension hn ht ha hR q) (initial hn ht ha hR q) q)∈FP:=native_companionQuery hn ht ha hR
example (q :List Bool) :sourceCap hn ht ha hR q≤2^width hn ht ha hR q:=sourceCap_le hn ht ha hR q
example (q :List Bool) :dimension hn ht ha hR q=3 :=by simpa only [number] using dimension_eq hn ht ha hR q
example (q :List Bool) :initial hn ht ha hR q=8 :=by simpa only [number] using initial_eq hn ht ha hR q
example :¬Valid hn ht ha hR [] :=fun hv=>not_canonical_nil hv.1.1

-- The short malformed table fails even before any physical root is considered.
example :¬Valid hn ht ha hR seed :=by
  intro hv
  have HH:=raw_count hn ht ha hR seed hv
  have H0 :WordListRecords.count ([]:List Bool)=0:=WordListRecords.count_encode []
  simp only [seed,payload,packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.raw,
    IntegralMixedRoadmapChain.packet,H0] at HH
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound at HH
  omega

#print axioms child_anchor
#print axioms block_end
#print axioms native_signature
#print axioms grammar_FP
#print axioms sourceCap_le
#print axioms wordBudget_polynomial
#print axioms evaluator
#print axioms decider
#print axioms mem_PSPACE
#print axioms raw_count
#print axioms raw_byte_bound
#print axioms candidate_byte_bound
#print axioms context_byte_bound
#print axioms own_height_record
#print axioms point
#print axioms anchor_active
#print axioms companions
#print axioms own_height_point
end AtomicVertexRegression
end RoadmapInternalAtomicVertex

namespace RoadmapInternalPrefixTransfer
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
variable (base w : List Bool) (hv : SquareSampleCompleteVertices.Valid
  (IntegralMixedMarkedReservedParent.input hn ht ha hR0) (IntegralMixedMarkedReservedParent.context base) w)

-- No earlier sampled word or interpretation is supplied, even at prefix zero.
example (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count base) :
    ∃z : ℕ→ℝ,(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base j hj).Roots z :=
  ⟨IntegralMixedMarkedPrefixTransfer.tuple hn ht ha hR0 base w hv,
    IntegralMixedMarkedPrefixTransfer.base_roots hn ht ha hR0 base w hv j hj⟩
example : ∃z : ℕ→ℝ,(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base 0 (Nat.zero_le _)).Roots z :=
  ⟨IntegralMixedMarkedPrefixTransfer.tuple hn ht ha hR0 base w hv,
    IntegralMixedMarkedPrefixTransfer.base_roots hn ht ha hR0 base w hv 0 (Nat.zero_le _)⟩

example (c q : List Bool) : IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixTransfer.chainRoot c q)=
    WordListRecords.count (IntegralMixedRoadmapChain.raw q) :=IntegralMixedMarkedPrefixTransfer.chainRoot_count c q
example (c q : List Bool) (i : ℕ) : IntegralMixedCausalRecordPlanBits.code (IntegralMixedMarkedPrefixTransfer.chainRoot c q) i=
    WordList.get (IntegralMixedRoadmapChain.raw q) i :=IntegralMixedMarkedPrefixTransfer.chainRoot_code c q i
example {dim scalar sourceCap initial budget : ℕ} {q : List Bool}
    (hq : IntegralMixedRoadmapChain.Checked dim scalar sourceCap initial budget q) (c : List Bool) :
    IntegralMixedRoadmapChain.rawStart dim q (IntegralMixedRoadmapChain.depth q)≤
      IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixTransfer.chainRoot c q) :=
  IntegralMixedMarkedPrefixTransfer.chain_prefix_good hq c

#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.fit
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.tuple
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.base_roots
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.transfer_realizes
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.transfer_canonical_realizes
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.chain_prefix_good
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer.appended_parent_realizes
end RoadmapInternalPrefixTransfer

namespace RoadmapInternalProperNative
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Encoding
open scoped Classical
noncomputable section
namespace RoadmapProperNativeRegression
private def frozen:=WordList.encode [BinaryNatCode.encode 0,BinaryNatCode.encode 3]
private def endpoint (producer : ℕ):=IntegralMixedRoadmapEndpointSyntax.spec 0 producer 0 0 0 0
private def level:=IntegralMixedRoadmapLevel.packet frozen (endpoint 2) (endpoint 1) false []
private theorem count : WordListRecords.count frozen=2:=by rfl
private theorem free : IntegralMixedRoadmapLevel.freeCount 4 level=2:=by rfl
private theorem left : IntegralMixedRoadmapLevel.freshLeft level=0:=by rfl
private theorem right : IntegralMixedRoadmapLevel.freshRight level=0:=by rfl

-- Both captures are read from the actual middle of the compiled level.
example : WordList.get (IntegralMixedRoadmapLevel.compiled 4 level) 1=
    IntegralMixedChronologicalMidpointCode.code 4 frozen 2 1 3 4 :=by
  exact IntegralMixedRoadmapCaptureRecords.level_mid_record 4 level 0 (by rw [free];decide)
example : WordList.get (IntegralMixedRoadmapLevel.compiled 4 level) 5=
    IntegralMixedChronologicalFrameCode.code 4 (IntegralMixedRoadmapLevel.childLabels level) 3 3 :=by
  exact IntegralMixedRoadmapCaptureRecords.level_child_record 4 level 1 (by rw [free];decide)

-- A false side keeps the left chronological producer; no midpoint alias is introduced.
example : IntegralMixedRoadmapLevel.chosen level=2:=by rfl
example : WordListRecords.count (IntegralMixedRoadmapLevel.childLabels level)=3:=by rfl
example : IntegralMixedRoadmapLevel.emittedCount 4 level=6:=by rfl
example : IntegralMixedRoadmapProperRow.coordinate (pair [] (BinaryNatCode.encode 4))=4:=by rfl

#print axioms IntegralMixedRoadmapCaptureRecords.checked_child_record
#print axioms IntegralMixedRoadmapCaptureRecords.checked_mid_record
#print axioms IntegralMixedRoadmapProper.badPacket_FP
#print axioms IntegralMixedRoadmapProperRow.code_FP
#print axioms IntegralMixedRoadmapProperRow.ordinaryData_code
#print axioms IntegralMixedRoadmapProperRow.meanData_code
#print axioms IntegralMixedRoadmapProperRow.near_decider
#print axioms IntegralMixedRoadmapProperRow.rank_decider
#print axioms IntegralMixedRoadmapProper.base_decider
#print axioms IntegralMixedRoadmapProper.midpoint_sound
#print axioms IntegralMixedRoadmapProperCritical.query_FP
#print axioms IntegralMixedRoadmapProperCritical.root_word
#print axioms IntegralMixedRoadmapProperCritical.noCritical_evaluator
#print axioms IntegralMixedRoadmapProperRowWitness.decider
#print axioms IntegralMixedRoadmapProperAllRows.decider
#print axioms IntegralMixedRoadmapProperMidSignature.decider
end RoadmapProperNativeRegression
end
end RoadmapInternalProperNative
