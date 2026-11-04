import LeanCanny.Connectivity.IntegralMixedRoadmapLocalPath
import LeanCanny.Connectivity.IntegralMixedRoadmapProperGeometry
import LeanCanny.Connectivity.IntegralMixedRoadmapSeedGeometry
import LeanCanny.Encoding.IntegralFramedPhysicalScalarPoint
import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
import LeanCanny.Encoding.IntegralMixedMarkedConstructedObservation
import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
import LeanCanny.Encoding.IntegralMixedPhysicalCriticalScanSemantics
import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
import LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuardComplete
import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics
import LeanCanny.Encoding.IntegralMixedRoadmapLocalCoordinates
import LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
import LeanCanny.Encoding.IntegralMixedRoadmapLocalFreeIndex
import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureReadback
import LeanCanny.Encoding.IntegralMixedRoadmapProperBadEndpoint
import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCriticalSound
import LeanCanny.Encoding.IntegralMixedRoadmapProperOrder
import LeanCanny.Encoding.IntegralMixedRoadmapProperProducerBounds
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowMeanRule
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowQuotients
import LeanCanny.Encoding.IntegralMixedRoadmapSeedAcceptance
import LeanCanny.Encoding.IntegralMixedRoadmapSeedFieldReadback
import LeanCanny.Encoding.IntegralMixedRoadmapSeedNoCut
import LeanCanny.Encoding.IntegralMixedRoadmapSeedPreludeReadback
import LeanCanny.Encoding.IntegralMixedRoadmapSeedScan
import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
import LeanCanny.Geometry.IntegralMixedGuardedProgramBirths
import Lean.Util.CollectAxioms
import LeanCanny.Algebra.IntegralMixedPrefixSnapshotRawBad
import LeanCanny.Connectivity
import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
import LeanCanny.Connectivity.IntegralMixedRoadmapGraphReachability
import LeanCanny.Encoding.IntegralMixedChosenLocalGuardReceipt
import LeanCanny.Encoding.IntegralMixedChronologicalEndpointSpec
import LeanCanny.Encoding.IntegralMixedMarkedMidpointReceipt
import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshotFamily
import LeanCanny.Encoding.IntegralMixedMarkedRecordContinuation
import LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
import LeanCanny.Encoding.IntegralMixedMarkedReservedRawRuling
import LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalMidpoint
import LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSignature
import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSize
import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCanonical
import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound
import LeanCanny.Encoding.IntegralMixedRoadmapChainRoom
import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
import LeanCanny.Encoding.IntegralMixedRoadmapChainTruncation
import LeanCanny.Encoding.IntegralMixedRoadmapEdge
import LeanCanny.Encoding.IntegralMixedRoadmapIdentityReadback
import LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
import LeanCanny.Encoding.IntegralMixedRoadmapMidpointRecord
import LeanCanny.Encoding.IntegralMixedRoadmapProperFieldReadback
import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointCaptures
import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointSource
import LeanCanny.Encoding.IntegralMixedRoadmapProperRankReadback
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowFields
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowInterpretation
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowRuling
import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSnapshot
import LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
import LeanCanny.Geometry.IntegralMixedChronologicalAtomicRealization
import LeanCanny.Geometry.IntegralMixedChronologicalGuardedPair
import LeanCanny.Geometry.IntegralMixedConstructedCriticalCorrelation
import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentCritical
import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentPaths
import LeanCanny.Geometry.IntegralMixedGuardedSeedProgram

/-! Actual bounded native graph algorithms and sampled geometric readback.
Native graph-path soundness and full canonical seed acceptance are checked;
global completeness and the original connectivity result remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapInternalTruncation
open LeanCanny LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open IntegralMixedRoadmapChain
example (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool) (hk : k≤depth q) :
    frozen (prefixPayload n q k p) k=frozen q k :=prefix_frozen n q k p hk
example {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (k : ℕ) (hk : k≤depth q) (p : List Bool)
    (hp : p.length≤IntegralMixedRoadmapRecordChain.codeBound n initial C) :
    Checked n B sourceCap initial C (prefixPayload n q k p) :=prefix_checked hq k hk p hp
example {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (k : ℕ) (hk : k≤depth q) (p : List Bool)
    (i : ℕ) (hi : i<rawStart n q k) :
    WordList.get (raw (prefixPayload n q k p)) i=WordList.get (raw q) i :=prefix_raw_before hq k hk p i hi
open IntegralMixedHistory IntegralMixedFrozenFrame
example {n k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) (hc : IsCompact (slice P F values))
    (z : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    ∃ y : Fin (n+1)→ℝ,y∈connectedComponentIn (slice P F values) z ∧
      ∀ i,i∉F.frozen→i≠h→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) y=0 :=exists_component_objective_critical P F values h hh hc z hz
example {n k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (hc : IsCompact (slice P F values))
    (z : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    ∃ y : Fin (n+1)→ℝ,y∈connectedComponentIn (slice P F values) z ∧
      y h∈realCriticalValues P (line F h) values h :=exists_component_critical_height P F values h hh HF hc z hz
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.prefix_checked
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.prefix_raw_before
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.exists_component_objective_critical
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.exists_component_critical_of_proper
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.exists_component_critical_height
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.regular_component_objective_critical
end
end RoadmapInternalTruncation

namespace RoadmapInternalHistoryCompletion
namespace HistoryCompletionRegression
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "V"=>IntegralMixedMarkedReservedCutView.plan hn ht ha hR0
local notation "Q"=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
 IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedSourceIntegerRecordAppend.plan
 IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point
 IntegralMixedFramedHistoryFamilyBits.family

variable (root : List Bool) (codes : List (List Bool)) (k : ℕ)
 (hcodes : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
   (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient root) [] 0 0)))

include hcodes in
example (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P V root (number n root+8+codes.length)
        (IntegralMixedSourceIntegerSeedTail.before_bound P (fun root=>number n root+8)
          (IntegralMixedMarkedReservedCutView.room hn ht ha hR0) root codes k hcodes)) v)
    (charge : ℕ) (hcharge : (Q root).degree=BoundedZeroSource.powerDegree charge)
    (p : Fin ((P).ambient root+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context root) w,
      w.length=SquareSampleCompleteVertices.width (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
        (IntegralMixedMarkedReservedParent.context root) ∧
      ∀i : Fin ((family P (B).plan (B).data).birth ((B).key (IntegralMixedMarkedReservedParent.context root))), k≤ i.val→
        IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive (IntegralMixedMarkedReservedParent.context root) w hw i=
            v (i.val-k) :=by
  have Hvertex:=IntegralMixedMarkedSeedTailVertex.exists_vertex hn ht ha hR0 root codes k hcodes v hv charge hcharge p hp hg
  exact Exists.elim Hvertex (fun w Hw=>Exists.elim Hw (fun hw Hrest=>
    ⟨w,hw,Hrest.1,fun i hi=>by
      simpa only [IntegralMixedCanonicalPadding.values,ite_eq_right (Nat.not_lt.mpr hi)] using Hrest.2 i⟩))

#print axioms LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail.full_seed_tail
#print axioms LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail.full_realizes
#print axioms LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex.full_length
#print axioms LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex.exists_vertex
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.raw_seed_tail
end HistoryCompletionRegression
end RoadmapInternalHistoryCompletion

namespace RoadmapInternalAtomicRealization
namespace AtomicRealizationRegression
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open LeanCanny LeanCanny.Geometry.IntegralMixedChronologicalFrame LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization
open IntegralMixedOptionalEndpoints IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

example (x : State P S B m ι) (hm : m≤S) (d : Descriptor n m)
    (g : Fin (n+1)) (hg : g∉d.frame.frozen) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P d.frame old)
    (hgcrit : ∀i,i∉d.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (js : List (IntegralMixedPointCompanion.Free d.frame.frozen)) (room : m+1+js.length≤S+1) :
    ∃ C : AtomicCaptures x hm d g hg hn hcap z φ old p js room,
      ∀i,C.anchor.tuple (Sum.inl (FlatAffineCriticalStage.ambient i))^physical S (2^B) m=p i :=by
  obtain ⟨C⟩:=exists_atomic_captures x hm d g hg hn charge hdegree hcap z hz φ hφ old H p hp hgcrit js room
  exact ⟨C,C.anchor.physical⟩

#print axioms LeanCanny.Geometry.IntegralMixedChronologicalFrame.exists_atomic_captures
end AtomicRealizationRegression
end RoadmapInternalAtomicRealization

namespace RoadmapInternalComponentPaths
open LeanCanny LeanCanny.Connectivity Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
example {X I : Type*} [TopologicalSpace X] {S : Set X} (C : ClopenPathCover S I)
    (x y : X) (hx : x∈S) (hy : y∈connectedComponentIn S x) : JoinedIn S x y :=
  C.joinedIn_of_component x y hx hy
#print axioms LeanCanny.Connectivity.ClopenPathCover.joinedIn_of_component
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.exists_joined_objective_critical
end RoadmapInternalComponentPaths

namespace RoadmapInternalAtomicSize
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace Endpoint
open IntegralMixedRoadmapEndpointSyntax
private theorem count_empty : WordListRecords.count []=0:=rfl
example : Good 2 1 1 3 5 [] (spec 0 2 0 0 0 0) :=by
  norm_num [Good,canonical,count_empty]
example : Good 2 1 1 3 5 [] (spec 1 5 0 0 0 0) :=by
  norm_num [Good,canonical,count_empty]
example : Good 2 1 1 3 5 [] (spec 2 5 1 0 2 1) :=by
  norm_num [Good,canonical,count_empty,IntegralMixedChronologicalCutCode.Bounds,
    IntegralMixedChronologicalCutCode.Good,IntegralMixedChronologicalFrameCode.Good]
example : ¬Good 2 1 1 3 5 [] (spec 0 5 0 0 0 0) :=by
  norm_num [Good,canonical,count_empty]
example : (spec 0 2 0 0 0 0).length≤specBudget 2 5 1 :=by
  apply good_length (by norm_num [Good,canonical,count_empty] : Good 2 1 1 3 5 [] (spec 0 2 0 0 0 0))
    (by decide) (by decide) (by decide) (by rw [count_empty];omega)
end Endpoint
example {n B cap initial C : ℕ} {q : List Bool}
    (hq : IntegralMixedRoadmapChain.Checked n B cap initial C q) :
    q.length≤IntegralMixedRoadmapChain.payloadBudget n initial C :=IntegralMixedRoadmapChain.payload_length hq
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example : ∃p : Polynomial ℕ,∀q,IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q→
    q.length≤p.eval (IntegralMixedRoadmapAtomic.original q).length :=
  IntegralMixedRoadmapAtomic.polynomial_byte_bound hn ht ha hR0
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax.good_length
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.entry_length
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.metadata_length
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.payload_length
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapAtomic.byte_bound
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapAtomic.polynomial_byte_bound
end RoadmapInternalAtomicSize

namespace RoadmapInternalLocalEdge
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (q : List Bool) (h : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 q) :
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q :=h.1
example (q : List Bool) (h : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 q) (i : ℕ)
    (hi : i<IntegralMixedRoadmapLocalEdge.count hn ht ha hR0 q) :
    ∃right : Bool,IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right
      (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i))) :=by
  rcases h.2.2.2 with HL|HR
  · refine ⟨false,?_⟩
    simpa only [IntegralMixedRoadmapLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,List.length_replicate]
      using HL i hi
  · refine ⟨true,?_⟩
    simpa only [IntegralMixedRoadmapLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,List.length_replicate]
      using HR i hi
example (right : Bool) (z : List Bool) (h : IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right z) :
    ∃r o m : List Bool,r.length=IntegralMixedRoadmapProperCoordinateSearch.rankWidth hn ht ha hR0 z∧
      o.length=IntegralMixedRoadmapProperCoordinateSearch.fullWidth hn ht ha hR0 false z∧
      m.length=IntegralMixedRoadmapProperCoordinateSearch.fullWidth hn ht ha hR0 true z∧
      IntegralMixedRoadmapProperRowWitness.packet z o m r∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right :=by
  rcases h with ⟨r,HR,o,HO,m,HM,H⟩
  exact ⟨r,o,m,HR,HO,HM,H⟩
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch.evaluator
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch.decider
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge.allCoordinates_evaluator
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge.evaluator
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge.decider
end RoadmapInternalLocalEdge

namespace RoadmapInternalIdentity
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapIdentity.point IntegralMixedRoadmapAtomic.Valid
example (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b)
    (h : pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0) :
    HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 a hA)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 b hB) :=
  (IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 a b hA hB hc).mp h
example (q : List Bool) (h : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 q q :=IntegralMixedRoadmapEdge.refl hn ht ha hR0 q h
example (a b : List Bool) (h : IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a b) :
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a∧IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b :=
  IntegralMixedRoadmapEdge.valid hn ht ha hR0 a b h
example (a b : List Bool) (h : IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a b) :
    IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b :=
  IntegralMixedRoadmapEdge.candidate_eq hn ht ha hR0 a b h
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapIdentity.query_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapIdentity.language_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapIdentity.decider
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapEdge.decider
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapEdge.valid
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapEdge.of_same_point
end RoadmapInternalIdentity

namespace RoadmapInternalLabelRoom
open LeanCanny LeanCanny.Encoding
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
example : IntegralMixedRoadmapWordLabel.decode (IntegralMixedRoadmapWordLabel.encode 0 [])=[] :=rfl
example : IntegralMixedRoadmapWordLabel.decode (IntegralMixedRoadmapWordLabel.encode 4 [false,true])=[false,true] :=
  IntegralMixedRoadmapWordLabel.decode_encode _ _
example : (IntegralMixedRoadmapWordLabel.encode 4 [false,true]).length=10 :=
  IntegralMixedRoadmapWordLabel.encode_length _ _ (by decide)
example (n : ℕ) (q : List Bool) (i : ℕ) (hi : i≤n+1) :
    IntegralMixedRoadmapChain.rawStart n q i+(n+1-i)≤IntegralMixedRoadmapRecordChain.recordBound n :=
  IntegralMixedRoadmapChain.rawStart_free_bound n q i hi
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapWordLabel.decode_encode
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapWordLabel.encode_length
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapChain.rawStart_free_bound
end RoadmapInternalLabelRoom

namespace RoadmapInternalGraph
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.Connectivity
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example : IntegralMixedRoadmapGraph.connectedLanguage hn ht ha hR0∈PSPACE :=
  IntegralMixedRoadmapGraph.connected_mem_PSPACE hn ht ha hR0
example : IntegralMixedRoadmapGraph.reachLanguage hn ht ha hR0∈PSPACE :=
  IntegralMixedRoadmapGraph.reach_mem_PSPACE hn ht ha hR0
example (c q : List Bool) (hq : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) : ∃r : List Bool,
    r.length=IntegralMixedRoadmapGraph.width hn ht ha hR0 c∧IntegralMixedRoadmapWordLabel.decode r=q∧
      IntegralMixedRoadmapGraph.Valid hn ht ha hR0 c r :=
  IntegralMixedRoadmapGraph.encode_vertex hn ht ha hR0 c q hq hc
example (q : List Bool) (h : q∈IntegralMixedRoadmapGraph.reachLanguage hn ht ha hR0) :
    (IntegralMixedRoadmapGraph.leftLabel q).length=IntegralMixedRoadmapGraph.width hn ht ha hR0 (pairFst q)∧
    (IntegralMixedRoadmapGraph.rightLabel q).length=IntegralMixedRoadmapGraph.width hn ht ha hR0 (pairFst q) :=
  ⟨h.1,h.2.1⟩
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.encode_vertex
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.edge_computable
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.connected_mem_PSPACE
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.reach_mem_PSPACE
end RoadmapInternalGraph

namespace RoadmapInternalAtomicSemantics
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapAtomic
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace AtomicSemanticsRegression

private def labels:=WordList.encode [BinaryNatCode.encode 0,BinaryNatCode.encode 2]
private def repeated:=WordList.encode [BinaryNatCode.encode 2,BinaryNatCode.encode 2]
private theorem zero_bits :Nat.fromBitsLE []=0:=rfl
private theorem good :IntegralMixedChronologicalFrameCode.PointGood 3 5 labels 2 3:=by
  refine ⟨⟨by norm_num [labels,WordListRecords.count_encode],?_⟩,
    by norm_num [labels,WordListRecords.count_encode],by omega,
    by norm_num [labels,WordListRecords.count_encode],by omega⟩
  intro i hi
  have HI :i<2:=by simpa only [labels,WordListRecords.count_encode,List.length_cons,List.length_nil] using hi
  interval_cases i <;> norm_num [labels,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits,zero_bits]
private theorem goodRepeated :IntegralMixedChronologicalFrameCode.PointGood 3 5 repeated 2 3:=by
  refine ⟨⟨by norm_num [repeated,WordListRecords.count_encode],?_⟩,
    by norm_num [repeated,WordListRecords.count_encode],by omega,
    by norm_num [repeated,WordListRecords.count_encode],by omega⟩
  intro i hi
  have HI :i<2:=by simpa only [repeated,WordListRecords.count_encode,List.length_cons,List.length_nil] using hi
  interval_cases i <;> norm_num [repeated,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]

example :(IntegralMixedChronologicalFrameCode.rawData 3 5 labels 2 3 good).rule.offset.val+
    (IntegralMixedChronologicalFrameCode.rawData 3 5 labels 2 3 good).rule.coordinate%
      (3-(IntegralMixedChronologicalFrameCode.rawData 3 5 labels 2 3 good).rule.offset.val+1)=3:=
  IntegralMixedChronologicalFrame.raw_selected 5 labels 2 3 good
example :(IntegralMixedChronologicalFrameCode.rawData 3 5 repeated 2 3 goodRepeated).rule.offset.val+
    (IntegralMixedChronologicalFrameCode.rawData 3 5 repeated 2 3 goodRepeated).rule.coordinate%
      (3-(IntegralMixedChronologicalFrameCode.rawData 3 5 repeated 2 3 goodRepeated).rule.offset.val+1)=3:=
  IntegralMixedChronologicalFrame.raw_selected 5 repeated 2 3 goodRepeated
example :¬IntegralMixedChronologicalFrameCode.PointGood 3 5 labels 2 1:=by
  intro H
  have HH:=H.2.2.2.1
  norm_num [labels,WordListRecords.count_encode] at HH
example :¬IntegralMixedChronologicalFrameCode.PointGood 3 2 labels 2 3:=by
  intro H
  have HH:=H.1.2 1 (by norm_num [labels,WordListRecords.count_encode])
  norm_num [labels,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HH
example :¬IntegralMixedChronologicalFrameCode.PointGood 3 5 labels 4 3:=by
  intro H
  exact Nat.lt_irrefl 4 H.2.2.1
example :IntegralMixedChronologicalFrameCode.PointGood 3 0 [] 0 0:=by
  have H0 :WordListRecords.count ([]:List Bool)=0:=WordListRecords.count_encode []
  norm_num [IntegralMixedChronologicalFrameCode.PointGood,IntegralMixedChronologicalFrameCode.Good,H0]

-- Signed, nonunit denominators remain in the actual quotient formula.
private def signedData :IntegralMixedFramedBankObservation.Data:=⟨0,1,1,fun _=>-3⟩
private def nonunitData :IntegralMixedFramedBankObservation.Data:=⟨0,1,1,fun _=>4⟩
example :signedData.point (fun _=>-6) 0=2:=by
  norm_num [signedData,IntegralMixedFramedBankObservation.Data.point,UniformIntegralPowerSchedule.weights,
    UniformIntegralPowerSchedule.birth,MonicParameterPowerSchedule.weight]
  rw [show signedData.denominator ⟨0,by decide⟩=(-3:ℤ) from rfl]
  norm_num
example :nonunitData.point (fun _=>-8) 0=(-2):=by
  norm_num [nonunitData,IntegralMixedFramedBankObservation.Data.point,UniformIntegralPowerSchedule.weights,
    UniformIntegralPowerSchedule.birth,MonicParameterPowerSchedule.weight]
  change (-8:ℝ)/4=-2
  norm_num
example :signedData.point (fun _=>-6) 1=0:=by
  norm_num [signedData,IntegralMixedFramedBankObservation.Data.point]
example :(-1:ℝ)^UniformIntegralPowerSchedule.physical 5 4 2=-1:=
  (UniformIntegralPowerSchedule.physical_odd 5 4 2).neg_one_pow
example :(-1:ℝ)^UniformIntegralPowerSchedule.physical 5 4 3=-1:=
  (UniformIntegralPowerSchedule.physical_odd 5 4 3).neg_one_pow
example :UniformIntegralPowerSchedule.weights 5 4 3 (⟨1,by decide⟩:Fin 3)=
    UniformIntegralPowerSchedule.weights 5 4 2 (⟨0,by decide⟩:Fin 2):=
  UniformIntegralPowerSchedule.old 5 4 2 0

private def number (_ :List Bool):ℕ:=0
private def term (_ :List Bool):Term:=.const 0
private def radius (_ :List Bool):ℕ:=0
private theorem hn :UnaryFn number:=UnaryFn.const 0
private theorem ht :(fun q=>(term q).toData.toBits)∈FP:=by
  simpa only [term] using constFn_mem_FP (Term.const (0:ℤ)).toData.toBits
private theorem ha :∀q,(term q).arity≤number q:=by intro q;change 0≤0;omega
private theorem hR :BinaryFn radius:=BinaryFn.const 0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank source point dimension initial width sourceCap
  scalarBudget wordBudget root context payload candidate word

-- The instantiated occurrence API needs only the actual native vertex validity.
example (q :List Bool) (hv :Valid hn ht ha hR q) :
    IntegralMixedAtomicOccurrence.Occurrence (source hn ht ha hR q) (depth q) (levels hn ht ha hR q hv)
      (point hn ht ha hR q hv):=occurrence hn ht ha hR q hv
example (q :List Bool) (hv :Valid hn ht ha hR q) :
    HEq (source hn ht ha hR q) (IntegralMixedOriginalRegularSource.source number term radius (original q)):=
  source_original hn ht ha hR q hv
example (q :List Bool) (hv :Valid hn ht ha hR q)
    (i :Fin ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false).parameters.ambient
      (pairFst ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false).key (context q)))+1)) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR)
      (context q) (word q) (full_valid hn ht ha hR q hv)
      (Nat.fromBitsLE (WordList.get (signature (dimension hn ht ha hR q) (initial hn ht ha hR q) q) i.val))=
      point hn ht ha hR q hv i:=signature_readback hn ht ha hR q hv i
example (q :List Bool) (hv :Valid hn ht ha hR q) :
    IntegralMixedChronologicalFrameCode.Good (dimension hn ht ha hR q)
      (endBirth (dimension hn ht ha hR q) (initial hn ht ha hR q) q-1) (frozen q):=
  own_frame_good hn ht ha hR q hv

#print axioms IntegralMixedStaticRecordLookup.instruction_receipt
#print axioms IntegralMixedStaticRecordLookup.source_receipt
#print axioms IntegralMixedStaticRecordLookup.critical_receipt
#print axioms IntegralMixedMarkedRecordReceipt.critical_at
#print axioms IntegralMixedMarkedRecordReceipt.source_at
#print axioms IntegralMixedChronologicalFrame.critical_readback
#print axioms IntegralMixedChronologicalFrame.raw_readback
#print axioms IntegralMixedFramedCriticalReadback.point_append
#print axioms IntegralFramedPhysicalCriticalReadback.quotient_full
#print axioms IntegralFramedPhysicalCriticalReadback.indexedPoint_key_cast
#print axioms IntegralMixedPhysicalPointCompanionScan.exists_critical
#print axioms IntegralMixedPhysicalPointCompanionScan.frame_point
#print axioms IntegralMixedPhysicalFieldEquality.retained_point
#print axioms own_creating_command
#print axioms own_creating_source
#print axioms source_original
#print axioms occurrence
#print axioms latest_capture_record
#print axioms capture_creating_command
#print axioms capture_selected
#print axioms signature_readback
#print axioms signature_bounded
end AtomicSemanticsRegression
end RoadmapInternalAtomicSemantics

namespace RoadmapInternalConstantRank
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Encoding Polynomial
open scoped Classical
noncomputable section
namespace ConstantRankRegression
open IntegralMixedSelectedCoordinateRank

-- A repeated root has one ordinal, with no separability premise.
example (a : ℝ) : Test ((X-C a)^2) 2 a 9 0 :=by
  have HP : ((X-C a)^2 : ℝ[X]).natDegree=2:=by simp
  apply (test_iff_rank _ 2 (by decide) HP a 9 (by norm_num) 0).mpr
  constructor
  · simp [Polynomial.roots_pow]
  · simp [OrderedRealRootWindow.rank,Polynomial.roots_pow]
example (a : ℝ) : ¬Test ((X-C a)^2) 2 a 9 1 :=by
  have HP : ((X-C a)^2 : ℝ[X]).natDegree=2:=by simp
  have HR : OrderedRealRootWindow.rank ((X-C a)^2 : ℝ[X]).roots.toFinset a=0:=by
    simp [OrderedRealRootWindow.rank,Polynomial.roots_pow]
  intro HT
  have HQ:=((test_iff_rank _ 2 (by decide) HP a 9 (by norm_num) 1).mp HT).2
  rw [HR] at HQ
  omega

-- A positive-degree head without real roots rejects every rank.
example (y : ℝ) (code : ℕ) : ¬Test (X^2+1) 2 y 4 code :=by
  have HP : (X^2+1 : ℝ[X]).natDegree=2:=by compute_degree;norm_num
  intro H
  have HM:=((test_iff_rank _ 2 (by decide) HP y 4 (by norm_num) code).mp H).1
  have HZ:=(Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp HM)).2
  change (X^2+1 : ℝ[X]).eval y=0 at HZ
  simp only [Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] at HZ
  nlinarith [sq_nonneg y]

-- A fixed distinct-root ordinal determines its point from all shrinking windows.
example (p : ℝ[X]) (k : ℕ) (y : ℝ) (H : ∀ε : ℝ,0<ε→IntegralMixedSelectedCoordinateWindow.Window p k y ε) :
    y∈p.roots.toFinset ∧OrderedRealRootWindow.rank p.roots.toFinset y=k:=
  (rank_iff_small_windows p k y).mpr ⟨1,by norm_num,fun ε hε _=>H ε hε⟩

#print axioms IntegralMixedSelectedCoordinateRank.rank_iff_small_windows
#print axioms IntegralMixedSelectedCoordinateRank.window_stable
#print axioms IntegralMixedSelectedCoordinateRank.test_iff_rank
#print axioms IntegralFramedZeroTarskiStatistic.rankPacket_iff
#print axioms IntegralFramedZeroTarskiStatistic.exists_rankPacket_iff
#print axioms IntegralMixedRoadmapProperRow.rankLanguage_iff
end ConstantRankRegression
end
end RoadmapInternalConstantRank

namespace RoadmapInternalSquareComposition
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
noncomputable section
namespace PhysicalSquareCompositionRegression
variable (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
  (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hp : ∀q,0<(family P D H).birth (key q))

-- Two reindexings preserve annihilators and all hash/root-order input fields.
example (f g : List Bool→List Bool) :
    IntegralFramedPhysicalSquare.input P D H L F C hs ((key∘f)∘g) (fun q=>hp (f (g q)))=
      SquareSampleInput.comp (SquareSampleInput.comp (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) f) g :=by
  exact (IntegralFramedPhysicalSquare.input_comp P D H L F C hs (key∘f) (fun q=>hp (f q)) g).trans
    (congrArg (fun I=>SquareSampleInput.comp I g) (IntegralFramedPhysicalSquare.input_comp P D H L F C hs key hp f))

-- Allocate at a paired context before placing that context inside another query.
example (q w : List Bool) :SquareSampleCompleteVertices.Valid
    (IntegralFramedPhysicalSquare.input P D H L F C hs (fun q=>key (pair q [])) (fun q=>hp (pair q []))) q w↔
      SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) (pair q []) w :=
  IntegralFramedPhysicalSquare.valid_comp P D H L F C hs key hp (fun q=>pair q []) q w

example (q w : List Bool)
    (hc : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input P D H L F C hs (fun q=>key (pair q [])) (fun q=>hp (pair q []))) q w)
    (ho : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) (pair q []) w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (fun q=>key (pair q [])) (fun q=>hp (pair q [])) q w hc 0=
      IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp (pair q []) w ho 0 :=
  congrFun (IntegralFramedPhysicalSquare.naturalPoint_comp P D H L F C hs key hp (fun q=>pair q []) q w hc ho) 0

example (f : List Bool→List Bool) (q w : List Bool)
    (hc : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs (key∘f) (fun q=>hp (f q))) q w)
    (ho : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) (f q) w) :
    IntegralFramedPhysicalSquare.point P D H L F C hs (key∘f) (fun q=>hp (f q)) q w hc=
      IntegralFramedPhysicalSquare.point P D H L F C hs key hp (f q) w ho :=
  IntegralFramedPhysicalSquare.point_comp P D H L F C hs key hp f q w hc ho

#print axioms IntegralFramedPhysicalSquare.input_comp
#print axioms IntegralFramedPhysicalSquare.valid_comp
#print axioms IntegralFramedPhysicalSquare.candidate_comp
#print axioms IntegralFramedPhysicalSquare.point_comp
#print axioms IntegralMixedRoadmapProperRow.sampler_comp
#print axioms IntegralMixedRoadmapProperRow.valid_at_context
#print axioms IntegralMixedRoadmapProperRow.point_at_context
#print axioms IntegralMixedRoadmapProperRowWitness.fieldMatch_sound
end PhysicalSquareCompositionRegression
end
end RoadmapInternalSquareComposition

namespace RoadmapInternalMidCritical
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory
noncomputable section
namespace MidpointCriticalRegression
private def labels:=WordList.encode [BinaryNatCode.encode 0,BinaryNatCode.encode 3]
private theorem HG : IntegralMixedChronologicalMidpointCode.Good 4 5 labels 2 1 3 4:=by
  refine ⟨⟨by decide,?_⟩,by decide,by decide,by decide,by decide,by decide,by decide⟩
  intro i hi
  have HI : i<2:=hi
  interval_cases i <;> decide

section ActualCriticalPoint
variable {S W : ℕ} {P : SpatialSource 4} {ι : Type} (x : State P S W 5 ι) (hm : 5≤S)
  (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (v : Fin 5→ℝ)
  (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v i)
  (p : Fin 5→ℝ)
  (HP : IntegralMixedCriticalReadback.CriticalPoint x hm
    (IntegralMixedChronologicalMidpointCode.rawData 4 5 labels 2 1 3 4 HG).rule φ p)

-- Chronological references2/1 become old newest-first indices2/3, never head0.
example : p 2=(v 2+v 3)/2:=
  (IntegralMixedChronologicalMidpoint.raw_readback x hm 5 rfl labels 2 1 3 4 HG φ v H p HP).2.2.1
example : p 0=v 4:=
  (IntegralMixedChronologicalMidpoint.raw_readback x hm 5 rfl labels 2 1 3 4 HG φ v H p HP).2.1 0 (by decide)
example : p 1=v 1:=
  (IntegralMixedChronologicalMidpoint.raw_readback x hm 5 rfl labels 2 1 3 4 HG φ v H p HP).2.1 1 (by decide)
example : (MvPolynomial.pderiv (4 : Fin 5) (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
    (Int.castRingHom ℝ) p=0:=
  (IntegralMixedChronologicalMidpoint.raw_readback x hm 5 rfl labels 2 1 3 4 HG φ v H p HP).2.2.2 4 HG.2.2.2.2.2.1 (by decide)
end ActualCriticalPoint

example : (IntegralMixedChronologicalMidpointCode.rawData 4 5 labels 2 1 3 4 HG).rule.offset.val+
    (IntegralMixedChronologicalMidpointCode.rawData 4 5 labels 2 1 3 4 HG).rule.coordinate%
      (4-(IntegralMixedChronologicalMidpointCode.rawData 4 5 labels 2 1 3 4 HG).rule.offset.val+1)=4 :=
  IntegralMixedChronologicalMidpoint.raw_selected 5 labels 2 1 3 4 HG

#print axioms IntegralMixedChronologicalMidpoint.raw_readback
#print axioms IntegralMixedChronologicalMidpoint.raw_selected
#print axioms IntegralMixedPhysicalPointCompanionScan.midpoint_frame_point
#print axioms IntegralMixedPhysicalPointCompanionScan.selected_of_midpoint
#print axioms IntegralMixedStaticRecordLookup.midpoint_receipt
#print axioms IntegralMixedMarkedMidpointReceipt.critical_at
#print axioms IntegralMixedRoadmapMidpointRecord.level_anchor_record
#print axioms IntegralMixedRoadmapMidpointRecord.checked_anchor_record
#print axioms IntegralMixedRoadmapProper.midpoint_command
#print axioms IntegralMixedRoadmapProper.midpoint_context_command
end MidpointCriticalRegression
end
end RoadmapInternalMidCritical

namespace RoadmapInternalMidValues
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
namespace MidpointValuesRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
variable (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
  (hd : 0<IntegralMixedRoadmapAtomic.depth q)

-- The first capture is the largest original coordinate.
example : IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapProper.midFirst (D q) (N q) q)=D q :=by
  have HC : 0<IntegralMixedRoadmapProper.captureCount (D q) q:=by
    have H:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
    unfold IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
    omega
  simpa only [Nat.add_zero,Nat.sub_zero] using
    IntegralMixedRoadmapProper.midpoint_capture_selected hn ht ha hR0 q hv hd 0 HC

-- Capture order decreases, with no new midpoint scalar alias.
example (hcount : 1<IntegralMixedRoadmapProper.captureCount (D q) q) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapProper.midFirst (D q) (N q) q+1)=D q-1 :=
  IntegralMixedRoadmapProper.midpoint_capture_selected hn ht ha hR0 q hv hd 1 hcount

example : IntegralMixedRoadmapProper.midpointSource hn ht ha hR0 q=
    IntegralMixedRoadmapAtomic.source hn ht ha hR0 q :=
  IntegralMixedRoadmapProper.midpoint_source_eq_own hn ht ha hR0 q hv hd
example : HEq (IntegralMixedRoadmapProper.midpointSource hn ht ha hR0 q)
    (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q)) :=
  IntegralMixedRoadmapProper.midpoint_source_original hn ht ha hR0 q hv hd

#print axioms IntegralMixedRoadmapProper.midpoint_companion_command
#print axioms IntegralMixedRoadmapProper.midpoint_companion_context_command
#print axioms IntegralMixedRoadmapProper.midpoint_capture_selected
#print axioms IntegralMixedRoadmapProper.midpoint_capture_readback
#print axioms IntegralMixedRoadmapProper.midpoint_source_eq_own
#print axioms IntegralMixedRoadmapProper.midpoint_source_original
end MidpointValuesRegression
end
end RoadmapInternalMidValues

namespace RoadmapInternalRowRuling
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralCriticalHistoryTask
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
namespace ProperRowRulingRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
variable (z : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z))
  (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)

-- Both independent replacement roots have the original physical dimension.
example : (P).ambient (IntegralMixedRoadmapProperRow.root hn ht ha hR0 false z)=
    IntegralMixedRoadmapProperRow.dimension hn ht ha hR0 z :=
  IntegralMixedRoadmapProperRow.root_dimension hn ht ha hR0 false z
example : (P).ambient (IntegralMixedRoadmapProperRow.root hn ht ha hR0 true z)=
    IntegralMixedRoadmapProperRow.dimension hn ht ha hR0 z :=
  IntegralMixedRoadmapProperRow.root_dimension hn ht ha hR0 true z

-- Neither coefficient probe is silently clipped to a different creating birth.
example (mean : Bool) :birth P (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 mean z)=
    IntegralMixedRoadmapProperRow.creating hn ht ha hR0 z :=
  IntegralMixedRoadmapProperRow.parent_birth hn ht ha hR0 mean z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hv)

-- The ordinary query uses its own actual current denominator.
example : ((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z)).slope=
    IntegralMixedHistory.commonDenominator ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z)) :=
  IntegralMixedRoadmapProperRow.rule_current hn ht ha hR0 false z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hv) hg

-- The mean-centered query does likewise; no equality of the two old homs is used.
example : ((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 true z)).slope=
    IntegralMixedHistory.commonDenominator ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 true z)) :=
  IntegralMixedRoadmapProperRow.rule_current hn ht ha hR0 true z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hv) hg

-- The final zero-degree probe retains every chronological older record.
example (mean : Bool) :IntegralMixedCausalRecordPlanBits.records
    (pairFst (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mean z))=
    WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProperRow.oldPacket z)++
      [IntegralMixedRoadmapProperRow.code hn ht ha hR0 mean z]) :=
  IntegralMixedRoadmapProperRow.parentKey_records hn ht ha hR0 mean z

#print axioms IntegralMixedRoadmapProperRow.creating_bound
#print axioms IntegralMixedRoadmapProperRow.parent_birth
#print axioms IntegralMixedRoadmapProperRow.parentKey_prefix
#print axioms IntegralMixedRoadmapProperRow.parentData_code
#print axioms IntegralMixedRoadmapProperRow.rule_at_parent
#print axioms IntegralMixedRoadmapProperRow.rule_current
#print axioms IntegralMixedRoadmapProperRow.row_count_positive
end ProperRowRulingRegression
end
end RoadmapInternalRowRuling

namespace RoadmapInternalRowSnapshot
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProperRowSnapshotRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
variable (z : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z))
-- Actual states, including their dependent coefficient algebras, agree before the reserved record.
example : IntegralMixedPrefixSnapshot.ofState ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z))=
    IntegralMixedPrefixSnapshot.ofState ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 true z)) :=
  IntegralMixedRoadmapProperRow.parent_state_snapshot_eq_valid hn ht ha hR0 z hv
-- The ordinary prefix remains canonical even if earlier roots are repeated or singular.
example : IntegralMixedHistory.Canonical ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z)) :=
  IntegralMixedRoadmapProperRow.parent_canonical hn ht ha hR0 false z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hv)
-- The mean query is a separate complete-word context of the same canonical older algebra.
example : IntegralMixedHistory.Canonical ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 true z)) :=
  IntegralMixedRoadmapProperRow.parent_canonical hn ht ha hR0 true z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hv)
#print axioms IntegralMixedRoadmapProperRow.parent_snapshot
#print axioms IntegralMixedRoadmapProperRow.parentSnapshot_eq
#print axioms IntegralMixedRoadmapProperRow.parent_state_snapshot_eq_valid
#print axioms IntegralMixedRoadmapProperRow.parent_canonical
end ProperRowSnapshotRegression
end
end RoadmapInternalRowSnapshot

namespace RoadmapInternalRowInterpretation
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProperRowInterpretationRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
variable (right : Bool) (u : List Bool)
  (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
  (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
local notation "CS"=>IntegralMixedRoadmapProperRowWitness.commonSnapshot hn ht ha hR0
-- A full native row witness itself supplies the old real interpretation.
example : Nonempty ((CS (IntegralMixedRoadmapProperRowWitness.key u)).state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :=by
  obtain ⟨_,_,φ,_,_⟩:=IntegralMixedRoadmapProperRowWitness.exists_common_interpretation hn ht ha hR0 right u hv HL
  exact ⟨φ⟩
-- Its coefficient state is the actual ordinary parent snapshot.
example : CS (IntegralMixedRoadmapProperRowWitness.key u)=
    IntegralMixedRoadmapProperRow.parentSnapshot hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u) :=
  IntegralMixedRoadmapProperRowWitness.commonSnapshot_eq_parent hn ht ha hR0 _
-- Canonicality does not need squarefree or nonsingular roots.
example : IntegralMixedHistory.Canonical (CS (IntegralMixedRoadmapProperRowWitness.key u)).state :=
  IntegralMixedRoadmapProperRowWitness.commonSnapshot_canonical hn ht ha hR0 _
#print axioms IntegralMixedRoadmapProperRowWitness.parent_values_equal
#print axioms IntegralMixedRoadmapProperRowWitness.commonSnapshot_eq_parent
#print axioms IntegralMixedRoadmapProperRowWitness.commonSnapshot_canonical
#print axioms IntegralMixedRoadmapProperRowWitness.exists_common_interpretation
end ProperRowInterpretationRegression
end
end RoadmapInternalRowInterpretation

namespace RoadmapInternalBadProbe
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ActualBadProbeRegression
private def Q : SpatialSource 1 where
 low:=-1
 leading:=-2
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
example : IntegralMixedCutRecordConstructor.degreeResidue Q
 (IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)=0:=Nat.mod_self _
example (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree) :
 IntegralMixedCutRecordConstructor.degreeResidue Q d=d:=Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd)
example (d : ℕ) : IntegralMixedCutRecordConstructor.degreeResidue Q
 ((IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)*d)=0:=Nat.mul_mod_right _ _
example : (-6:ℤ)%6=0:=by decide
example : (-12:ℝ)/(-6)=2:=by norm_num
example : ((1:Polynomial ℝ).eval 0)≠0:=by norm_num
example : ∀a:ℝ,(Polynomial.X^2+1:Polynomial ℝ).eval a≠0:=by
 intro a h
 norm_num at h
 nlinarith [sq_nonneg a]
example : (PaddedIntegralNormalization.polynomial (1:Polynomial ℤ) 0 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial,FixedDegreeIntegralNormalization.polynomial]
example : (PaddedIntegralNormalization.polynomial (Polynomial.X^2+1:Polynomial ℤ) 2 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial]
example : IntegralMixedChronologicalCutCode.ordinaryTag 0=.coordinate:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 1=.squarefree:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 2=.value:=rfl
example (old aux p q :List Bool) (codes:List (List Bool)) :
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes p aux)=
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes q aux):=by
 rw [IntegralMixedMarkedPrefixRun.reserved_count,IntegralMixedMarkedPrefixRun.reserved_count]
example (q:List Bool) (codes:List (List Bool)) (last:List Bool)
 (h:IntegralMixedRoadmapBadProbePacket.raw q=WordList.encode (codes++[last])) :
 IntegralMixedRoadmapBadProbePacket.prefixCodes q=codes:=
 IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq q codes last h
section Selected
variable {n S B m:ℕ} {P:SpatialSource n} {ι:Type} (x:State P S B m ι) (hm:m≤S)
 (r:IntegralMixedCriticalSweep.Rule n) (φ:x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (c:Choices x hm r φ) (a:ℝ)
example : a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c ↔
 ∃k:Kind P r,Valid x hm r φ k ∧ IntegralMixedSelectedBadMembership.Ordinary r k ∧(factor x hm r k).eval₂ φ.toRingHom a=0:=
 IntegralMixedSelectedBadMembership.mem_bad_iff x hm r φ c a
example (j:ℕ) (d:Choices x hm (IntegralMixedSweepRetarget.rule r j) φ) :
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm (IntegralMixedSweepRetarget.rule r j) φ d ↔
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c:=
 IntegralMixedSweepRetarget.bad_iff x hm r j φ c d a
end Selected

#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.valid_kind_selected
#print axioms LeanCanny.Encoding.IntegralMixedCutRecordConstructor.command_decode_mod
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence.interpreted_present_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.prefix_congr
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.reserved_eq
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedPoint.values_eq
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.exists_interpretation
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.bad_eq_of_parent_fields
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.family_eq_original
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.family_keyAt
#print axioms LeanCanny.Algebra.IntegralMixedSweepRetarget.bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedChronologicalCutCode.raw_chosenCode_actual
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape.command
#print axioms LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation.quotient_prefix_at
#print axioms LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction.rule_at_parent
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_eq
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint.quotients
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_retarget_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_raw
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.ofState_mem_bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.ordinary
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.rule_raw
end ActualBadProbeRegression
end
end RoadmapInternalBadProbe

namespace RoadmapInternalBadSound
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ActualBadProbeRegression
private def Q : SpatialSource 1 where
 low:=-1
 leading:=-2
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
example : IntegralMixedCutRecordConstructor.degreeResidue Q
 (IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)=0:=Nat.mod_self _
example (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree) :
 IntegralMixedCutRecordConstructor.degreeResidue Q d=d:=Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd)
example (d : ℕ) : IntegralMixedCutRecordConstructor.degreeResidue Q
 ((IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)*d)=0:=Nat.mul_mod_right _ _
example : (-6:ℤ)%6=0:=by decide
example : (-12:ℝ)/(-6)=2:=by norm_num
example : ((1:Polynomial ℝ).eval 0)≠0:=by norm_num
example : ∀a:ℝ,(Polynomial.X^2+1:Polynomial ℝ).eval a≠0:=by
 intro a h
 norm_num at h
 nlinarith [sq_nonneg a]
example : (PaddedIntegralNormalization.polynomial (1:Polynomial ℤ) 0 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial,FixedDegreeIntegralNormalization.polynomial]
example : (PaddedIntegralNormalization.polynomial (Polynomial.X^2+1:Polynomial ℤ) 2 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial]
example : IntegralMixedChronologicalCutCode.ordinaryTag 0=.coordinate:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 1=.squarefree:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 2=.value:=rfl
example (old aux p q :List Bool) (codes:List (List Bool)) :
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes p aux)=
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes q aux):=by
 rw [IntegralMixedMarkedPrefixRun.reserved_count,IntegralMixedMarkedPrefixRun.reserved_count]
example (q:List Bool) (codes:List (List Bool)) (last:List Bool)
 (h:IntegralMixedRoadmapBadProbePacket.raw q=WordList.encode (codes++[last])) :
 IntegralMixedRoadmapBadProbePacket.prefixCodes q=codes:=
 IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq q codes last h
section Selected
variable {n S B m:ℕ} {P:SpatialSource n} {ι:Type} (x:State P S B m ι) (hm:m≤S)
 (r:IntegralMixedCriticalSweep.Rule n) (φ:x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (c:Choices x hm r φ) (a:ℝ)
example : a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c ↔
 ∃k:Kind P r,Valid x hm r φ k ∧ IntegralMixedSelectedBadMembership.Ordinary r k ∧(factor x hm r k).eval₂ φ.toRingHom a=0:=
 IntegralMixedSelectedBadMembership.mem_bad_iff x hm r φ c a
example (j:ℕ) (d:Choices x hm (IntegralMixedSweepRetarget.rule r j) φ) :
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm (IntegralMixedSweepRetarget.rule r j) φ d ↔
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c:=
 IntegralMixedSweepRetarget.bad_iff x hm r j φ c d a
end Selected

#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.valid_kind_selected
#print axioms LeanCanny.Encoding.IntegralMixedCutRecordConstructor.command_decode_mod
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence.interpreted_present_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.prefix_congr
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.reserved_eq
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedPoint.values_eq
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.exists_interpretation
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.bad_eq_of_parent_fields
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.family_eq_original
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.family_keyAt
#print axioms LeanCanny.Algebra.IntegralMixedSweepRetarget.bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedChronologicalCutCode.raw_chosenCode_actual
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape.command
#print axioms LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation.quotient_prefix_at
#print axioms LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction.rule_at_parent
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_eq
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint.quotients
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_retarget_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_raw
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.ofState_mem_bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.ordinary
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.rule_raw
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutOrdinaryPresence.present
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutEndpointField.endpoint_field
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent.snapshot_prepared
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent.bad_eq_of_fields
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent.saved_snapshot
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeEndpoint.endpoint_parent
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbePresence.present_prepared
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound.ordinary_bad
end ActualBadProbeRegression
end
end RoadmapInternalBadSound

namespace RoadmapInternalContinuation
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace CausalContinuationRegression

private def currentCode:=WordList.encode [[],[],[],[],[],[],[],[],[],[],[true],[]]
private theorem current_true :IntegralMixedCausalUnitRecordBits.current currentCode=true:=by
  norm_num [currentCode,IntegralMixedCausalUnitRecordBits.current,IntegralMixedUnitRecordCode.field,WordList.get_encode]

example {n B :ℕ} (Q :SpatialSource n) (hn :0<n) (b :ℕ)
    (hc :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) :
    ((IntegralMixedCausalUnitRecordBits.cut Q hn b currentCode hc).rule (-3) (by norm_num)).slope=-3:=by
  rw [IntegralMixedCausalUnitRecordBits.cut_slope,current_true]
  rfl
example {n B :ℕ} (Q :SpatialSource n) (hn :0<n) (b :ℕ)
    (hc :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) :
    ((IntegralMixedCausalUnitRecordBits.cut Q hn b currentCode hc).rule 6 (by norm_num)).slope=6:=by
  rw [IntegralMixedCausalUnitRecordBits.cut_slope,current_true]
  rfl

section LiteralRecords
variable {n B :ℕ} (Q :SpatialSource n) (hn :0<n)
  (hc :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)

example (b :ℕ) :(IntegralMixedCausalUnitContinuation.records Q hn hc b [currentCode,[]]).length=2:=by
  rw [IntegralMixedCausalUnitContinuation.records_length]
  rfl
example (b :ℕ) :(IntegralMixedCausalUnitContinuation.records Q hn hc b [currentCode,[]]).reverse[0]?=
    some (IntegralMixedCausalUnitRecordBits.record Q hn b [] hc):=by
  simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,
    List.getElem?_cons_zero,Option.getD_some,Nat.add_zero] using
    IntegralMixedCausalUnitContinuation.records_reverse_get Q hn hc b [currentCode,[]] 0 (by decide)
example (b :ℕ) :(IntegralMixedCausalUnitContinuation.records Q hn hc b [currentCode,[]]).reverse[1]?=
    some (IntegralMixedCausalUnitRecordBits.record Q hn (b+1) currentCode hc):=by
  simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using
    IntegralMixedCausalUnitContinuation.records_reverse_get Q hn hc b [currentCode,[]] 1 (by decide)
example (b :ℕ) :IntegralMixedCausalUnitContinuation.records Q hn hc b []=[]:=rfl
end LiteralRecords

-- One current-Q command is decoded at the actual older causal state.
example {n S B :ℕ} {P :SpatialSource n} (initial :State P S B 0 (Fin 0))
    (Q :SpatialSource n) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (older :List (IntegralMixedCausalRecordBits.Record n B)) (ho :older.length≤S+1)
    (room :(IntegralMixedCausalPlanBits.commands initial older ho).length+1≤S+1) :
    let old:=IntegralMixedCausalPlanBits.commands initial older ho
    let x:=IntegralMixedCausalUnitContinuation.start initial Q hcap older ho
    let c:=(IntegralMixedCausalUnitRecordBits.record Q hn old.length currentCode hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)
    HEq (reframe (IntegralMixedFramedHistoryScript.run initial
      (IntegralMixedCausalPlanBits.commands initial
        (IntegralMixedCausalUnitContinuation.records Q hn hcap old.length [currentCode]++older)
        (by rw [List.length_append,IntegralMixedCausalUnitContinuation.records_length,List.length_singleton];
            have HL:=IntegralMixedCausalPlanBits.commands_length initial older ho;omega))
        (by rw [IntegralMixedCausalPlanBits.commands_length,List.length_append,IntegralMixedCausalUnitContinuation.records_length,List.length_singleton];
            have HL:=IntegralMixedCausalPlanBits.commands_length initial older ho;omega)) Q
      (IntegralMixedStaticRecordPrefix.cap Q hcap))
      (IntegralMixedFullHistoryScript.continueRun x [c] room):=by
  exact IntegralMixedCausalUnitContinuation.compile_run initial Q hn hcap older ho [_] room [currentCode] ⟨rfl,rfl⟩

private def number (_ :List Bool):ℕ:=0
private def term (_ :List Bool):Term:=.const 0
private def radius (_ :List Bool):ℕ:=0
private theorem hn :UnaryFn number:=UnaryFn.const 0
private theorem ht :(fun q=>(term q).toData.toBits)∈FP:=by
  simpa only [term] using constFn_mem_FP (Term.const (0:ℤ)).toData.toBits
private theorem ha :∀q,(term q).arity≤number q:=by intro q;change 0≤0;omega
private theorem hR :BinaryFn radius:=BinaryFn.const 0
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR)

example (root :List Bool) :(IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR root 0 (Nat.zero_le _)).length=
    IntegralMixedAuxiliaryMarkedIntegerSource.number number root+8:=by
  simpa only [Nat.add_zero] using IntegralMixedMarkedRecordContinuation.oldCommands_length hn ht ha hR root 0 (Nat.zero_le _)

example (root aux :List Bool) :
    HEq (IntegralMixedMarkedRecordContinuation.framedState P D
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR))
      (IntegralMixedFramedHistoryFamilyBits.keyAt root
        (IntegralMixedAuxiliaryMarkedIntegerSource.number number root+8+0+([]:List (List Bool)).length) aux)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial number term (IntegralMixedOriginalRegularSource.radius radius) root)
      (by
        rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root]
        exact IntegralMixedStaticRecordPrefix.cap _ (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR root)))
      (IntegralMixedFullHistoryScript.continueRun
        (IntegralMixedMarkedRecordContinuation.start hn ht ha hR root 0 (Nat.zero_le _)) []
        (by rw [List.length_nil,Nat.add_zero,IntegralMixedCausalPlanBits.commands_length]
            exact IntegralMixedMarkedRecordContinuation.room_before hn ht ha hR root 0 (Nat.zero_le _))):=by
  exact IntegralMixedMarkedRecordContinuation.family_run hn ht ha hR root aux 0 [] (Nat.zero_le _)
    (by intro i hi;simp only [List.length_nil] at hi;omega)
    [] _ rfl

#print axioms IntegralMixedFramedFixedContinuation.index_append
#print axioms IntegralMixedFramedFixedContinuation.run_append
#print axioms IntegralMixedCausalUnitContinuation.records_reverse_get
#print axioms IntegralMixedCausalUnitContinuation.compile_commands
#print axioms IntegralMixedCausalUnitContinuation.compile_run
#print axioms IntegralMixedCausalUnitContinuation.compile_index
#print axioms IntegralMixedStaticRecordContinuation.prefix_records
#print axioms IntegralMixedStaticRecordContinuation.start_actual
#print axioms IntegralMixedStaticRecordContinuation.prefix_commands
#print axioms IntegralMixedStaticRecordContinuation.prefix_run
#print axioms IntegralMixedStaticRecordContinuation.prefix_index
#print axioms IntegralMixedMarkedRecordContinuation.start_actual
#print axioms IntegralMixedMarkedRecordContinuation.runAt
#print axioms IntegralMixedMarkedRecordContinuation.family_run
#print axioms IntegralMixedMarkedRecordContinuation.runAt_index
end CausalContinuationRegression
end RoadmapInternalContinuation

namespace RoadmapInternalRetainedCompletion
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace RetainedCompletionRegression

-- Every physical test polynomial, including multiplier variables, is preserved.
example (P :IntegralCriticalHistoryTask.Parameters) (D :Plan P)
    (H :IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C :List Bool→ℕ)
    (hs :IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key :List Bool→List Bool)
    (hpos :∀c,0<(family P D H).birth (key c)) (c :List Bool)
    (y :(family P D H).physical (key c)→ℝ)
    (hy :∀i,(((family P D H).state (key c)).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0)
    (test :MvPolynomial ((family P D H).physical (key c)) ℤ) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) c w,
      test.eval₂ (Int.castRingHom ℝ) (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos c w hw)=
        test.eval₂ (Int.castRingHom ℝ) y:=by
  obtain ⟨w,hw,_,hr⟩:=IntegralFramedPhysicalSquare.exists_raw P D H L F C hs key hpos c y hy
  exact ⟨w,hw,congrArg (fun z=>test.eval₂ (Int.castRingHom ℝ) z) hr⟩

section Chosen
open IntegralMixedChosenLocalRealization IntegralMixedFullHistoryScript
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
variable (x :State P S B m ι) (hm :m≤S) (hn :0<n)
  (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
  (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
  (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
    z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) m i)
  (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)

-- The constructed receipt keeps the guard and EVERY old raw coordinate together.
example (w :Choice x hm φ) :
    ∃r :Receipt x hm hn hcap z φ values (w.value x hm φ) (w.code x hm φ),
      Guard x hm φ r.command (w.value x hm φ) r.tuple ∧
      ∀i,r.tuple (oldColumn r.command i)=z i:=by
  obtain ⟨r⟩:=realize_receipt x hm hn hcap z hz φ hφ values H w
  exact ⟨r,r.guard,r.old_raw⟩

example (p :Polynomial ℤ) (hp :p≠0) (hd :p.natDegree≤2^B)
    (a :ℝ) (y :NextIndex ι (.integer p hp hd :Command P B)→ℝ) :
    ¬Guard x hm φ (.integer p hp hd) a y:=by exact id
end Chosen

example :IntegralMixedCanonicalPadding.values (-2) (fun i=>(i:ℝ)) 2 0=-2:=by
  norm_num [IntegralMixedCanonicalPadding.values]
example :IntegralMixedCanonicalPadding.values (-2) (fun i=>(i:ℝ)) 2 1=-2:=by
  norm_num [IntegralMixedCanonicalPadding.values]
example :IntegralMixedCanonicalPadding.values (-2) (fun i=>(i:ℝ)) 2 5=3:=by
  norm_num [IntegralMixedCanonicalPadding.values]
example :IntegralMixedCanonicalPadding.values (-2) (fun i=>(i:ℝ)) 0 5=5:=by
  norm_num [IntegralMixedCanonicalPadding.values]
example :((Polynomial.X-Polynomial.C (2:ℤ))^2).eval₂ (Int.castRingHom ℝ) 2=0:=by
  norm_num
example :(-1:ℝ)^UniformIntegralPowerSchedule.physical 7 4 2=-1:=
  (UniformIntegralPowerSchedule.physical_odd 7 4 2).neg_one_pow
example :(-1:ℝ)^UniformIntegralPowerSchedule.physical 7 4 5=-1:=
  (UniformIntegralPowerSchedule.physical_odd 7 4 5).neg_one_pow

#print axioms IntegralFramedPhysicalSquare.exists_raw
#print axioms IntegralFramedPhysicalSquare.exists_exact
#print axioms IntegralFramedPhysicalSquare.exists_full_observation
#print axioms IntegralFramedPhysicalSquare.point_of_joint_natural
#print axioms IntegralMixedCanonicalPadding.run_observation
#print axioms IntegralMixedSourceIntegerSeedTail.full_observation
#print axioms IntegralMixedMarkedSeedTailRetained.exists_observation
#print axioms IntegralMixedMarkedSeedTailRetained.sample_observation
#print axioms IntegralMixedMarkedSeedTailRetained.exists_vertex
#print axioms IntegralMixedChosenLocalRealization.Receipt.encoded
#print axioms IntegralMixedChosenLocalRealization.critical_receipt
#print axioms IntegralMixedChosenLocalRealization.cut_receipt
#print axioms IntegralMixedChosenLocalRealization.realize_receipt
end RetainedCompletionRegression
end RoadmapInternalRetainedCompletion

namespace RoadmapInternalGuardedLocal
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace GuardedLocalCompletionRegression
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

-- Retained equal endpoints emit no fresh commands, with the SAME indexed tuple.
example (x :State P S B m ι) (hm :m≤S) (hroom :m+1≤S) (hn :0<n)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG :g.val=d.labels.length+1)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old :IntegralMixedRelativeCuts.Choices x hm
      (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ) (u :Fin m) :
    ∃R :NativePair x d z φ values (.retained u) (.retained u) hn hcap,
      R.result.commands=[] ∧ GuardedProgram x hn hcap z φ values R.result.commands R.result.room R.result.codes
        R.result.tuple R.result.hom R.result.nextValues:=by
  obtain ⟨R,HR⟩:=optional_pair_guarded x hm hroom hn charge hdegree hcap d hk g hg HG z hz φ hφ values H old
    (.retained u) (.retained u) trivial trivial
  refine ⟨R,?_,HR⟩
  apply List.length_eq_zero_iff.mp
  simpa only [Endpoint.freshCount,Nat.add_zero] using R.count

-- A trace's arbitrary old physical polynomial retains its value, not just bank coordinates.
example (x :State P S B m ι) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin m→ℝ)
    (cs :List (Command P B)) (room :m+cs.length≤S+1) (codes :List (List Bool))
    (y :Index ι cs→ℝ) (ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (next :Fin (m+cs.length)→ℝ) (H :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (p :MvPolynomial ι ℤ) :
    (MvPolynomial.rename (oldColumns cs) p).eval₂ (Int.castRingHom ℝ) y=p.eval₂ (Int.castRingHom ℝ) z:=by
  rw [MvPolynomial.eval₂_rename]
  exact congrArg (fun f=>p.eval₂ (Int.castRingHom ℝ) f) (funext H.old_raw)

example :(-1:ℝ)^physical 8 4 2=(-1:ℝ)^physical 8 4 6:=by
  rw [(physical_odd 8 4 2).neg_one_pow,(physical_odd 8 4 6).neg_one_pow]
example :physical 3 2 1=7:=by norm_num [physical,cap,birth,MonicParameterPowerSchedule.weight]
example :physical 3 2 2=91:=by norm_num [physical,cap,birth,MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]

#print axioms FreshReceipt.fresh
#print axioms critical_guard_receipt
#print axioms selected_cut_guard_receipt
#print axioms selected_cut_guard_ofRule
#print axioms joint_endpoint_guard_receipt
#print axioms optional_pair_guarded
#print axioms GuardedProgram.decode
#print axioms GuardedProgram.code_count
#print axioms GuardedProgram.roots
#print axioms GuardedProgram.generators
#print axioms GuardedProgram.quotients
#print axioms GuardedProgram.old_raw
#print axioms GuardedProgram.old_hom
#print axioms exists_guarded_seeds
#print axioms IntegralMixedPointCompanion.Realized.selected_correlation
#print axioms IntegralMixedPointCompanion.Realized.all_coordinate_correlation
#print axioms PhysicalEndpointRecord.selected_correlation
end GuardedLocalCompletionRegression
end RoadmapInternalGuardedLocal

namespace RoadmapInternalRowFields
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProperRowFieldsRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
variable (z : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z))
  (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
-- Coordinate digits are not silently clipped by the query header.
example (mean : Bool) :get P .slot13 (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 mean z)=
    IntegralMixedRoadmapProperRow.relativeCoordinate z :=
  IntegralMixedRoadmapProperRow.parent_coordinate hn ht ha hR0 mean z hg
-- Both prepared queries retain virtual context 2.
example (mean : Bool) :get P .slot15 (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 mean z)=2 :=
  IntegralMixedRoadmapProperRow.parent_context hn ht ha hR0 mean z
-- The actual rule freezes exactly the intended chronological prefix plus swept height.
example (mean : Bool) :((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mean z)).critical.offset.val=
    IntegralMixedRoadmapProperRow.offset z :=
  IntegralMixedRoadmapProperRow.rule_offset hn ht ha hR0 mean z hv hg
-- Subsequent coordinate modulo reduction also leaves the ordinal axis unchanged.
example (mean : Bool) :(IntegralMixedCoordinateCoefficientSnapshot.coordinate G
    (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mean z)
    (get P .slot13 (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 mean z))).val=
    IntegralMixedRoadmapProperRow.relativeCoordinate z :=
  IntegralMixedRoadmapProperRow.selected_coordinate hn ht ha hR0 mean z hv hg
#print axioms IntegralMixedRoadmapProperRow.parent_coordinate
#print axioms IntegralMixedRoadmapProperRow.parent_context
#print axioms IntegralMixedRoadmapProperRow.parentData_offset
#print axioms IntegralMixedRoadmapProperRow.rule_offset
#print axioms IntegralMixedRoadmapProperRow.selected_coordinate
#print axioms IntegralMixedRoadmapProperRow.parentKey_aux
end ProperRowFieldsRegression
end
end RoadmapInternalRowFields

namespace RoadmapInternalNativeGeometry
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open LeanCanny.Connectivity
open Turing.MultiTapeTM
open IntegralMixedRoadmapGraph
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example : nativeConnectedLanguage hn ht ha hR0∈PSPACE:=native_connected_mem_PSPACE hn ht ha hR0
example : nativeReachLanguage hn ht ha hR0∈PSPACE:=native_reach_mem_PSPACE hn ht ha hR0
example (c a b : List Bool) (H : RawReachable hn ht ha hR0 c a b) :
    ImplicitGraph.Reachable (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c) (width hn ht ha hR0 c)
      (label hn ht ha hR0 c a) (label hn ht ha hR0 c b):=
  (label_reachable_iff hn ht ha hR0 c a b).mpr H
example (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    pointAt hn ht ha hR0 c q hv hc∈zeroSet (n:=n) (t:=t) (R0:=R0) c:=
  pointAt_zero hn ht ha hR0 c q hv hc
example (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (hI : pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c) (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd):=
  identity_joined hn ht ha hR0 c a b hA hB hc hd hI
end
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.label_reachable_iff
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.connected_iff_native
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.native_connected_mem_PSPACE
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.native_reach_mem_PSPACE
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.pointAt_occurrence
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.original_proper
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.exists_global_seed
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.identity_pointAt_eq
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.identity_joined
end RoadmapInternalNativeGeometry

namespace RoadmapInternalMidSignatureActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper IntegralMixedRoadmapProperMidSignature
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (H : IntegralMixedRoadmapEdge.Proper hn ht ha hR0 (pair a b)) :
    HEq (midpointPoint hn ht ha hR0 a hA) (midpointPoint hn ht ha hR0 b hB):=
  proper_midpoint_eq hn ht ha hR0 a b hA hB H
example (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (H : pair a b∈IntegralMixedRoadmapProperMidSignature.language hn ht ha hR0)
    (i : ℕ) (hi : i < IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a+2) :
    signatureValue hn ht ha hR0 a hA i=signatureValue hn ht ha hR0 b hB i:=
  language_values hn ht ha hR0 a b hA hB H i hi
end
example (n initial : ℕ) (q : List Bool) :
    Nat.fromBitsLE (WordList.get (signature n initial q) (n+1))=producer true q:=
  signature_lookup_right n initial q
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.signature_lookup_frozen
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.signature_lookup_left
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.signature_lookup_free
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.signature_lookup_right
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.language_values
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.midpointPoint_frozen
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.midpointPoint_free
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.midpointPoint_height
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.point_signature
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.language_midpoint_eq
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature.proper_midpoint_eq
end RoadmapInternalMidSignatureActual

namespace RoadmapInternalGuardCompleteActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace PhysicalGuardCompleteRegression
private def constantSign (z :List Bool):=if Nat.fromBitsLE (pairFst (pairSnd z))=0 then
  InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0
private def repeatedSign (z :List Bool):=if Nat.fromBitsLE (pairFst (pairSnd z))=1 then
  InfinitesimalSign.encode (-1) else if Nat.fromBitsLE (pairFst (pairSnd z))≤2 then
    InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0

example :FiniteCoefficientSignScan.Guards constantSign (fun _=>InfinitesimalSign.encode 1)
    (fun _=>0) (fun _=>0) (fun _=>2) []:=by
  dsimp only [FiniteCoefficientSignScan.Guards]
  refine ⟨by omega,?_,?_,Or.inl (by decide)⟩
  · decide
  · intro e _he hed
    simp only [FiniteCoefficientSignScan.Zero,FiniteCoefficientSignScan.query,constantSign,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,ite_eq_right (Nat.ne_of_gt hed)]

example :¬FiniteCoefficientSignScan.Guards constantSign (fun _=>InfinitesimalSign.encode 0)
    (fun _=>0) (fun _=>0) (fun _=>2) []:=by
  intro H
  rcases H.2.2.2 with H|H
  · exact H rfl
  · exact (show ¬FiniteCoefficientSignScan.Zero constantSign [] 0 0 by decide) H

example :FiniteCoefficientSignScan.Guards repeatedSign (fun _=>InfinitesimalSign.encode 1)
    (fun _=>0) (fun _=>2) (fun _=>2) []:=by
  dsimp only [FiniteCoefficientSignScan.Guards]
  refine ⟨by omega,?_,by omega,Or.inl (by decide)⟩
  decide

example :¬FiniteCoefficientSignScan.Guards repeatedSign (fun _=>InfinitesimalSign.encode 0)
    (fun _=>0) (fun _=>2) (fun _=>2) []:=by
  intro H
  rcases H.2.2.2 with H|H
  · exact H rfl
  · exact (show ¬FiniteCoefficientSignScan.Zero repeatedSign [] 0 0 by decide) H

example :((Polynomial.X-Polynomial.C (2:ℤ))^2).eval₂ (Int.castRingHom ℝ) 2=0:=by norm_num

-- Full-word malformedness remains a necessary guard condition.
example {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
    (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
    {R :List Bool→ℕ} (hR :BinaryFn R) (outer :Bool) (c w :List Bool)
    (hnot :¬SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer)
      (IntegralMixedPhysicalMarkedTest.sampleContext c) w) :
    pair c w∉IntegralMixedPhysicalGuardScan.language hn ht ha hR outer:=by
  rw [IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha hR outer]
  rintro ⟨hv,_⟩
  exact hnot hv

#print axioms IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_inactive
#print axioms IntegralMixedPhysicalPointCompanionScan.critical_holds_iff
#print axioms IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff
#print axioms IntegralMixedPhysicalCutCoefficientSemantics.coefficient_evaluation_at
#print axioms IntegralMixedPhysicalCutCoefficientSemantics.guards_of_coefficient_receipt
#print axioms IntegralMixedPhysicalCutCoefficientSemantics.guards_of_valid_degree
end PhysicalGuardCompleteRegression
end RoadmapInternalGuardCompleteActual

namespace RoadmapInternalGuardedPrefixActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedOptionalEndpoints UniformIntegralPowerSchedule
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace GuardedPrefixBridgeRegression

-- Empty local continuation retains the exact old physical tuple, including all multipliers.
example {n S B :ℕ} {P :SpatialSource n} (initial :State P S B 0 (Fin 0))
    (Q :SpatialSource n) (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (z :Index (Fin 0) older→ℝ)
    (hz :∀i,((run initial older ho).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃y :Index (Fin 0) older→ℝ,y=z ∧
      ∀i,((run initial older ho).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0:=by
  obtain ⟨y,hy,hr⟩:=IntegralMixedFramedFixedContinuation.tuple_append initial Q hQ older ho []
    (by simpa only [List.length_nil,Nat.add_zero] using ho) z hz
  exact ⟨y,eq_of_heq hy,hr⟩

-- Fresh local guarded programs cannot smuggle in an integer command.
example {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
    (x :State P S B m ι) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin m→ℝ)
    (p :Polynomial ℤ) (hp :p≠0) (hd :p.natDegree≤2^B) (room :m+1≤S+1)
    (code :List Bool)
    (y :IntegralMixedFullHistoryScript.Index ι [(.integer p hp hd :IntegralMixedFullHistoryScript.Command P B)]→ℝ)
    (ψ :(IntegralMixedFullHistoryScript.continueRun x [.integer p hp hd] room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (next :Fin (m+1)→ℝ)
    (H :GuardedProgram x hn hcap z φ values [.integer p hp hd] room [code] y ψ next)
    (HC :Canonical x)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) :False:=by
  exact (H.birth_guards HC hφ).2

#print axioms IntegralMixedFramedFixedContinuation.tuple_append
#print axioms IntegralMixedFramedFixedContinuation.tuple_list
#print axioms IntegralMixedMarkedConstructedPrefix.compiled_commands
#print axioms GuardedProgram.birth_guards
end GuardedPrefixBridgeRegression
end RoadmapInternalGuardedPrefixActual

namespace RoadmapInternalRowQuotientsActual
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProperRowQuotientsRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
local notation "L"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "F"=>IntegralFramedBankQuery.Bank.factor BK
local notation "C"=>IntegralFramedBankQuery.Bank.seed BK
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
-- The complete native theorem is available, not just its header or helper declarations.
#check IntegralMixedRoadmapProperRow.statistic_parent_quotients
-- Current-Q probes still use their own complete-word context; no ordinary/mean word copying.
example (mode : Bool) (z w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input P D H L F C hs (IntegralMixedRoadmapProperRow.terminal hn ht ha hR0 mode)
        (IntegralMixedRoadmapProperRow.positive hn ht ha hR0 mode)) z w) :
    SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapProperRow.context hn ht ha hR0 mode z) w :=
  (IntegralMixedRoadmapProperRow.valid_at_context hn ht ha hR0 mode z w).mp hw
example (mode : Bool) (z : List Bool)
    (hf : (G).birth (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mode z)≤
      (G).birth (IntegralMixedRoadmapProperRow.terminal hn ht ha hR0 mode z)) :
    (G).birth (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mode z)≤
      (G).birth (IntegralMixedRoadmapProperRow.terminal hn ht ha hR0 mode z) :=hf
#print axioms IntegralMixedRoadmapProperRow.statistic_parent_quotients
end ProperRowQuotientsRegression
end
end RoadmapInternalRowQuotientsActual

namespace RoadmapInternalBadProbeConverseActual
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ActualBadProbeRegression
private def Q : SpatialSource 1 where
 low:=-1
 leading:=-2
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
example : IntegralMixedCutRecordConstructor.degreeResidue Q
 (IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)=0:=Nat.mod_self _
example (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree) :
 IntegralMixedCutRecordConstructor.degreeResidue Q d=d:=Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd)
example (d : ℕ) : IntegralMixedCutRecordConstructor.degreeResidue Q
 ((IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree+1)*d)=0:=Nat.mul_mod_right _ _
example : (-6:ℤ)%6=0:=by decide
example : (-12:ℝ)/(-6)=2:=by norm_num
example : ((1:Polynomial ℝ).eval 0)≠0:=by norm_num
example : ∀a:ℝ,(Polynomial.X^2+1:Polynomial ℝ).eval a≠0:=by
 intro a h
 norm_num at h
 nlinarith [sq_nonneg a]
example : (PaddedIntegralNormalization.polynomial (1:Polynomial ℤ) 0 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial,FixedDegreeIntegralNormalization.polynomial]
example : (PaddedIntegralNormalization.polynomial (Polynomial.X^2+1:Polynomial ℤ) 2 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial]
example : IntegralMixedChronologicalCutCode.ordinaryTag 0=.coordinate:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 1=.squarefree:=rfl
example : IntegralMixedChronologicalCutCode.ordinaryTag 2=.value:=rfl
example (old aux p q :List Bool) (codes:List (List Bool)) :
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes p aux)=
 IntegralMixedCausalRecordPlanBits.count (IntegralMixedMarkedPrefixRun.reservedRoot old codes q aux):=by
 rw [IntegralMixedMarkedPrefixRun.reserved_count,IntegralMixedMarkedPrefixRun.reserved_count]
example (q:List Bool) (codes:List (List Bool)) (last:List Bool)
 (h:IntegralMixedRoadmapBadProbePacket.raw q=WordList.encode (codes++[last])) :
 IntegralMixedRoadmapBadProbePacket.prefixCodes q=codes:=
 IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq q codes last h
section Selected
variable {n S B m:ℕ} {P:SpatialSource n} {ι:Type} (x:State P S B m ι) (hm:m≤S)
 (r:IntegralMixedCriticalSweep.Rule n) (φ:x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (c:Choices x hm r φ) (a:ℝ)
example : a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c ↔
 ∃k:Kind P r,Valid x hm r φ k ∧ IntegralMixedSelectedBadMembership.Ordinary r k ∧(factor x hm r k).eval₂ φ.toRingHom a=0:=
 IntegralMixedSelectedBadMembership.mem_bad_iff x hm r φ c a
example (j:ℕ) (d:Choices x hm (IntegralMixedSweepRetarget.rule r j) φ) :
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm (IntegralMixedSweepRetarget.rule r j) φ d ↔
 a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ c:=
 IntegralMixedSweepRetarget.bad_iff x hm r j φ c d a
end Selected

#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedSelectedBadMembership.valid_kind_selected
#print axioms LeanCanny.Encoding.IntegralMixedCutRecordConstructor.command_decode_mod
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence.interpreted_present_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.prefix_congr
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.reserved_eq
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_iff
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedPoint.values_eq
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.exists_interpretation
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.mem_bad_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet.bad_eq_of_parent_fields
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.family_eq_original
#print axioms LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot.family_keyAt
#print axioms LeanCanny.Algebra.IntegralMixedSweepRetarget.bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedChronologicalCutCode.raw_chosenCode_actual
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape.command
#print axioms LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation.quotient_prefix_at
#print axioms LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction.rule_at_parent
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_eq
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint.quotients
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_retarget_factor_iff
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedRuling.rule_raw
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.ofState_mem_bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.ordinary
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance.rule_raw

private theorem count_nil :WordListRecords.count ([] : List Bool)=0:=rfl
private theorem decode_encode (k : ℕ) :Nat.fromBitsLE (BinaryNatCode.encode k)=k:=Nat.fromBitsLE_bits k
private def basePacket:=IntegralMixedRoadmapBadProbePacket.packet [] (WordList.encode [[]]) [] []
 (BinaryNatCode.encode 0) (BinaryNatCode.encode 1)
private def hint (tag j choice degree : ℕ):=WordList.encode
 [BinaryNatCode.encode tag,BinaryNatCode.encode j,BinaryNatCode.encode choice,BinaryNatCode.encode degree]
example : IntegralMixedRoadmapBadProbePacket.HintGood 3 8 2 (pair basePacket (hint 2 1 3 2)):=by
 norm_num [IntegralMixedRoadmapBadProbePacket.HintGood,IntegralMixedChronologicalFrameCode.Good,
 IntegralMixedRoadmapBadProbePacket.creating,IntegralMixedRoadmapBadProbePacket.count,
 IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapBadProbePacket.producer,
 IntegralMixedRoadmapBadProbePacket.endpoints,IntegralMixedRoadmapBadProbePacket.raw,
 IntegralMixedRoadmapBadProbePacket.field,basePacket,hint,IntegralMixedRoadmapBadProbePacket.packet,
 pairFst_pair,pairSnd_pair,WordListRecords.count_encode,count_nil,WordList.get_encode,decode_encode]
example : ¬IntegralMixedRoadmapBadProbePacket.HintGood 3 8 2 (pair basePacket (hint 3 1 3 2)):=by
 norm_num [IntegralMixedRoadmapBadProbePacket.HintGood,IntegralMixedChronologicalFrameCode.Good,
 IntegralMixedRoadmapBadProbePacket.creating,IntegralMixedRoadmapBadProbePacket.count,
 IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapBadProbePacket.producer,
 IntegralMixedRoadmapBadProbePacket.endpoints,IntegralMixedRoadmapBadProbePacket.raw,
 IntegralMixedRoadmapBadProbePacket.field,basePacket,hint,IntegralMixedRoadmapBadProbePacket.packet,
 pairFst_pair,pairSnd_pair,WordListRecords.count_encode,count_nil,WordList.get_encode,decode_encode]
example : ¬IntegralMixedRoadmapBadProbePacket.HintGood 3 8 2 (pair basePacket (hint 2 0 3 2)):=by
 norm_num [IntegralMixedRoadmapBadProbePacket.HintGood,IntegralMixedChronologicalFrameCode.Good,
 IntegralMixedRoadmapBadProbePacket.creating,IntegralMixedRoadmapBadProbePacket.count,
 IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapBadProbePacket.producer,
 IntegralMixedRoadmapBadProbePacket.endpoints,IntegralMixedRoadmapBadProbePacket.raw,
 IntegralMixedRoadmapBadProbePacket.field,basePacket,hint,IntegralMixedRoadmapBadProbePacket.packet,
 pairFst_pair,pairSnd_pair,WordListRecords.count_encode,count_nil,WordList.get_encode,decode_encode]
example : ¬IntegralMixedRoadmapBadProbePacket.HintGood 3 8 2 (pair basePacket (hint 2 1 3 5)):=by
 norm_num [IntegralMixedRoadmapBadProbePacket.HintGood,IntegralMixedChronologicalFrameCode.Good,
 IntegralMixedRoadmapBadProbePacket.creating,IntegralMixedRoadmapBadProbePacket.count,
 IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapBadProbePacket.producer,
 IntegralMixedRoadmapBadProbePacket.endpoints,IntegralMixedRoadmapBadProbePacket.raw,
 IntegralMixedRoadmapBadProbePacket.field,basePacket,hint,IntegralMixedRoadmapBadProbePacket.packet,
 pairFst_pair,pairSnd_pair,WordListRecords.count_encode,count_nil,WordList.get_encode,decode_encode]
example : IntegralMixedRoadmapBadProbePacket.creating 8 basePacket=8:=by decide
example : IntegralMixedCausalRecordPlanBits.count
 (IntegralMixedRoadmapBadProbePacket.preparedRoot 3 (pair basePacket (hint 2 1 3 2)))=1:=
 (IntegralMixedRoadmapBadProbePacket.prepared_count 3 _ (by decide)).trans (by decide)
example : (IntegralMixedRoadmapBadProbePacket.prefixCodes basePacket).length=0:=by decide
example : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedChronologicalCutCode.ordinaryTag 2)=2:=rfl

#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedFieldVertex.exists_parent_fields
#print axioms LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits.selection_of_command
#print axioms LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits.selection_of_command_heq
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.mem_bad_iff_coded
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.coded_transport
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.coded_length
#print axioms LeanCanny.Algebra.IntegralMixedCutCreationReceipt.coded_command
#print axioms LeanCanny.Algebra.IntegralMixedCutCreationReceipt.coded_instruction
#print axioms LeanCanny.Algebra.IntegralMixedCutCreationReceipt.native_root_iff
#print axioms LeanCanny.Algebra.IntegralMixedCutCreationReceipt.atKey_isCut
#print axioms LeanCanny.Algebra.IntegralMixedCutCreationReceipt.atKey_some_native
#print axioms LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt.instruction_record
#print axioms LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt.native_receipt
#print axioms LeanCanny.Encoding.IntegralMixedMarkedReservedSelectionReceipt.native_receipt
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRootAcceptance.accepted
#print axioms LeanCanny.Encoding.IntegralMixedChronologicalCutCode.raw_offset
#print axioms LeanCanny.Algebra.IntegralMixedPrefixSnapshot.Data.coded_hint
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent.packet_birth
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent.auxiliary_cap
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbePreparedWord.exists_fields
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTask.saved
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTask.snapshot
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRuntime.receipt
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRuntime.bounds
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCodedTransport.actual
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeComplete.at_hint
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics.complete
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics.hasBadProbe_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics.noBadProbe_iff
end ActualBadProbeRegression
end
end RoadmapInternalBadProbeConverseActual

namespace RoadmapInternalMarkedRetentionActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedRetention IntegralMixedAuxiliaryMarkedIntegerSource
open IntegralMixedOriginalRegularSource
open IntegralMixedPhysicalMarkedTest
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (cL cR wL wR : List Bool)
 (hL : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cL) wL)
 (hR : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cR) wR)
 (hc : candidate cL=candidate cR)
 (he : ∀i < number n cL+8,IntegralMixedPhysicalMarkedSemantics.env hn ht ha (radius_binary hR0) false cL wL hL i=
   IntegralMixedPhysicalMarkedSemantics.env hn ht ha (radius_binary hR0) false cR wR hR i)
 (HL : pair cL wL∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false) :
 pair cR wR∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=
 language_transfer hn ht ha hR0 cL cR wL wR hL hR hc he HL
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.leaves_transfer
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.mark_eq
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.regular_eq
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.language_transfer
end RoadmapInternalMarkedRetentionActual

namespace RoadmapInternalMarkedFieldRetentionActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedRetention IntegralMixedAuxiliaryMarkedIntegerSource
open IntegralMixedOriginalRegularSource IntegralMixedPhysicalMarkedTest
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (cL cR wL wR : List Bool)
 (hL : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cL) wL)
 (hR : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cR) wR)
 (hc : candidate cL=candidate cR)
 (he : ∀i < number n cL+8,
   IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext cL) wL hL i=
   IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext cR) wR hR i)
 (HL : pair cL wL∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false) :
 pair cR wR∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=
 language_transfer_fields hn ht ha hR0 cL cR wL wR hL hR hc he HL
example (ctx w : List Bool)
 (hV : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext ctx) w)
 (i : ℕ) (hi : i < number n ctx+8) :
 IntegralMixedPhysicalMarkedSemantics.env hn ht ha (radius_binary hR0) false ctx w hV i=
 IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext ctx) w hV i:=
 env_field hn ht ha hR0 ctx w hV i hi
#print axioms LeanCanny.Encoding.IntegralFramedPhysicalBankTerm.env_chronological
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.env_field
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention.language_transfer_fields
end RoadmapInternalMarkedFieldRetentionActual

namespace RoadmapInternalRowMeanRuleActual
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProperRowMeanRuleRegression
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
example (z : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    HEq ((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 true z))
      (IntegralMixedMeanCenteredSweep.rule ((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z))
        (IntegralMixedRoadmapProperRow.meanReference hn ht ha hR0 false z hv hg)
        (IntegralMixedRoadmapProperRow.meanReference hn ht ha hR0 true z hv hg)) :=
  IntegralMixedRoadmapProperRow.actual_mean_rule hn ht ha hR0 z hv hg
-- References address the genuine old chronological producers, even after captures/padding.
example (right : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    (IntegralMixedRoadmapProperRow.meanReference hn ht ha hR0 right z hv hg).val=
      IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false z-1-
        IntegralMixedRoadmapProperRow.oldProducer right z :=rfl
#print axioms IntegralMixedRoadmapProperRow.parent_denominator_eq
#print axioms IntegralMixedRoadmapProperRow.actual_mean_rule
end ProperRowMeanRuleRegression
end
end RoadmapInternalRowMeanRuleActual

namespace RoadmapInternalConstructedObservationActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option warningAsError true
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

-- The natural observation retains every column, not only scalar coordinates.
example {n S B :ℕ} {P :SpatialSource n} (x :State P S B 0 (Fin 0))
    (cs :List (Instruction n B)) (hc :cs.length≤S+1)
    (z :Index (Fin 0) cs→ℝ)
    (hz :∀i,((run x cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃u :ℕ→ℝ,(IntegralMixedFramedRunObservation.ofCommands x cs hc).Roots u ∧
      ∀i,u (IntegralMixedFramedPhysicalIndex.enumerate cs i).val=z i:=
  IntegralMixedFramedFixedContinuation.tuple_observation x cs hc z hz

-- An empty observation introduces no spurious coordinate restriction.
example {n S B :ℕ} {P :SpatialSource n} (x :State P S B 0 (Fin 0))
    (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) (fun i=>Fin.elim0 i)=0) :
    ∃u :ℕ→ℝ,(IntegralMixedFramedRunObservation.ofCommands x [] (by simp)).Roots u:=by
  obtain ⟨u,hu,_⟩:=IntegralMixedFramedFixedContinuation.tuple_observation x [] (by simp)
    (fun i=>Fin.elim0 i) hz
  exact ⟨u,hu⟩

#print axioms IntegralMixedMarkedConstructedPrefix.instruction_receipt
#print axioms IntegralMixedFramedFixedContinuation.tuple_observation
#print axioms IntegralMixedFramedFixedContinuation.tuple_append_observation
#print axioms IntegralMixedMarkedConstructedPrefix.exists_observation
end RoadmapInternalConstructedObservationActual

namespace RoadmapInternalNoCriticalActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
noncomputable section
namespace RealCriticalCoverRegression
private def P : SpatialSource 1 where
 low:=-1
 leading:=1
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
private def F : Frame 1:={
 frozen:=∅
 scales _:=1
 scales_ne_zero _:=one_ne_zero
 heights _:=.constant 0 }
private theorem HF : FreeNormal F:=fun _ _=>⟨rfl,rfl⟩
private theorem hh : (⟨0,by decide⟩ : Fin 2)∉F.frozen:=Finset.notMem_empty _
private theorem peval (y : Fin 2→ℝ) :
 (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=
   -1+y 0^2+y 1^2:=by
 simp [P,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two]
 ring
private theorem gradient (y : Fin 2→ℝ) :
 (MvPolynomial.pderiv (1 : Fin 2) (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
   (Int.castRingHom ℝ) y=2*y 1:=by
 norm_num [P,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two,MvPolynomial.pderiv_pow]
 simp [Fin.sum_univ_two,Pi.single_apply]
example : (1 : ℝ)∈realCriticalValues P (line F 0) (Fin.elim0 : Fin 0→ℝ) 0:=by
 apply (line_realCriticalValues_iff P F Fin.elim0 0 hh HF 1).mpr
 refine ⟨![1,0],⟨?_,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩,by simp,?_⟩
 · rw [peval]
   norm_num
 · intro i _ hi
   have HE : i=1:=by fin_cases i <;> simp_all
   subst i
   rw [gradient]
   norm_num
example : (-1 : ℝ)∈realCriticalValues P (line F 0) (Fin.elim0 : Fin 0→ℝ) 0:=by
 apply (line_realCriticalValues_iff P F Fin.elim0 0 hh HF (-1)).mpr
 refine ⟨![-1,0],⟨?_,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩,by simp,?_⟩
 · rw [peval]
   norm_num
 · intro i _ hi
   have HE : i=1:=by fin_cases i <;> simp_all
   subst i
   rw [gradient]
   norm_num
private theorem zero_regular : (0 : ℝ)∉realCriticalValues P (line F 0) (Fin.elim0 : Fin 0→ℝ) 0:=by
 intro H
 obtain ⟨y,hy,hy0,hg⟩:=(line_realCriticalValues_iff P F Fin.elim0 0 hh HF 0).mp H
 have HD:=hg 1 (Finset.notMem_empty _) (by decide)
 rw [gradient] at HD
 have Hz:=hy.1
 rw [peval,hy0] at Hz
 nlinarith
example : (0 : ℝ)∉realCriticalValues P (line F 0) (Fin.elim0 : Fin 0→ℝ) 0:=zero_regular
example (y : Fin 2→ℝ) (hy : y∈shiftedSlice P (line F 0) (Fin.elim0 : Fin 0→ℝ) 0 0) :
 Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
   (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) (line F 0).frozen (coordinateNormals (line F 0)) y):=
 regular_of_not_realCriticalValue P (line F 0) Fin.elim0 0 0 zero_regular y hy

end RealCriticalCoverRegression

namespace NoCriticalOriginalRegression
private def descriptor : IntegralMixedChronologicalFrame.Descriptor 2 4 where
  labels:=[⟨1,by decide⟩,⟨0,by decide⟩]
  length_le:=by decide
example : (descriptor.reference ⟨0,by decide⟩).val=2:=by decide
example : (descriptor.reference ⟨1,by decide⟩).val=3:=by decide
example : descriptor.frame.heights (0 : Fin 3)=.reference 2:=descriptor.height ⟨0,by decide⟩
example : descriptor.frame.heights (1 : Fin 3)=.reference 3:=descriptor.height ⟨1,by decide⟩
example : (2 : Fin 3)∉descriptor.frame.frozen:=by rw [descriptor.frozen_mem];decide
example : PrefixFrozen descriptor.frame:=descriptor.prefix_frozen
example : FreeNormal descriptor.frame:=descriptor.free_normal
example : (descriptor.atomic.pointData (2 : Fin 3) 2
    (by rw [descriptor.frozen_mem];decide) (by rw [descriptor.frozen_mem];decide)).code=
    IntegralMixedChronologicalFrameCode.code 2 (IntegralMixedChronologicalFrameCode.labels descriptor) 2 2:=
  descriptor.atomic_pointData_code 2 2 _ _
private def observation : IntegralMixedFullBankObservation.Data where
  bank:=⟨2,1,2,![-2,3]⟩
  column i:=if i=0 then 4 else 1
private def tuple (i : ℕ) : ℝ:=if i=4 then -2 else if i=1 then 3 else 0
example : observation.point tuple 0=256:=by
  norm_num [observation,tuple,IntegralMixedFullBankObservation.Data.point,
    IntegralMixedFramedBankObservation.Data.point,UniformIntegralPowerSchedule.weights,
    UniformIntegralPowerSchedule.birth,UniformIntegralPowerSchedule.cap,
    MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
  have HD : observation.bank.denominator ⟨0,by decide⟩=(-2 : ℤ):=rfl
  rw [HD]
  norm_num
example : observation.point tuple 1=1:=by
  norm_num [observation,tuple,IntegralMixedFullBankObservation.Data.point,
    IntegralMixedFramedBankObservation.Data.point,UniformIntegralPowerSchedule.weights,
    UniformIntegralPowerSchedule.birth,UniformIntegralPowerSchedule.cap,
    MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
  change (3 : ℝ)/3=1
  norm_num
example : observation.point tuple 2=0:=by
  simp [observation,IntegralMixedFullBankObservation.Data.point,IntegralMixedFramedBankObservation.Data.point]
end NoCriticalOriginalRegression
#print axioms LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor.atomic_pointData
#print axioms LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor.atomic_pointData_code
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical.command
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical.command_key
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical.empty_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.query_candidate
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.query_dimension
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.query_count
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.query_birth
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.coarse_point_good
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.parent_point_good
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.query_degree
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.witness_coarse_critical_free
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.noCritical_coarse_critical_free
#print axioms LeanCanny.Algebra.IntegralMixedFullBankObservation.data_sibling
#print axioms LeanCanny.Algebra.IntegralMixedFullBankObservation.point_sibling
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext.valid_full
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext.natural_full
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext.child_point_field
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext.parentValues_field
#print axioms LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext.endpoint_field
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.fields_sound
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.witness_parent_fields
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.witness_endpoint_field
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.witness_original_critical_free
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProperCritical.noCritical_original_critical_free
end
end RoadmapInternalNoCriticalActual

namespace RoadmapInternalProducerBoundsActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
 (hd : 0<IntegralMixedRoadmapAtomic.depth q) (j : ℕ)
 (hj : IntegralMixedRoadmapAtomic.depth q ≤ j) (hjn : j ≤ IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) :
 midProducer (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q j <
 IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (pair q (BinaryNatCode.encode j)):=
 mid_producer_before_probe hn ht ha hR0 q hv hd j hj hjn
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
 childProducer (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
  (IntegralMixedRoadmapAtomic.depth q) < IntegralMixedRoadmapProperRow.creating hn ht ha hR0
  (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q))):=
 child_producer_before_probe hn ht ha hR0 q hv _ le_rfl (IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv)
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.creating_eq
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.child_producer_before_probe
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapProper.mid_producer_before_probe
end RoadmapInternalProducerBoundsActual

namespace RoadmapInternalLocalFrameActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapLocalFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapLocalFrame.midpoint
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
 (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
 (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
 (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) :
 midpoint hn ht ha hR0 q hv∈LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber.physical
  ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ
  ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
    field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2):=
 midpoint_physical hn ht ha hR0 q hv HB HR φ Hφ
end
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.midpoint_source_rows
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.child_frozen_labels
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.child_height
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.midpoint_physical
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.child_frozen
#print axioms LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback.constraint
#print axioms LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback.raw_physical
#print axioms LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback.raw_frozen
end RoadmapInternalLocalFrameActual

namespace RoadmapInternalSeedMetadataActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapSeedMetadata
open scoped Classical
namespace SeedMetadataRegression
example : selected 3 0=0:=rfl
example : selected 3 1=3:=rfl
example : selected 3 2=2:=rfl
example : selected 3 3=1:=rfl
example : selected 3 4=0:=rfl
example : selected 3 5=0:=rfl
example : selected 0 0=0:=rfl
example : selected 0 1=0:=rfl
example : selected 0 2=0:=rfl
example (a : ℕ) : selected 3 a<4:=selected_lt 3 a
example : (IntegralMixedRoadmapChain.seedCodes 3).length=5:=seedCodes_length 3
example : (IntegralMixedRoadmapChain.seedCodes 3)[1]?=some
    (IntegralMixedChronologicalFrameCode.code 3 [] 0 3):=seedCode_get 3 1 (by decide)
example : (IntegralMixedRoadmapChain.seedCodes 3)[4]?=some
    (IntegralMixedChronologicalFrameCode.code 3 [] 0 0):=seedCode_get 3 4 (by decide)
example : (IntegralMixedCommandHeaderBits.zero).context=0:=rfl
example : (⟨1,3,0,0,0,0,1⟩ : IntegralMixedCommandHeaderBits.Header).coordinate=3:=rfl
example {n B : ℕ} {P : SpatialSource n} (rule : CriticalRule n) :
    IntegralMixedCommandHeaderBits.command ((IntegralMixedCausalRecordBits.Template.critical (P:=P) (B:=B) rule).command (-3) (by decide))=
      (IntegralMixedCausalRecordBits.Template.critical (P:=P) (B:=B) rule).header :=
  IntegralMixedCausalRecordBits.Template.header_command _ _ _
example {n B : ℕ} {P : SpatialSource n} (p : Polynomial ℤ) (hp : p≠0) (hd : p.natDegree≤2^B) :
    IntegralMixedCommandHeaderBits.command ((IntegralMixedCausalRecordBits.Template.integer (P:=P) p hp hd).command (-2) (by decide))=
      IntegralMixedCommandHeaderBits.zero :=rfl
end SeedMetadataRegression
#print axioms LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt.commands_header
#print axioms LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt.chronological_headers
#print axioms LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt.integer_header
#print axioms LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt.later_header
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.selected_lt
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.seedCode_get
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.raw_lookup
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.stageHeader_records
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.prelude_header
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.later_header
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.dimension_root
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.initial_root
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.code_root
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.seed_header
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.native_header
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.prelude_inactive
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.critical_active
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.critical_selected
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.prefix_arity
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.no_cut_at
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.before_probe_holds
end RoadmapInternalSeedMetadataActual

namespace RoadmapInternalProperOrderActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
namespace ProperOrderRegression
example : IntegralMixedPhysicalFieldEquality.newest 5 0=4:=rfl
example : IntegralMixedPhysicalFieldEquality.newest 5 2=2:=rfl
example : IntegralMixedPhysicalFieldEquality.newest 5 4=0:=rfl
example : IntegralMixedPhysicalFieldEquality.newest 5 8=0:=rfl
example : ¬8<5:=by decide
example : InfinitesimalSign.encode (SignType.sign ((-2 : ℝ)-(-3)))=InfinitesimalSign.encode 1:=by norm_num
example : InfinitesimalSign.encode (SignType.sign ((-3 : ℝ)-(-2)))=InfinitesimalSign.encode (-1):=by norm_num
example : InfinitesimalSign.encode (SignType.sign ((-2 : ℝ)-(-2)))=InfinitesimalSign.encode 0:=by norm_num
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q) :
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)<
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q):=
  IntegralMixedRoadmapLocalFrame.order_of_base hn ht ha hR0 q hv HB
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HE : IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)) :
    ¬IntegralMixedRoadmapProper.Base hn ht ha hR0 q:=by
  intro HB
  exact (ne_of_lt (IntegralMixedRoadmapLocalFrame.order_of_base hn ht ha hR0 q hv HB)) HE
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HE : IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)<
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)) :
    ¬IntegralMixedRoadmapProper.Base hn ht ha hR0 q:=by
  intro HB
  exact (not_lt_of_ge (IntegralMixedRoadmapLocalFrame.order_of_base hn ht ha hR0 q hv HB).le) HE
end ProperOrderRegression
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_context_root
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_selected
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_count
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_valid
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_selected_lt
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_endpoint
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.order_of_base
end RoadmapInternalProperOrderActual

namespace RoadmapInternalBadEndpointActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedRoadmapLocalFrame
open scoped Classical
namespace ProperBadEndpointRegression
example (q :List Bool) :IntegralMixedRoadmapBadProbePacket.word (IntegralMixedRoadmapProper.badPacket q)=
    IntegralMixedRoadmapAtomic.word q:=bad_packet_word q
example (q :List Bool) :IntegralMixedRoadmapBadProbePacket.producer false (IntegralMixedRoadmapProper.badPacket q)=
    IntegralMixedRoadmapProper.producer false q:=bad_packet_producer false q
example (q :List Bool) :IntegralMixedRoadmapBadProbePacket.producer true (IntegralMixedRoadmapProper.badPacket q)=
    IntegralMixedRoadmapProper.producer true q:=bad_packet_producer true q
example :9-1-(9-1-8)=8:=by decide
example :9-1-(9-1-0)=0:=by decide
example :¬(9:ℕ)<9:=by decide
example :(-24:ℝ)/(-3)=8:=by norm_num
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0) (q :List Bool)
  (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
  (HR :IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.dimension
  field IntegralMixedMarkedPrefixFieldReadback.parentPoint
example (side :Bool) : IntegralMixedRoadmapProper.producer side q<
    IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q):=
  bad_producer_lt_parent hn ht ha hR0 q HR side
example (i :ℕ) (hi :i<IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)) :
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) i=
    field hn ht ha hR0 q hv (IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)-1-i):=
  bad_parent_values hn ht ha hR0 q hv i hi
example (side :Bool) : IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0
    (IntegralMixedRoadmapProper.badPacket q) (bad_full_valid hn ht ha hR0 q hv) side=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer side q):=
  bad_endpoint hn ht ha hR0 q hv HR side
end ProperBadEndpointRegression
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_packet_word
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_packet_producer
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_packet_count
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_packet_initial
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_parent_birth
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_full_valid
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_producer_lt_parent
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_record_positive
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_parent_values
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_endpoint
end RoadmapInternalBadEndpointActual

namespace RoadmapInternalSeedScanActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedRoadmapSeedMetadata
open scoped Classical
namespace SeedScanRegression
example : ((-2:ℝ)^3)=(-8:ℝ)^1:=by norm_num
example : (2:ℝ)^2=(4:ℝ)^1:=by norm_num
example : (-24:ℝ)/3=(-2:ℝ)^3:=by norm_num
example : (24:ℝ)/(-3)=(-2:ℝ)^3:=by norm_num
example : (24:ℝ)/(-3)≠(2:ℝ)^3:=by norm_num
example : selected 3 0=0 ∧ selected 3 1=3 ∧ selected 3 4=0 ∧ selected 3 99=0:=by decide
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0) (old w :List Bool)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
variable (hw :SquareSampleCompleteVertices.Valid
    (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
    (context hn ht ha hR0 old) w)
  (p q :Fin ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters.ambient
      (pairFst ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).key
        (context hn ht ha hR0 old)))+1)→ℝ)
  (hr :Readback hn ht ha hR0 old w hw p)
example : pair (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old) w∈
    IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false:=
  all_critical_of_readback hn ht ha hR0 old w hw p hr
example (hneq :p≠q) :¬Readback hn ht ha hR0 old w hw q:=by
  intro hq
  have H:=seed_count_lower hn ht ha hR0 old
  have H0 :0<IntegralMixedCausalRecordPlanBits.count
      (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old):=by omega
  exact hneq ((hr.physical 0 H0).symm.trans (hq.physical 0 H0))
example (w' :List Bool) : IntegralMixedRoadmapAtomic.context
    (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=
    IntegralMixedRoadmapAtomic.context
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w'):=
  (packet_context hn ht ha hR0 old w).trans (packet_context hn ht ha hR0 old w').symm
example :IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha (radius_binary hR0) false
    (pair (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old) w):=
  before_probe_holds hn ht ha hR0 old w
example : IntegralMixedRoadmapAtomic.companionQuery
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
    (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false:=
  atomic_companion_of_readback hn ht ha hR0 old w hw p hr
end SeedScanRegression
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.readback_retained
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.all_critical_of_readback
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.seed_count_lower
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.companion_of_readback
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.packet_context
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.packet_companion_query
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata.atomic_companion_of_readback
end RoadmapInternalSeedScanActual

namespace RoadmapInternalBadAvoidanceActual
open LeanCanny LeanCanny.Connectivity LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapLocalFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapLocalFrame.midpoint
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val))
    (c : IntegralMixedRelativeCuts.Choices ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ) :
    ∀a,a∈Set.Ioo (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
      (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))→
      a∉IntegralMixedSelectedCriticalCuts.bad ((G).state (oldKey hn ht ha hR0 q))
        ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ c :=
  no_bad_of_base hn ht ha hR0 q hv HB HR φ Hφ c
end
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.bad_raw_domain
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.old_snapshot_original
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.old_bad_iff
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.no_bad_of_base
end RoadmapInternalBadAvoidanceActual

namespace RoadmapInternalSeedPreludeActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapSeedResampling
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family

section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
example (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (label :ℕ) (hl :label<(seedOlder hn ht ha hR0 old).length) :
    seedPoint hn ht ha hR0 old hv ⟨(seedOlder hn ht ha hR0 old).length-1-label,by omega⟩=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) label:=
  seedPoint_old_field hn ht ha hR0 old hv label hl
end
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.original_prelude_value
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seedPoint_observation
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seedPoint_original
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.oldTuple_natural
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seedPoint_old_field
end RoadmapInternalSeedPreludeActual

namespace RoadmapInternalLocalCoordinatesActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapLocalFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapLocalFrame.midpoint
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (i : Fin (ambient hn ht ha hR0 q+1)) (hi : IntegralMixedRoadmapAtomic.depth q ≤ i.val) :
    midpoint hn ht ha hR0 q hv i=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.midProducer (D q) (N q) q i.val) :=
  midpoint_free hn ht ha hR0 q hv HB i hi
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : Fin (ambient hn ht ha hR0 q+1)) (hi : IntegralMixedRoadmapAtomic.depth q ≤ i.val) :
    child hn ht ha hR0 q hv i=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.childProducer (D q) (N q) q i.val) :=
  child_free hn ht ha hR0 q hv i hi
end
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.midpoint_free
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.child_free
end RoadmapInternalLocalCoordinatesActual

namespace RoadmapInternalLocalFreeIndexActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedRoadmapLocalFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapLocalFrame.midpoint
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
open LeanCanny.Connectivity IntegralMixedSelectedGeometry IntegralCriticalHistoryTask
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (i : Free ((G).rule (oldKey hn ht ha hR0 q))) :
    IntegralMixedRoadmapAtomic.depth q+i.val≤D q :=
  free_global_le hn ht ha hR0 q hv HB HR i
example (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (i : Free ((G).rule (oldKey hn ht ha hR0 q))) :
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate G
      (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false
        (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i.val))))
      (get (IntegralFramedBankQuery.Bank.parameters BK) Field.slot13
        (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 false
          (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i.val)))))).val=i.val :=
  selected_free_value hn ht ha hR0 q hv HB HR i
end
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.reference_rule_offset
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.free_global_le
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.row_good_coordinate
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame.selected_free_value
end RoadmapInternalLocalFreeIndexActual

namespace RoadmapInternalScalarPointActual
/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-! # Scalar-prefix bank points are the same full physical bank point -/
open LeanCanny LeanCanny.Encoding LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
 (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)

set_option maxHeartbeats 200000
example (i : Fin ((family P D H).birth (key c))) :
    IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key c))
      (scalarTuple P D H L F C hs key hpos c w hv) i=
    point P D H L F C hs key hpos c w hv i :=by
  exact scalarTuple_point P D H L F C hs key hpos c w hv i


#print axioms LeanCanny.Encoding.IntegralFramedPhysicalSquare.scalarTuple_point
end RoadmapInternalScalarPointActual

namespace RoadmapInternalSeedExistenceActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.Connectivity.IntegralMixedRoadmapGraph IntegralMixedOriginalRegularSource
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "root" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
local notation "Q" old=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root old)
example (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∃p : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (root old)+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial (Q old).low (Q old).leading (Q old).degree).eval₂
        (Int.castRingHom ℝ) p=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial (Q old).low (Q old).leading (Q old).degree)).eval₂
          (Int.castRingHom ℝ) p=0 :=
  exists_prepared_critical hn ht ha hR0 old hv
example (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∃w,IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w) ∧
      IntegralMixedRoadmapAtomic.depth
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=0 ∧
      IntegralMixedRoadmapAtomic.candidate
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=
          IntegralMixedRoadmapAtomic.candidate old :=
  exists_resampled_seed hn ht ha hR0 old hv
end
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.exists_prepared_critical
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.exists_resampled_seed
end RoadmapInternalSeedExistenceActual

namespace RoadmapInternalSeedFieldActual
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedRoadmapSeedResampling
open scoped Classical
namespace SeedFieldReadbackRegression
def j0 :IntegralMixedPointCompanion.Free (∅:Finset (Fin 2)):=⟨0,by simp⟩
def j1 :IntegralMixedPointCompanion.Free (∅:Finset (Fin 2)):=⟨1,by simp⟩
def js :=[j0,j0,j1,j0]
def point :Fin 2→ℝ:=![7,-3]
def oldValues :Fin 2→ℝ:=![-2,5]
example :IntegralMixedPointCompanion.values point oldValues js ⟨0,of_decide_eq_true rfl⟩=7:=rfl
example :IntegralMixedPointCompanion.values point oldValues js ⟨1,of_decide_eq_true rfl⟩=7:=rfl
example :IntegralMixedPointCompanion.values point oldValues js ⟨2,of_decide_eq_true rfl⟩=(-3):=rfl
example :IntegralMixedPointCompanion.values point oldValues js ⟨3,of_decide_eq_true rfl⟩=7:=rfl
example :IntegralMixedPointCompanion.values point oldValues js ⟨4,of_decide_eq_true rfl⟩=(-2):=rfl
example :IntegralMixedPointCompanion.values point oldValues js ⟨5,of_decide_eq_true rfl⟩=5:=rfl
example :IntegralMixedRoadmapSeedMetadata.selected 1 0=0:=rfl
example :IntegralMixedRoadmapSeedMetadata.selected 1 1=1:=rfl
example :IntegralMixedRoadmapSeedMetadata.selected 1 2=0:=rfl
example :IntegralMixedRoadmapSeedMetadata.selected 1 3=0:=rfl
example :(-21:ℝ)/(-3)=7:=by norm_num
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0) (old :List Bool)
  (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (p :Fin ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient
    (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ) (w :List Bool)
  (hw :SquareSampleCompleteVertices.Valid
    (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
    (pair (preparedRoot hn ht ha hR0 old) []) w)
  (HJ :FieldJoint hn ht ha hR0 old w hw u) (HV :FieldValues hn ht ha hR0 old hv p u)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot seedOlder seedSelections
  IntegralMixedPhysicalFieldEquality.point seedObservation
example (a :ℕ) (ha0 :a<IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old)) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (pair (preparedRoot hn ht ha hR0 old) []) w hw
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old)+8+a)=
    p ⟨IntegralMixedRoadmapSeedMetadata.selected
      ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient
        (preparedRoot hn ht ha hR0 old)) a,IntegralMixedRoadmapSeedMetadata.selected_lt _ _⟩:=
  seed_selected_field hn ht ha hR0 old hv p u w hw HJ HV a ha0
example (label :ℕ)
    (hl :label<IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old)+8) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (pair (preparedRoot hn ht ha hR0 old) []) w hw label=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) label:=
  seed_prelude_field hn ht ha hR0 old hv p u w hw HJ HV label hl
end SeedFieldReadbackRegression
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seed_field_count
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seed_field_observation
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seed_field_values
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seed_selected_field
#print axioms LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling.seed_prelude_field
end RoadmapInternalSeedFieldActual

namespace RoadmapInternalSeedAcceptanceActual
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex UniformIntegralPowerSchedule
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical

-- The anchor, all coordinate captures, and padding use the exact chronology.
example : IntegralMixedRoadmapSeedMetadata.selected 2 0=0 :=by decide
example : IntegralMixedRoadmapSeedMetadata.selected 2 1=2 :=by decide
example : IntegralMixedRoadmapSeedMetadata.selected 2 2=1 :=by decide
example : IntegralMixedRoadmapSeedMetadata.selected 2 3=0 :=by decide
example : IntegralMixedRoadmapSeedMetadata.selected 2 19=0 :=by decide
example : (IntegralMixedChronologicalSeedProgram.selections 0 8 2).length=4 :=by
  rw [IntegralMixedChronologicalSeedProgram.selections_length]
example (d :ℕ) (old w :List Bool) :
    IntegralMixedRoadmapAtomic.depth (IntegralMixedRoadmapSeedResampling.packet d old w)=0 :=
  IntegralMixedRoadmapSeedResampling.depth_packet d old w

-- Distinct creating powers are retained; no equality between successive Qs is used.
example {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
    (x :State P S B m ι) (frozen :Finset (Fin (n+1)))
    (double :Fin (n+1)→Bool) (rows :Fin (n+1)→IntegralMixedCausalRowConstructor.Row m)
    (g :IntegralMixedPointCompanion.Free frozen) (z :ι→ℝ)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (old :Fin m→ℝ) (p :Fin (n+1)→ℝ)
    (js :List (IntegralMixedPointCompanion.Free frozen)) (room :m+js.length≤S+1)
    (R :IntegralMixedPointCompanion.Realized x frozen double rows g z φ old p js room)
    (k :Fin js.length) (i :Fin (n+1)) :
    R.tuple (IntegralMixedPointCompanion.blockColumn frozen double rows g js k i)^
      physical S (2^B) (m+(js.length-1-k.val))=p i :=R.blocks k i

-- The final constructor has no history-realizability, guard, or evaluator premise.
example {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
    (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
    {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
    (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient
      (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).degree).eval₂
          (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)
        (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)).degree)).eval₂
          (Int.castRingHom ℝ) p=0) :
    ∃w,IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w) :=by
  obtain ⟨w,_,hw,_⟩:=IntegralMixedRoadmapSeedResampling.exists_valid hn ht ha hR0 old hv p hp hg
  exact ⟨w,hw⟩

#print axioms IntegralMixedChronologicalSeedProgram.exists_realized_seed
#print axioms IntegralMixedFramedFixedContinuation.companion_observation
#print axioms IntegralMixedRoadmapSeedResampling.grammar
#print axioms IntegralMixedRoadmapSeedResampling.exists_realized
#print axioms IntegralMixedRoadmapSeedResampling.exists_seed_word
#print axioms IntegralMixedRoadmapSeedResampling.seed_older_arity
#print axioms IntegralMixedRoadmapSeedResampling.geometricPoint_of_columns
#print axioms IntegralMixedRoadmapSeedResampling.valid_of_readback
#print axioms IntegralMixedRoadmapSeedResampling.exists_valid
end RoadmapInternalSeedAcceptanceActual

namespace RoadmapInternalLocalPathActual
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RoadmapLocalPathRegression
-- Ordinals count distinct roots, including an empty or repeated-root list.
example : OrderedRealRootWindow.rank (∅ : Finset ℝ) 17=0 :=by
  simp only [OrderedRealRootWindow.rank,Finset.filter_empty,Finset.card_empty]
example : OrderedRealRootWindow.rank ({1} : Finset ℝ) 1=0 :=by
  norm_num [OrderedRealRootWindow.rank]
example : OrderedRealRootWindow.rank ([1,1,3] : List ℝ).toFinset 2=1 :=by
  norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
 (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
-- Every coordinate witness yields its own interpreting hom and actual midpoint rank.
example (right : Bool) (q : List Bool) (j : ℕ)
 (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
 (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
 (hj : IntegralMixedRoadmapAtomic.depth q≤j)
 (hjn : j≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
 (HC : IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right (pair q (BinaryNatCode.encode j))) :
 IntegralMixedRoadmapProperRow.CoordinateMeaning hn ht ha hR0 right q j hv :=
 IntegralMixedRoadmapProperRow.coordinate_meaning hn ht ha hR0 right q j hv HB hj hjn HC
-- Different coordinate queries share an actual whole prefix, without copying words.
example (q a b : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
 IntegralMixedPrefixSnapshot.ofState ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q a)))=
 IntegralMixedPrefixSnapshot.ofState ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q b))) :=
 IntegralMixedRoadmapProperRow.parent_coordinate_snapshot_eq hn ht ha hR0 q a b hv
-- The final soundness theorem consumes only the actual native Local predicate.
example (q : List Bool) (H : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 q) :
 JoinedIn {p : Fin (IntegralMixedRoadmapLocalFrame.ambient hn ht ha hR0 q+1)→ℝ |
 (FermatCriticalHomogenization.polynomial
  ((G).spatial (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).low
  ((G).spatial (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).leading
  ((G).spatial (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).degree).eval₂ (Int.castRingHom ℝ) p=0}
 (IntegralMixedRoadmapLocalFrame.child hn ht ha hR0 q H.1)
 (IntegralMixedRoadmapLocalFrame.midpoint hn ht ha hR0 q H.1) :=
 IntegralMixedRoadmapLocalFrame.local_joined hn ht ha hR0 q H
#print axioms IntegralMixedRoadmapLocalFrame.local_joined
#print axioms IntegralMixedRoadmapProperRow.coordinate_meaning
#print axioms IntegralMixedRoadmapProperRow.actual_mean_roots
#print axioms IntegralMixedRoadmapProperRow.native_scalar_value
#print axioms IntegralMixedRoadmapProperRow.parent_coordinate_snapshot_eq
#print axioms IntegralMixedRoadmapProperRow.ordinary_coordinate_shape
#print axioms IntegralMixedSelectedNearTransport.anchored_near_iff_of_snapshot
#print axioms IntegralMixedSelectedCoordinateEndpoint.joined_source_of_near
#print axioms IntegralFramedPhysicalNear.accept_rank_word
end RoadmapLocalPathRegression
end
end RoadmapInternalLocalPathActual

namespace RoadmapInternalGraphPathSoundnessActual
open LeanCanny LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.Connectivity IntegralMixedRoadmapGraph
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
section
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
example (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (H : IntegralMixedRoadmapEdge.Proper hn ht ha hR0 (pair a b)) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=
  proper_joined hn ht ha hR0 c a b hA hB hc hd H
example (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (H : IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a b) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=
  adjacent_joined hn ht ha hR0 c a b hA hB hc hd H
example (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c)
    (H : Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) (hd : IntegralMixedRoadmapAtomic.candidate b=c) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=
  path_joined hn ht ha hR0 c a b hA hc H hB hd
example (c a b : List Bool) (H : RawReachable hn ht ha hR0 c a b) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a H.1 H.2.2.1) (pointAt hn ht ha hR0 c b H.2.1 H.2.2.2.1) :=
  raw_reachable_joined hn ht ha hR0 c a b H
end
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.proper_midpointAt_eq
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.proper_joined
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.adjacent_joined
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.path_joined
#print axioms LeanCanny.Connectivity.IntegralMixedRoadmapGraph.raw_reachable_joined
end RoadmapInternalGraphPathSoundnessActual
