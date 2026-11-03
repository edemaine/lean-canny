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
Proper-edge soundness and the global graph/path equivalence remain open. -/
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
