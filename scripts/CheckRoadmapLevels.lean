import LeanCanny.Algebra.IntegralMixedIntegerRealization
import LeanCanny.Connectivity
import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
import LeanCanny.Encoding.IntegralMixedChronologicalMidpointCompanionCode
import LeanCanny.Encoding.IntegralMixedChronologicalMidpointDecode
import LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureBounds
import LeanCanny.Encoding.IntegralMixedRoadmapLevelLedger
import LeanCanny.Encoding.IntegralMixedRoadmapLevelOriginalBudget
import LeanCanny.Encoding.IntegralMixedRoadmapPrefixVertexBudget
import LeanCanny.Encoding.IntegralMixedRoadmapVertexBudget
import LeanCanny.Geometry.IntegralMixedMatchedOptionalAnchorCaptures
import LeanCanny.Geometry.IntegralMixedPointCompanionBounds

/-! Native chronological levels, exact captures, correlated endpoints and
original full/prefix word-budget regressions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapLevelsChronologicalCuts
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRecordBits
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace ChronologicalCutRegression
private def d : IntegralMixedChronologicalFrame.Descriptor 2 4 where
  labels:=[0]
  length_le:=by decide
private def w:=IntegralMixedChronologicalFrameCode.labels d
private theorem good : IntegralMixedChronologicalCutCode.Good 2 4 w 2 2:=
  ⟨IntegralMixedChronologicalFrameCode.labels_good d,by decide,by decide,by decide,by decide⟩
private theorem hg : (2 : Fin 3)∉(IntegralMixedChronologicalSweepFrame.frame d (by decide)).frozen:=
  (IntegralMixedChronologicalSweepFrame.free_iff d (by decide) 2).mpr (by decide)

example : IntegralMixedChronologicalSweepFrame.next d (by decide)=1:=rfl
example : (IntegralMixedChronologicalSweepFrame.frame d (by decide)).frozen.card=2:=
  IntegralMixedChronologicalSweepFrame.frozen_card d (by decide)
example : ((IntegralMixedChronologicalSweepFrame.data d (by decide) 2 2 hg hg).rule (-24) (by decide)).slope=-24:=rfl
example : ((IntegralMixedChronologicalSweepFrame.data d (by decide) 2 2 hg hg).rule (-24) (by decide)).height=1:=rfl
example : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedChronologicalCutCode.ordinaryTag 0)=0:=rfl
example : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedChronologicalCutCode.ordinaryTag 1)=1:=rfl
example : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedChronologicalCutCode.ordinaryTag 2)=2:=rfl
example : IntegralMixedChronologicalCutCode.Bounds 2 4 3 11 w 2 2 2 7 11:=⟨good,by decide,by decide,by decide⟩
example : ¬IntegralMixedChronologicalCutCode.Bounds 2 4 3 11 w 2 2 3 7 11:=by
  intro H
  have HC:=H.2.1
  omega
example : ¬IntegralMixedChronologicalCutCode.Bounds 2 4 3 11 w 2 2 2 9 11:=by
  intro H
  have HC:=H.2.2.1
  change 9≤8 at HC
  omega
example : ¬IntegralMixedChronologicalCutCode.Bounds 2 4 3 11 w 2 2 2 7 12:=by
  intro H
  have HC:=H.2.2.2
  omega
example : ¬IntegralMixedChronologicalCutCode.Good 2 4
    (WordList.encode [BinaryNatCode.encode 4]) 2 2:=by
  intro H
  have HC:=H.1.2 0 (by decide)
  change 4<4 at HC
  omega
-- The one-free-coordinate case has no free auxiliary objective after freezing.
example : ¬IntegralMixedChronologicalCutCode.Good 2 4
    (WordList.encode [BinaryNatCode.encode 0,BinaryNatCode.encode 1]) 2 2:=by
  intro H
  have HC:=H.2.1
  change 3≤2 at HC
  omega
example : (IntegralMixedChronologicalCutCode.code 2 w 2 2 2 7 0).length≤
    IntegralMixedCutRecordConstructor.codeBudget 2 4 3:=
  IntegralMixedChronologicalCutCode.raw_code_size 2 4 3 w 2 2 2 7 0 good (by decide) (by decide) (by decide)
example {S B : ℕ} {P : SpatialSource 2} {ι : Type} (x : State P S B 4 ι) :
    (IntegralMixedChronologicalSweepFrame.data d (by decide) 2 2 hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)=
      IntegralMixedSweepRetarget.rule (cutRule x d.frame 1 2 hg) 0:=
  IntegralMixedChronologicalSweepFrame.data_rule x d (by decide) 2 2 hg hg
example {B : ℕ} (P : SpatialSource 2)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
    (IntegralMixedCausalUnitRecordBits.record P (by decide) 4
      (IntegralMixedChronologicalCutCode.code 2 w 2 2 2 7 0) hc).template.command (-24) (by decide)=
      .cut ((IntegralMixedChronologicalCutCode.rawData 2 4 w 2 2 good).rule (-24) (by decide))
        (((IntegralMixedChronologicalCutCode.rawData 2 4 w 2 2 good).cut P .value 7 0 (Nat.zero_le _) hc).kind (-24) (by decide))
        0 (Nat.zero_le _) ((Nat.zero_le _).trans hc):=
  IntegralMixedChronologicalCutCode.raw_command (birth:=4) (B:=B) P (by decide) w 2 2 2 7 0 good
    (by decide) (Nat.zero_le _) hc (-24) (by decide)

end ChronologicalCutRegression
#print axioms IntegralMixedChronologicalSweepFrame.prefix_frozen
#print axioms IntegralMixedChronologicalSweepFrame.pointData_rule
#print axioms IntegralMixedChronologicalSweepFrame.data_rule
#print axioms IntegralMixedChronologicalCutCode.code_FP
#print axioms IntegralMixedChronologicalCutCode.good_FP
#print axioms IntegralMixedChronologicalCutCode.data_code
#print axioms IntegralMixedChronologicalCutCode.command_decode
#print axioms IntegralMixedChronologicalCutCode.bounds_FP
#print axioms IntegralMixedChronologicalCutCode.rawData_code
#print axioms IntegralMixedChronologicalCutCode.raw_command
#print axioms IntegralMixedChronologicalCutCode.raw_code_size
end
end RoadmapLevelsChronologicalCuts

namespace RoadmapLevelsOriginalBudget
open LeanCanny LeanCanny.Encoding IntegralMixedRoadmapRecordChain
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace OriginalLevelBudgetRegression
private def L : Level 2 1 1 9 where
  left:=.retained 8
  right:=.fresh ⟨[],by decide⟩
  anchor:=⟨[true],by decide⟩
  midpoint:=fun _=>⟨[false],by decide⟩
  endpoint:=⟨[false],by decide⟩
  companions:=fun _=>⟨[true],by decide⟩
example : (L.weaken (by decide : 1≤5) (by decide : 9≤20)).left=.retained 8:=rfl
example : (L.weaken (by decide : 1≤5) (by decide : 9≤20)).codes.map Subtype.val=
    [[],[true],[false],[false],[true]]:=rfl
example : (L.weaken (by decide : 1≤5) (by decide : 9≤20)).codes.map Subtype.val=L.codes.map Subtype.val:=
  L.codes_weaken (by decide) (by decide)
example {n B sourceCap birth initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapLevel.Checked n B sourceCap birth q)
    (hm : IntegralMixedRoadmapLevel.endBirth n birth q≤maxBirth n initial) (hB : B≤C) :
    WordList.encode ((originalLevel h hm hB).codes.map Subtype.val)=IntegralMixedRoadmapLevel.slice q:=
  originalLevel_word h hm hB
end OriginalLevelBudgetRegression
#print axioms Endpoint.codes_weaken
#print axioms Level.codes_weaken
#print axioms local_budget_le
#print axioms originalLevel_codes
#print axioms originalLevel_word
end RoadmapLevelsOriginalBudget

namespace RoadmapLevelsWordBudget
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapRecordChain
open scoped Classical
namespace RoadmapVertexBudgetRegression
private def n (_ : List Bool) :=0
private def t (_ : List Bool) : Term:=.const 0
private def R (_ : List Bool) :=0
private theorem hn : UnaryFn n:=UnaryFn.const 0
private theorem ht : (fun q=>(t q).toData.toBits)∈FP:=by
  simpa only [t] using constFn_mem_FP (Term.const (0:ℤ)).toData.toBits
private theorem ha : ∀q,(t q).arity≤n q:=by intro q;change 0≤0;omega
private theorem hR : BinaryFn R:=BinaryFn.const 0

-- Exact pairing constants, including the outer sampler context and metadata.
private def emptyWord : Word 0:=⟨[],by decide⟩
private def zero : Records 0 0 0:=⟨fun _=>emptyWord,.stop 0⟩
private def ambientThree : Records 3 0 0:=⟨fun _=>emptyWord,.stop 0⟩
example : (zero.paddedWord emptyWord emptyWord).length=14 :=by decide
example : (zero.root emptyWord emptyWord [] []).length=32 :=by decide
example : (pair (zero.root emptyWord emptyWord [] []) []).length=66 :=by decide
example : (pair (zero.root emptyWord emptyWord [true,false] [true,false,true]) []).length=80 :=by decide
example : probedRecordBound 3=34 :=by decide
private theorem threeLength : (ambientThree.paddedWord emptyWord emptyWord).length=68 :=by decide
example : (pair (ambientThree.root emptyWord emptyWord [] []) []).length=282 :=by
  simp only [IntegralMixedRoadmapRecordChain.Records.root,pair_length,List.length_nil,threeLength]
example : cap 3 8=44 :=by decide
example : (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap
    (ambientThree.root emptyWord emptyWord (pair [] []) [])=44 :=by
  exact (ambientThree.actual_marked_cap hn ht ha emptyWord emptyWord (pair [] []) []).trans rfl

-- Arbitrary raw records and metadata preserve B, not sampler words or points.
example (candidate : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width
      (pair candidate (pair [true,false,true] [true]))=
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair candidate []) :=
  IntegralMixedRoadmapWidth.width_context hn ht ha candidate _ []
example (candidate c e : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha (pair candidate c)=
      IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha (pair candidate e) :=
  IntegralMixedRoadmapWidth.degreeBound_context hn ht ha candidate c e
example : UnaryFn (IntegralMixedRoadmapWidth.scalarBudget hn ht ha):=
  IntegralMixedRoadmapWidth.scalarBudget_unary hn ht ha
example : UnaryFn (IntegralMixedRoadmapWidth.contextBudget hn ht ha):=
  IntegralMixedRoadmapWidth.contextBudget_unary hn ht ha
example : UnaryFn (IntegralMixedRoadmapWidth.vertexBudget hn ht ha hR):=
  IntegralMixedRoadmapWidth.vertexBudget_unary hn ht ha hR
example : ∃p : Polynomial ℕ,∀q,IntegralMixedRoadmapWidth.vertexBudget hn ht ha hR q≤p.eval q.length:=
  IntegralMixedRoadmapWidth.vertexBudget_polynomial hn ht ha hR

example (original label : List Bool)
    (hl : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ}
    (records : Records (n original+3) (IntegralMixedRoadmapWidth.recordBudget hn ht ha original) labels)
    (seed probe : Word (IntegralMixedRoadmapWidth.recordBudget hn ht ha original))
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (pair (records.root seed probe (pair original label) []) []) w) :
    w.length≤IntegralMixedRoadmapWidth.vertexBudget hn ht ha hR original :=
  IntegralMixedRoadmapWidth.word_length_le_vertexBudget hn ht ha hR original label hl records seed probe w hw

end RoadmapVertexBudgetRegression
#print axioms IntegralMixedRoadmapWidth.rank_context
#print axioms IntegralMixedRoadmapWidth.sphereDegree_context
#print axioms IntegralMixedRoadmapWidth.regularDegree_context
#print axioms IntegralMixedRoadmapWidth.degreeBound_context
#print axioms IntegralMixedRoadmapWidth.width_context
#print axioms IntegralMixedRoadmapWidth.candidate_length
#print axioms IntegralMixedRoadmapWidth.scalarBudget_unary
#print axioms IntegralMixedRoadmapWidth.width_le_scalarBudget
#print axioms IntegralMixedRoadmapWidth.Records.root_length
#print axioms IntegralMixedRoadmapWidth.Records.context_length
#print axioms IntegralMixedRoadmapWidth.recordBudget_unary
#print axioms IntegralMixedRoadmapWidth.contextBudget_unary
#print axioms IntegralMixedRoadmapWidth.padded_context_length
#print axioms IntegralMixedRoadmapWidth.padded_root_length
#print axioms IntegralMixedRoadmapWidth.contextBudget_polynomial
#print axioms IntegralMixedRoadmapWidth.padded_scalar_width
#print axioms IntegralMixedRoadmapWidth.padded_cap
#print axioms IntegralMixedRoadmapWidth.cut_code_length
#print axioms IntegralMixedRoadmapWidth.certified_width
#print axioms IntegralMixedRoadmapWidth.certified_cap
#print axioms IntegralMixedRoadmapWidth.vertexBudget_unary
#print axioms IntegralMixedRoadmapWidth.width_le_vertexBudget
#print axioms IntegralMixedRoadmapWidth.word_length_le_vertexBudget
#print axioms IntegralMixedRoadmapWidth.vertexBudget_polynomial
end RoadmapLevelsWordBudget

namespace RoadmapLevelsMidpointCaptures
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MidpointCompanionSignatureRegression
private def D:=BoundedZeroSource.powerDegree 0
private theorem Dval : D=18:=rfl
private def P : SpatialSource 1 where
 low:=-1
 leading:=1
 degree:=D
 degree_two:=by rw [Dval]; decide
 low_degree:=by
  simpa only [MvPolynomial.totalDegree_neg,MvPolynomial.totalDegree_one] using
    (show 0<D from by rw [Dval]; decide)
 leading_ne_zero:=by decide
private def F : Frame 1:={frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
private theorem HA : AtomicRows F 4:=AtomicRows.initial 1 4
private theorem HF : FreeNormal F:=fun _ _=>⟨rfl,rfl⟩
private theorem HP : PrefixFrozen F:=PrefixFrozen.of_empty F rfl
private theorem hh : (0 : Fin 2)∉F.frozen:=Finset.notMem_empty _
private theorem hg : (1 : Fin 2)∉(line F 0).frozen:=by decide
private theorem evalP (v : Fin 2→ℝ) :
 (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) v=
  -1+v 0^18+v 1^18:=by
 simp [P,Dval,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two]
 ring
private theorem gradP (v : Fin 2→ℝ) :
 (MvPolynomial.pderiv (1 : Fin 2) (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
   (Int.castRingHom ℝ) v=18*v 1^17:=by
 norm_num [P,Dval,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two,MvPolynomial.pderiv_pow]
 simp [Fin.sum_univ_two,Pi.single_apply]
private theorem endpoint {k : ℕ} (values : Fin k→ℝ) (a : ℝ) (ha : a=1 ∨ a=-1) :
 a∈realCriticalValues P (line F 0) values 0:=by
 apply (line_realCriticalValues_iff P F values 0 hh HF a).mpr
 refine ⟨![a,0],⟨?_,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩,by simp,?_⟩
 · rw [evalP]
   rcases ha with rfl|rfl <;> norm_num
 · intro i _ hi
   have HE : i=1:=by fin_cases i <;> simp_all
   subst i
   rw [gradP]
   norm_num
private theorem cap : PurePowerReductionBounds.dimension 2 P.degree≤IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree:=by
 unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
 omega
private def initial (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : State P 6 B 0 (Fin 0):=
 IntegralMixedHistory.base P (IntegralHistorySampler.base 6 (2^B)) (cap.trans hc)
open IntegralMixedFullHistoryScript IntegralMixedOptionalEndpoints Polynomial
private theorem poly_coeff (l b : ℤ) : (C l*X-C b : Polynomial ℤ).coeff 1=l:=by
 rw [coeff_sub,coeff_C_mul,coeff_X_one,coeff_C,ite_eq_right (by decide : (1:ℕ)≠0)]
 ring
private theorem poly_nonzero (l b : ℤ) (hl : l≠0) : (C l*X-C b : Polynomial ℤ)≠0:=by
 intro HZ
 have H:=congrArg (fun p : Polynomial ℤ=>p.coeff 1) HZ
 rw [poly_coeff,Polynomial.coeff_zero] at H
 exact hl H
private theorem poly_degree_le (l b : ℤ) (hl : l≠0) : (C l*X-C b : Polynomial ℤ).natDegree≤1:=by
 exact (natDegree_sub_le (C l*X) (C b)).trans (by rw [natDegree_C_mul_X l hl,natDegree_C]; omega)
private theorem poly_leading (l b : ℤ) (hl : l≠0) : (C l*X-C b : Polynomial ℤ).leadingCoeff=l:=by
 have HD : (C l*X-C b : Polynomial ℤ).natDegree=1:=
   Nat.le_antisymm (poly_degree_le l b hl) (le_natDegree_of_ne_zero (by rw [poly_coeff]; exact hl))
 rw [leadingCoeff,HD,poly_coeff]
private def leaf (B : ℕ) (l b : ℤ) (hl : l≠0) : Command P B:=
 .integer (C l*X-C b) (poly_nonzero l b hl) ((poly_degree_le l b hl).trans Nat.one_le_two_pow)
private def leaves (B : ℕ) :=[leaf B (-2) 1 (by decide),leaf B 2 1 (by decide),
 leaf B 2 (-2) (by decide),leaf B 3 3 (by decide)]
private def vals : Fin 4→ℝ:=![-(1/2),1/2,-1,1]
private def before (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 State P 6 B 4 (Index (Fin 0) (leaves B)) :=
 run (initial B hc) (leaves B) (by change (4:ℕ)≤7; decide)
private theorem before_realized (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃ z : Index (Fin 0) (leaves B)→ℝ,
 ∃ φ : (before B hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
   (∀ i,((before B hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) ∧
   (∀ i,φ ((before B hc).sampler.scalarPrefix.basis.generator i)=
     z ((before B hc).sampler.scalar i)^UniformIntegralPowerSchedule.weights 6 (2^B) 4 i) ∧
   ∀ i,φ ((before B hc).bank.numerator i)/((before B hc).bank.denominator i:ℝ)=vals i :=by
 apply IntegralMixedIntegerRealization.exists_realization (initial B hc) Fin.elim0 (fun i=>Fin.elim0 i)
   (leaves B) (by change (4:ℕ)≤7; decide) vals
 intro i
 fin_cases i
 · change (C (-2)*X-C 1 : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) (-(1/2))=0
   norm_num
 · change (C 2*X-C 1 : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) (1/2)=0
   norm_num
 · change (C 2*X-C (-2) : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) (-1)=0
   norm_num
 · change (C 3*X-C 3 : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) 1=0
   norm_num


open IntegralMixedPointCompanion IntegralMixedCausalRowConstructor
open IntegralMixedChronologicalMidpointSignature
private def desc : IntegralMixedChronologicalFrame.Descriptor 1 4:=⟨[],by decide⟩
private theorem hk : desc.labels.length<2:=by decide
private def leftEnd : Fin 4:=3
private def rightEnd : Fin 4:=2
private noncomputable def midFrame:=IntegralMixedChronologicalMidpoint.frame desc hk leftEnd rightEnd
private noncomputable def midRows:=IntegralMixedChronologicalMidpoint.rows desc hk leftEnd rightEnd
private noncomputable def midDouble:=IntegralMixedFrozenFrame.midpointDouble (IntegralMixedChronologicalMidpoint.next desc hk)
private noncomputable def obj : Free midFrame.frozen:=⟨1,by
 apply (IntegralMixedChronologicalMidpoint.free_iff desc hk leftEnd rightEnd 1).mpr
 decide⟩
private def midPoint : Fin 2→ℝ:=![0,1]
private theorem mid_slice : midPoint∈slice P midFrame vals:=by
 unfold midFrame
 rw [IntegralMixedChronologicalMidpoint.slice_eq]
 constructor
 · apply (desc.slice_iff P vals midPoint).mpr
   exact ⟨by rw [evalP];norm_num [midPoint],fun i=>Fin.elim0 i⟩
 · norm_num [IntegralMixedChronologicalMidpoint.next,IntegralMixedChronologicalMidpoint.reference,
     midPoint,desc,leftEnd,rightEnd,vals]
private noncomputable def freeList:=orderedFree desc hk leftEnd rightEnd
private theorem room : 4+freeList.length≤6+1:=by
 unfold freeList
 rw [orderedFree_length]
 decide
private theorem capture (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃z,∃φ,Nonempty (Realized (before B hc) midFrame.frozen midDouble midRows obj z φ vals midPoint freeList room) ∧
 Decoded (before B hc) midFrame.frozen midDouble midRows obj (by decide) hc freeList room:=by
 obtain ⟨z,φ,hz,hφ,H⟩:=before_realized B hc
 have HP : PrefixFrozen (originalFrame midFrame.frozen midDouble midRows):=
   IntegralMixedChronologicalMidpoint.prefix_frozen desc hk leftEnd rightEnd
 have HG : ∀i : Fin 2,i∉midFrame.frozen→i≠obj.val→
   (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
     (Int.castRingHom ℝ) midPoint=0:=by
  intro i hi he
  have HH:=(IntegralMixedChronologicalMidpoint.free_iff desc hk leftEnd rightEnd i).mp hi
  have HN : (1 : ℕ)≤ i.val:=HH
  have HE : i=1:=Fin.ext (by change i.val=1;have :=i.isLt;omega)
  exact False.elim (he HE)
 exact ⟨z,φ,exists_realized (before B hc) midFrame.frozen midDouble midRows obj (by decide) 0 rfl hc HP
   z hz φ hφ vals H midPoint mid_slice HG freeList room⟩

example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃z,∃φ,∃R : Realized (before B hc) midFrame.frozen midDouble midRows obj z φ vals midPoint freeList room,
   ∀i : Fin 2, let result:=IntegralMixedPointCompanion.run (before B hc) midFrame.frozen midDouble midRows obj freeList room
              let values : Fin 5→ℝ:=fun j=>R.hom (result.bank.numerator j)/(result.bank.denominator j:ℝ)
              Feature.eval values (signature desc leftEnd rightEnd i)=midPoint i:=by
 obtain ⟨z,φ,⟨R⟩,_⟩:=capture B hc
 refine ⟨z,φ,R,fun i=>?_⟩
 exact realized_signature_value desc hk leftEnd rightEnd (before B hc) obj z φ vals midPoint mid_slice room R i
example : IntegralMixedChronologicalMidpointCompanionCode.codes 1
 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1=
 [IntegralMixedChronologicalMidpointCode.code 1 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1 1]:=rfl
example : (codes midFrame.frozen midDouble midRows obj freeList).reverse=
 IntegralMixedChronologicalMidpointCompanionCode.codes 1 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1:=
 IntegralMixedChronologicalMidpointCompanionCode.codes_actual desc hk leftEnd rightEnd obj
example : IntegralMixedCausalUnitRecordBits.physical 1 4
 (IntegralMixedChronologicalMidpointCode.code 1 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1 1)=
 pointRule midFrame 1 obj.property 1 obj.property:=
 IntegralMixedChronologicalMidpointCode.decode desc hk leftEnd rightEnd 1 1 obj.property obj.property
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 (IntegralMixedCausalUnitRecordBits.record P (by decide) 4
   (IntegralMixedChronologicalMidpointCode.code 1 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1 1) hc).template.command
   (commonDenominator (before B hc)) (commonDenominator_ne_zero _)=
 .critical (pointRule midFrame 1 obj.property 1 obj.property):=
 IntegralMixedChronologicalMidpointCode.command_currentQ (before B hc) (by decide) hc desc hk leftEnd rightEnd 1 1 obj.property obj.property
example : midFrame.scales 0=2:=rfl
example : midRows 0=.sum (some 0) (some 1):=rfl
example : signature desc leftEnd rightEnd 0=.mean ⟨3,by decide⟩ ⟨2,by decide⟩:=rfl
example : signature desc leftEnd rightEnd 1=.producer ⟨4,by decide⟩:=rfl
example : Feature.eval (postValues desc hk leftEnd rightEnd midPoint vals) (signature desc leftEnd rightEnd 0)=0:=by
 exact point_values desc hk leftEnd rightEnd P vals midPoint mid_slice 0
private theorem after_values : postValues desc hk leftEnd rightEnd midPoint vals=(![1,-(1/2),1/2,-1,1] : Fin 5→ℝ):=by
 funext i
 fin_cases i <;> rfl
example : ∀a : Fin 5,Feature.eval (postValues desc hk leftEnd rightEnd midPoint vals) (.producer a)≠0:=by
 rw [after_values]
 intro a
 fin_cases a <;> norm_num [Feature.eval,IntegralMixedChronologicalMidpoint.reference,freeCount,desc]
example : vals (IntegralMixedChronologicalMidpoint.reference leftEnd)≠vals (IntegralMixedChronologicalMidpoint.reference (1 : Fin 4)) ∧
 (vals (IntegralMixedChronologicalMidpoint.reference leftEnd)+vals (IntegralMixedChronologicalMidpoint.reference rightEnd))/2=
 (vals (IntegralMixedChronologicalMidpoint.reference (1 : Fin 4))+vals (IntegralMixedChronologicalMidpoint.reference (0 : Fin 4)))/2:=by
 norm_num [vals,IntegralMixedChronologicalMidpoint.reference,leftEnd,rightEnd]

private def otherDesc : IntegralMixedChronologicalFrame.Descriptor 1 5:=⟨[],by decide⟩
private def otherVals : Fin 5→ℝ:=![7,-(1/2),1/2,-1,1]
example (q : Fin 2→ℝ)
 (hq : q∈slice P (IntegralMixedChronologicalMidpoint.frame otherDesc (by decide) 3 2) otherVals)
 (hfree : Feature.eval (postValues otherDesc (by decide) 3 2 q otherVals)
   (signature otherDesc 3 2 1)=1) : midPoint=q:=by
 apply same_slab_point_eq desc otherDesc hk (by decide) rfl leftEnd rightEnd 3 2 vals otherVals midPoint q mid_slice hq
 · intro i
   exact Fin.elim0 i
 · norm_num [vals,otherVals,leftEnd,IntegralMixedChronologicalMidpoint.reference]
 · norm_num [vals,otherVals,rightEnd,IntegralMixedChronologicalMidpoint.reference]
 · intro i hi
   have HN : (1 : ℕ)≤ i.val:=hi
   have HE : i=1:=Fin.ext (by change i.val=1;have :=i.isLt;omega)
   subst i
   rw [point_values desc hk leftEnd rightEnd P vals midPoint mid_slice]
   exact hfree.symm
example : WordList.get (IntegralMixedChronologicalMidpointSignatureCode.code 1 4
 (IntegralMixedChronologicalFrameCode.labels desc) 3 2) 0=
 IntegralMixedChronologicalMidpointSignatureCode.meanWord 3 2:=
 IntegralMixedChronologicalMidpointSignatureCode.code_lookup_actual desc leftEnd rightEnd 0
example : WordList.get (IntegralMixedChronologicalMidpointSignatureCode.code 1 4
 (IntegralMixedChronologicalFrameCode.labels desc) 3 2) 1=
 IntegralMixedChronologicalMidpointSignatureCode.producerWord 4:=
 IntegralMixedChronologicalMidpointSignatureCode.code_lookup_actual desc leftEnd rightEnd 1
example : (IntegralMixedChronologicalMidpointCompanionCode.word 1
 (IntegralMixedChronologicalFrameCode.labels desc) 3 2 1).length≤
 IntegralMixedChronologicalMidpointCompanionCode.wordBound 1 4:=
 IntegralMixedChronologicalMidpointCompanionCode.word_size desc hk leftEnd rightEnd obj
example : (IntegralMixedChronologicalMidpointSignatureCode.code 1 4
 (IntegralMixedChronologicalFrameCode.labels desc) 3 2).length≤
 IntegralMixedChronologicalMidpointSignatureCode.wordBound 1 4:=
 IntegralMixedChronologicalMidpointSignatureCode.word_size desc leftEnd rightEnd
example : (fun q : List Bool=>IntegralMixedChronologicalMidpointCompanionCode.word q.length q
 (Nat.fromBitsLE q) 2 1)∈LeanCanny.FP:=
 IntegralMixedChronologicalMidpointCompanionCode.word_FP (UnaryFn.length id_mem_FP)
 (BinaryFn.fromBits id_mem_FP) (BinaryFn.const 2) (BinaryFn.const 1) id_mem_FP
example : (fun q : List Bool=>IntegralMixedChronologicalMidpointSignatureCode.code q.length
 (Nat.fromBitsLE q) q 3 2)∈LeanCanny.FP:=
 IntegralMixedChronologicalMidpointSignatureCode.code_FP (UnaryFn.length id_mem_FP)
 (BinaryFn.fromBits id_mem_FP) (BinaryFn.const 3) (BinaryFn.const 2) id_mem_FP
example : UnaryFn (fun q=>IntegralMixedChronologicalMidpointCompanionCode.wordBound q.length (Nat.fromBitsLE q)):=
 IntegralMixedChronologicalMidpointCompanionCode.wordBound_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP)
example : UnaryFn (fun q=>IntegralMixedChronologicalMidpointSignatureCode.wordBound q.length (Nat.fromBitsLE q)):=
 IntegralMixedChronologicalMidpointSignatureCode.wordBound_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP)
example : UniformIntegralPowerSchedule.physical 6 4 4≠UniformIntegralPowerSchedule.physical 6 4 5:=by
 norm_num [UniformIntegralPowerSchedule.physical,UniformIntegralPowerSchedule.cap,UniformIntegralPowerSchedule.birth,
  MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
example : ((-24:ℤ)%6)=0:=by decide
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [IntegralMixedFullHistoryScript.run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]
private def prefixDesc : IntegralMixedChronologicalFrame.Descriptor 3 5:=⟨[0],by decide⟩
example : signature prefixDesc 3 2 0=.producer ⟨0,by decide⟩:=rfl
example : signature prefixDesc 3 2 1=.mean ⟨3,by decide⟩ ⟨2,by decide⟩:=rfl
example : signature prefixDesc 3 2 2=.producer ⟨6,by decide⟩:=rfl
example : signature prefixDesc 3 2 3=.producer ⟨5,by decide⟩:=rfl
example : IntegralMixedChronologicalMidpointCompanionCode.codes 3
 (IntegralMixedChronologicalFrameCode.labels prefixDesc) 3 2 2=
 [IntegralMixedChronologicalMidpointCode.code 3 (IntegralMixedChronologicalFrameCode.labels prefixDesc) 3 2 2 3,
  IntegralMixedChronologicalMidpointCode.code 3 (IntegralMixedChronologicalFrameCode.labels prefixDesc) 3 2 2 2]:=rfl
#print axioms realized_signature_value
#print axioms same_slab_point_eq
#print axioms point_values
#print axioms IntegralMixedChronologicalMidpointCompanionCode.word_actual
#print axioms IntegralMixedChronologicalMidpointCompanionCode.codes_actual
#print axioms IntegralMixedChronologicalMidpointCompanionCode.word_FP
#print axioms IntegralMixedChronologicalMidpointCompanionCode.word_size
#print axioms IntegralMixedChronologicalMidpointCompanionCode.wordBound_unary
#print axioms IntegralMixedChronologicalMidpointSignatureCode.code_FP
#print axioms IntegralMixedChronologicalMidpointSignatureCode.entry_actual
#print axioms IntegralMixedChronologicalMidpointSignatureCode.code_lookup_actual
#print axioms IntegralMixedChronologicalMidpointSignatureCode.word_size
#print axioms IntegralMixedChronologicalMidpointSignatureCode.wordBound_unary
#print axioms capture
end MidpointCompanionSignatureRegression
end
end RoadmapLevelsMidpointCaptures

namespace RoadmapLevelsCapturedEndpoints
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open IntegralMixedOptionalEndpoints Set
open scoped Classical
noncomputable section
namespace OptionalCapturedEndpointRegression

private def initial (n : ℕ) : Frame n:=
  {frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
private def circle : SpatialSource 1:=
  {low:=MvPolynomial.C (-4),leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_C]; decide,leading_ne_zero:=by decide}
private def endpoint (right : Bool) : Fin 2→ℝ:=Fin.cons (if right then 2 else -2) (fun _=>0)
private theorem circle_root (right : Bool) :
    (FermatCriticalHomogenization.polynomial circle.low circle.leading circle.degree).eval₂
      (Int.castRingHom ℝ) (endpoint right)=0:=by
  cases right <;> norm_num [circle,endpoint,FermatCriticalHomogenization.polynomial,
    MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
private def endpointValues : Fin 2→ℝ:=Fin.cons 2 (Fin.cons (-2) Fin.elim0)
private def capturePoint : Fin 2→ℝ:=Fin.cons 17 (fun _=>23)
private def captures : List (IntegralMixedPointCompanion.Free (∅ : Finset (Fin 2))):=
  [⟨1,by simp⟩,⟨0,by simp⟩,⟨1,by simp⟩]
private theorem baseAtomic : AtomicRows (initial 1) 2:=AtomicRows.initial 1 2

-- Three captures precede the anchor99 and the endpoints2,-2. Neither head
-- nor anchor is an endpoint, and the negative endpoint remains at index5.
example : (capturedReference captures.length (2 : Fin 3)).val=5:=by decide
example : (capturedReference captures.length (1 : Fin 3)).val=4:=by decide
example : IntegralMixedPointCompanion.values capturePoint (Fin.cons 99 endpointValues) captures
    (capturedReference captures.length (2 : Fin 3))=(-2 : ℝ):=by
  rw [capturedReference_value]
  rfl
example : IntegralMixedPointCompanion.values capturePoint (Fin.cons 99 endpointValues) captures
    (capturedReference captures.length (1 : Fin 3))=(2 : ℝ):=by
  rw [capturedReference_value]
  rfl
example : IntegralMixedPointCompanion.values capturePoint (Fin.cons 99 endpointValues) captures
    (0 : Fin 6)=(23 : ℝ):=rfl

private theorem endpoint_member (right : Bool) : endpoint right∈
    slice circle (referencedEndpointFrame (capturedBaseFrame_atomic baseAtomic.retained captures.length)
      0 (capturedReference captures.length (if right then (1 : Fin 3) else 2)))
      (IntegralMixedPointCompanion.values capturePoint (Fin.cons 99 endpointValues) captures):=by
  have hh : (0 : Fin 2)∉(capturedBaseFrame baseAtomic.retained captures.length).frozen:=by
    change (0 : Fin 2)∉(∅ : Finset (Fin 2))
    simp
  rw [referencedEndpointFrame_slice _ 0 hh,capturedBaseFrame_slice,slice_retained,capturedReference_value]
  refine ⟨⟨circle_root right,?_⟩,?_⟩
  · intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  · cases right <;> rfl

example := endpoint_member false
example := endpoint_member true

-- With no captures, the old2/1 layout is recovered exactly.
example : (capturedReference 0 (2 : Fin 3)).val=2 ∧ (capturedReference 0 (1 : Fin 3)).val=1:=by decide

private def oldFrame : Frame 2:=
  {frozen:={0},scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,
    heights:=fun i=>if i=0 then .reference 0 else .constant 0}
private theorem oldAtomic : AtomicRows oldFrame 1:=by
  constructor
  · intro i; rfl
  · intro i
    by_cases hi : i=0
    · exact ⟨some 0,by subst i; rfl⟩
    · exact ⟨none,by simp only [oldFrame,hi,ite_false,Atom.value]⟩

-- The previously frozen row shifts through the anchor and three captures;
-- its value is never replaced by a captured coordinate.
example : (capturedBaseFrame oldAtomic.retained 3).heights 0=.reference 4:=by
  rw [capturedBaseFrame_succ,capturedBaseFrame_succ,capturedBaseFrame_succ,capturedBaseFrame_zero]
  rfl
example : (referencedEndpointFrame (capturedBaseFrame_atomic oldAtomic.retained 3)
    1 (capturedReference 3 (1 : Fin 2))).heights 0=.reference 4:=by
  rw [referencedEndpointFrame_old_height _ 1 _ 0 (by decide)]
  rw [capturedBaseFrame_succ,capturedBaseFrame_succ,capturedBaseFrame_succ,capturedBaseFrame_zero]
  rfl
example : (referencedEndpointFrame (capturedBaseFrame_atomic oldAtomic.retained 3)
    1 (capturedReference 3 (1 : Fin 2))).heights 1=.reference 4:=
  referencedEndpointFrame_height _ _ _
example : (referencedMidpointFrame oldAtomic 1 0 0).scales 1=2 ∧
    (referencedEndpointFrame (capturedBaseFrame_atomic oldAtomic.retained 3)
      1 (capturedReference 3 (1 : Fin 2))).scales 1=1:=by
  constructor
  · exact referencedMidpointFrame_scale oldAtomic 1 0 0 1
  · rfl

-- Endpoint fibers can be singular; the physical endpoint construction has
-- no simple-root hypothesis there.
example : Polynomial.IsRoot ((Polynomial.X : Polynomial ℝ)^2) 0 ∧
    (Polynomial.derivative ((Polynomial.X : Polynomial ℝ)^2)).eval 0=0:=by simp [Polynomial.IsRoot]

section GenericPair
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {a b : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    (R : PairResult x F z φ values a b hn hcap) (h : Fin (n+1)) (q : ℕ) (right : Bool)

-- Retained, fresh, and mixed optional endpoint cases all use the actual
-- returned references; the recursive child grammar needs no new premise.
example : (R.endpointIndex q right).val=q+1+(if right then R.right.val else R.left.val):=
  R.endpointIndex_val q right
example : AtomicRows (R.endpointFrame h q right) (m+R.commands.length+1+q):=
  referencedEndpointFrame_atomic (R.capturedFrame_atomic q) h (R.endpointIndex q right)
example : FreeNormal (R.endpointFrame h q right):=
  (R.freeNormal.retained.capturedBaseFrame R.atomic.retained q).referencedEndpointFrame
    (R.capturedFrame_atomic q) h (R.endpointIndex q right)
example (p : Fin (n+1)→ℝ) (v : Fin (m+R.commands.length+1+q)→ℝ)
    (hp : p∈slice P (R.endpointFrame h q right) v) (newest : ℝ) :
    p∈slice P (retained (R.endpointFrame h q right)) (Fin.cons newest v):=by
  rw [slice_retained]
  exact hp
end GenericPair

#check PairResult.endpointIndex_val
#check PairResult.anchor_captures_endpoint_record
#check PairResult.exists_matched_endpoint_extension
#print axioms capturedBaseFrame_slice
#print axioms PairResult.endpointFrame_slice
#print axioms PairResult.endpointFrame_prefix
#print axioms PairResult.matched_endpoint_record
#print axioms PairResult.anchor_captures_endpoint_record
#print axioms PairResult.exists_matched_midpoint_captures
#print axioms PairResult.exists_matched_endpoint_extension
#print axioms PairResult.MidpointCaptures.original_raw
#print axioms PairResult.MidpointCaptures.original_hom
end OptionalCapturedEndpointRegression
end
end RoadmapLevelsCapturedEndpoints

namespace RoadmapLevelsPrefixWords
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedPhysicalPrefixSampler
open IntegralMixedRoadmapRecordChain IntegralMixedRoadmapWidth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PrefixVertexBudgetRegression
private def P : Parameters where
 cap:=fun _=>6
 width:=fun _=>3
 ambient:=fun _=>2
 sourceWidth:=fun _=>5
 degree:=fun _=>18
 height:=fun _=>0
 modulusBound:=fun _=>6
private theorem PA : Access P where
 cap:=UnaryFn.const 6
 width:=UnaryFn.const 3
 ambient:=UnaryFn.const 2
 sourceWidth:=UnaryFn.const 5
 degree:=BinaryFn.const 18
 height:=BinaryFn.const 0
 modulusBound:=BinaryFn.const 6
example : key P∈FP:=key_FP P PA
example : UnaryFn (stage P):=stage_unary P PA
example : stage P (packet [true,false] 0)=1:=rfl
example : stage P (packet [true,false] 1)=1:=rfl
example : stage P (packet [true,false] 4)=4:=rfl
example : stage P (packet [true,false] 7)=7:=rfl
example : stage P (packet [true,false] 8)=7:=rfl
example : key P (packet [true,false] 4)=IntegralMixedFramedHistoryFamilyBits.keyAt [true,false] 4 []:=
 key_packet P _ _ (by decide) (by decide)
example : key P (packet [true,false] 7)=IntegralMixedFramedHistoryFamilyBits.keyAt [true,false] 7 []:=
 key_packet P _ _ (by decide) (by decide)
example : pairFst (key P (packet [true,false] 4))=pairFst (key P (packet [true,false] 5)):=by
 rw [key_packet P _ _ (by decide) (by decide),key_packet P _ _ (by decide) (by decide)]
 rfl
example : P.width (pairFst (key P (packet [true,false] 4)))=P.width (pairFst (key P (packet [true,false] 5))) ∧
 P.cap (pairFst (key P (packet [true,false] 4)))=P.cap (pairFst (key P (packet [true,false] 5))):=by
 exact ⟨rfl,rfl⟩

variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R)
variable (original label : List Bool)
 (hl : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
 {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
 (seed probe : Word (recordBudget hn ht ha original))
private def prepared:=records.root seed probe (pair original label) []
example : (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false).Access:=
 IntegralMixedPhysicalPrefixSampler.access hn ht ha hR false
example : UnaryFn (prefixVertexBudget hn ht ha hR):=prefixVertexBudget_unary hn ht ha hR
example : ∃p : Polynomial ℕ,∀o,prefixVertexBudget hn ht ha hR o≤p.eval o.length:=
 prefixVertexBudget_polynomial hn ht ha hR
example (b : ℕ) (hb : 0<b)
 (hc : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) :
 key (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
  (packet (prepared hn ht ha original label records seed probe) b)=
 IntegralMixedFramedHistoryFamilyBits.keyAt (prepared hn ht ha original label records seed probe) b []:=
 padded_prefix_key hn ht ha hR original label records seed probe b hb hc
example (b : ℕ) (hb : 0<b)
 (hc : b≤(IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap
  (prepared hn ht ha original label records seed probe)+1) :
 SquareSampleInput.comp (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
  (fun _=>packet (prepared hn ht ha original label records seed probe) b)=
 atPrefix hn ht ha hR false (prepared hn ht ha original label records seed probe) b hb hc:=
 input_packet hn ht ha hR false _ b hb hc
example (b : ℕ) (hc : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) :
 SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
  (packet (prepared hn ht ha original label records seed probe) b)≤prefixVertexBudget hn ht ha hR original:=
 width_le_prefixVertexBudget hn ht ha hR original label hl records seed probe b hc
example : SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
  (packet (prepared hn ht ha original label records seed probe)
    (maxBirth (dimension (n:=n) original) (initial (n:=n) original)))≤prefixVertexBudget hn ht ha hR original:=by
 apply width_le_prefixVertexBudget hn ht ha hR original label hl records seed probe
 unfold cap fullBirth
 omega
example : SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
  (packet (prepared hn ht ha original label records seed probe)
    (fullBirth (dimension (n:=n) original) (initial (n:=n) original)))≤prefixVertexBudget hn ht ha hR original:=by
 apply width_le_prefixVertexBudget hn ht ha hR original label hl records seed probe
 unfold cap
 omega
#print axioms IntegralMixedPhysicalPrefixSampler.access
#print axioms IntegralMixedPhysicalPrefixSampler.key_packet
#print axioms IntegralMixedPhysicalPrefixSampler.input_packet
#print axioms IntegralMixedPhysicalPrefixSampler.width_packet
#print axioms prefixContextBudget_unary
#print axioms padded_prefix_context_length
#print axioms actual_padded_cap
#print axioms padded_prefix_key
#print axioms prefixVertexBudget_unary
#print axioms prefixVertexBudget_polynomial
#print axioms width_le_prefixVertexBudget
#print axioms atPrefix_width_le_prefixVertexBudget
#print axioms word_length_le_prefixVertexBudget
end PrefixVertexBudgetRegression
end
end RoadmapLevelsPrefixWords

namespace RoadmapLevelsNativeLevel
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedRoadmapLevel
open IntegralMixedRoadmapEndpointSyntax (spec)
open scoped Classical
namespace RoadmapLevelRegression
private def frozen:=WordList.encode [BinaryNatCode.encode 0]
private def retained (i : ℕ):=spec 0 i 0 0 0 0
private def critical (i : ℕ):=spec 1 i 1 0 0 0
private def cut (i j tag c d : ℕ):=spec 2 i j tag c d
private def query (l r : List Bool) (s : Bool):=packet frozen l r s []
private def built (l r : List Bool) (s : Bool):=
  packet frozen l r s (compiled 2 (query l r s))
private theorem fromNil :Nat.fromBitsLE []=0:=rfl
private theorem fromOne :Nat.fromBitsLE [true]=1:=rfl
private theorem getNil (i : ℕ) :WordList.get [] i=[]:=by
  simp only [WordList.get,List.length_nil,Nat.min_zero,Function.iterate_zero_apply]
  rfl

macro "check_numeric" : tactic => `(tactic|
  norm_num [IntegralMixedRoadmapEndpointSyntax.Good,IntegralMixedRoadmapEndpointSyntax.canonical,
    IntegralMixedRoadmapEndpointSyntax.field,IntegralMixedRoadmapEndpointSyntax.fresh,
    IntegralMixedRoadmapEndpointSyntax.spec,IntegralMixedChronologicalCutCode.Bounds,
    IntegralMixedChronologicalCutCode.Good,IntegralMixedChronologicalFrameCode.Good,
    WordListRecords.count_encode,WordList.get_encode,retained,critical,cut,frozen,Nat.lt_one_iff,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,fromNil,fromOne,getNil,WordListRecords.encode_eq_nil])

private theorem goodRet : Good 2 3 8 4 (query (retained 1) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
private theorem goodFresh : Good 2 3 8 4 (query (cut 4 2 2 8 8) (critical 5) true) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
private theorem checkedRet : Checked 2 3 8 4 (built (retained 1) (retained 2) false):=
  checked_packet 2 3 8 4 frozen _ _ false goodRet
private theorem checkedFresh : Checked 2 3 8 4 (built (cut 4 2 2 8 8) (critical 5) true):=
  checked_packet 2 3 8 4 frozen _ _ true goodFresh

example : FPPred (fun q=>Checked 2 3 8 4 q):=
  checked_FP (UnaryFn.const 2) (UnaryFn.const 3) (BinaryFn.const 8) (BinaryFn.const 4)
example : UnaryFn (fun q=>budget 2 3 4 q):=
  budget_unary (UnaryFn.const 2) (UnaryFn.const 3) (BinaryFn.const 4)
example : FPPred (fun q=>InRaw 2 q (pairFst q) 0):=
  inRaw_FP (UnaryFn.const 2) pairFst_mem_FP (BinaryFn.const 0)
example : rawSlice (WordList.encode [[true],[false],[]]) 1 2=WordList.encode [[false],[]] :=rfl
example : rawSlice (WordList.encode [[true],[false],[]]) 2 2=WordList.encode [[],[]] :=rfl
example : ¬InRaw 2 (query (retained 1) (retained 2) false) (WordList.encode [[true]]) 0 :=by
  intro h
  have H:=h.1
  change 4≤1 at H
  omega

-- Raw critical and cut ABI fields retain distinct producer and physical heads.
example : chosen (built (retained 1) (retained 2) false)=1 :=by rfl
example : chosen (built (retained 1) (retained 2) true)=2 :=by decide
example : childBirth 2 4 (built (retained 1) (retained 2) false)=6 :=by rfl
example : chosen (built (cut 4 2 2 8 8) (critical 5) true)=5 :=by decide
example : afterEndpoints 4 (built (cut 4 2 2 8 8) (critical 5) true)=6 :=by rfl
example : endBirth 2 4 (built (cut 4 2 2 8 8) (critical 5) true)=10 :=by rfl
example : WordListRecords.count (childLabels (built (retained 1) (retained 2) false))=2 :=by
  rw [child_labels_count];rfl
example : WordListRecords.count (slice (built (retained 1) (retained 2) false))=4 :=by
  rw [checked_count checkedRet];rfl
example : WordListRecords.count (slice (built (cut 4 2 2 8 8) (critical 5) true))=6 :=by
  rw [checked_count checkedFresh];rfl
example : WordList.encode ((ledger checkedFresh).codes.map Subtype.val)=slice (built (cut 4 2 2 8 8) (critical 5) true):=
  ledger_word checkedFresh
example : IntegralMixedChronologicalEndpointCode.PointGood 2 8
    (labels (built (cut 4 2 2 8 8) (critical 5) true)) 5 2 2 :=
  checked_child_anchor checkedFresh

-- Right retained endpoints must already exist BEFORE either fresh endpoint.
example : ¬Good 2 3 8 4 (query (critical 4) (retained 4) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
-- A fresh right producer must include the fresh left birth.
example : ¬Good 2 3 8 4 (query (critical 4) (critical 4) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query (cut 4 2 3 8 8) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query (cut 4 1 2 8 8) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query (cut 4 2 2 9 8) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query (cut 4 2 2 8 9) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query [] (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (query (spec 0 1 1 0 0 0) (retained 2) false) :=by
  simp only [Good,query,g,k,labels,left,right,sideWord,side,slice,freshLeft,packet,pairFst_pair,pairSnd_pair]
  check_numeric
example : ¬Good 2 3 8 4 (pair frozen (pair (retained 1) (pair (retained 2) (pair [false] [])))) :=by
  intro h
  have HS:=h.2.2.2.2.1
  change ([false]=([] : List Bool) ∨ [false]=[true]) at HS
  rcases HS with h|h <;> cases h
example : ¬Good 2 3 8 4 (packet (WordList.encode [BinaryNatCode.encode 4]) (retained 1) (retained 2) false []) :=by
  intro h
  have HI:=h.1.2 0 (by
    simp only [labels,packet,pairFst_pair,WordListRecords.count_encode,List.length_singleton]
    omega)
  simp only [labels,packet,pairFst_pair,WordList.get_encode,List.getElem?_cons_zero,Option.getD_some,
    BinaryNatCode.encode,Nat.fromBitsLE_bits] at HI
  omega
example : ¬Checked 1 3 8 4 (query (retained 1) (retained 2) false) :=
  reject_terminal (by rfl)
example : ¬Checked 2 3 8 4 (query (retained 1) (retained 2) false) :=by
  intro h
  have H:=checked_count h
  change 0=4 at H
  omega

end RoadmapLevelRegression
#print axioms IntegralMixedRoadmapEndpointSyntax.field_binary
#print axioms IntegralMixedRoadmapEndpointSyntax.good_FP
#print axioms IntegralMixedRoadmapEndpointSyntax.checked_code
#print axioms IntegralMixedRoadmapLevel.compiled_FP
#print axioms IntegralMixedRoadmapLevel.rawSlice_FP
#print axioms IntegralMixedRoadmapLevel.inRaw_FP
#print axioms IntegralMixedRoadmapLevel.checked_raw_record
#print axioms IntegralMixedRoadmapLevel.compiled_packet
#print axioms IntegralMixedRoadmapLevel.codes_length
#print axioms IntegralMixedRoadmapLevel.endBirth_binary
#print axioms IntegralMixedRoadmapLevel.good_FP
#print axioms IntegralMixedRoadmapLevel.checked_FP
#print axioms IntegralMixedRoadmapLevel.checked_packet
#print axioms IntegralMixedRoadmapLevel.chosen_lt
#print axioms IntegralMixedRoadmapLevel.child_frame_good
#print axioms IntegralMixedRoadmapLevel.checked_count
#print axioms IntegralMixedRoadmapLevel.checked_endBirth
#print axioms IntegralMixedRoadmapLevel.checked_codes
#print axioms IntegralMixedRoadmapLevel.checked_midpoint_anchor
#print axioms IntegralMixedRoadmapLevel.checked_midpoint_companion
#print axioms IntegralMixedRoadmapLevel.checked_child_anchor
#print axioms IntegralMixedRoadmapLevel.checked_child_companion
#print axioms IntegralMixedRoadmapLevel.reject_terminal
#print axioms IntegralMixedRoadmapLevel.budget_unary
#print axioms IntegralMixedRoadmapLevel.endpoint_size
#print axioms IntegralMixedRoadmapLevel.ledger
#print axioms IntegralMixedRoadmapLevel.ledger_codes
#print axioms IntegralMixedRoadmapLevel.ledger_word
end RoadmapLevelsNativeLevel
