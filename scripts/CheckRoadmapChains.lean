import LeanCanny.Algebra.IntegralMixedIntegerRealization
import LeanCanny.Algebra.IntegralMixedMeanCenteredSweep
import LeanCanny.Connectivity
import LeanCanny.Connectivity.IntegralMixedSpecializedRootRankComparison
import LeanCanny.Encoding.IntegralFramedPaddedCutVertex
import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientInterval
import LeanCanny.Encoding.IntegralMixedPhysicalCutStrictMargin
import LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe
import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
import LeanCanny.Geometry.IntegralMixedDegenerateBoundarySampling
import LeanCanny.Geometry.IntegralMixedPointCompanionBounds

/-! Whole native chains, reserved probes, equal-height programs and
specialized coordinate-rank regressions. Geometric graph validity is separate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapChainsWholeChain
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedRoadmapChain
open IntegralMixedRoadmapEndpointSyntax (spec)
open scoped Classical
namespace RoadmapChainRegression
private theorem countNil :WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []
private theorem fromNil :Nat.fromBitsLE []=0:=rfl
private theorem fromOne :Nat.fromBitsLE [true]=1:=rfl
private def step (l r : List Bool) (s : Bool):=WordList.encode [l,r,if s then [true] else []]
private def retained (i : ℕ):=spec 0 i 0 0 0 0
private def m2:=WordList.encode [step (spec 1 25 0 0 0 0) (retained 2) false,
  step (retained 25) (spec 2 34 2 0 1 1) true]
private def q2:=packet m2 [] []

macro "prefix_numeric" : tactic => `(tactic|
  norm_num [q2,m2,step,packet,metadata,depth,entry,left,right,sideWord,chosen,freshCount,blockCount,
    IntegralMixedRoadmapEndpointSyntax.fresh,IntegralMixedRoadmapEndpointSyntax.field,
    IntegralMixedRoadmapEndpointSyntax.spec,retained,WordListRecords.count_encode,
    WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits,fromNil,fromOne])

example : depth q2=2 :=by prefix_numeric
example : chosen q2 0=25 :=by prefix_numeric
example : chosen q2 1=34 :=by prefix_numeric
example : freshCount q2 0=1 :=by prefix_numeric
example : freshCount q2 1=1 :=by prefix_numeric
example : blockCount 3 q2 0=9 :=by prefix_numeric
example : blockCount 3 q2 1=7 :=by prefix_numeric
example : rawStart 3 q2 0=5 :=by simp only [rawStart,prefixCount,Finset.range_zero,Finset.sum_empty];rfl
example : rawStart 3 q2 1=14 :=by
  simp only [rawStart,prefixCount,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty]
  prefix_numeric
example : rawStart 3 q2 2=21 :=by
  simp only [rawStart,prefixCount,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty]
  prefix_numeric
example : birth 3 20 q2 2=41 :=by
  unfold birth
  simp only [rawStart,prefixCount,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty]
  prefix_numeric
example : WordListRecords.count (frozen q2 2)=2:=frozen_count _ _
example : Nat.fromBitsLE (WordList.get (frozen q2 2) 0)=25 :=by
  rw [frozen_lookup _ _ _ (by omega)]
  prefix_numeric
example : Nat.fromBitsLE (WordList.get (frozen q2 2) 1)=34 :=by
  rw [frozen_lookup _ _ _ (by omega)]
  prefix_numeric
example : (compiledCodes 3 q2).length=34 :=compiledCodes_length 3 q2 (by prefix_numeric)
example : FPPred (fun q=>Checked 3 2 4 20 2 q):=
  checked_FP (UnaryFn.const 3) (UnaryFn.const 2) (BinaryFn.const 4) (BinaryFn.const 20) (UnaryFn.const 2)
example : (fun q=>compiled 3 q)∈FP:=compiled_FP (UnaryFn.const 3)
example {n : List Bool→ℕ} (hn :UnaryFn n) :
    (fun q=>compiled (n (pairFst q)) (pairSnd q))∈FP:=
  compiledAt_FP (hn.comp pairFst_mem_FP) pairSnd_mem_FP
example {n : List Bool→ℕ} (hn :UnaryFn n) :
    FPPred (fun q=>Checked (n (pairFst q)) 0 0 0 0 (pairSnd q)):=
  checkedAt_FP (hn.comp pairFst_mem_FP) (UnaryFn.const 0) (BinaryFn.const 0)
    (BinaryFn.const 0) (UnaryFn.const 0) pairSnd_mem_FP

-- A genuine accepted full table, with canonical root seed/padding and a
-- reserved empty probe; no interpreted point or graph predicate is assumed.
private def base:=packet [] [] []
private def accepted:=packet [] (compiled 0 base) []
private theorem hdepth :depth accepted=0:=by
  simp only [depth,metadata,accepted,packet,pairFst_pair,countNil]
private theorem accepted_checked :Checked 0 0 0 0 0 accepted:=by
  have HM :metadata accepted=[]:=by simp only [metadata,accepted,packet,pairFst_pair]
  have HR :raw accepted=compiled 0 base:=by simp only [raw,accepted,packet,pairFst_pair,pairSnd_pair]
  have HP :probe accepted=[]:=by simp only [probe,accepted,packet,pairSnd_pair]
  refine ⟨by rw [hdepth],le_rfl,by decide,?_,?_,?_,?_,?_,?_⟩
  · rw [HM,hdepth]
    rfl
  · intro i hi
    rw [hdepth] at hi
    omega
  · rw [HR]
    exact (compiled_packet 0 [] [] (compiled 0 base) []).symm
  · rw [HR,compiled,WordListRecords.count_encode,compiledCodes_length]
    simp only [depth,metadata,base,packet,pairFst_pair,countNil]
    omega
  · rw [HP]
    exact Nat.zero_le _
  · simp only [accepted,packet,metadata,raw,probe,pairFst_pair,pairSnd_pair]

example : (records accepted_checked).chain.depth=0 :=by rw [records_depth,hdepth]
example : (records accepted_checked).codes.length=2 :=by
  rw [records_length,hdepth]
  rfl
example : raw accepted=(records accepted_checked).paddedWord (seed 0 0 0 ⟨0,by omega⟩) (reservedProbe accepted_checked):=
  raw_paddedWord accepted_checked
example : WordListRecords.count (raw accepted)=7:=accepted_checked.2.2.2.2.2.2.1
example : ¬Checked 1 2 4 20 2 q2 :=by
  intro h
  have HD:=h.1
  have HE :depth q2=2:=by prefix_numeric
  omega
example : ¬Checked 0 0 0 0 0 base :=by
  intro h
  have HC:=h.2.2.2.2.2.2.1
  change WordListRecords.count []=7 at HC
  rw [countNil] at HC
  omega
example (q : List Bool) (_h :Checked 3 2 4 20 2 q) (i : ℕ) (_hi :i<depth q) :
    IntegralMixedRoadmapLevel.childLabels (levelPacket 3 q i)=frozen q (i+1):=
  level_frozen _ _ _
example (q : List Bool) (h :Checked 3 2 4 20 2 q) :
    (raw q).length≤(2*IntegralMixedRoadmapRecordChain.codeBound 3 20 2+2)*34 :=raw_length_le h
example (q : List Bool) (hprobe :IntegralMixedRoadmapRecordChain.codeBound 3 20 2<(probe q).length) :
    ¬Checked 3 2 4 20 2 q:=by
  intro h
  exact (Nat.not_le.mpr hprobe) h.2.2.2.2.2.2.2.1

end RoadmapChainRegression
#print axioms IntegralMixedRoadmapChain.frozen_FP
#print axioms IntegralMixedRoadmapChain.prefixCount_unary
#print axioms IntegralMixedRoadmapChain.rawStart_unary
#print axioms IntegralMixedRoadmapChain.birth_binary
#print axioms IntegralMixedRoadmapChain.frozen_succ
#print axioms IntegralMixedRoadmapChain.prefixCount_bound
#print axioms IntegralMixedRoadmapChain.rawStart_bound
#print axioms IntegralMixedRoadmapChain.compiled_FP
#print axioms IntegralMixedRoadmapChain.compiledAt_FP
#print axioms IntegralMixedRoadmapChain.compiled_packet
#print axioms IntegralMixedRoadmapChain.levelPacket_FP
#print axioms IntegralMixedRoadmapChain.level_count
#print axioms IntegralMixedRoadmapChain.level_end
#print axioms IntegralMixedRoadmapChain.checked_FP
#print axioms IntegralMixedRoadmapChain.checkedAt_FP
#print axioms IntegralMixedRoadmapChain.level_checked
#print axioms IntegralMixedRoadmapChain.level_frozen
#print axioms IntegralMixedRoadmapChain.level_end_bound
#print axioms IntegralMixedRoadmapChain.seed_values
#print axioms IntegralMixedRoadmapChain.typedLevel_codes
#print axioms IntegralMixedRoadmapChain.chainFrom_codes
#print axioms IntegralMixedRoadmapChain.records_codes
#print axioms IntegralMixedRoadmapChain.records_depth
#print axioms IntegralMixedRoadmapChain.records_length
#print axioms IntegralMixedRoadmapChain.raw_paddedWord
#print axioms IntegralMixedRoadmapChain.raw_length_le
end RoadmapChainsWholeChain

namespace RoadmapChainsReservedProbe
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ReservedIntervalProbeRegression
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



private theorem padding_root (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B)
 (p : Polynomial (before B hc).sampler.scalarPrefix.carrier) (d : ℕ) (hd : d<2^B) :
 ∃y,∃ψ : (normalizedScalarStep (before B hc) (by decide) p d).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
   (∀i,((normalizedScalarStep (before B hc) (by decide) p d).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
   y (Sum.inr ())=0 ∧
   ψ ((normalizedScalarStep (before B hc) (by decide) p d).bank.numerator 0)/
     ((normalizedScalarStep (before B hc) (by decide) p d).bank.denominator 0:ℝ)=0 ∧
   ∀i : Fin 4,ψ ((normalizedScalarStep (before B hc) (by decide) p d).bank.numerator i.succ)/
     ((normalizedScalarStep (before B hc) (by decide) p d).bank.denominator i.succ:ℝ)=vals i:=by
 obtain ⟨z,φ,hz,hφ,hvals⟩:=before_realized B hc
 obtain ⟨y,ψ,hy,_,hz0,_,_,hhead,htail⟩:=normalizedScalar_padding_zero_extend (before B hc)
   (by decide) p d hd z hz φ hφ
 exact ⟨y,ψ,hy,hz0,hhead,fun i=>(htail i).trans (hvals i)⟩

example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃y,∀i,((normalizedScalarStep (before B hc) (by decide) (1 : Polynomial _) 0).sampler.rows i).eval₂
    (Int.castRingHom ℝ) y=0:=by
 obtain ⟨y,ψ,hy,_,_,_⟩:=padding_root B hc 1 0 (Nat.two_pow_pos B)
 exact ⟨y,hy⟩
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) (hd : 2<2^B) :
 ∃y,∀i,((normalizedScalarStep (before B hc) (by decide) ((X^2+1) : Polynomial _) 2).sampler.rows i).eval₂
    (Int.castRingHom ℝ) y=0:=by
 obtain ⟨y,ψ,hy,_,_,_⟩:=padding_root B hc (X^2+1) 2 hd
 exact ⟨y,hy⟩
example : (PaddedIntegralNormalization.polynomial (1 : Polynomial ℤ) 0 8)=X^8:=by
 simp [PaddedIntegralNormalization.polynomial,FixedDegreeIntegralNormalization.polynomial]
example : (PaddedIntegralNormalization.polynomial (X^2+1 : Polynomial ℤ) 2 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial]
example : (1 : Polynomial ℝ).eval 0=1:=by simp
example : (X^2+1 : Polynomial ℝ).eval 0=1:=by norm_num
example : ∀r : ℝ,(X^2+1 : Polynomial ℝ).eval r≠0:=by
 intro r hr
 norm_num at hr
 nlinarith [sq_nonneg r]
example : ∀r : ℝ,(1 : Polynomial ℝ).eval r=0 → r ∉ Set.Ioo (-1) 1:=
 IntegralFramedFullCutOpenInterval.constant_empty 1 one_ne_zero (by simp) (-1) 1
example : RealRootOpenIntervalOrdered.value (X^2+1) 2 (-1) ((-24:ℝ)^2) true=
 RealRootOpenIntervalOrdered.value (X^2+1) 2 1 ((-24:ℝ)^2) false:=by
 apply (RealRootOpenIntervalOrdered.empty_iff (X^2+1) 2 (by decide) (by compute_degree;norm_num) (by norm_num) _ (by norm_num)).mp
 intro r hr
 norm_num at hr
 nlinarith [sq_nonneg r]
open LeanCanny.Computation
private def constantSign (q : List Bool):=if Nat.fromBitsLE (pairFst (pairSnd q))=0 then InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0
example (cap : ℕ) : FiniteCoefficientSignScan.Guards constantSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>0) (fun _=>cap) []:=by
 refine ⟨?_,?_,?_,Or.inl ?_⟩
 · intro k hk
   have HK : k<0:=hk
   omega
 · decide
 · intro e _ he
   have HE : e≠0:=Nat.ne_of_gt he
   simp [FiniteCoefficientSignScan.Zero,constantSign,FiniteCoefficientSignScan.query,BinaryNatCode.encode,Nat.fromBitsLE_bits,HE]
 · decide
example (cap : ℕ) : ¬FiniteCoefficientSignScan.Guards constantSign (fun _=>InfinitesimalSign.encode 0)
 (fun _=>0) (fun _=>0) (fun _=>cap) []:=by
 intro H
 have HX:=H.2.2.2
 norm_num [FiniteCoefficientSignScan.Zero,constantSign,FiniteCoefficientSignScan.query,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HX
 exact (by decide : InfinitesimalSign.encode 1≠InfinitesimalSign.encode 0) (HX rfl)
example : ((-24:ℤ)%6)=0:=by decide

variable {n : List Bool→ℕ} {t : List Bool→LeanCanny.ETR.Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R)
example (outer : Bool) (root : List Bool) :
 IntegralMixedExceptionalBounds.auxiliaryCap ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters.ambient root+1)
  ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters.degree root)<
  2^(IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters.width root:=
 IntegralMixedPhysicalCutStrictMargin.actual_cap_lt hn ht ha hR outer root
example (outer : Bool) : SpaceDecider (IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer):=
 IntegralMixedPhysicalCutCoefficientInterval.decider hn ht ha hR outer
example (outer : Bool) : IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer∈PSPACE:=
 IntegralMixedPhysicalCutCoefficientInterval.mem_PSPACE hn ht ha hR outer
example (outer : Bool) (q : List Bool) : IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha hR outer q ↔
 (∀j<IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer q,
 j≠IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer q-1→
 IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR outer (IntegralFramedTraceCutScan.stagePacket q j)→
 IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (IntegralFramedTraceCutScan.stagePacket q j)):=
 IntegralMixedPhysicalTraceBeforeProbe.except_last_iff hn ht ha hR outer q
example (outer : Bool) : SpaceDecider (IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha hR outer):=
 IntegralMixedPhysicalTraceBeforeProbe.decider hn ht ha hR outer
example (outer : Bool) (ctx w : List Bool) : IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer (pair ctx w)-1=
 IntegralFramedTraceCutMetadata.length (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters
 (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).plan ctx-1:=
 IntegralMixedPhysicalTraceBeforeProbe.bound_actual hn ht ha hR outer ctx w
#print axioms normalizedScalar_padding_zero_extend
#print axioms IntegralMixedPhysicalCutStrictMargin.source_cap_lt
#print axioms IntegralMixedPhysicalCutStrictMargin.actual_cap_lt
#print axioms IntegralMixedPhysicalCutStrictMargin.selected_degree_lt
#print axioms IntegralMixedPhysicalCutCoefficientOnly.evaluator
#print axioms IntegralMixedPhysicalCutCoefficientOnly.coefficient_guards
#print axioms IntegralMixedPhysicalCutCoefficientOnly.interpreted_guards
#print axioms IntegralMixedPhysicalCutCoefficientInterval.decider
#print axioms IntegralMixedPhysicalCutCoefficientInterval.mem_PSPACE
#print axioms IntegralMixedPhysicalCutCoefficientInterval.interpreted_empty_iff
#print axioms IntegralFramedPaddedCutVertex.step_realizes
#print axioms IntegralFramedPaddedCutVertex.run_realizes
#print axioms IntegralFramedPaddedCutVertex.full_positive
#print axioms IntegralFramedPaddedCutVertex.exists_vertex
#print axioms padding_root
#print axioms IntegralMixedPhysicalTraceBeforeProbe.earlier_iff
#print axioms IntegralMixedPhysicalTraceBeforeProbe.except_last_iff
#print axioms IntegralMixedPhysicalTraceBeforeProbe.bound_actual
#print axioms IntegralMixedPhysicalTraceBeforeProbe.evaluator
#print axioms IntegralMixedPhysicalTraceBeforeProbe.decider
end ReservedIntervalProbeRegression
end
end RoadmapChainsReservedProbe

namespace RoadmapChainsEqualHeight
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open IntegralMixedOptionalEndpoints Set
open scoped Classical
noncomputable section
namespace DegenerateBoundaryRegression
private def initial (n : ℕ) : Frame n:=
  {frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
private def sphere : SpatialSource 2:=
  {low:=MvPolynomial.C (-4),leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_C]; decide,leading_ne_zero:=by decide}
private def point (i : Fin 3) : ℝ:=if i=0 then 2 else 0
private def noValues : Fin 0→ℝ:=Fin.elim0
private theorem source_root :
    (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree).eval₂
      (Int.castRingHom ℝ) point=0:=by
  norm_num [sphere,point,FermatCriticalHomogenization.polynomial,MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
private theorem source_member {m : ℕ} (v : Fin m→ℝ) : point∈slice sphere (initial 2) v:=by
  refine ⟨source_root,?_⟩
  intro i hi
  exact False.elim (Finset.notMem_empty i hi)
private theorem gradient_eval (i : Fin 3) :
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=2*point i:=by
  change ((MvPolynomial.pderiv i) (FermatCriticalHomogenization.polynomial (MvPolynomial.C (-4)) 1 2)).eval₂
    (Int.castRingHom ℝ) point=2*point i
  rw [FermatCriticalHomogenization.pderiv_polynomial,MvPolynomial.pderiv_C]
  norm_num [MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
private theorem parent_critical : ∀i,i∉(initial 2).frozen→i≠(0 : Fin 3)→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0:=by
  intro i _ hi
  fin_cases i
  · exact (hi rfl).elim
  · exact (gradient_eval 1).trans (by norm_num [point])
  · exact (gradient_eval 2).trans (by norm_num [point])

-- The old h-critical point is g-critical after freezing h at its own height.
example : ∀i,i∉insert (0 : Fin 3) (initial 2).frozen→i≠(1 : Fin 3)→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0:=critical_after_freezing 0 1 point parent_critical
example : (2 : ℝ)∈realCriticalValues sphere (line (initial 2) 0) noValues 0:=
  parent_critical_height (by intro i _;exact ⟨rfl,rfl⟩) 0 (by simp [initial])
    point (source_member noValues) rfl parent_critical
example : Ioo (2 : ℝ) 2=∅:=Ioo_self 2

-- Distinct endpoint producers carry the SAME height. No interval is created.
private def endpointValues : Fin 2→ℝ:=Fin.cons 2 (Fin.cons 2 Fin.elim0)
private abbrev captures : List (IntegralMixedPointCompanion.Free ({0} : Finset (Fin 3))):=
  [⟨1,by decide⟩,⟨2,by decide⟩]
private theorem oldAtomic : AtomicRows (initial 2) 2:=AtomicRows.initial 2 2
private abbrev midpointValues : Fin 5→ℝ:=
  IntegralMixedPointCompanion.values point (Fin.cons (point 1) endpointValues) captures
example : (capturedReference 2 (2 : Fin 3)).val=4 ∧
    (capturedReference 2 (1 : Fin 3)).val=3:=by decide
example : midpointValues (capturedReference 2 (2 : Fin 3))=(2 : ℝ):=by
  exact capturedReference_value point (Fin.cons (point 1) endpointValues) captures (2 : Fin 3)
example : midpointValues (capturedReference 2 (1 : Fin 3))=(2 : ℝ):=by
  exact capturedReference_value point (Fin.cons (point 1) endpointValues) captures (1 : Fin 3)
example : midpointValues (0 : Fin 5)=(0 : ℝ):=rfl

private theorem endpoint_member (right : Bool) : point∈slice sphere
    (referencedEndpointFrame (capturedBaseFrame_atomic oldAtomic.retained captures.length) 0
      (capturedReference captures.length (if right then (1 : Fin 3) else 2))) midpointValues:=by
  have hh : (0 : Fin 3)∉(capturedBaseFrame oldAtomic.retained captures.length).frozen:=by
    change (0 : Fin 3)∉(∅ : Finset (Fin 3));simp
  rw [referencedEndpointFrame_slice _ 0 hh,capturedBaseFrame_slice,slice_retained]
  exact ⟨source_member endpointValues,by cases right <;> rfl⟩
example := endpoint_member false
example := endpoint_member true

-- Endpoint record +two more captures shift both old endpoints by another3.
example : IntegralMixedPointCompanion.values point (Fin.cons (point 1) midpointValues) captures
    (capturedReference 2 (capturedReference 2 (2 : Fin 3)).succ)=(2 : ℝ):=by
  exact capturedReference_value point (Fin.cons (point 1) midpointValues) captures
    (capturedReference 2 (2 : Fin 3)).succ
example : (capturedReference 2 (capturedReference 2 (2 : Fin 3)).succ).val=7:=by decide
example : (2 : ℕ)+2+2*captures.length=8:=by decide
example : (IntegralMixedPointCompanion.allFree ({0} : Finset (Fin 3))).length=2:=by
  rw [allFree_length_eq]
  decide

-- The boundary fiber is singular: all derivatives in its free variables
-- vanish. The full source still has nonzero h derivative.
example :
    (MvPolynomial.pderiv (1 : Fin 3) (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0 ∧
    (MvPolynomial.pderiv (2 : Fin 3) (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=0 ∧
    (MvPolynomial.pderiv (0 : Fin 3) (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree)).eval₂
      (Int.castRingHom ℝ) point=4:=by
  exact ⟨(gradient_eval 1).trans (by norm_num [point]),
    (gradient_eval 2).trans (by norm_num [point]),(gradient_eval 0).trans (by norm_num [point])⟩

#check PairResult.exists_degenerate_program
#check PairResult.exists_parent_critical_degenerate_program
#check PairResult.exists_component_degenerate_program
#check PairResult.degenerateCodes_fresh_count
#check PairResult.degenerateCodes_command_count
#check PairResult.degenerateCodes_allFree_level_budget
#print axioms critical_after_freezing
#print axioms parent_critical_height
#print axioms PairResult.exists_degenerate_midpoint_captures
#print axioms PairResult.exists_degenerate_child_captures
#print axioms PairResult.exists_degenerate_program
#print axioms PairResult.exists_parent_critical_degenerate_program
#print axioms PairResult.exists_component_degenerate_program
#print axioms PairResult.degenerateCodes_length
#print axioms PairResult.degenerateCodes_command_count
#print axioms PairResult.degenerateCodes_allFree_level_budget
#print axioms PairResult.degenerateCodes_size
#print axioms PairResult.degenerate_word_size
end DegenerateBoundaryRegression
end
end RoadmapChainsEqualHeight

namespace RoadmapChainsSpecializedRanks
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Polynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace MeanCenteredRegression
private def r : Rule 1 where
 critical:=
  { offset:=⟨1,by decide⟩
    objective:=0
    coordinate:=0
    scales:=fun _=>1
    scales_ne_zero:=fun _=>one_ne_zero
    heights:=fun _=>.constant 0 }
 height:=0
 height_frozen:=by decide
 slope:=-24
 slope_ne_zero:=by decide
private def values (i : Fin 2) : ℝ:=if i=0 then -2 else 6
example : r.slope=-24:=rfl
example : (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 1).critical.scales 0=2:=rfl
example : (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 1).critical.scales 1=1:=rfl
example : (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 1).critical.heights 0=
    AffineExpr.add (.reference 0) (.reference 1):=rfl
example : (values 0+values 1)/2=2:=by norm_num [values]
example : (normalized r values 0).eval 2=2:=by
 norm_num [normalized,ClearedCoordinateNormalization.normalized,numericalHeights,r,AffineExpr.evaluate]
example : (normalized (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 1) values 0).eval 0=2:=by
 norm_num [normalized,ClearedCoordinateNormalization.normalized,numericalHeights,r,IntegralMixedMeanCenteredSweep.rule,values,AffineExpr.evaluate]
example (P : SpatialSource 1) (j : Fin 1) :
    coordinateAt P r values ((values 0+values 1)/2) j=
      coordinateAt P (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 1) values 0 j :=
 IntegralMixedMeanCenteredSweep.coordinateAt_mean P r 0 1 values (by norm_num [r,AffineExpr.evaluate]) rfl j
example : (normalized (IntegralMixedMeanCenteredSweep.rule r (0 : Fin 2) 0) values 0).eval 0=values 0:=by
 norm_num [normalized,ClearedCoordinateNormalization.normalized,numericalHeights,r,IntegralMixedMeanCenteredSweep.rule,values,AffineExpr.evaluate]
example (p : Polynomial ℝ) : (C (-24 : ℝ)*p).roots=p.roots:=Polynomial.roots_C_mul p (by norm_num)
#print axioms IntegralMixedNumericalSweep.coordinate_specialize
#print axioms IntegralMixedNumericalSweep.coordinateAt_congr
#print axioms IntegralMixedNumericalSweep.specialized_selected_roots
#print axioms IntegralMixedMeanCenteredSweep.normalized_at_mean
#print axioms IntegralMixedMeanCenteredSweep.coordinateAt_mean
#print axioms IntegralMixedSpecializedRootRankComparison.root_sets
#print axioms IntegralMixedSpecializedRootRankComparison.ranks
#print axioms IntegralMixedSpecializedRootRankComparison.ordinals
end MeanCenteredRegression
end RoadmapChainsSpecializedRanks
