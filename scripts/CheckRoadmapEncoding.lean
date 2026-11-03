import LeanCanny.Algebra.IntegralMixedCommandClearing
import LeanCanny.Algebra.IntegralMixedIntegerRealization
import LeanCanny.Connectivity
import LeanCanny.Encoding.IntegralFramedPhysicalSquareContext
import LeanCanny.Encoding.IntegralMixedChronologicalCompanionCode
import LeanCanny.Encoding.IntegralMixedChronologicalEndpointRaw
import LeanCanny.Encoding.IntegralMixedChronologicalMidpointRaw
import LeanCanny.Encoding.IntegralMixedChronologicalPointSignatureCode
import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
import LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison
import LeanCanny.Encoding.IntegralMixedRoadmapFramedColumns
import LeanCanny.Encoding.IntegralMixedRoadmapPaddedWord
import LeanCanny.Encoding.IntegralMixedRoadmapRecordBudget
import LeanCanny.Encoding.NoInfinitySquareWordWidth
import LeanCanny.Geometry.IntegralMixedChronologicalFrameFreeze
import LeanCanny.Geometry.IntegralMixedChronologicalPointReadback
import LeanCanny.Geometry.IntegralMixedMatchedSlabBlock
import LeanCanny.Geometry.IntegralMixedPointCompanionBounds
import LeanCanny.Geometry.IntegralMixedPointCompanionPaddingBounds

/-! Regressions for actual captures, native frame and point compilers,
fixed record caps, same-word sampling and cross-context equality. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapChronological
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace ChronologicalRoadmapRegression

private def d : IntegralMixedChronologicalFrame.Descriptor 3 5 where
  labels:=[0,3]
  length_le:=by decide

example : (d.reference ⟨0,by decide⟩).val=4 ∧ (d.reference ⟨1,by decide⟩).val=1:=by decide
example : d.freeCount=2:=by decide
example : List.ofFn (fun i : Fin 4=>(d.pointProducer i).val)=[0,3,6,5]:=by decide
example : List.ofFn (fun i : Fin 4=>(d.pointReference i).val)=[6,3,0,1]:=by decide
example : (d.freeze 2 (by decide)).labels.map Fin.val=[0,3,2]:=by decide
example : d.retain.labels.map Fin.val=[0,3]:=by decide
example (i : Fin 4) : (d.retain.atom i).word=(d.atom i).word:=d.atom_word_retain i
example (P : SpatialSource 3) (v : Fin 5→ℝ) :
    IntegralMixedFrozenFrame.slice P (d.freeze 2 (by decide)).frame v=
      IntegralMixedFrozenFrame.slice P d.frame v∩{p | p 2=v 2}:=d.freeze_slice 2 (by decide) P v

private theorem good : IntegralMixedChronologicalFrameCode.PointGood 3 5
    (IntegralMixedChronologicalFrameCode.labels d) 2 3:=
  ⟨IntegralMixedChronologicalFrameCode.labels_good d,by decide,by decide,by decide,by decide⟩
example : ¬IntegralMixedChronologicalFrameCode.PointGood 3 5
    (IntegralMixedChronologicalFrameCode.labels d) 1 3:=by
  intro H
  have HC:=H.2.1
  change 2≤1 at HC
  omega
example : ¬IntegralMixedChronologicalFrameCode.Good 3 5
    (WordList.encode [BinaryNatCode.encode 5]):=by
  intro H
  have HC:=H.2 0 (by decide)
  change 5<5 at HC
  omega
example : ¬IntegralMixedChronologicalFrameCode.Good 3 5
    (WordList.encode (List.replicate 5 (BinaryNatCode.encode 0))):=by
  intro H
  have HC:=H.1
  change 5≤4 at HC
  omega

example (P : SpatialSource 3) {B : ℕ}
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap 4 P.degree≤2^B) :
    (IntegralMixedCausalUnitRecordBits.record P (by decide) 5
      (IntegralMixedChronologicalFrameCode.code 3 (IntegralMixedChronologicalFrameCode.labels d) 2 3) hc).template.command (-6) (by decide)=
      .critical (IntegralMixedChronologicalFrameCode.rawData 3 5
        (IntegralMixedChronologicalFrameCode.labels d) 2 3 good).rule:=
  IntegralMixedChronologicalFrameCode.raw_command (birth:=5) (B:=B) P (by decide)
    (IntegralMixedChronologicalFrameCode.labels d) 2 3 good hc (-6) (by decide)

example : (List.range 4).map (fun i=>Nat.fromBitsLE (WordList.get
    (IntegralMixedChronologicalPointSignatureCode.code 3 5 (IntegralMixedChronologicalFrameCode.labels d)) i))=
    [0,3,6,5]:=by decide

private def level (k : ℕ) : IntegralMixedRoadmapRecordChain.Level 2 k 0 0 where
  left:=.fresh ⟨[],by decide⟩
  right:=.fresh ⟨[],by decide⟩
  anchor:=⟨[],by decide⟩
  midpoint:=fun _=>⟨[],by decide⟩
  endpoint:=⟨[],by decide⟩
  companions:=fun _=>⟨[],by decide⟩

private def records : IntegralMixedRoadmapRecordChain.Records 2 0 0 where
  seed:=fun _=>⟨[],by decide⟩
  chain:=.descend 0 (by decide) (level 0)
    (.descend 1 (by decide) (level 1) (.descend 2 (by decide) (level 2) (.stop 3)))

-- These empty payloads test the syntax bound only, not native record validity.
example : records.codes.length=22:=by decide
example : records.word.length=44:=by decide
example : IntegralMixedRoadmapRecordChain.recordBound 2=22:=by decide
example : IntegralMixedRoadmapRecordChain.cap 2 5=30:=by decide
example : records.word.length=IntegralMixedRoadmapRecordChain.byteBound 2 0:=by decide


private def e : IntegralMixedChronologicalFrame.Descriptor 3 7 where
  labels:=[1,4]
  length_le:=by decide

example : (List.range 4).map (fun i=>
    let field:=WordList.get (IntegralMixedPhysicalPointSignatureComparison.signaturePairs d e) i
    (Nat.fromBitsLE (pairFst field),Nat.fromBitsLE (pairSnd field)))=[(0,1),(3,4),(6,8),(5,7)]:=by decide
example : WordList.get (IntegralMixedChronologicalCompanionCode.word 3
    (IntegralMixedChronologicalFrameCode.labels d) 2) 0=
      IntegralMixedChronologicalFrameCode.code 3 (IntegralMixedChronologicalFrameCode.labels d) 2 3:=by
  simp only [IntegralMixedChronologicalCompanionCode.word,IntegralMixedChronologicalCompanionCode.codes,
    IntegralMixedChronologicalFrameCode.labels_count]
  rw [WordList.get_encode]
  rfl
example : WordList.get (IntegralMixedChronologicalCompanionCode.word 3
    (IntegralMixedChronologicalFrameCode.labels d) 2) 1=
      IntegralMixedChronologicalFrameCode.code 3 (IntegralMixedChronologicalFrameCode.labels d) 2 2:=by
  simp only [IntegralMixedChronologicalCompanionCode.word,IntegralMixedChronologicalCompanionCode.codes,
    IntegralMixedChronologicalFrameCode.labels_count]
  rw [WordList.get_encode]
  rfl
example : WordListRecords.count (records.paddedWord ⟨[],by decide⟩ ⟨[],by decide⟩)=23:=by decide
example : (records.paddedWord ⟨[],by decide⟩ ⟨[],by decide⟩).length=46:=by decide
example : IntegralMixedCausalRecordPlanBits.count
    (records.root ⟨[],by decide⟩ ⟨[],by decide⟩ [true] [false])=23:=by decide

example {B : ℕ} (cs : List (IntegralMixedFramedHistoryScript.Instruction 2 B))
    (hc : cs.length≤28) : Fintype.card (IntegralMixedFramedHistoryScript.Index (Fin 0) cs)≤224:=
  IntegralMixedRoadmapRecordChain.actual_framed_physical_columns (initial:=5) cs hc

end ChronologicalRoadmapRegression
#print axioms IntegralMixedChronologicalFrame.Descriptor.freeze_slice
#print axioms IntegralMixedChronologicalFrameCode.pointGood_FP
#print axioms IntegralMixedChronologicalFrameCode.raw_command
#print axioms IntegralMixedRoadmapRecordChain.Chain.codes_length_le
#print axioms IntegralMixedRoadmapRecordChain.wordBound_unary
#print axioms IntegralMixedRoadmapRecordChain.actual_physical_columns
#print axioms IntegralMixedChronologicalFrame.Descriptor.point_values
#print axioms IntegralMixedChronologicalFrame.Descriptor.point_eq_iff
#print axioms IntegralMixedChronologicalFrame.Descriptor.realized_point_value
#print axioms IntegralMixedChronologicalPointSignatureCode.code_FP
#print axioms IntegralMixedChronologicalPointSignatureCode.code_lookup_actual
#print axioms IntegralMixedChronologicalCompanionCode.word_FP
#print axioms IntegralMixedChronologicalCompanionCode.codes_actual
#print axioms IntegralMixedRoadmapRecordChain.Records.paddedWord_count
#print axioms IntegralMixedRoadmapRecordChain.Records.actual_marked_cap
#print axioms IntegralMixedPhysicalPointSignatureComparison.pairs_FP
#print axioms IntegralMixedPhysicalPointSignatureComparison.language_points_iff
#print axioms IntegralMixedRoadmapRecordChain.Records.actual_marked_fullCount
#print axioms IntegralMixedRoadmapRecordChain.actual_framed_physical_columns
end
end RoadmapChronological

namespace RoadmapCaptures
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PointCompanionRegression
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
private def rows0 : Fin 2→Row 4:=fun _=>.single none
private def objective : Free (∅ : Finset (Fin 2)):=⟨0,Finset.notMem_empty _⟩
private def chosen : List (Free (∅ : Finset (Fin 2))):=[⟨1,Finset.notMem_empty _⟩,⟨0,Finset.notMem_empty _⟩]
private def point : Fin 2→ℝ:=![1,0]
private theorem capture (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃ z : Index (Fin 0) (leaves B)→ℝ,∃φ : (before B hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
 Nonempty (Realized (before B hc) ∅ (fun _=>false) rows0 objective z φ vals point chosen (by decide)) ∧
 Decoded (before B hc) ∅ (fun _=>false) rows0 objective (by decide) hc chosen (by decide) :=by
 obtain ⟨z,φ,hz,hφ,H⟩:=before_realized B hc
 have HM : point∈slice P (originalFrame ∅ (fun _=>false) rows0) vals:=by
  refine ⟨?_,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  rw [evalP]
  norm_num [point]
 have HG : ∀i : Fin 2,i∉(∅ : Finset (Fin 2))→i≠objective.val→
   (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
     (Int.castRingHom ℝ) point=0:=by
  intro i _ hi
  have HE : i=1:=by fin_cases i <;> simp_all [objective]
  subst i
  rw [gradP]
  norm_num [point]
 refine ⟨z,φ,?_⟩
 exact exists_realized (before B hc) ∅ (fun _=>false) rows0 objective (by decide) 0 rfl hc
   (PrefixFrozen.of_empty _ rfl) z hz φ hφ vals H point HM HG chosen (by decide)

example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃z,∃φ,∃R : Realized (before B hc) ∅ (fun _=>false) rows0 objective z φ vals point chosen (by decide),
 R.hom ((IntegralMixedPointCompanion.run (before B hc) ∅ (fun _=>false) rows0 objective chosen (by decide)).bank.numerator 0)/
   ((IntegralMixedPointCompanion.run (before B hc) ∅ (fun _=>false) rows0 objective chosen (by decide)).bank.denominator 0:ℝ)=0 ∧
 R.hom ((IntegralMixedPointCompanion.run (before B hc) ∅ (fun _=>false) rows0 objective chosen (by decide)).bank.numerator 1)/
   ((IntegralMixedPointCompanion.run (before B hc) ∅ (fun _=>false) rows0 objective chosen (by decide)).bank.denominator 1:ℝ)=1 ∧
 (∀i,R.tuple (blockColumn ∅ (fun _=>false) rows0 objective chosen ⟨0,by decide⟩ i)^UniformIntegralPowerSchedule.physical 6 (2^B) 5=point i) ∧
 (∀i,R.tuple (blockColumn ∅ (fun _=>false) rows0 objective chosen ⟨1,by decide⟩ i)^UniformIntegralPowerSchedule.physical 6 (2^B) 4=point i) :=by
 obtain ⟨z,φ,⟨R⟩,_⟩:=capture B hc
 refine ⟨z,φ,R,?_,?_,?_,?_⟩
 · exact R.quotients 0
 · exact R.quotients 1
 · exact R.blocks ⟨0,by decide⟩
 · exact R.blocks ⟨1,by decide⟩

private def midpointRows : Fin 2→Row 4:=fun i=>if i=0 then .sum (some 0) (some 1) else .single none
private def midpointDouble : Fin 2→Bool:=fun i=>if i=0 then true else false
private def midpointObjective : Free ({0} : Finset (Fin 2)):=⟨1,by decide⟩
private def midpointChosen : List (Free ({0} : Finset (Fin 2))):=[midpointObjective]
private def midpoint : Fin 2→ℝ:=![0,1]
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) :
 ∃z,∃φ,Nonempty (Realized (before B hc) {0} midpointDouble midpointRows midpointObjective z φ vals midpoint midpointChosen (by decide)) ∧
 Decoded (before B hc) {0} midpointDouble midpointRows midpointObjective (by decide) hc midpointChosen (by decide) :=by
 obtain ⟨z,φ,hz,hφ,H⟩:=before_realized B hc
 have HM : midpoint∈slice P (originalFrame {0} midpointDouble midpointRows) vals:=by
  constructor
  · rw [evalP]
    norm_num [midpoint]
  · intro i hi
    have HE : i=0:=by simpa only [originalFrame,Finset.mem_singleton] using hi
    subst i
    norm_num [originalFrame,midpointDouble,midpointRows,Row.value,Atom.value,AffineExpr.evaluate,vals,midpoint]
 have HG : ∀i : Fin 2,i∉({0} : Finset (Fin 2))→i≠midpointObjective.val→
   (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
     (Int.castRingHom ℝ) midpoint=0:=by
  intro i hi he
  fin_cases i <;> simp_all [midpointObjective]
 have HP' : PrefixFrozen (originalFrame ({0} : Finset (Fin 2)) midpointDouble midpointRows):=by
  intro i
  fin_cases i <;> decide
 refine ⟨z,φ,?_⟩
 exact exists_realized (before B hc) {0} midpointDouble midpointRows midpointObjective (by decide) 0 rfl hc HP'
   z hz φ hφ vals H midpoint HM HG midpointChosen (by decide)

example : shiftRows midpointRows 2 (0 : Fin 2)=.sum (some 2) (some 3) :=rfl
example : (originalFrame ({0} : Finset (Fin 2)) midpointDouble midpointRows).scales 0=2:=rfl
example : (commands (P:=P) (B:=1) ∅ (fun _=>false) rows0 objective chosen).length=2:=rfl
example : UniformIntegralPowerSchedule.physical 6 4 4≠UniformIntegralPowerSchedule.physical 6 4 5 :=by
 norm_num [UniformIntegralPowerSchedule.physical,UniformIntegralPowerSchedule.cap,UniformIntegralPowerSchedule.birth,
   MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
example : (![0,1] : Fin 2→ℝ) 0=(![0,-1] : Fin 2→ℝ) 0 ∧ (![0,1] : Fin 2→ℝ)≠![0,-1] :=by
 constructor
 · rfl
 · intro HE
   have HH:=congrArg (fun p : Fin 2→ℝ=>p 1) HE
   norm_num at HH
example : UnaryFn (fun q=>byteBound q.length (Nat.fromBitsLE q) q.length q.length):=
 byteBound_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (UnaryFn.length id_mem_FP) (UnaryFn.length id_mem_FP)
example : (WordList.encode (codes ∅ (fun _=>false) rows0 objective chosen).reverse).length≤byteBound 1 4 1 2 :=
 bytes (B:=1) ∅ (fun _=>false) rows0 objective chosen
example : ((-24:ℤ)%6)=0:=by decide
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [IntegralMixedFullHistoryScript.run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),
   poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]
example (B : ℕ) (e : Index (Fin 0) (leaves B)≃Fin 4) (i : Fin 2) :
 (columns (P:=P) (B:=B) ∅ (fun _=>false) rows0 objective e chosen
   (blockColumn ∅ (fun _=>false) rows0 objective chosen ⟨0,by decide⟩ i)).val=10+i.val :=by
 simpa only [chosen,List.length_cons,List.length_nil,Fin.val_mk] using
   columns_block (P:=P) (B:=B) ∅ (fun _=>false) rows0 objective e chosen ⟨0,by decide⟩ i
example (B : ℕ) (e : Index (Fin 0) (leaves B)≃Fin 4) (i : Fin 2) :
 (columns (P:=P) (B:=B) ∅ (fun _=>false) rows0 objective e chosen
   (blockColumn ∅ (fun _=>false) rows0 objective chosen ⟨1,by decide⟩ i)).val=4+i.val :=by
 simpa only [chosen,List.length_cons,List.length_nil,Fin.val_mk] using
   columns_block (P:=P) (B:=B) ∅ (fun _=>false) rows0 objective e chosen ⟨1,by decide⟩ i
example : UnaryFn (fun q=>byteBound q.length (Nat.fromBitsLE q) q.length (q.length+1)):=
 allFreeByteBound_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (UnaryFn.length id_mem_FP)
example : (WordList.encode (codes ∅ (fun _=>false) rows0 objective (allFree ∅)).reverse).length≤byteBound 1 4 1 2:=
 bytes_all_free (B:=1) ∅ (fun _=>false) rows0 objective
#print axioms allFreeByteBound_unary
#print axioms bytes_all_free
#print axioms exists_realized
#print axioms exists_all_free
#print axioms run_continue
#print axioms columns_old
#print axioms columns_block
#print axioms physical_columns
#print axioms Realized.capture
#print axioms Realized.old_value
#print axioms point_eq_of_free
#print axioms count_all_free
#print axioms columns_all_free
#print axioms bytes
#print axioms byteBound_unary
end PointCompanionRegression
end
end RoadmapCaptures

namespace RoadmapPadding
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PaddingRegression
private def D:=BoundedZeroSource.powerDegree 0
private theorem Dval : D=18:=rfl
private def P : SpatialSource 1 where
 low:=MvPolynomial.C (-(4^18+1):ℤ)
 leading:=4^18
 degree:=D
 degree_two:=by rw [Dval]; decide
 low_degree:=by
  simpa only [MvPolynomial.totalDegree_C] using
    (show 0<D from by rw [Dval]; decide)
 leading_ne_zero:=by norm_num
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
private def frozen : Finset (Fin 2):={0}
private def doubles : Fin 2→Bool:=fun i=>if i=0 then true else false
private def rows : Fin 2→Row 4:=fun i=>if i=0 then .sum (some 0) (some 3) else .single none
private def g : Free frozen:=⟨1,by decide⟩
private def point : Fin 2→ℝ:=![1/4,1]
private theorem HP : PrefixFrozen (originalFrame frozen doubles rows):=by intro i;fin_cases i <;> decide
private theorem point_slice : point∈slice P (originalFrame frozen doubles rows) vals:=by
 constructor
 · norm_num [P,FermatCriticalHomogenization.polynomial,Dval,point,Fin.sum_univ_succ]
 · intro i hi
   have HE : i=0:=by simpa only [originalFrame,frozen,Finset.mem_singleton] using hi
   subst i
   norm_num [originalFrame,doubles,rows,Row.value,Atom.value,AffineExpr.evaluate,vals,point]
private theorem gradient : ∀i : Fin 2,i∉frozen→i≠g.val→
 (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
   (Int.castRingHom ℝ) point=0:=by
 intro i hi he
 fin_cases i <;> simp_all [g,frozen]

private def Scenario (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B)
 (k : ℕ) (hk : k≤2) : Prop:=
 ∃z,∃φ,∃R : Realized (before B hc) frozen doubles rows g z φ vals point (List.replicate 1 g) (by decide),
 let seed:=IntegralMixedPointCompanion.run (before B hc) frozen doubles rows g (List.replicate 1 g) (by decide)
 let sr:=shiftRows rows 1
 ∃U : Realized seed frozen doubles sr g R.tuple R.hom (values point vals (List.replicate 1 g)) point
   (List.replicate k g) (by simp only [List.length_replicate];omega),
 Decoded seed frozen doubles sr g (by decide) hc (List.replicate k g) (by simp only [List.length_replicate];omega) ∧
 ∀i,U.tuple (IntegralMixedOptionalEndpoints.oldColumns (commands frozen doubles sr g (List.replicate k g))
   (blockColumn frozen doubles rows g (List.replicate 1 g) ⟨0,by decide⟩ i))^
     UniformIntegralPowerSchedule.physical 6 (2^B) 4=point i

private theorem scenario (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B)
 (k : ℕ) (hk : k≤2) : Scenario B hc k hk :=by
 obtain ⟨z,φ,hz,hφ,H⟩:=before_realized B hc
 obtain ⟨⟨R⟩,_⟩:=exists_repeat (before B hc) frozen doubles rows g (by decide) 0 rfl hc HP
   z hz φ hφ vals H point point_slice gradient 1 (by decide)
 refine ⟨z,φ,R,?_⟩
 exact repeat_from_realized (before B hc) frozen doubles rows g (by decide) 0 rfl hc HP
   z φ vals point point_slice gradient (List.replicate 1 g) (by decide) R ⟨0,by decide⟩ k
     (by simp only [List.length_replicate];omega)

example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc 0 (by decide):=scenario B hc 0 (by decide)
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc 1 (by decide):=scenario B hc 1 (by decide)
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc 2 (by decide):=scenario B hc 2 (by decide)
example (k : ℕ) : codes frozen doubles rows g (List.replicate k g)=List.replicate k (pointData frozen doubles rows g 0 g).code :=codes_replicate frozen doubles rows g k
example : shiftRows rows 3 (0 : Fin 2)=.sum (some 3) (some 6):=rfl
example : (pointData frozen doubles rows g 0 g).code=(pointData frozen doubles rows g 7 g).code :=(pointData_code_stable frozen doubles rows g g 7).symm
example : (pointData frozen doubles rows g 0 g).rule.heights 0≠(pointData frozen doubles rows g 1 g).rule.heights 0:=by
 have HEperm : FrozenCoordinateOrdering.permutation frozen=Equiv.refl (Fin 2):=HP.permutation
 simp only [pointData,originalPointData,IntegralMixedCriticalRecordConstructor.Data.rule,HEperm,Equiv.refl_apply]
 change (.add (.reference 0) (.reference 3) : AffineExpr)≠.add (.reference 1) (.reference 4)
 intro HE
 cases HE
example : IntegralMixedCausalUnitRecordBits.physical 1 5 (pointData frozen doubles rows g 0 g).code=
 (pointData frozen doubles rows g 1 g).rule :=by
 rw [←pointData_code_stable frozen doubles rows g g 1]
 exact IntegralMixedCriticalRecordConstructor.rule_decode _
example : (WordList.encode (codes frozen doubles rows g (List.replicate 20 g)).reverse).length≤paddingByteBound 1 4 1 20:=padding_bytes (B:=1) frozen doubles rows g 20
example : UnaryFn (fun q=>paddingByteBound q.length (Nat.fromBitsLE q) q.length q.length):=
 paddingByteBound_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (UnaryFn.length id_mem_FP) (UnaryFn.length id_mem_FP)
example : UnaryFn (fun q=>q.length+(2*q.length+4)*q.length):=
 paddingColumnBound_unary (UnaryFn.length id_mem_FP) (UnaryFn.length id_mem_FP) (UnaryFn.length id_mem_FP)
example : UniformIntegralPowerSchedule.physical 6 4 5≠UniformIntegralPowerSchedule.physical 6 4 6 :=by
 norm_num [UniformIntegralPowerSchedule.physical,UniformIntegralPowerSchedule.cap,UniformIntegralPowerSchedule.birth,
   MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [IntegralMixedFullHistoryScript.run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),
   poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]

#print axioms laterAtom_word
#print axioms shiftRows_base
#print axioms shiftRows_midpoint
#print axioms pointData_code_stable
#print axioms codes_replicate
#print axioms command_replicate_get
#print axioms exists_repeat
#print axioms repeat_from_realized
#print axioms repeat_commonDenominator
#print axioms padding_bytes
#print axioms paddingByteBound_unary
#print axioms padding_columns
#print axioms Realized.padding_value
end PaddingRegression
end
end RoadmapPadding

namespace RoadmapPhysicalGuards
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open scoped Classical
namespace PhysicalPointCompanionRegression
private def n (_ : List Bool) :=0
private def t (_ : List Bool) : Term:=.const 0
private def R (_ : List Bool) :=0
private theorem hn : UnaryFn n:=UnaryFn.const 0
private theorem ht : (fun q=>(t q).toData.toBits)∈FP:=by
  simpa only [t] using (constFn_mem_FP (Term.const (0:ℤ)).toData.toBits)
private theorem ha : ∀q,(t q).arity≤n q:=by intro q;change 0≤0;omega
private theorem hR : BinaryFn R:=BinaryFn.const 0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
example : SpaceDecider (IntegralMixedPhysicalPointCompanionScan.language hn ht ha hR false):=
  IntegralMixedPhysicalPointCompanionScan.decider hn ht ha hR false
example : SpaceDecider (IntegralMixedPhysicalPointCompanionScan.language hn ht ha hR true):=
  IntegralMixedPhysicalPointCompanionScan.decider hn ht ha hR true
example (c w : List Bool) : IntegralMixedPhysicalPointEquality.Wellformed
    (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum 3 5 1)) :=
  IntegralMixedPhysicalPointEquality.wellformed_packet c w 3 5 1
example : IntegralMixedPhysicalPointEquality.coordinate
    (pair [true,false] (IntegralMixedPhysicalPointEquality.datum 3 5 1))=1 :=
  (IntegralMixedPhysicalPointEquality.datum_fields [true,false] 3 5 1).2.2
example (c w : List Bool) : IntegralMixedPhysicalPointCompanionScan.Wellformed
    (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor 2 4 3)) :=
  IntegralMixedPhysicalPointCompanionScan.descriptor_packet c w 2 4 3
example : [true]∉IntegralMixedPhysicalPointCompanionScan.language hn ht ha hR false :=by
  apply IntegralMixedPhysicalPointCompanionScan.reject_malformed hn ht ha hR false
  change [true]≠IntegralMixedPhysicalPointCompanionScan.canonical [true]
  decide
example (c w : List Bool) (a b i : ℕ)
    (hi : (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.ambient
      (pairFst ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key c))+1 ≤ i) :
    ¬IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR false
      (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i)) :=
  IntegralMixedPhysicalPointCompanionScan.reject_outside_coordinate hn ht ha hR false c w a b i hi
example (c w : List Bool) (a f k : ℕ)
    (hb : ¬IntegralMixedPhysicalPointCompanionScan.Active hn ht ha hR true c a) :
    pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∉
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha hR true :=
  IntegralMixedPhysicalPointCompanionScan.reject_noncritical_anchor hn ht ha hR true c w a f k hb
example : (FixedWidthMonomialBits.polynomial (fun _=>0) (fun _=>0) (fun _=>7) (fun _=>1) [])=0 :=by
  simp only [FixedWidthMonomialBits.polynomial,lt_self_iff_false,dite_false]
example : UniformIntegralPowerSchedule.physical 2 2 1=5 ∧
    UniformIntegralPowerSchedule.physical 2 2 2=45 :=by
  norm_num [UniformIntegralPowerSchedule.physical,UniformIntegralPowerSchedule.birth,
    UniformIntegralPowerSchedule.cap,MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
example : (-512:ℝ)^UniformIntegralPowerSchedule.physical 2 2 1=
    (-2:ℝ)^UniformIntegralPowerSchedule.physical 2 2 2 :=by
  norm_num [UniformIntegralPowerSchedule.physical,UniformIntegralPowerSchedule.birth,
    UniformIntegralPowerSchedule.cap,MonicParameterPowerSchedule.weight,MonicParameterPowerSchedule.ratio]
example : (-512:ℝ)≠-2 ∧ (-512:ℝ)^5≠(-2)^5 :=by norm_num
noncomputable def p : MvPolynomial (Fin 2) ℤ:=MvPolynomial.X 0^5-MvPolynomial.X 1^45
example : p.eval₂ (Int.castRingHom ℝ) (fun _=>0)=0 :=by norm_num [p]
example : (MvPolynomial.pderiv (0:Fin 2) p).eval₂ (Int.castRingHom ℝ) (fun _=>0)=0 :=by
  norm_num [p,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X]
example : (MvPolynomial.pderiv (1:Fin 2) p).eval₂ (Int.castRingHom ℝ) (fun _=>0)=0 :=by
  norm_num [p,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X]
example : ((-2:ℝ)^3-(-4)*2=0) ∧ ((-2:ℝ)^3/(-4)=2) :=by norm_num
#print axioms IntegralMixedFramedPointEqualityBits.column_lt
#print axioms IntegralMixedFramedPointEqualityBits.admissible_FP
#print axioms IntegralMixedFramedPointEqualityBits.coefficient_evaluator
#print axioms IntegralMixedFramedPointEqualityBits.polynomial_eval
#print axioms IntegralFramedPhysicalPointEqualityTest.access
#print axioms IntegralFramedPhysicalPointEqualityTest.evaluator
#print axioms IntegralFramedPhysicalPointEqualityTest.zero_iff
#print axioms IntegralMixedPhysicalPointEquality.evaluator
#print axioms IntegralMixedPhysicalPointEquality.accepted_evaluator
#print axioms IntegralMixedPhysicalPointEquality.zero_iff_block
#print axioms IntegralMixedPhysicalPointCompanionScan.grammar_FP
#print axioms IntegralMixedPhysicalPointCompanionScan.holds_evaluator
#print axioms IntegralMixedPhysicalPointCompanionScan.decider
#print axioms IntegralMixedPhysicalPointCompanionScan.mem_PSPACE
#print axioms IntegralMixedPhysicalPointCompanionScan.selected_lt
#print axioms IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_iff
#print axioms IntegralMixedPhysicalPointCompanionScan.holds_iff_points
#print axioms IntegralMixedPhysicalPointCompanionScan.language_packet_iff
#print axioms IntegralMixedPhysicalPointCompanionScan.reject_malformed
#print axioms IntegralMixedPhysicalPointCompanionScan.reject_outside_coordinate
#print axioms IntegralMixedPhysicalPointCompanionScan.reject_noncritical_anchor
end PhysicalPointCompanionRegression
end RoadmapPhysicalGuards

namespace RoadmapMatchedSlab
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame Set
open scoped Classical
noncomputable section
namespace MatchedSlabRegression
variable {n S B m : ℕ} {P : SpatialSource n} {ι L R : Type}
    {x : State P S B m ι} {hm : m≤S}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {F : Frame n}
    {h : Fin (n+1)} {hh : h∈F.frozen} {g : Fin (n+1)} {hg : g∉F.frozen}
    {values : Fin m→ℝ} {a b : ℝ} {t₀ : Ioo a b}
    (M : MatchedSlabInterior x hm φ F h hh g hg values a b t₀)
local notation "I"=>IntegralMixedSelectedPhysicalFiber.physical
  (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
  (sweep x F h hh g hg) φ t₀.val

-- Both CLOSED endpoints use the same physical family and permutation.
example (i : I) : (M.interior.arc i a).val=
    M.curve i a∘(FrozenCoordinateOrdering.permutation F.frozen).symm :=
  M.readback i a ⟨le_rfl,(t₀.property.1.trans t₀.property.2).le⟩
example (i : I) : (M.interior.arc i b).val=
    M.curve i b∘(FrozenCoordinateOrdering.permutation F.frozen).symm :=
  M.readback i b ⟨(t₀.property.1.trans t₀.property.2).le,le_rfl⟩
example (i : I) : (M.interior.arc i t₀.val).val=
    i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm :=by
  rw [M.readback i t₀.val (Ioo_subset_Icc_self t₀.property),M.anchor i]

-- The code names the literal midpoint point, rather than another family's point.
example (i : I) : M.code i=IntegralMixedFrozenFrameSectionCode.word
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t₀.val i :=by
  have HE : (⟨M.curve i t₀.val,M.physical i t₀.val (Ioo_subset_Icc_self t₀.property)⟩ : I)=i:=
    Subtype.ext (M.anchor i)
  have HW:=M.code_word i t₀
  rw [HE] at HW
  exact HW.symm
example (i j : I) (Hcode : M.code i=M.code j) : i=j:=M.code_injective Hcode

-- Empty midpoint physical fibers force an empty open slab, not a phantom branch.
example (hempty : ∀_i : I,False) : IsEmpty ((coarseProjection P F values h) ⁻¹' Ioo a b) :=by
  refine ⟨fun z=>?_⟩
  obtain ⟨i,_⟩:=M.interior.cover z
  exact hempty i

-- Distinct anchors joined in the midpoint fiber connect at BOTH recursive fibers.
example (left : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {a}) L)
    (right : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {b}) R)
    (i j : I)
    (Hmid : JoinedIn (shiftedSlice P F values h t₀.val)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (j.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)) :
    JoinedIn (shiftedSlice P F values h a)
      (M.curve i a∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (M.curve j a∘(FrozenCoordinateOrdering.permutation F.frozen).symm) ∧
    JoinedIn (shiftedSlice P F values h b)
      (M.curve i b∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (M.curve j b∘(FrozenCoordinateOrdering.permutation F.frozen).symm) :=
  ⟨M.left_endpoints_joined left i j Hmid,M.right_endpoints_joined right i j Hmid⟩

-- Endpoint fibers may be singular/repeated; the constructor has no regularity premise there.
example : Polynomial.IsRoot ((Polynomial.X:Polynomial ℝ)^2) 0 ∧
    (Polynomial.derivative ((Polynomial.X:Polynomial ℝ)^2)).eval 0=0 :=by
  simp [Polynomial.IsRoot]

#check exists_matched_slab_interior
#check joint_midpoint_block_same_family
#check matched_branch_endpoint_real_extend
#print axioms exists_matched_slab_interior
#print axioms MatchedSlabInterior.left_endpoints_joined
#print axioms MatchedSlabInterior.right_endpoints_joined
#print axioms joint_midpoint_block_same_family
#print axioms matched_branch_endpoint_real_extend
end MatchedSlabRegression
end
end RoadmapMatchedSlab

namespace RoadmapMidpointCompiler
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ChronologicalMidpointRegression
private def D:=BoundedZeroSource.powerDegree 0
private theorem Dval : D=18:=rfl
private def P : SpatialSource 2 where
 low:=-1
 leading:=1
 degree:=D
 degree_two:=by rw [Dval]; decide
 low_degree:=by
  simpa only [MvPolynomial.totalDegree_neg,MvPolynomial.totalDegree_one] using
    (show 0<D from by rw [Dval]; decide)
 leading_ne_zero:=by decide
private theorem cap : PurePowerReductionBounds.dimension 3 P.degree≤IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree:=by
 unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
 omega
private def initial (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) : State P 6 B 0 (Fin 0):=
 IntegralMixedHistory.base P (IntegralHistorySampler.base 6 (2^B)) (cap.trans hc)
open IntegralMixedFullHistoryScript Polynomial
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
private def before (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 State P 6 B 4 (Index (Fin 0) (leaves B)) :=
 run (initial B hc) (leaves B) (by change (4:ℕ)≤7; decide)
private theorem before_realized (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
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


open IntegralMixedChronologicalMidpoint IntegralMixedChronologicalMidpointCode IntegralMixedCausalRowConstructor
private def d : IntegralMixedChronologicalFrame.Descriptor 2 4 where
 labels:=[0]
 length_le:=by decide
private theorem fit : d.labels.length<3:=by decide
private def a : Fin 4:=3
private def b : Fin 4:=2
private def g : Fin 3:=2
private theorem hg : g∉(frame d fit a b).frozen:=by rw [free_iff];decide
private def W:=IntegralMixedChronologicalFrameCode.labels d
private def codeWord:=code 2 W a.val b.val g.val g.val
example : Good 2 4 W a.val b.val g.val g.val:=good_descriptor d fit a b g g hg hg
example : PrefixFrozen (frame d fit a b):=prefix_frozen d fit a b
example : FreeNormal (frame d fit a b):=free_normal d fit a b
example : ¬AtomicRows (frame d fit a b) 4:=by
 intro HA
 have HH:=HA.scale (next d fit)
 rw [frame_eq,referencedMidpointFrame_scale] at HH
 norm_num at HH
example : IntegralMixedUnitRecordCode.field codeWord 12=[false,true,false]:=by
 rw [show codeWord=(data d fit a b g g hg hg).code from (data_code d fit a b g g hg hg).symm,
   IntegralMixedCriticalRecordConstructor.field_12]
 unfold IntegralMixedChronologicalMidpointCode.data originalPointData
 simp only [(prefix_frozen d fit a b).permutation,Equiv.refl_apply]
 rfl
example : WordList.get (IntegralMixedUnitRecordCode.field codeWord 14) 1=
 sumWord (producerWord 3) (producerWord 2):=by
 rw [show codeWord=(data d fit a b g g hg hg).code from (data_code d fit a b g g hg hg).symm,
   IntegralMixedCriticalRecordConstructor.field_14,data_midRows]
 unfold midRows midRow
 have HK : WordListRecords.count W=1:=IntegralMixedChronologicalFrameCode.labels_count d
 change WordList.get (WordList.encode ((List.range 3).map (fun i=>if i=WordListRecords.count W then
   sumWord (producerWord a.val) (producerWord b.val) else []))) 1=_
 rw [HK,WordList.get_encode]
 rfl
example : IntegralMixedCausalUnitRecordBits.physical 2 4 codeWord=pointRule (frame d fit a b) g hg g hg:=
 decode d fit a b g g hg hg
example : (code 2 W a.val b.val g.val g.val).length≤IntegralMixedCriticalRecordConstructor.codeBudget 2 4:=
 code_size d fit a b g g hg hg
example : code 2 (IntegralMixedChronologicalFrameCode.labels d.retain) a.castSucc.val b.castSucc.val g.val g.val=codeWord:=
 code_retain d a b g.val g.val
private theorem point_slice : (![1,0,0] : Fin 3→ℝ)∈slice P (frame d fit a b) vals:=by
 rw [slice_eq]
 constructor
 · apply (d.slice_iff P vals _).mpr
   constructor
   · norm_num [P,Dval,FermatCriticalHomogenization.polynomial,Fin.sum_univ_succ]
   · intro i
     have HI : i.val=0:=by have :=i.isLt;change i.val<1 at this;omega
     have HE : i=(⟨0,by decide⟩ : Fin d.labels.length):=Fin.ext HI
     subst i
     rfl
 · norm_num [next,d,reference,a,b,vals]
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 ∃φ : (before B hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  (![1,0,0] : Fin 3→ℝ)∈actualSlice (before B hc) φ (frame d fit a b) :=by
 obtain ⟨_,φ,_,_,H⟩:=before_realized B hc
 refine ⟨φ,?_⟩
 rw [IntegralMixedFrozenFrame.actualSlice_eq (before B hc) φ _ vals H]
 exact point_slice
example : ¬Good 2 4 W 4 2 2 2:=by intro H;exact Nat.lt_irrefl 4 H.2.1
example : ¬Good 2 4 W 3 2 1 2:=by
 intro H
 have HH:=H.2.2.2.1
 change WordListRecords.count (IntegralMixedChronologicalFrameCode.labels d)+1≤1 at HH
 rw [IntegralMixedChronologicalFrameCode.labels_count] at HH
 change (2:ℕ)≤1 at HH
 omega
example : ¬Good 2 4 W 3 2 2 3:=by intro H;exact Nat.lt_irrefl 3 H.2.2.2.2.2.2
example : (rawData 2 4 W 3 2 2 2 (good_descriptor d fit a b g g hg hg)).code=codeWord:=
 rawData_code 2 4 W 3 2 2 2 (good_descriptor d fit a b g g hg hg)
example : (fun q=>code q.length q (Nat.fromBitsLE q) (Nat.fromBitsLE q) (Nat.fromBitsLE q) (Nat.fromBitsLE q))∈FP:=
 code_FP (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP)
   (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP) id_mem_FP
example : FPPred (fun q=>Good q.length (Nat.fromBitsLE q) q (Nat.fromBitsLE q)
 (Nat.fromBitsLE q) (Nat.fromBitsLE q) (Nat.fromBitsLE q)):=
 good_FP (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP)
   (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP) id_mem_FP
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 (IntegralMixedCausalUnitRecordBits.record P (by decide) 4 codeWord hc).template.command
   (commonDenominator (before B hc)) (commonDenominator_ne_zero _)=
 (.critical (pointRule (frame d fit a b) g hg g hg) : Command P B) :=
 command_currentQ (before B hc) (by decide) hc d fit a b g g hg hg
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [IntegralMixedFullHistoryScript.run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),
   poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]

example : ((-24:ℤ)%6)=0:=by decide
#print axioms frame_eq
#print axioms prefix_frozen
#print axioms free_normal
#print axioms slice_eq
#print axioms code_FP
#print axioms good_FP
#print axioms data_code
#print axioms decode
#print axioms command_currentQ
#print axioms actual_slice_eq
#print axioms step_currentQ
#print axioms retained_labels
#print axioms code_retain
#print axioms code_descriptor
#print axioms rawData_code
#print axioms rawData_rule
#print axioms raw_command
#print axioms raw_code_size
end ChronologicalMidpointRegression
end
end RoadmapMidpointCompiler

namespace RoadmapNaturality
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding
open scoped Classical
noncomputable section
namespace SquareNaturalityRegression

private theorem candidate_source_heq (F : SquareSampleInput.Inputs) (a b : List Bool)
    (h : a=b) (w : List Bool) (ha : SquareSampleCompleteVertices.Valid F a w)
    (hb : SquareSampleCompleteVertices.Valid F b w) :
    HEq (SquareSampleCompleteVertices.candidate F a w ha).val
      (SquareSampleCompleteVertices.candidate F b w hb).val :=by
  cases h
  rfl

-- Allocate the word before putting that SAME word into its own opaque context.
private theorem self_context (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F)
    (c : List Bool) (z : SquareSampleComplete.Roots F c) :
    let w:=SquareSampleCompleteVertices.word F hF c z
    let q:=pair c (pair w [])
    ∃hq : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp F pairFst) q w,
      HEq (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp F pairFst) q w hq).val z.val :=by
  let w:=SquareSampleCompleteVertices.word F hF c z
  let q:=pair c (pair w [])
  have h0:=SquareSampleCompleteVertices.word_valid F hF c z
  have h1 : SquareSampleCompleteVertices.Valid F (pairFst q) w:=by
    simpa only [q,pairFst_pair] using h0
  have hq:=(SquareSampleCompleteNaturality.complete_valid_comp F pairFst q w).mpr h1
  refine ⟨hq,?_⟩
  apply (heq_of_eq (SquareSampleCompleteNaturality.candidate_comp F pairFst q w hq h1)).trans
  have HE:=heq_of_eq (congrArg Subtype.val (SquareSampleCompleteVertices.candidate_word F hF c z))
  exact (candidate_source_heq F (pairFst q) c (by simp only [q,pairFst_pair]) w h1 h0).trans HE

example (F : SquareSampleInput.Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleCompleteVertices.width (SquareSampleInput.comp F f) u=
      SquareSampleCompleteVertices.width F (f u):=
  SquareSampleCompleteNaturality.complete_width_comp F f u

example (F : SquareSampleInput.Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleCoordinates.parameter (SquareSampleInput.comp F f) u=
      SquareSampleCoordinates.parameter F (f u):=
  SquareSampleParameterNaturality.parameter_comp F f u

example (F : SquareSampleInput.Inputs) (f : List Bool→List Bool) (u w : List Bool)
    (h : ¬SquareSampleCompleteVertices.Valid F (f u) w) :
    ¬SquareSampleCompleteVertices.Valid (SquareSampleInput.comp F f) u w:=
  fun hu=>h ((SquareSampleCompleteNaturality.complete_valid_comp F f u w).mp hu)

-- Noninjective projection is allowed; this is not an ordinal permutation.
example (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F)
    (c : List Bool) (z : SquareSampleComplete.Roots F c) :
    let w:=SquareSampleCompleteVertices.word F hF c z
    let q:=pair c (pair w [])
    ∃hq : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp F pairFst) q w,
      HEq (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp F pairFst) q w hq).val z.val :=
  self_context F hF c z

private def repeated : NoInfinitySquareSample.Family where
  count _:=1
  degree _:=2
  mass _:=0
  rowDegree _ _:=2
  rows _ _:=(MvPolynomial.X (0 : Fin 1))^2
  count_pos _:=by decide
  degree_pos _:=by decide
  row_degree _ _:=(MvPolynomial.totalDegree_X_pow _ _).le
  rowDegree_pos _ _:=by decide
  rowDegree_le _ _:=le_rfl
  row_mass _ _:=by
    simpa only [MvMass.X,one_pow,pow_zero] using MvMass.pow_le (MvPolynomial.X (0 : Fin 1)) 2
  noInfinity _:=by
    intro y hy hz
    have H:=hz 0
    change (WeightedHomogenization.homogenize (fun _=>1) 2
      ((MvPolynomial.X (0 : Fin 1))^2)).eval₂ (Int.castRingHom ℂ) y=0 at H
    rw [WeightedHomogenization.homogenize_X_pow] at H
    simp only [MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X] at H
    have Hz : y (some 0)=0:=(pow_eq_zero_iff (by decide : 2≠0)).mp H
    funext j
    cases j with
    | none=>exact hy
    | some i=>simpa only [Subsingleton.elim i 0,Pi.zero_apply] using Hz

private def zeroRoot (c : List Bool) : SquareSampleComplete.Roots (NoInfinitySquareSample.input repeated) c:=
  ⟨fun _=>0,by intro i;simp only [NoInfinitySquareSample.input,repeated,MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X,zero_pow (by decide : 2≠0)]⟩

-- A singular original root is preserved even with its label inside its context.
example (c : List Bool) :
    let F:=NoInfinitySquareSample.input repeated
    let w:=SquareSampleCompleteVertices.word F (NoInfinitySquareSample.complete repeated) c (zeroRoot c)
    let q:=pair c (pair w [])
    ∃hq : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp F pairFst) q w,
      HEq (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp F pairFst) q w hq).val
        (zeroRoot c).val :=
  self_context _ (NoInfinitySquareSample.complete repeated) c (zeroRoot c)

example : (MvPolynomial.pderiv (0 : Fin 1) ((MvPolynomial.X (0 : Fin 1))^2 : MvPolynomial (Fin 1) ℤ)).eval
    (fun _=>0)=0 :=by simp

example (c : List Bool) :
    ((NoInfinitySquareSample.input repeated).annihilator c ⟨0,by change 0<1;decide⟩).eval₂ (Int.castRingHom ℝ) 0=0:=
  NoInfinitySquareSample.complete repeated c (zeroRoot c).val (zeroRoot c).property ⟨0,by change 0<1;decide⟩

#check SquareSampleCompleteNaturality.complete_width_comp
#check SquareSampleCompleteNaturality.complete_valid_comp
#check SquareSampleCompleteNaturality.candidate_comp
#check IntegralFramedPhysicalSquareContext.input_aux_eq
#check IntegralFramedPhysicalSquareContext.input_root_factor
#check IntegralFramedPhysicalSquareContext.natural_root
#print axioms SquareSampleParameterNaturality.parameter_comp
#print axioms SquareSampleParameterNaturality.decode_comp
#print axioms SquareSampleParameterNaturality.roots_comp
#print axioms SquareSampleRankNaturality.prefixRank_congr
#print axioms SquareSampleRankNaturality.chosen_congr
#print axioms SquareSampleRankNaturality.integerValue_congr
#print axioms SquareSampleHashNaturality.index_congr
#print axioms SquareSampleHashNaturality.hash_congr
#print axioms SquareSampleOrdinalNaturality.root_val_comp
#print axioms SquareSampleCompleteNaturality.complete_width_comp
#print axioms SquareSampleCompleteNaturality.complete_valid_comp
#print axioms SquareSampleCompleteNaturality.candidate_comp
#print axioms IntegralFramedPhysicalSquareContext.input_aux_eq
#print axioms IntegralFramedPhysicalSquareContext.input_root_factor
#print axioms IntegralFramedPhysicalSquareContext.natural_root
#print axioms self_context
end SquareNaturalityRegression
end
end RoadmapNaturality

namespace RoadmapFieldEquality
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR Polynomial
open MatrixPower
open scoped Classical
namespace PhysicalFieldEqualityRegression
private def n (_ : List Bool) :=0
private def t (_ : List Bool) : Term:=.const 0
private def R (_ : List Bool) :=0
private theorem hn : UnaryFn n:=UnaryFn.const 0
private theorem ht : (fun q=>(t q).toData.toBits)∈FP:=by
  simpa only [t] using (constFn_mem_FP (Term.const (0:ℤ)).toData.toBits)
private theorem ha : ∀q,(t q).arity≤n q:=by intro q;change 0≤0;omega
private theorem hR : BinaryFn R:=BinaryFn.const 0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
example : SpaceDecider (IntegralMixedPhysicalFieldEquality.language hn ht ha hR):=
  IntegralMixedPhysicalFieldEquality.decider hn ht ha hR
example : SpaceDecider (IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR):=
  IntegralMixedPhysicalFieldEqualityList.decider hn ht ha hR
example : IntegerPolynomialRootQueriesBits.Access (IntegralMixedPhysicalFieldEquality.originalSource hn ht ha hR):=
  IntegralMixedPhysicalFieldEquality.originalAccess hn ht ha hR
example : IntegralMixedPhysicalFieldEquality.context true
    (IntegralMixedPhysicalFieldEquality.packet (pair [true] []) [true,false]
      (pair [false,true] []) [false,false,true] 1 4)=pair [false,true] [] :=
  (IntegralMixedPhysicalFieldEquality.packet_fields _ _ _ _ 1 4).2.2.1
example : IntegralMixedPhysicalFieldEquality.word false
    (IntegralMixedPhysicalFieldEquality.packet (pair [true] []) [true,false]
      (pair [false,true] []) [false,false,true] 1 4)=[true,false] :=
  (IntegralMixedPhysicalFieldEquality.packet_fields _ _ _ _ 1 4).2.1
example (own old : List Bool) : IntegralMixedPhysicalFieldEquality.derivativePacket
    (pair own (pair old (pair (BinaryNatCode.encode 5) (BinaryNatCode.encode 3))))=
      pair old (BinaryNatCode.encode 3) :=by
  simp only [IntegralMixedPhysicalFieldEquality.derivativePacket,pairFst_pair,pairSnd_pair]
example : IntegralMixedPhysicalFieldEquality.newest 5 1=3 ∧ IntegralMixedPhysicalFieldEquality.newest 8 2=5 :=by
  decide
example (z : List Bool)
    (hbad : IntegralMixedPhysicalFieldEquality.count hn ht ha hR (IntegralMixedPhysicalFieldEquality.context false z)≤
      IntegralMixedPhysicalFieldEquality.label false z) : z∉IntegralMixedPhysicalFieldEquality.language hn ht ha hR :=
  IntegralMixedPhysicalFieldEquality.reject_left hn ht ha hR z hbad
example (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cL wL)
    (hR' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cR wR)
    (a b : ℕ) (ha' : a<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cL)
    (hb : b<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cR)
    (he : IntegralMixedPhysicalFieldEquality.point hn ht ha hR cL wL hL a=
      IntegralMixedPhysicalFieldEquality.point hn ht ha hR cR wR hR' b) :
    IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b∈IntegralMixedPhysicalFieldEquality.language hn ht ha hR :=
  (IntegralMixedPhysicalFieldEquality.language_packet_iff hn ht ha hR cL wL cR wR hL hR' a b ha' hb).mpr he
private def fields:=WordList.encode [pair (BinaryNatCode.encode 1) (BinaryNatCode.encode 4),
  pair (BinaryNatCode.encode 2) (BinaryNatCode.encode 7)]
example : WordListRecords.count fields=2 :=by
  rw [fields,WordListRecords.count_encode]
  rfl
example (cL wL cR wR : List Bool) : IntegralMixedPhysicalFieldEqualityList.query
    (pair (IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR fields) [true])=
      IntegralMixedPhysicalFieldEquality.packet cL wL cR wR 2 7 :=by
  change IntegralMixedPhysicalFieldEqualityList.query
    (pair (IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR fields) (List.replicate 1 true))=_
  rw [IntegralMixedPhysicalFieldEqualityList.query_packet]
  simp only [fields,WordList.get_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    IntegralMixedPhysicalFieldEqualityList.label,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,ite_true,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
example (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cL wL)
    (hR' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cR wR) :
    IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR []∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR :=by
  apply (IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha hR cL wL cR wR [] hL hR' (by
    intro i hi
    change i<0 at hi
    omega)).mpr
  intro i hi
  change i<0 at hi
  omega
noncomputable def p : ℝ[X]:=C (-6)*(X-C 2)^2*(X+C 1)^2
example : p.eval 2=0 ∧ p.eval (-1)=0 :=by norm_num [p]
example : ThomEncoding.sign p 2 0=ThomEncoding.sign p (-1) 0 :=by norm_num [ThomEncoding.sign,p]
example : ThomEncoding.sign p 2 1=ThomEncoding.sign p (-1) 1 :=by
  norm_num [ThomEncoding.sign,p,Function.iterate_succ_apply,Polynomial.derivative_mul,Polynomial.derivative_pow]
example : ThomEncoding.sign p 2 3≠ThomEncoding.sign p (-1) 3 :=by
  norm_num [ThomEncoding.sign,p,Function.iterate_succ_apply,Polynomial.derivative_mul,Polynomial.derivative_pow]
example : ThomEncoding.sign p 2 0≠ThomEncoding.sign p 0 0 :=by norm_num [ThomEncoding.sign,p]
example : p.eval ((-12:ℝ)/(-6))=0 :=by norm_num [p]
example : residueBits ((-6:ℤ):ZMod 6)=[] ∧ residueBits ((-4:ℤ):ZMod 6)=BinaryNatCode.encode 2 :=by
  decide
#print axioms IntegralFramedPhysicalSquare.bank_polynomial_root
#print axioms IntegralMixedPhysicalFieldEquality.originalAccess
#print axioms IntegralMixedPhysicalFieldEquality.evaluator
#print axioms IntegralMixedPhysicalFieldEquality.agrees_evaluator
#print axioms IntegralMixedPhysicalFieldEquality.decider
#print axioms IntegralMixedPhysicalFieldEquality.mem_PSPACE
#print axioms IntegralMixedPhysicalFieldEquality.below_cap
#print axioms IntegralMixedPhysicalFieldEquality.value_packet
#print axioms IntegralMixedPhysicalFieldEquality.source_nonzero
#print axioms IntegralMixedPhysicalFieldEquality.left_root
#print axioms IntegralMixedPhysicalFieldEquality.agrees_iff
#print axioms IntegralMixedPhysicalFieldEquality.language_packet_iff
#print axioms IntegralMixedPhysicalFieldEquality.reject_left
#print axioms IntegralMixedPhysicalFieldEqualityList.query_FP
#print axioms IntegralMixedPhysicalFieldEqualityList.holds_evaluator
#print axioms IntegralMixedPhysicalFieldEqualityList.decider
#print axioms IntegralMixedPhysicalFieldEqualityList.language_packet_iff
end PhysicalFieldEqualityRegression
end RoadmapFieldEquality

namespace RoadmapChildCompiler
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ChronologicalEndpointRegression
private def D:=BoundedZeroSource.powerDegree 0
private theorem Dval : D=18:=rfl
private def P : SpatialSource 2 where
 low:=MvPolynomial.C (-(2^18+1):ℤ)
 leading:=2^18
 degree:=D
 degree_two:=by rw [Dval]; decide
 low_degree:=by
  simpa only [MvPolynomial.totalDegree_C] using
    (show 0<D from by rw [Dval]; decide)
 leading_ne_zero:=by norm_num
private theorem cap : PurePowerReductionBounds.dimension 3 P.degree≤IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree:=by
 unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
 omega
private def initial (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) : State P 6 B 0 (Fin 0):=
 IntegralMixedHistory.base P (IntegralHistorySampler.base 6 (2^B)) (cap.trans hc)
open IntegralMixedFullHistoryScript Polynomial
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
private def before (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 State P 6 B 4 (Index (Fin 0) (leaves B)) :=
 run (initial B hc) (leaves B) (by change (4:ℕ)≤7; decide)
private theorem before_realized (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
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



open IntegralMixedChronologicalEndpointCode
private def d : IntegralMixedChronologicalFrame.Descriptor 2 4 where
 labels:=[0]
 length_le:=by decide
private theorem fit : d.labels.length<3:=by decide
private def a : Fin 4:=3
private def g : Fin 3:=2
private theorem hg : g∉(d.freeze a fit).frame.frozen:=by
 rw [(d.freeze a fit).frozen_mem,d.freeze_length]
 decide
private def W:=IntegralMixedChronologicalFrameCode.labels d
private def codeWord:=code 2 W a.val g.val g.val
example : appendLabels W a.val=IntegralMixedChronologicalFrameCode.labels (d.freeze a fit):=append_actual d a fit
example : WordListRecords.count (appendLabels W a.val)=2:=by rw [append_count];unfold W;rw [IntegralMixedChronologicalFrameCode.labels_count];rfl
example : Nat.fromBitsLE (WordList.get (appendLabels W a.val) 0)=0:=by
 rw [append_lookup_old W a.val 0 (by change (0:ℕ)<WordListRecords.count (IntegralMixedChronologicalFrameCode.labels d);rw [IntegralMixedChronologicalFrameCode.labels_count];decide)]
 unfold W
 rw [IntegralMixedChronologicalFrameCode.labels_lookup d 0 (by decide)]
 rfl
example : Nat.fromBitsLE (WordList.get (appendLabels W a.val) 1)=3:=append_lookup_last W a.val
example : appendLabels [] 0=WordList.encode [[]]:=rfl
example : Good 2 4 W 3:=good_descriptor d a fit
example : PointGood 2 4 W 3 2 2:=point_good_descriptor d a fit g g hg hg
example : ¬Good 2 4 W 4:=by intro H;exact Nat.lt_irrefl 4 H.2.2
example : ¬Good 2 4 (WordList.encode [BinaryNatCode.encode 0,BinaryNatCode.encode 1,BinaryNatCode.encode 2]) 3:=by
 intro H
 have HH:=H.2.1
 rw [WordListRecords.count_encode] at HH
 change (3:ℕ)<3 at HH
 exact Nat.lt_irrefl 3 HH
example : ¬PointGood 2 4 W 3 1 2:=by
 intro H
 have HH:=H.2.1
 change WordListRecords.count (IntegralMixedChronologicalFrameCode.labels d)+1≤1 at HH
 rw [IntegralMixedChronologicalFrameCode.labels_count] at HH
 change (2:ℕ)≤1 at HH
 omega
example : IntegralMixedCausalUnitRecordBits.physical 2 4 codeWord=pointRule (d.freeze a fit).frame g hg g hg:=
 decode d a fit g g hg hg
example : (code 2 W a.val g.val g.val).length≤IntegralMixedCriticalRecordConstructor.codeBudget 2 4:=
 code_size d a fit g g hg hg
example : IntegralMixedUnitRecordCode.field codeWord 12=[false,false,false]:=by
 rw [show codeWord=(data d a fit g g hg hg).code from (data_code d a fit g g hg hg).symm,
   IntegralMixedCriticalRecordConstructor.field_12]
 rfl
private theorem point_slice : (![1,-(1/2),0] : Fin 3→ℝ)∈slice P (d.freeze a fit).frame vals:=by
 rw [child_slice]
 constructor
 · apply (d.slice_iff P vals _).mpr
   constructor
   · norm_num [P,Dval,FermatCriticalHomogenization.polynomial,Fin.sum_univ_succ]
   · intro i
     have HI : i.val=0:=by have :=i.isLt;change i.val<1 at this;omega
     have HE : i=(⟨0,by decide⟩ : Fin d.labels.length):=Fin.ext HI
     subst i
     rfl
 · rfl
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 ∃φ : (before B hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  (![1,-(1/2),0] : Fin 3→ℝ)∈actualSlice (before B hc) φ (d.freeze a fit).frame :=by
 obtain ⟨_,φ,_,_,H⟩:=before_realized B hc
 refine ⟨φ,?_⟩
 rw [actualSlice_eq (before B hc) φ _ vals H]
 exact point_slice
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) :
 (IntegralMixedCausalUnitRecordBits.record P (by decide) 4 codeWord hc).template.command
   (commonDenominator (before B hc)) (commonDenominator_ne_zero _)=
 (.critical (pointRule (d.freeze a fit).frame g hg g hg) : Command P B) :=
 command_currentQ (before B hc) (by decide) hc d a fit g g hg hg
example : (rawData 2 4 W 3 2 2 (point_good_descriptor d a fit g g hg hg)).code=codeWord:=
 rawData_code 2 4 W 3 2 2 (point_good_descriptor d a fit g g hg hg)
example : (fun q=>appendLabels q (Nat.fromBitsLE q))∈FP:=appendLabels_FP id_mem_FP (BinaryFn.fromBits id_mem_FP)
example : (fun q=>code q.length q (Nat.fromBitsLE q) (Nat.fromBitsLE q) (Nat.fromBitsLE q))∈FP:=
 code_FP (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP)
   (BinaryFn.fromBits id_mem_FP) id_mem_FP
example : FPPred (fun q=>PointGood q.length (Nat.fromBitsLE q) q (Nat.fromBitsLE q) (Nat.fromBitsLE q) (Nat.fromBitsLE q)):=
 pointGood_FP (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP)
   (BinaryFn.fromBits id_mem_FP) (BinaryFn.fromBits id_mem_FP) id_mem_FP
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 3 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [IntegralMixedFullHistoryScript.run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),
   poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]

example : ((-24:ℤ)%6)=0:=by decide

#print axioms appendLabels_FP
#print axioms append_good_iff
#print axioms point_good_iff
#print axioms pointGood_FP
#print axioms append_actual
#print axioms data_code
#print axioms data_rule
#print axioms decode
#print axioms command_currentQ
#print axioms child_slice
#print axioms actual_child_slice
#print axioms append_descriptor
#print axioms rawChild_labels
#print axioms rawData_code
#print axioms rawData_rule
#print axioms raw_command
#print axioms raw_code_size
end ChronologicalEndpointRegression
end
end RoadmapChildCompiler

namespace RoadmapWordWidth
open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding
open NoInfinitySquareWordWidth
open scoped Classical
noncomputable section
namespace SquareWordWidthRegression
private def repeated : NoInfinitySquareSample.Family where
  count _:=1
  degree _:=2
  mass _:=0
  rowDegree _ _:=2
  rows _ _:=(MvPolynomial.X (0 : Fin 1))^2
  count_pos _:=by decide
  degree_pos _:=by decide
  row_degree _ _:=(MvPolynomial.totalDegree_X_pow _ _).le
  rowDegree_pos _ _:=by decide
  rowDegree_le _ _:=le_rfl
  row_mass _ _:=by
    simpa only [MvMass.X,one_pow,pow_zero] using MvMass.pow_le (MvPolynomial.X (0 : Fin 1)) 2
  noInfinity _:=by
    intro y hy hz
    have H:=hz 0
    change (WeightedHomogenization.homogenize (fun _=>1) 2
      ((MvPolynomial.X (0 : Fin 1))^2)).eval₂ (Int.castRingHom ℂ) y=0 at H
    rw [WeightedHomogenization.homogenize_X_pow] at H
    simp only [MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X] at H
    have Hz : y (some 0)=0:=(pow_eq_zero_iff (by decide : 2≠0)).mp H
    funext j
    cases j with
    | none=>exact hy
    | some i=>simpa only [Subsingleton.elim i 0,Pi.zero_apply] using Hz


example : ceiling 0 0=2:=by decide
example : ceiling 1 2=12:=by decide
example : ceiling 2 2=32:=by decide
example : SquareSampleCompleteVertices.width (NoInfinitySquareSample.input repeated) []=8:=by
  rw [width_exact]
  decide
example : SquareSampleCompleteVertices.width (NoInfinitySquareSample.input repeated) []≤12:=by
  exact width_le repeated [] 2 (fun _=>le_rfl)

private def largeMass (H : ℕ) : NoInfinitySquareSample.Family :=
  { repeated with mass:=fun _=>H
                  row_mass:=fun c i=>(repeated.row_mass c i).trans
                    (Nat.pow_le_pow_right (by decide) (Nat.zero_le H)) }

-- The sampler's coefficient-height allowance does not enlarge its word width.
example (H : ℕ) : SquareSampleCompleteVertices.width (NoInfinitySquareSample.input (largeMass H)) []=8:=by
  rw [width_exact]
  have HD : NoInfinitySquareSample.dimension (largeMass H) []=NoInfinitySquareSample.dimension repeated []:=rfl
  have HC : (largeMass H).count []=1:=rfl
  rw [HD,HC]
  decide
example : ceiling 1 2≤ceiling 3 20:=ceiling_mono (by decide) (by decide)
example : UnaryFn (fun q=>ceiling q.length (2^q.length)):=
  ceiling_unary (UnaryFn.length id_mem_FP) ((BinaryFn.const 2).powUnary (UnaryFn.length id_mem_FP))
example (n : ℕ) : (2^n+1).size≤n+2:=size_pow_add_one n
example (F : NoInfinitySquareSample.Family) (u : List Bool) (D : ℕ)
    (h : ∀i : Fin (F.count u),F.rowDegree u i.val≤D) :
    SquareSampleCompleteVertices.width (NoInfinitySquareSample.input F) u≤ceiling (F.count u) D:=
  width_le F u D h

#print axioms size_pow_add_one
#print axioms size_scaled_power_add_two
#print axioms level_le
#print axioms width_exact
#print axioms width_le
#print axioms ceiling_mono
#print axioms ceiling_unary
end SquareWordWidthRegression
end
end RoadmapWordWidth
