import LeanCanny.Connectivity
import LeanCanny.Connectivity.FiniteCriticalSweepInternal
import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientIntervalComplete
import LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
import LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingRealization
import LeanCanny.Geometry.IntegralMixedChronologicalFreshEndpoint
import LeanCanny.Geometry.IntegralMixedChronologicalOptionalPairSweep
import LeanCanny.Geometry.IntegralMixedFrozenFrameCriticalRange
import LeanCanny.Geometry.IntegralMixedFrozenFrameInternalSweep

/-! Internal critical sweeps, native endpoint pairs and honest padding.
The whole bounded graph/path theorem remains separate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapInternalExtrema
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame Set
open scoped Classical
noncomputable section
namespace FrozenCriticalExtremaRegression
private def P : SpatialSource 1:=
  {low:=0,leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_zero]; decide,leading_ne_zero:=by decide}
private def F : Frame 1:=
  {frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
private def values : Fin 0→ℝ:=Fin.elim0
private def zeroPoint : Fin 2→ℝ:=fun _=>0
private theorem free : (0 : Fin 2)∉F.frozen:=by simp [F]
private theorem normal : FreeNormal F:=by intro _ _;exact ⟨rfl,rfl⟩
private theorem source_eval (y : Fin 2→ℝ) :
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂
      (Int.castRingHom ℝ) y=y 0^2+y 1^2:=by
  norm_num [P,FermatCriticalHomogenization.polynomial,MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
private theorem member : zeroPoint∈slice P F values:=by
  refine ⟨?_,?_⟩
  · rw [source_eval];norm_num [zeroPoint]
  · intro i hi;exact False.elim (Finset.notMem_empty i hi)
private theorem coordinate_zero (y : Fin 2→ℝ) (hy : y∈slice P F values) : y 0=0:=by
  have HY:=hy.1
  rw [source_eval] at HY
  have H0:=sq_nonneg (y 0)
  have H1:=sq_nonneg (y 1)
  nlinarith
private theorem maximum : IsMaxOn (fun y : Fin 2→ℝ=>y 0) (slice P F values) zeroPoint:=by
  intro y hy
  change y 0≤zeroPoint 0
  rw [coordinate_zero y hy]
  exact le_rfl
private theorem minimum : IsMinOn (fun y : Fin 2→ℝ=>y 0) (slice P F values) zeroPoint:=by
  intro y hy
  change zeroPoint 0≤y 0
  rw [coordinate_zero y hy]
  exact le_rfl

-- The full source gradient vanishes: this is an actual singular zero slice.
example (i : Fin 2) :
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) zeroPoint=0:=by
  rw [FermatCriticalHomogenization.pderiv_polynomial]
  norm_num [P,zeroPoint,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
example : (0 : ℝ)∈realCriticalValues P (line F 0) values 0:=
  critical_height_of_isMaxOn P F values 0 free normal zeroPoint member maximum
example : (0 : ℝ)∈realCriticalValues P (line F 0) values 0:=
  critical_height_of_isMinOn P F values 0 free normal zeroPoint member minimum
example : ∀i,i∉F.frozen→i≠(0 : Fin 2)→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) zeroPoint=0:=by
  apply free_partials_of_signed_max P F values 0 free (-7) (by norm_num) zeroPoint member
  have HM : IsMaxOn (fun y : Fin 2→ℝ=>(-7)*y 0) (slice P F values) zeroPoint:=by
    intro y hy
    change (-7)*y 0≤(-7)*zeroPoint 0
    rw [coordinate_zero y hy]
    exact le_rfl
  exact HM.isLocalMaxOn
example : realCriticalValues P (line F 0) values 0={0}:=by
  ext t
  rw [line_realCriticalValues_iff P F values 0 free normal]
  constructor
  · rintro ⟨y,hy,hyt,_⟩
    exact hyt.symm.trans (coordinate_zero y hy)
  · intro ht
    have HT : t=0:=ht
    subst t
    exact (line_realCriticalValues_iff P F values 0 free normal 0).mp
      (critical_height_of_isMaxOn P F values 0 free normal zeroPoint member maximum)

-- Actual original bounded-regular properness supplies the only compactness input.
example (R : BoundedFullWriter.Readers) (q : List Bool)
    (G : Frame (R.dim q+3)) (v : Fin 0→ℝ) (h : Fin (R.dim q+4))
    (hh : h∉G.frozen) (HG : FreeNormal G)
    (hne : (slice (BoundedRegularLowModularTerm.source R q) G v).Nonempty) :
    ∃ lo hi : Fin (R.dim q+4)→ℝ,
      lo∈slice (BoundedRegularLowModularTerm.source R q) G v ∧
      hi∈slice (BoundedRegularLowModularTerm.source R q) G v ∧
      lo h∈realCriticalValues (BoundedRegularLowModularTerm.source R q) (line G h) v h ∧
      hi h∈realCriticalValues (BoundedRegularLowModularTerm.source R q) (line G h) v h ∧
      ∀ y∈slice (BoundedRegularLowModularTerm.source R q) G v,lo h≤y h ∧ y h≤hi h:=
  exists_critical_extrema _ G v h hh HG (regular_source_proper R q) hne

example {n k : ℕ} (Q : SpatialSource n) (G : Frame n) (v : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉G.frozen) (HG : FreeNormal G)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice Q G v).Nonempty) (c : ℝ)
    (HC : realCriticalValues Q (line G h) v h⊆{c}) :
    ∀y∈slice Q G v,y h=c:=by
  obtain ⟨_,a,b,Ha,Hb,Henclose⟩:=finite_critical_range Q G v h hh HG hp hne {c}
    (finite_singleton c) HC
  have HA : a=c:=Ha.1
  have HB : b=c:=Hb.1
  intro y hy
  have HY:=Henclose y hy
  rw [HA,HB] at HY
  exact le_antisymm HY.2 HY.1

#print axioms free_partials_of_signed_max
#print axioms critical_height_of_isMaxOn
#print axioms critical_height_of_isMinOn
#print axioms exists_critical_extrema
#print axioms finite_critical_range
#print axioms sweepBadReal_range
end FrozenCriticalExtremaRegression
end
end RoadmapInternalExtrema

namespace RoadmapInternalCoefficients
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCutOpenInterval (parent Bounds)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CoefficientCompleteRegression
private def constantSign (z : List Bool):=
 if Nat.fromBitsLE (pairFst (pairSnd z))=0 then InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0
private theorem constant_guards (cap : ℕ) :
 FiniteCoefficientSignScan.Guards constantSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>0) (fun _=>cap) []:=by
 refine ⟨?_,?_,?_,Or.inl ?_⟩
 · intro k hk
   change k<0 at hk
   omega
 · decide
 · intro e _ he
   have HE : e≠0:=Nat.ne_of_gt he
   simp only [FiniteCoefficientSignScan.Zero,constantSign,FiniteCoefficientSignScan.query,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HE,ite_false]
 · decide
example : FiniteCoefficientSignScan.Guards constantSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>0) (fun _=>8) []:=constant_guards 8
example : FiniteCoefficientSignScan.Guards constantSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>0) (fun _=>1024) []:=constant_guards 1024
example : ¬FiniteCoefficientSignScan.Guards constantSign (fun _=>InfinitesimalSign.encode 0)
 (fun _=>0) (fun _=>0) (fun _=>8) []:=by
 intro H
 have HX:=H.2.2.2
 norm_num [FiniteCoefficientSignScan.Zero,constantSign,FiniteCoefficientSignScan.query,
   BinaryNatCode.encode,Nat.fromBitsLE_bits] at HX
 exact (by decide : InfinitesimalSign.encode 1≠InfinitesimalSign.encode 0) (HX rfl)
private def quadraticSign (z : List Bool):=
 if Nat.fromBitsLE (pairFst (pairSnd z))=0 ∨ Nat.fromBitsLE (pairFst (pairSnd z))=2
 then InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0
example : FiniteCoefficientSignScan.Guards quadraticSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>2) (fun _=>8) []:=by
 refine ⟨?_,?_,?_,Or.inl ?_⟩
 · intro k hk
   change k<0 at hk
   omega
 · decide
 · intro e _ he
   have HE : 2<e:=he
   have H0 : e≠0:=by omega
   have H2 : e≠2:=by omega
   simp only [FiniteCoefficientSignScan.Zero,quadraticSign,FiniteCoefficientSignScan.query,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,H0,H2,or_self,ite_false]
 · decide
example : ¬FiniteCoefficientSignScan.Guards quadraticSign IntegralMixedPhysicalCutCoefficientOnly.head
 (fun _=>0) (fun _=>1) (fun _=>8) []:=by
 intro H
 exact H.2.1 (by decide)
example : (1 : Polynomial ℝ).natDegree=0:=by simp
example : (Polynomial.X^2+1 : Polynomial ℝ).natDegree=2:=by compute_degree;norm_num
example : ∀r : ℝ,(Polynomial.X^2+1 : Polynomial ℝ).eval r≠0:=by
 intro r hr
 norm_num at hr
 nlinarith [sq_nonneg r]
example : (PaddedIntegralNormalization.polynomial (1 : Polynomial ℤ) 0 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial,FixedDegreeIntegralNormalization.polynomial]
example : (PaddedIntegralNormalization.polynomial (Polynomial.X^2+1 : Polynomial ℤ) 2 8).eval 0=0:=by
 norm_num [PaddedIntegralNormalization.polynomial]
example : ((-24 : ℤ)%6)=0:=by decide
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => family P D H
variable (q w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "hm" => IntegralMixedCutSource.Family.birth_bound G old
local notation "r" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
example (hb : Bounds hn ht ha hR outer (pair q w))
 (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (hφ : IntegralMixedPhysicalCutCoefficientComplete.Tail hn ht ha hR outer q w hv φ) :
 IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w) ↔
 IntegralMixedRelativeCuts.CoefficientGuards x hm r φ kind ((G).degree old):=
 IntegralMixedPhysicalCutCoefficientComplete.guards_iff hn ht ha hR outer q w hv hb φ hφ
example (hb : Bounds hn ht ha hR outer (pair q w))
 (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (hφ : IntegralMixedPhysicalCutCoefficientComplete.Tail hn ht ha hR outer q w hv φ) :
 IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w) ↔
 IntegralMixedRelativeCuts.Valid x hm r φ kind ∧
 ((IntegralMixedRelativeCuts.factor x hm r kind).map φ.toRingHom).natDegree=(G).degree old:=
 IntegralMixedPhysicalCutCoefficientComplete.guards_iff_valid_degree hn ht ha hR outer q w hv hb φ hφ
example (hb : Bounds hn ht ha hR outer (pair q w))
 (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
 (hφ : IntegralMixedPhysicalCutCoefficientComplete.Tail hn ht ha hR outer q w hv φ)
 (hvalid : IntegralMixedRelativeCuts.Valid x hm r φ kind)
 (hd : ((IntegralMixedRelativeCuts.factor x hm r kind).map φ.toRingHom).natDegree=(G).degree old) :
 IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w):=
 (IntegralMixedPhysicalCutCoefficientComplete.guards_iff_valid_degree hn ht ha hR outer q w hv hb φ hφ).mpr ⟨hvalid,hd⟩
example : SpaceDecider (IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer):=
 IntegralMixedPhysicalCutCoefficientInterval.decider hn ht ha hR outer
#print axioms IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree
#print axioms IntegralMixedPhysicalCutCoefficientComplete.coefficient_evaluation_at
#print axioms IntegralMixedPhysicalCutCoefficientComplete.guards_iff
#print axioms IntegralMixedPhysicalCutCoefficientComplete.guards_iff_valid_degree
#print axioms IntegralMixedPhysicalCutCoefficientComplete.full_tail
#print axioms IntegralMixedPhysicalCutCoefficientComplete.empty_iff_at
#print axioms IntegralMixedPhysicalCutCoefficientInterval.decider
#print axioms constant_guards
end CoefficientCompleteRegression
end
end RoadmapInternalCoefficients

namespace RoadmapInternalSources
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open IntegralMixedFramedHistoryFamilyBits (family instruction keyAt)
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace OriginalRegularSourceRegression

example (input label records aux : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.original (context input label (pair records aux))=input :=
  original_context _ _ _
example (R0 : List Bool→ℕ) (input label records aux : List Bool) :
    radius R0 (context input label (pair records aux))=R0 input :=radius_context _ _ _ _
example : radius Nat.fromBitsLE (context [true,false,true] (List.replicate 400 true)
    (pair (WordList.encode [[],[true],[false]]) (List.replicate 200 false)))=5 :=by
  rw [radius_context]
  decide
example : radius (fun q=>q.length) (context [true,false] [] (List.replicate 900 true))=2 :=by
  rw [radius_context]
  rfl
example : BinaryFn (radius Nat.fromBitsLE) :=radius_binary (BinaryFn.fromBits id_mem_FP)
example : (fun q : List Bool=>context (pairFst q) (pairSnd q) (pair q []))∈FP :=
  context_FP pairFst_mem_FP pairSnd_mem_FP (mem_FP_pair id_mem_FP (constFn_mem_FP []))

example (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input l r tail tail' : List Bool) :
    HEq (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input l tail))
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input r tail')) :=
  (spatial_context n t R0 input l tail).trans (spatial_context n t R0 input r tail').symm
example (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input l tail : List Bool) :
    HEq (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input l tail)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).low :=
  low_context n t R0 input l tail
example (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input l tail : List Bool) :
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input l tail)).leading=
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).leading :=
  leading_context n t R0 input l tail
example (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input l tail : List Bool) :
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input l tail)).degree=
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).degree :=
  degree_context n t R0 input l tail

-- Record counts can differ despite source equality. No horizon or word transport follows.
example : IntegralMixedCausalRecordPlanBits.count (context [] [] (pair (WordList.encode []) []))=0 :=by
  decide
example : IntegralMixedCausalRecordPlanBits.count (context [] [true] (pair (WordList.encode [[]]) [true]))=1 :=by
  decide

section Actual
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "O"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) true

example (input label tail saved : List Bool) :
    HEq (instruction (B).parameters (B).plan (keyAt (context input label tail) 999999 saved)).source
      (instruction (B).parameters (B).plan (keyAt (canonical input) 0 [])).source :=
  IntegralMixedPhysicalOriginalSource.instruction_canonical hn ht ha hR0 false _ _ _ _ _
example (input label tail saved label' tail' saved' : List Bool) (a b : ℕ) :
    HEq ((family (B).parameters (B).plan (B).data).spatial (keyAt (context input label tail) a saved))
      ((family (O).parameters (O).plan (O).data).spatial (keyAt (context input label' tail') b saved')) :=
  IntegralMixedPhysicalOriginalSource.family_modes hn ht ha hR0 false true _ _ _ _ _ _ _ _ _
example (root : List Bool) :
    HEq ((O).plan.initialSource root)
      (source n t R0 (IntegralMixedAuxiliaryMarkedIntegerSource.original root)) :=
  IntegralMixedPhysicalOriginalSource.initial_source hn ht ha hR0 true root
end Actual

#print axioms radius_binary
#print axioms context_FP
#print axioms spatial_context
#print axioms low_context
#print axioms leading_context
#print axioms degree_context
#print axioms source_polynomial
#print axioms spatial_polynomial
#print axioms IntegralMixedPhysicalOriginalSource.instruction_source
#print axioms IntegralMixedPhysicalOriginalSource.family_packet
#print axioms IntegralMixedPhysicalOriginalSource.instruction_context
#print axioms IntegralMixedPhysicalOriginalSource.family_modes
#print axioms IntegralMixedPhysicalOriginalSource.initial_source
end OriginalRegularSourceRegression
end RoadmapInternalSources

namespace RoadmapInternalInternalSweep
open LeanCanny LeanCanny.Geometry LeanCanny.Connectivity Set
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace InternalSweepRegression
private noncomputable def cuts : Finset ℝ:={-2,0,5}
private theorem lower : IsLeast (cuts : Set ℝ) (-2):=by
 constructor
 · norm_num [cuts]
 · intro y hy
   have HY : y=-2 ∨ y=0 ∨ y=5:=by simpa [cuts] using hy
   rcases HY with rfl|rfl|rfl <;> norm_num
private theorem upper : IsGreatest (cuts : Set ℝ) 5:=by
 constructor
 · norm_num [cuts]
 · intro y hy
   have HY : y=-2 ∨ y=0 ∨ y=5:=by simpa [cuts] using hy
   rcases HY with rfl|rfl|rfl <;> norm_num
example : ∃n : ℕ,∃cut : Fin (n+2)→ℝ,StrictMono cut ∧
    (∀j,cut j∈cuts) ∧ ∀t∈Icc (-2) 5,∃i : Fin (n+1),t∈Icc (cut i.castSucc) (cut i.succ):=by
 obtain ⟨n,cut,HM,_,_,HJ,_,_,HC⟩:=FiniteCriticalSweepInternal.exists_cuts cuts (-2) 5 lower upper (by norm_num)
 exact ⟨n,cut,HM,HJ,HC⟩
example : ∃n : ℕ,∃cut : Fin (n+2)→ℝ,(∀j,cut j∈cuts) ∧
    ∃i : Fin (n+1),(4 : ℝ)∈Icc (cut i.castSucc) (cut i.succ):=by
 obtain ⟨n,cut,_,_,_,HJ,_,_,HC⟩:=FiniteCriticalSweepInternal.exists_cuts cuts (-2) 5 lower upper (by norm_num)
 exact ⟨n,cut,HJ,HC 4 (by norm_num)⟩
private theorem singleton_lower : IsLeast (({3} : Finset ℝ) : Set ℝ) 3:=by
 constructor
 · simp
 · intro t ht
   have HE : t=3:=by simpa using ht
   rw [HE]
private theorem singleton_upper : IsGreatest (({3} : Finset ℝ) : Set ℝ) 3:=by
 constructor
 · simp
 · intro t ht
   have HE : t=3:=by simpa using ht
   rw [HE]
example : ({(3 : ℝ)} : Finset ℝ)={3}:=
 FiniteCriticalSweepInternal.singleton_of_equal_extrema _ 3 singleton_lower singleton_upper
example (cut : Fin 2→ℝ) {x : ℝ} (hx : x∈Icc (cut 0) (cut 1)) :
    ∃i : Fin 1,x∈Icc (cut i.castSucc) (cut i.succ):=FiniteCriticalSweepInternal.adjacent_cover cut hx
#print axioms FiniteCriticalSweepInternal.adjacent_cover
#print axioms FiniteCriticalSweepInternal.singleton_of_equal_extrema
#print axioms FiniteCriticalSweepInternal.extrema_cases
#print axioms FiniteCriticalSweepInternal.exists_cuts
#print axioms Geometry.IntegralMixedFrozenFrame.internal_sweep_cases
end InternalSweepRegression
end RoadmapInternalInternalSweep

namespace RoadmapInternalFreshEndpoints
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedRelativeCuts IntegralMixedChronologicalEndpoint Set
open scoped Classical
noncomputable section
namespace ChronologicalFreshEndpointRegression
private def d : Descriptor 4 5:=⟨[0,3],by decide⟩
private theorem hk : d.labels.length<5:=by decide
private def g : Fin 5:=3
private theorem hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen:=by
  rw [IntegralMixedChronologicalSweepFrame.free_iff]
  decide
private def P : SpatialSource 4:=
  {low:=MvPolynomial.C (-1),leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_C];decide,leading_ne_zero:=by decide}
private def D:=IntegralMixedChronologicalSweepFrame.data d hk g g hg hg
private theorem offset : D.critical.offset.val=3:=
  IntegralMixedChronologicalSweepFrame.pointData_offset d hk g g hg hg
private def j : Fin (4-D.critical.offset.val+1):=⟨1,by have H:=offset;omega⟩
private def c : Kind P (D.rule (-6) (by decide)):=.coordinate j ⟨0,by
  exact Nat.zero_lt_succ _⟩

example : IntegralMixedRoadmapEndpointSyntax.Good 4 12 9 5 5
    (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.criticalSpec d):=
  IntegralMixedRoadmapEndpointSyntax.criticalSpec_good d 12 9 5
example : IntegralMixedRoadmapEndpointSyntax.field
    (IntegralMixedRoadmapEndpointSyntax.criticalSpec d) 1=5:=
  IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _
example : IntegralMixedRoadmapEndpointSyntax.field
    (IntegralMixedRoadmapEndpointSyntax.criticalSpec d) 2=2:=
  IntegralMixedRoadmapEndpointSyntax.field_spec_2 _ _ _ _ _ _

private theorem physical_j : (IntegralMixedChronologicalCutCode.physicalCoordinate d hk g hg j).val=4:=by
  change D.critical.offset.val+1=4
  rw [offset]
example : (D.rule (-6) (by decide)).slope=(-6 : ℤ):=rfl
example : IntegralMixedChronologicalCutCode.physicalCoordinate d hk g hg j∉
    (IntegralMixedChronologicalSweepFrame.frame d hk).frozen:=
  IntegralMixedChronologicalCutCode.physicalCoordinate_free d hk g hg j
example : D.chosenCode (-6) (by decide) c 7=
    IntegralMixedChronologicalCutCode.code 4 (IntegralMixedChronologicalFrameCode.labels d) 3 4 0 0 7:=by
  have HC:=IntegralMixedChronologicalCutCode.chosenCode_actual d hk g hg P (-6) (by decide) c 7
  change D.chosenCode (-6) (by decide) c 7=
    IntegralMixedChronologicalCutCode.code 4 (IntegralMixedChronologicalFrameCode.labels d) 3
      (IntegralMixedChronologicalCutCode.physicalCoordinate d hk g hg j).val 0 0 7 at HC
  exact HC.trans (congrArg (fun t=>IntegralMixedChronologicalCutCode.code 4
    (IntegralMixedChronologicalFrameCode.labels d) 3 t 0 0 7) physical_j)

private theorem cutBounds : IntegralMixedChronologicalCutCode.Bounds 4 5 12 9
    (IntegralMixedChronologicalFrameCode.labels d) 3 4 2 7 9:=by
  refine ⟨⟨IntegralMixedChronologicalFrameCode.labels_good d,?_,?_,?_,?_⟩,by decide,by decide,le_rfl⟩
  · rw [IntegralMixedChronologicalFrameCode.labels_count];decide
  · decide
  · rw [IntegralMixedChronologicalFrameCode.labels_count];decide
  · decide
example : IntegralMixedRoadmapEndpointSyntax.Good 4 12 9 5 5
    (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.cutSpec d 4 2 7 9):=
  IntegralMixedRoadmapEndpointSyntax.cutSpec_good d 12 9 5 4 2 7 9 cutBounds
example : IntegralMixedRoadmapEndpointSyntax.code 4 (IntegralMixedChronologicalFrameCode.labels d)
    (IntegralMixedRoadmapEndpointSyntax.cutSpec d 4 2 7 9)=
    IntegralMixedChronologicalCutCode.code 4 (IntegralMixedChronologicalFrameCode.labels d) 3 4 2 7 9:=
  IntegralMixedRoadmapEndpointSyntax.cutSpec_code d 4 2 7 9
example : IntegralMixedRoadmapEndpointSyntax.codes 4 (IntegralMixedChronologicalFrameCode.labels d)
    (IntegralMixedRoadmapEndpointSyntax.cutSpec d 4 2 7 9)=
    [IntegralMixedRoadmapEndpointSyntax.code 4 (IntegralMixedChronologicalFrameCode.labels d)
      (IntegralMixedRoadmapEndpointSyntax.cutSpec d 4 2 7 9)]:=
  IntegralMixedRoadmapEndpointSyntax.freshSpec_codes d 2 4 2 7 9 (by decide)

-- Retention shifts newest-first references but keeps original producer bytes.
example : IntegralMixedChronologicalFrameCode.labels d.retain=IntegralMixedChronologicalFrameCode.labels d:=
  IntegralMixedRoadmapEndpointSyntax.labels_retain d
example : (d.reference ⟨0,by decide⟩).val=4 ∧ (d.reference ⟨1,by decide⟩).val=1:=by decide
example : ((childDescriptor d hk).reference ⟨0,by decide⟩).val=5 ∧
    ((childDescriptor d hk).reference ⟨1,by decide⟩).val=2 ∧
    ((childDescriptor d hk).reference ⟨2,by decide⟩).val=0:=by decide
example (v : Fin 5→ℝ) (a : ℝ) : slice P (childDescriptor d hk).frame (Fin.cons a v)=
    slice P d.frame v∩{p | p (2 : Fin 5)=a}:=childDescriptor_slice d hk v a
example : (childDescriptor d hk).labels=d.labels.map Fin.castSucc++[Fin.last 5]:=
  childDescriptor_labels d hk

#print axioms IntegralMixedRoadmapEndpointSyntax.criticalSpec_good
#print axioms IntegralMixedRoadmapEndpointSyntax.cutSpec_good
#print axioms IntegralMixedChronologicalCutCode.data_retarget
#print axioms IntegralMixedChronologicalCutCode.chosenCode_actual
#print axioms Fresh.codes
#print axioms Fresh.word
#print axioms IntegralMixedChronologicalEndpoint.critical
#print axioms selected_cut
#print axioms selected_cut_ofRule
#print axioms base_rule
#print axioms joint_endpoint
#print axioms sweep_endpoint
#print axioms childDescriptor_slice
end ChronologicalFreshEndpointRegression
end
end RoadmapInternalFreshEndpoints

namespace RoadmapInternalPadding
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralHistorySampler IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ActualPaddingRegression
private def degree:=BoundedZeroSource.powerDegree 0
private theorem degree_value : degree=18:=rfl
private def Q : SpatialSource 1 where
 low:=-1
 leading:=1
 degree:=degree
 degree_two:=by rw [degree_value];decide
 low_degree:=by
  simpa only [MvPolynomial.totalDegree_neg,MvPolynomial.totalDegree_one] using
   (show 0<degree from by rw [degree_value];decide)
 leading_ne_zero:=by decide
private theorem cap : PurePowerReductionBounds.dimension 2 Q.degree≤IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree:=by
 unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
 omega
private def initial (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree≤2^B) : State Q 6 B 0 (Fin 0):=
 IntegralMixedHistory.base Q (IntegralHistorySampler.base 6 (2^B)) (cap.trans hc)
private def p : Polynomial ℤ:=C (-2)*X-C 2
private theorem p_nonzero : p≠0:=by
 intro H
 have HE:=congrArg (fun f : Polynomial ℤ=>f.coeff 1) H
 norm_num [p] at HE
private theorem p_degree : p.natDegree≤1:=by unfold p;compute_degree
private def cmd (B : ℕ) : IntegralMixedFullHistoryScript.Command Q B:=
 .integer p p_nonzero (p_degree.trans Nat.one_le_two_pow)
private def leaf (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree≤2^B) : Instruction 1 B:=
 ⟨Q,(initial B hc).critical_cap,cmd B⟩
private def parent (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree≤2^B):=
 run (initial B hc) [leaf B hc] (by change (1:ℕ)≤7;decide)
private theorem parent_realized (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree≤2^B) :
 IntegralMixedIntegerRealization.Realizes (parent B hc) (fun _=>-1):=by
 have HR:=IntegralMixedIntegerRealization.realizes (initial B hc) Fin.elim0 (fun i=>Fin.elim0 i)
   [cmd B] (by change (1:ℕ)≤7;decide) (fun _=>-1) (by intro i;fin_cases i;change p.eval₂ (Int.castRingHom ℝ) (-1)=0;norm_num [p])
 exact HR
private def point : Fin 2→ℝ:=![1,0]
private theorem point_zero :
 (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) point=0:=by
 norm_num [Q,degree_value,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two,point]
 change -(1:ℝ)+(∑i : Fin 2,((![1,0] : Fin 2→ℝ) i)^18)=0
 rw [Fin.sum_univ_two]
 norm_num
private theorem point_grad (i : Fin 2) (hi : i≠0) :
 (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂ (Int.castRingHom ℝ) point=0:=by
 have HE : i=1:=by fin_cases i <;> simp_all
 subst i
 norm_num [Q,degree_value,FermatCriticalHomogenization.polynomial,Fin.sum_univ_two,
   MvPolynomial.pderiv_pow,point]
 simp [Fin.sum_univ_two,Pi.single_apply]
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 Q.degree≤2^B) :
 IntegralMixedIntegerRealization.Realizes
  (run (initial B hc) (List.replicate 2 (IntegralMixedCanonicalPaddingSeed.instruction Q (cap.trans hc))++[leaf B hc]) (by simp only [List.length_append,List.length_replicate,List.length_singleton];decide))
  (IntegralMixedCanonicalPadding.values (point 0) (fun _=>-1) 2):=
 IntegralMixedCanonicalPadding.run_realizes (initial B hc) [leaf B hc] (by change (1:ℕ)≤7;decide) Q (cap.trans hc)
  (by decide) 0 rfl hc (fun _=>-1) (parent_realized B hc) point point_zero point_grad 2 (by simp only [List.length_append,List.length_replicate,List.length_singleton];decide)
example : IntegralMixedCanonicalPadding.values 1 (fun _=>-1) 2 0=1:=rfl
example : IntegralMixedCanonicalPadding.values 1 (fun _=>-1) 2 1=1:=rfl
example : IntegralMixedCanonicalPadding.values 1 (fun _=>-1) 2 2=-1:=rfl
example : IntegralMixedCanonicalPadding.values 1 (fun _=>-1) 2 7=-1:=rfl
example : UniformIntegralPowerSchedule.physical 6 8 1≠UniformIntegralPowerSchedule.physical 6 8 2:=by decide
example : ((-2 : ℤ)%6)=4:=by decide
example : (p.eval₂ (Int.castRingHom ℝ) (-1))=0:=by norm_num [p]
example (n a b : ℕ) : (IntegralMixedCanonicalPaddingSeed.data n a).code=(IntegralMixedCanonicalPaddingSeed.data n b).code:=
 (IntegralMixedCanonicalPaddingSeed.data_code n a).trans (IntegralMixedCanonicalPaddingSeed.data_code n b).symm
example (n b : ℕ) : IntegralMixedCausalUnitRecordBits.physical n b (IntegralMixedChronologicalFrameCode.code n [] 0 0)=
 IntegralMixedCanonicalPaddingSeed.rule n:=IntegralMixedCanonicalPaddingSeed.physical n b
example (n b : ℕ) : (IntegralMixedCanonicalPaddingSeed.data n b).rows 0=IntegralMixedCausalRowConstructor.Row.single none:=rfl
example : (fun _ : List Bool=>IntegralMixedChronologicalFrameCode.code 3 [] 0 0)∈FP:=
 IntegralMixedChronologicalFrameCode.code_FP (UnaryFn.const 3) (BinaryFn.const 0) (BinaryFn.const 0) (constFn_mem_FP [])
private def params : Parameters where
 cap _:=12
 width _:=1
 ambient _:=1
 sourceWidth _:=1
 degree _:=2
 height _:=0
 modulusBound _:=2
private def rawRoot:=pair [] (pair (WordList.encode
 ([[true],[false]]++List.replicate 2 (IntegralMixedChronologicalFrameCode.code 1 [] 0 0)++[[false,true,false]])) [])
private theorem raw_table : IntegralMixedCausalRecordPlanBits.records rawRoot=WordList.encode
 ([[true],[false]]++List.replicate 2 (IntegralMixedChronologicalFrameCode.code (params.ambient rawRoot) [] 0 0)++[[false,true,false]]):=by
 simp only [rawRoot,IntegralMixedCausalRecordPlanBits.records,pairFst_pair,pairSnd_pair,params]
example : IntegralMixedCausalRecordPlanBits.code rawRoot 2=IntegralMixedChronologicalFrameCode.code 1 [] 0 0:=
 IntegralMixedSourceIntegerPaddingPrefix.padding_code params rawRoot [[true],[false]] 2 [false,true,false] raw_table 0 (by decide)
example : IntegralMixedCausalRecordPlanBits.code rawRoot 3=IntegralMixedChronologicalFrameCode.code 1 [] 0 0:=
 IntegralMixedSourceIntegerPaddingPrefix.padding_code params rawRoot [[true],[false]] 2 [false,true,false] raw_table 1 (by decide)
example : IntegralMixedCausalRecordPlanBits.code rawRoot 4=[false,true,false]:=by
 simp only [IntegralMixedCausalRecordPlanBits.code,raw_table,WordList.get_encode]
 rfl
#print axioms IntegralMixedCanonicalPaddingSeed.data_code
#print axioms IntegralMixedCanonicalPaddingSeed.physical
#print axioms IntegralMixedCanonicalPaddingSeed.command
#print axioms IntegralMixedCanonicalPaddingSeed.instantiate
#print axioms IntegralMixedSourceIntegerPaddingPrefix.padding_code
#print axioms IntegralMixedSourceIntegerPaddingPrefix.prefix_bound
#print axioms IntegralMixedSourceIntegerPaddingPrefix.instruction_at
#print axioms IntegralMixedSourceIntegerPaddingPrefix.past_padding
#print axioms IntegralMixedCanonicalPadding.original_rule
#print axioms IntegralMixedCanonicalPadding.step
#print axioms IntegralMixedCanonicalPadding.run_exists
#print axioms IntegralMixedCanonicalPadding.run_realizes
#print axioms IntegralMixedSourceIntegerPaddingRealization.realizes_at_key_iff
#print axioms IntegralMixedSourceIntegerPaddingRealization.runAt_realizes
#print axioms IntegralMixedSourceIntegerPaddingRealization.canonical_realizes
#print axioms parent_realized
end ActualPaddingRegression
end
end RoadmapInternalPadding

namespace RoadmapInternalOptionalPairs
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints Set
open scoped Classical
noncomputable section
namespace ChronologicalOptionalPairRegression
private def d : Descriptor 4 5:=⟨[0,3],by decide⟩
private def u : Fin 5:=4
private def v : Fin 5:=1
example : IntegralMixedRoadmapEndpointSyntax.field
    (IntegralMixedRoadmapEndpointSyntax.retainedSpec d u) 1=0:=
  IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d u
example : IntegralMixedRoadmapEndpointSyntax.field
    (IntegralMixedRoadmapEndpointSyntax.retainedSpec d v) 1=3:=
  IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d v
example : IntegralMixedRoadmapEndpointSyntax.Good 4 12 9 5 6
    (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.retainedSpec d v):=
  IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d v 12 9 6

-- The newly appended LEFT producer5 is not OLD: a retained RIGHT cannot use it.
example : ¬IntegralMixedRoadmapEndpointSyntax.Good 4 12 9 5 6
    (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.spec 0 5 0 0 0 0):=by
  intro H
  rcases H.2 with H|H|H
  · have HH:=H.2.1
    rw [IntegralMixedRoadmapEndpointSyntax.field_spec_1] at HH
    omega
  · have HH:=H.1
    rw [IntegralMixedRoadmapEndpointSyntax.field_spec_0] at HH
    omega
  · have HH:=H.1
    rw [IntegralMixedRoadmapEndpointSyntax.field_spec_0] at HH
    omega

-- A fresh RIGHT does use actual current producer6 while its oldBirth stays5.
example : IntegralMixedRoadmapEndpointSyntax.Good 4 12 9 5 6
    (IntegralMixedChronologicalFrameCode.labels d) (IntegralMixedRoadmapEndpointSyntax.criticalSpec d.retain):=by
  have H:=IntegralMixedRoadmapEndpointSyntax.criticalSpec_good d.retain 12 9 6
  have HK : IntegralMixedRoadmapEndpointSyntax.field
      (IntegralMixedRoadmapEndpointSyntax.criticalSpec d.retain) 0≠0:=by
    norm_num [IntegralMixedRoadmapEndpointSyntax.criticalSpec]
  simpa only [IntegralMixedRoadmapEndpointSyntax.labels_retain] using H.fresh_oldBirth HK 5
example : IntegralMixedRoadmapEndpointSyntax.field
    (IntegralMixedRoadmapEndpointSyntax.criticalSpec d.retain) 1=6:=
  IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _
example : IntegralMixedChronologicalFrameCode.labels (retainMany d 2)=IntegralMixedChronologicalFrameCode.labels d:=
  retainMany_labels d 2
example : ((retainMany d 2).reference ⟨0,by decide⟩).val=6 ∧
    ((retainMany d 2).reference ⟨1,by decide⟩).val=3:=by decide
example : 7-1-(5 : ℕ)=1 ∧ 7-1-(6 : ℕ)=0:=by decide

section ActualPair
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d0 : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

example (i j : Fin m) (R : NativePair x d0 z φ values (.retained i) (.retained j) hn hcap) :
    R.result.commands.length=0:=R.count
example (i : Fin m) (b : ℝ) (R : NativePair x d0 z φ values (.retained i) (.fresh b) hn hcap) :
    R.result.commands.length=1:=R.count
example (a : ℝ) (j : Fin m) (R : NativePair x d0 z φ values (.fresh a) (.retained j) hn hcap) :
    R.result.commands.length=1:=R.count
example (a b : ℝ) (R : NativePair x d0 z φ values (.fresh a) (.fresh b) hn hcap) :
    R.result.commands.length=2:=R.count
example (i : Fin m) (b : ℝ) (R : NativePair x d0 z φ values (.retained i) (.fresh b) hn hcap) :
    R.result.left.val=i.val+1:=by
  have HC:=R.count
  have HI:=R.left_reference
  have HP:=R.left_producer
  have HB:=i.isLt
  change R.result.commands.length=1 at HC
  change IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1=m-1-i.val at HP
  omega
example (a : ℝ) (j : Fin m) (R : NativePair x d0 z φ values (.fresh a) (.retained j) hn hcap) :
    R.result.right.val=j.val+1:=by
  have HC:=R.count
  have HI:=R.right_reference
  have HP:=R.right_producer
  have HB:=j.isLt
  change R.result.commands.length=1 at HC
  change IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1=m-1-j.val at HP
  omega
example (a b : ℝ) (R : NativePair x d0 z φ values (.fresh a) (.fresh b) hn hcap) :
    R.result.left.val=1 ∧ R.result.right.val=0:=by
  have HC:=R.count
  have HI:=R.left_reference
  have HJ:=R.right_reference
  have HP:=R.left_producer
  have HQ:=R.right_producer
  change R.result.commands.length=2 at HC
  change IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1=m at HP
  change IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1=m+1 at HQ
  omega
example (a b : ℝ) (R : NativePair x d0 z φ values (.fresh a) (.fresh b) hn hcap) :
    R.result.frame=d0.retain.retain.frame:=by
  have HF:=R.frame
  have HC : R.result.commands.length=2:=R.count
  rw [HC] at HF
  exact HF
example (left right : Endpoint m) (R : NativePair x d0 z φ values left right hn hcap) :
    R.result.codes.reverse=IntegralMixedRoadmapEndpointSyntax.codes n
      (IntegralMixedChronologicalFrameCode.labels d0) R.leftSpec++
        IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d0) R.rightSpec:=R.codes
end ActualPair

#print axioms IntegralMixedRoadmapEndpointSyntax.retainedSpec_good
#print axioms IntegralMixedRoadmapEndpointSyntax.Good.fresh_oldBirth
#print axioms retainMany_labels
#print axioms Fresh.code_length
#print axioms joint_endpoint_at
#print axioms fresh_after
#print axioms optional_pair
#print axioms optional_pair_sweep
#print axioms NativePair.native_count
#print axioms NativePair.word
#print axioms NativePair.reference
end ChronologicalOptionalPairRegression
end
end RoadmapInternalOptionalPairs
