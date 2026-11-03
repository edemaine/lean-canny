import LeanCanny.Algebra.IntegralMixedIntegerRealization
import LeanCanny.Algebra.IntegralMixedNumericalSweepBad
import LeanCanny.Connectivity
import LeanCanny.Connectivity.ComponentSlabAnchorEndpoints
import LeanCanny.Encoding.IntegralMixedPhysicalCutOrderedInterval
import LeanCanny.Geometry.IntegralMixedJointBranchEndpointRecord
import LeanCanny.Geometry.IntegralMixedJointMidpointSound
import LeanCanny.Geometry.IntegralMixedOptionalJointSlab

/-! Concrete regressions for retained endpoints, independent frozen sweeps,
literal physical branch attachments and same-context ordered intervals. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapNumericalSweep
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
open LeanCanny.Algebra Polynomial
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
noncomputable section
namespace NumericalSweepRegression

def signedScales : Fin 2→ℤ:=![-2,3]
def otherScales : Fin 2→ℤ:=![5,-7]
def heights : Fin 2→Polynomial ℝ:=![C (-4)+C (-2)*X,C 99]
def otherHeights : Fin 2→Polynomial ℝ:=![C 10+C 5*X,X^7+1]

example : CoordinateFrozenCriticalElimination.denominator signedScales=-6:=by decide
example : CoordinateFrozenCriticalElimination.denominator otherScales=-35:=by decide

example : CoordinateFrozenCriticalElimination.numerators signedScales heights 0=C (-12)+C (-6)*X:=by
  have HE : CommonIntegerDenominator.denominator (Finset.univ.erase (0:Fin 2)) signedScales=3:=by decide
  rw [CoordinateFrozenCriticalElimination.numerators,dite_eq_left (show 0<2 from by decide)]
  change (C (-4)+C (-2)*X)*(CommonIntegerDenominator.denominator (Finset.univ.erase (0:Fin 2)) signedScales:Polynomial ℝ)=_
  rw [HE,←C_eq_intCast]
  calc
    _=C ((-4:ℝ)*3)+C ((-2:ℝ)*3)*X:=by simp only [C_mul];ring_nf
    _=_:=by norm_num

theorem same_frozen (i : ℕ) (hi : i<1) :
    ClearedCoordinateNormalization.normalized signedScales heights i=
      ClearedCoordinateNormalization.normalized otherScales otherHeights i:=by
  have HE : i=0:=by omega
  subst i
  norm_num [ClearedCoordinateNormalization.normalized,signedScales,otherScales,heights,otherHeights,
    mul_add,←mul_assoc,←C_mul]

example (p : MvPolynomial (Fin 2) (Polynomial ℝ)) (a : Polynomial ℝ) :
    ClearedCoordinateCritical.annihilator 4 1
        (ClearedCoordinateNormalization.normalized signedScales heights) 1 (by decide) p a (0:Fin 1) 0=
      ClearedCoordinateCritical.annihilator 4 1
        (ClearedCoordinateNormalization.normalized otherScales otherHeights) 1 (by decide) p a (0:Fin 1) 0 :=by
  exact ClearedCoordinateFrozenCongruence.annihilator 4 1 _ _ 1 rfl same_frozen p a 0 0

example : ClearedCoordinateNormalization.normalized signedScales heights 2=0:=by
  rfl

def rule : Rule 2 where
  critical:={
    offset:=2
    objective:=0
    coordinate:=0
    scales:=fun _=>1
    scales_ne_zero:=fun _=>one_ne_zero
    heights:=fun _=>.reference 0}
  height:=0
  height_frozen:=by decide
  slope:=1
  slope_ne_zero:=one_ne_zero

def alternate : Rule 2 where
  critical:={
    offset:=2
    objective:=0
    coordinate:=2
    scales:=![1,2,-3]
    scales_ne_zero:=fun i=>by fin_cases i <;> norm_num
    heights:=fun i=>if i=1 then .scale 2 (.reference 1) else .reference 1}
  height:=0
  height_frozen:=by decide
  slope:=-11
  slope_ne_zero:=by decide

-- Different bank lengths, shifted references and a doubled frozen row.
theorem different_banks : ∀i,i<rule.critical.offset.val→
    IntegralMixedNumericalSweep.normalized rule (![7]:Fin 1→ℝ) i=
      IntegralMixedNumericalSweep.normalized alternate (![99,7]:Fin 2→ℝ) i :=by
  apply IntegralMixedNumericalSweep.normalized_frozen_eq_of_levels rule alternate rfl rfl
  intro i hi
  have HV : i.val=0 ∨ i.val=1:=by change i.val<2 at hi;omega
  rcases HV with hi|hi
  · have HE : i=0:=Fin.ext hi
    subst i
    norm_num [rule,alternate,AffineExpr.evaluate]
  · have HE : i=1:=Fin.ext hi
    subst i
    norm_num [rule,alternate,AffineExpr.evaluate]

example {S B T C : ℕ} {P : SpatialSource 2} {ι κ : Type}
    (x : State P S B 1 ι) (hm : 1≤S) (y : State P T C 2 κ) (hl : 2≤T)
    (hr : rule.slope=commonDenominator x) (hs : alternate.slope=commonDenominator y)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=(![7]:Fin 1→ℝ) i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=(![99,7]:Fin 2→ℝ) i)
    (old : IntegralMixedRelativeCuts.Choices x hm rule φ)
    (next : IntegralMixedRelativeCuts.Choices y hl alternate ψ) (t : ℝ) :
    t∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad y hl alternate ψ next ↔
      t∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm rule φ old :=by
  exact IntegralMixedNumericalSweep.bad_iff x hm y hl rule alternate hr hs rfl rfl φ ψ
    (![7]:Fin 1→ℝ) (![99,7]:Fin 2→ℝ) H K different_banks old next t

end NumericalSweepRegression
#print axioms ClearedCoordinateNormalization.annihilator
#print axioms ClearedCoordinateFrozenCongruence.annihilator
#print axioms IntegralMixedNumericalSweep.normalized_eq
#print axioms IntegralMixedNumericalSweep.selected_eq
#print axioms IntegralMixedNumericalSweep.selected_row_eq
#print axioms IntegralMixedNumericalSweep.normalized_frozen_eq_of_levels
#print axioms IntegralMixedNumericalSweep.coordinate_congr
#print axioms IntegralMixedNumericalSweep.row_congr
#print axioms IntegralMixedNumericalSweep.selected_scaling
#print axioms IntegralMixedNumericalSweep.row_scaling
#print axioms IntegralMixedNumericalSweep.coefficient_zero_iff
#print axioms IntegralMixedNumericalSweep.principal_zero_iff
#print axioms IntegralMixedNumericalSweep.value_trailing_degree
#print axioms IntegralMixedNumericalSweep.value_trailing_zero
#print axioms IntegralMixedNumericalSweep.bad_iff
#print axioms IntegralMixedNumericalSweep.bad_iff_of_levels
end
end RoadmapNumericalSweep

namespace RoadmapOptionalEndpoints
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OptionalEndpointRegression
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
private def left (lf rf : Bool) : Endpoint 4:=if lf then .fresh (-1) else .retained (if rf then 2 else 0)
private def right (lf rf : Bool) : Endpoint 4:=if rf then .fresh 1 else .retained (if lf then 3 else 1)
private theorem mid_zero (lf rf : Bool) : ((left lf rf).value vals+(right lf rf).value vals)/2=0:=by
 cases lf <;> cases rf <;> norm_num [left,right,Endpoint.value,vals]

private def Scenario (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) (lf rf : Bool) : Prop:=
 ∃ z : Index (Fin 0) (leaves B)→ℝ,∃ φ : (before B hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
 ∃ R : PairResult (before B hc) F z φ vals ((left lf rf).value vals) ((right lf rf).value vals) (by decide) hc,
 ∃ hg' : (1:Fin 2)∉insert 0 R.frame.frozen,∃ hj' : (1:Fin 2)∉insert 0 R.frame.frozen,
 let d:=referencedMidpointData R.atomic 0 R.left R.right 1 1 hg' hj'
 let cs:=(.critical d.rule : Command P B)::R.commands
 ∃ room : 4+cs.length≤6+1,
 cs.length=(left lf rf).freshCount+(right lf rf).freshCount+1 ∧
 Decodes (before B hc) (by decide) hc cs room (d.code::R.codes) ∧
 (WordList.encode (d.code::R.codes).reverse).length≤byteBudget 1 4 B ∧
 let born:=continueRun (before B hc) cs room
 ∃ y : Index (Index (Fin 0) (leaves B)) cs→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
 (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
 ψ (born.bank.numerator 0)/(born.bank.denominator 0:ℝ)=1 ∧
 ψ (born.bank.numerator R.left.succ)/(born.bank.denominator R.left.succ:ℝ)=(left lf rf).value vals ∧
 ψ (born.bank.numerator R.right.succ)/(born.bank.denominator R.right.succ:ℝ)=(right lf rf).value vals

private theorem scenario (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B)
 (lf rf : Bool) : Scenario B hc lf rf :=by
 obtain ⟨z,φ,hz,hφ,H⟩:=before_realized B hc
 obtain ⟨old⟩:=IntegralMixedRelativeCuts.exists_choices (before B hc) (by decide)
   (cutRule (before B hc) F 0 1 hg) φ
 have HL : (left lf rf).Allowed (jointEndpointSet (before B hc) (by decide) φ F 0 1 hg vals old):=by
   cases lf
   · trivial
   · exact Or.inr (endpoint vals (-1) (Or.inr rfl))
 have HR : (right lf rf).Allowed (jointEndpointSet (before B hc) (by decide) φ F 0 1 hg vals old):=by
   cases rf
   · trivial
   · exact Or.inr (endpoint vals 1 (Or.inl rfl))
 have HM : (![0,1]:Fin 2→ℝ)∈slice P F vals:=by
   refine ⟨?_,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
   rw [evalP]
   norm_num
 obtain ⟨R,_,hg',hj',room,Hcount,_,_,HD,Hbytes,y,ψ,hy,_,_,_,_,Hvalues,Hleft,Hright⟩:=
   realize_slab (before B hc) (by decide) (by decide) (by decide) 0 rfl hc F HF HA HP 0 1 1 rfl hh hg hg
     z hz φ hφ vals H old (left lf rf) (right lf rf) HL HR ![0,1] HM
     (by rw [mid_zero]; norm_num) (by intro i hi; fin_cases i <;> simp_all [F])
 refine ⟨z,φ,R,hg',hj',room,Hcount,HD,Hbytes,y,ψ,hy,?_,Hleft,Hright⟩
 simpa using Hvalues 0

example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc false false:=scenario B hc false false
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc true false:=scenario B hc true false
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc false true:=scenario B hc false true
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : Scenario B hc true true:=scenario B hc true true
example : (left false false).value vals=-(1/2) ∧ (right false false).value vals=1/2:=by constructor <;> rfl
example (B : ℕ) (hc : IntegralMixedExceptionalBounds.auxiliaryCap 2 P.degree≤2^B) : commonDenominator (before B hc)=(-24):=by
 unfold before leaves
 simp only [run]
 rw [command_commonDenominator,command_commonDenominator,command_commonDenominator,command_commonDenominator]
 change (C (-2)*X-C 1 : Polynomial ℤ).leadingCoeff*
   ((C 2*X-C 1 : Polynomial ℤ).leadingCoeff*
     ((C 2*X-C (-2) : Polynomial ℤ).leadingCoeff*
       ((C 3*X-C 3 : Polynomial ℤ).leadingCoeff*commonDenominator (initial B hc))))=(-24)
 rw [poly_leading (-2) 1 (by decide),poly_leading 2 1 (by decide),
   poly_leading 2 (-2) (by decide),poly_leading 3 3 (by decide)]
 norm_num [initial,commonDenominator,CommonIntegerDenominator.denominator,IntegralMixedHistory.base]
example : ((-24:ℤ)%6)=0:=by decide
example : UnaryFn (fun q=>byteBudget q.length (Nat.fromBitsLE q) q.length):=
 byteBudget_unary (UnaryFn.length id_mem_FP) (BinaryFn.fromBits id_mem_FP) (UnaryFn.length id_mem_FP)
example : (-(1/2):ℝ)∉realCriticalValues P (line F 0) vals 0 ∧
 (1/2:ℝ)∉realCriticalValues P (line F 0) vals 0 :=by
 have HN (a : ℝ) (ha : a=-(1/2) ∨ a=1/2) : a∉realCriticalValues P (line F 0) vals 0:=by
   intro Hbad
   obtain ⟨y,HY,H0,HG⟩:=(line_realCriticalValues_iff P F vals 0 hh HF a).mp Hbad
   have H1:=HG 1 (Finset.notMem_empty _) (by decide)
   rw [gradP] at H1
   have HZ : y 1=0:=by
     have HPow : y 1^17=0:=(mul_eq_zero.mp H1).resolve_left (by norm_num)
     exact (pow_eq_zero_iff (by decide : (17:ℕ)≠0)).mp HPow
   have HS:=HY.1
   rw [evalP,H0,HZ] at HS
   rcases ha with rfl|rfl <;> norm_num at HS
 exact ⟨HN _ (Or.inl rfl),HN _ (Or.inr rfl)⟩
#print axioms referencedMidpointFrame_slice
#print axioms referencedEndpointFrame_slice
#print axioms referencedEndpointFrame_atomic
#print axioms FreeNormal.referencedEndpointFrame
#print axioms PrefixFrozen.referencedEndpointFrame
#print axioms referenced_midpoint_realize
#print axioms referenced_midpoint_sound
#print axioms realize_pair
#print axioms realize_slab
#print axioms byteBudget_unary
#print axioms physical_columns_le
end OptionalEndpointRegression
end
end RoadmapOptionalEndpoints

namespace RoadmapBranchEndpoint
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor Polynomial
open scoped Classical
noncomputable section
namespace JointMidpointEndpointRegression
private def initial (n : ℕ) : Frame n :=
  {frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0}
private def circle : SpatialSource 1 :=
  {low:=MvPolynomial.C (-4),leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_C]; decide,leading_ne_zero:=by decide}
private def values : Fin 0→ℝ:=Fin.elim0
private def endpoint (right : Bool) : Fin 2→ℝ:=Fin.cons (if right then 2 else -2) (fun _=>0)
private theorem circle_root (right : Bool) :
    (FermatCriticalHomogenization.polynomial circle.low circle.leading circle.degree).eval₂
      (Int.castRingHom ℝ) (endpoint right)=0 :=by
  cases right <;> norm_num [circle,endpoint,FermatCriticalHomogenization.polynomial,
    MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]

-- The head99 is neither endpoint. The left and right rows must read2/1.
example : endpoint false∈slice circle (jointEndpointFrame (AtomicRows.initial 1 0) 0 false)
    (Fin.cons 99 (Fin.cons 2 (Fin.cons (-2) values))) :=by
  rw [jointEndpointFrame_slice (AtomicRows.initial 1 0) 0 (by simp) false values 99 (-2) 2]
  refine ⟨⟨circle_root false,?_⟩,rfl⟩
  intro i hi
  exact False.elim (Finset.notMem_empty i hi)
example : endpoint true∈slice circle (jointEndpointFrame (AtomicRows.initial 1 0) 0 true)
    (Fin.cons 99 (Fin.cons 2 (Fin.cons (-2) values))) :=by
  rw [jointEndpointFrame_slice (AtomicRows.initial 1 0) 0 (by simp) true values 99 (-2) 2]
  refine ⟨⟨circle_root true,?_⟩,rfl⟩
  intro i hi
  exact False.elim (Finset.notMem_empty i hi)
example : (jointEndpointIndex 0 false).val=2 ∧ (jointEndpointIndex 0 true).val=1 :=by
  decide

private def oldFrame : Frame 2 :=
  {frozen:={0},scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,
    heights:=fun i=>if i=0 then .reference 0 else .constant 0}
private theorem oldAtomic : AtomicRows oldFrame 1 :=by
  constructor
  · intro i
    rfl
  · intro i
    by_cases hi : i=0
    · exact ⟨some 0,by subst i; rfl⟩
    · exact ⟨none,by simp only [oldFrame,hi,ite_false,Atom.value]⟩
example : (jointEndpointFrame oldAtomic 1 false).heights 0=.reference 3 :=by
  rw [jointEndpointFrame_old_height oldAtomic 1 0 false (by decide)]
  rfl
example : (jointEndpointFrame oldAtomic 1 false).heights 1=.reference 2 :=
  jointEndpointFrame_height oldAtomic 1 false
example : (jointEndpointFrame oldAtomic 1 true).heights 1=.reference 1 :=
  jointEndpointFrame_height oldAtomic 1 true

-- The circle's endpoint fiber is y²=0 and is singular as a frozen fiber.
example (y : ℝ) :
    (FermatCriticalHomogenization.polynomial circle.low circle.leading circle.degree).eval₂
      (Int.castRingHom ℝ) (Fin.cons (2 : ℝ) (fun _=>y))=y^2 :=by
  norm_num [circle,FermatCriticalHomogenization.polynomial,
    MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
example : Polynomial.IsRoot ((Polynomial.X:ℝ[X])^2) 0 ∧
    (Polynomial.derivative ((Polynomial.X:ℝ[X])^2)).eval 0=0 :=by simp [Polynomial.IsRoot]

#check joint_midpoint_block_branch
#check selected_endpoint_real_extend
#check branch_endpoint_real_extend
#print axioms source_gradients_anchor_sweep
#print axioms midpoint_point_anchors_sweep
#print axioms midpoint_block_anchors_sweep
#print axioms selected_point_endpoint
#print axioms joint_midpoint_block_branch
#print axioms jointEndpointFrame_height
#print axioms jointEndpointFrame_old_height
#print axioms jointEndpointFrame_slice
#print axioms jointEndpointFrame_atomic
#print axioms PrefixFrozen.jointEndpointFrame
#print axioms FreeNormal.jointEndpointFrame
#print axioms selected_endpoint_child_point
#print axioms selected_endpoint_critical_height
#print axioms selected_endpoint_real_extend
#print axioms branch_endpoint_real_extend
end JointMidpointEndpointRegression
end
end RoadmapBranchEndpoint

namespace RoadmapOrderedInterval
set_option maxHeartbeats 200000
set_option warningAsError true
set_option relaxedAutoImplicit false
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR Polynomial
open scoped Classical
namespace PhysicalCutLocalOrderedRegression
private def n (_ : List Bool) :=0
private def t (_ : List Bool) : Term:=.const 0
private def R (_ : List Bool) :=0
private theorem hn : UnaryFn n:=UnaryFn.const 0
private theorem ht : (fun q=>(t q).toData.toBits)∈FP:=by
  simpa only [t] using (constFn_mem_FP (Term.const (0:ℤ)).toData.toBits)
private theorem ha : ∀q,(t q).arity≤n q:=by intro q;change 0≤0;omega
private theorem hR : BinaryFn R:=BinaryFn.const 0
example : SpaceDecider (IntegralMixedPhysicalCutOrderedInterval.language hn ht ha hR false):=
  IntegralMixedPhysicalCutOrderedInterval.decider hn ht ha hR false
example : SpaceDecider (IntegralMixedPhysicalCutOrderedInterval.language hn ht ha hR true):=
  IntegralMixedPhysicalCutOrderedInterval.decider hn ht ha hR true
example : SpaceFunction (fun z=>[decide (IntegralMixedPhysicalCutLocalGuards.Guards hn ht ha hR false z)]):=
  IntegralMixedPhysicalCutLocalGuards.evaluator hn ht ha hR false
example (z : List Bool)
    (hbad : IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR false (pairFst z)≤
      IntegralMixedPhysicalCutOpenInterval.selected false (pairFst z)) :
    z∉IntegralMixedPhysicalCutOrderedInterval.language hn ht ha hR false :=
  IntegralMixedPhysicalCutOrderedInterval.reject_left hn ht ha hR false z hbad
example : IntegralMixedPhysicalCutOpenInterval.selected true
    (pairFst (IntegralMixedPhysicalCutOrderedInterval.packet [true,false] [true,true]
      (BinaryNatCode.encode 2) (BinaryNatCode.encode 5) [false,true]))=5 :=by
  rw [IntegralMixedPhysicalCutOrderedInterval.packet_selected]
  simp only [ite_true,BinaryNatCode.encode,Nat.fromBitsLE_bits]
example : pairSnd (IntegralMixedPhysicalCutOrderedInterval.packet [true,false] [true,true]
    (BinaryNatCode.encode 2) (BinaryNatCode.encode 5) [false,true])=[false,true] :=
  IntegralMixedPhysicalCutOrderedInterval.packet_vertex _ _ _ _ _
example (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w)
    (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (pair q w))
    (heq : IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha hR false false q w hv
      (IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha hR false q w hb)=
      IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha hR false true q w hv
      (IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha hR false q w hb)) :
    pair q w∉IntegralMixedPhysicalCutOrderedInterval.language hn ht ha hR false :=
  IntegralMixedPhysicalCutOrderedInterval.reject_unordered hn ht ha hR false q w hv hb heq.symm.le
example (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR true) q w)
    (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR true (pair q w))
    (hrev : IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha hR true true q w hv
      (IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha hR true q w hb)<
      IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha hR true false q w hv
      (IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha hR true q w hb)) :
    pair q w∉IntegralMixedPhysicalCutOrderedInterval.language hn ht ha hR true :=
  IntegralMixedPhysicalCutOrderedInterval.reject_unordered hn ht ha hR true q w hv hb hrev.le
example : SignType.sign (((-6:ℝ)^2)*(2-5))=(-1:SignType) :=by norm_num
example : ∀ r : ℝ, (C (-6:ℝ)).eval r = 0 → r ∉ Set.Ioo (0:ℝ) 1 :=
  IntegralFramedFullCutOpenInterval.constant_empty _ (by norm_num) (by simp) 0 1
noncomputable def p : ℝ[X]:=C (-3)*(X-C 0)^2*(X-C 1)^2
example : RealRootOpenIntervalOrdered.value p 4 0 36 true=RealRootOpenIntervalOrdered.value p 4 1 36 false :=by
  apply (RealRootOpenIntervalOrdered.empty_iff p 4 (by decide) (by unfold p;compute_degree!)
    (by norm_num : (0:ℝ)<1) 36 (by norm_num)).mp
  intro r hr
  have HE : r=0 ∨ r=1:=by
    simpa [p,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
      mul_eq_zero,sub_eq_zero] using hr
  rcases HE with rfl|rfl <;> norm_num
noncomputable def s : ℝ[X]:=p*(X-C (1/2))^2
example : RealRootOpenIntervalOrdered.value s 6 0 36 true≠RealRootOpenIntervalOrdered.value s 6 1 36 false :=by
  intro HE
  have HN:=(RealRootOpenIntervalOrdered.empty_iff s 6 (by decide) (by unfold s p;compute_degree!)
    (by norm_num : (0:ℝ)<1) 36 (by norm_num)).mpr HE
  exact HN (1/2) (by norm_num [s,p]) (by norm_num)
#print axioms IntegralFramedPhysicalBankOrderSource.access
#print axioms IntegralFramedPhysicalBankOrderSource.polynomial_eval
#print axioms IntegralFramedPhysicalBankOrderSource.evaluator
#print axioms IntegralFramedPhysicalBankOrderSource.packet
#print axioms IntegralMixedPhysicalCutLocalGuards.evaluator
#print axioms IntegralMixedPhysicalCutLocalGuards.sign_packet
#print axioms IntegralMixedPhysicalCutLocalInterpretation.active
#print axioms IntegralMixedPhysicalCutLocalInterpretation.coefficient_evaluation
#print axioms IntegralMixedPhysicalCutLocalInterpretation.coefficient_guards
#print axioms IntegralMixedPhysicalCutLocalInterpretation.interpreted_guards
#print axioms IntegralMixedPhysicalCutOrderedInterval.packet_FP
#print axioms IntegralMixedPhysicalCutOrderedInterval.packet_selected
#print axioms IntegralMixedPhysicalCutOrderedInterval.order_evaluator
#print axioms IntegralMixedPhysicalCutOrderedInterval.decider
#print axioms IntegralMixedPhysicalCutOrderedInterval.mem_PSPACE
#print axioms IntegralMixedPhysicalCutOrderedInterval.order_iff
#print axioms IntegralMixedPhysicalCutOrderedInterval.reject_unordered
#print axioms IntegralMixedPhysicalCutOrderedInterval.interpreted_empty_iff
end PhysicalCutLocalOrderedRegression
end RoadmapOrderedInterval

namespace RoadmapAnchorLimits
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
#print axioms LeanCanny.Connectivity.ComponentSlabCover.InteriorData.piece_eq_of_overlap
#print axioms LeanCanny.Connectivity.ComponentSlabCover.InteriorData.left_endpoints_joined
#print axioms LeanCanny.Connectivity.ComponentSlabCover.InteriorData.right_endpoints_joined
end RoadmapAnchorLimits
