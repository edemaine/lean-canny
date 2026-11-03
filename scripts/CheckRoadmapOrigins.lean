import LeanCanny.Connectivity
import LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow
import LeanCanny.Connectivity.IntegralMixedSpecializedSectionWordComparison
import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutRaw
import LeanCanny.Encoding.IntegralMixedPhysicalZeroTarskiSelected
import LeanCanny.Encoding.IntegralMixedReservedCutPlanning
import LeanCanny.Encoding.IntegralMixedReservedCutVertex
import LeanCanny.Encoding.IntegralMixedReservedProbePosition
import LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode
import LeanCanny.Geometry.IntegralMixedChronologicalMeanCutSpecialization
import LeanCanny.Geometry.IntegralMixedMatchedSlabNearEdge

/-! Native midpoint rank windows, literal cut records and local path soundness.
The whole implicit graph/path theorem remains separate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace RoadmapOriginsNativeWindows
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation Polynomial
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace ZeroTarskiRegression

private noncomputable def p : Polynomial (MvPolynomial (Fin 2) ℤ) :=
  X^2-C (MvPolynomial.X 1)+C (MvPolynomial.X 0)*X
private noncomputable def source (_ : List Bool) :=p

-- Zero specialization removes the creating parameter and keeps the old raw coordinate.
example (z : Fin 1→ℝ) (δ ε : ℝ) :
    ((FixedWidthBivariateZeroLiftBits.head (fun _=>1) source []).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z))))=X^2-C (z 0) :=by
  rw [FixedWidthBivariateZeroLiftBits.selected (fun _=>1) source [] z δ ε]
  simp [source,p]

-- Neither dummy parameter leaks into the specialized head, for any raw tuple.
example (z : Fin 1→ℝ) (δ ε δ' ε' : ℝ) :
    ((FixedWidthBivariateZeroLiftBits.head (fun _=>1) source []).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z))))=
    ((FixedWidthBivariateZeroLiftBits.head (fun _=>1) source []).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ' (Fin.cons ε' z)))) :=by
  rw [FixedWidthBivariateZeroLiftBits.selected (fun _=>1) source [] z δ ε,
    FixedWidthBivariateZeroLiftBits.selected (fun _=>1) source [] z δ' ε']

-- Epsilon is retained on slot one, while delta is unused.
example (z : Fin 1→ℝ) (δ ε : ℝ) :
    ((FixedWidthBivariateZeroLiftBits.epsilonHead (fun _=>1) source []).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z))))=
        X^2-C (z 0)+C ε*X :=by
  rw [FixedWidthBivariateZeroLiftBits.epsilon_selected (fun _=>1) source [] z δ ε]
  simp [source,p]

-- The raw coefficient can be negative and is retained without any sign restriction.
example : ((FixedWidthBivariateZeroLiftBits.head (fun _=>1) source []).map
    (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons 99 (Fin.cons (-7) (fun _=>-4)))))=X^2+C 4 :=by
  rw [FixedWidthBivariateZeroLiftBits.selected (fun _=>1) source [] (fun _=>-4) 99 (-7)]
  norm_num [source,p]

private noncomputable def roots2 : ℝ[X]:=(X-C (-1))*(X-C 1)
private theorem roots2_degree : roots2.natDegree=2 :=by
  rw [roots2,Polynomial.natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)]
  simp only [Polynomial.natDegree_X_sub_C]
private theorem roots2_roots : roots2.roots.toFinset={-1,1} :=by
  rw [roots2,Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C,Polynomial.roots_X_sub_C]
  simp

-- Keeping epsilon prevents the seed-degree drop present in the exact q=X query.
example : (PseudoRemainder.seed (roots2.map Polynomial.C)
    ((WindowTarskiSeedDegree.affineQuery (X-C (0 : ℝ)) 1)^1) 2 4).natDegree=1 :=
  WindowTarskiSeedDegree.ternary_seed_degree roots2 (X-C 0) 1 one_ne_zero (1 : Fin 3)
    2 (by decide) roots2_degree (Polynomial.natDegree_X_sub_C_le _)

example (negative : Bool) (e : Fin 3) :
    (PseudoRemainder.seed (IntegralMixedSelectedCoordinateWindowDegree.head (roots2.map Polynomial.C))
      (IntegralMixedSelectedCoordinateWindowDegree.query 0 ((-6 : ℝ)^2) negative e) 2 4).natDegree=1 :=by
  exact IntegralMixedSelectedCoordinateWindowDegree.seed_degree (roots2.map Polynomial.C) 2 (by decide)
    ((Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective _).trans roots2_degree)
    0 ((-6 : ℝ)^2) (by norm_num) negative e

example : LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.Test roots2 2 1 ((-6 : ℝ)^2) 1 :=by
  rw [LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.test_iff roots2 2 (by decide) roots2_degree
    1 ((-6 : ℝ)^2) (by norm_num),roots2_roots]
  norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : ¬LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.Test roots2 2 1 36 0 :=by
  rw [LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.test_iff roots2 2 (by decide) roots2_degree
    1 36 (by norm_num),roots2_roots]
  norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example (code : ℕ) : ¬LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.Test roots2 2 0 36 code :=by
  rw [LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.test_iff roots2 2 (by decide) roots2_degree
    0 36 (by norm_num),roots2_roots]
  simp

-- Five-statistic packet orientation: false is the lower window, true the upper.
example : OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack (BinaryNatCode.encode 1)
    (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode 0)
    (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode (-2))) :=by
  rw [OrderedWindowStatisticBits.packet]
  norm_num
example : ¬OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack (BinaryNatCode.encode 0)
    (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode 0)
    (SignStatisticBits.integerCode 2) (SignStatisticBits.integerCode (-2))) :=by
  rw [OrderedWindowStatisticBits.packet]
  norm_num

-- Repeated roots count once. A zero-width query cannot replace the epsilon windows.
example : LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow.ScaledWindow ((X-C (2 : ℝ))^2) 0 2 1 :=by
  rw [LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow.scaled_window_iff,
    LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow.window_iff]
  refine ⟨2,by simp,?_,by norm_num⟩
  norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack (BinaryNatCode.encode 0)
    (SignStatisticBits.integerCode 1) (SignStatisticBits.integerCode 1) (SignStatisticBits.integerCode 1)
    (SignStatisticBits.integerCode 1) (SignStatisticBits.integerCode (-1))) :=by
  rw [OrderedWindowStatisticBits.packet]
  norm_num
example : ¬OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack (BinaryNatCode.encode 0)
    (SignStatisticBits.integerCode 1) (SignStatisticBits.integerCode 0) (SignStatisticBits.integerCode 0)
    (SignStatisticBits.integerCode 0) (SignStatisticBits.integerCode 0)) :=by
  rw [OrderedWindowStatisticBits.packet]
  norm_num

#print axioms FixedWidthBivariateZeroLiftBits.selected
#print axioms FixedWidthBivariateZeroLiftBits.epsilon_selected
#print axioms FixedWidthBivariateZeroLiftBits.reader
#print axioms FixedWidthBivariateZeroLiftBits.epsilonReader
#print axioms IntegralMixedFramedZeroTarskiBits.access
#print axioms IntegralMixedFramedZeroTarskiBits.principal_mass
#print axioms IntegralMixedFramedZeroTarskiBits.head_model
#print axioms IntegralMixedFramedZeroTarskiBits.query_model
#print axioms IntegralFramedZeroTarskiStatistic.evaluator
#print axioms IntegralFramedZeroTarskiStatistic.value_selected
#print axioms IntegralFramedZeroTarskiStatistic.exists_selected
#print axioms IntegralMixedPhysicalZeroTarski.evaluator
#print axioms IntegralMixedPhysicalZeroTarski.packet_evaluator
#print axioms IntegralMixedPhysicalZeroTarski.decider
#print axioms IntegralMixedPhysicalZeroTarski.exists_language_iff
end ZeroTarskiRegression
end RoadmapOriginsNativeWindows

namespace RoadmapOriginsMeanCuts
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open IntegralMixedNumericalSweep
open scoped Classical
noncomputable section
namespace ChronologicalMeanCutRegression
private def descriptor : IntegralMixedChronologicalFrame.Descriptor 2 3:=
  {labels:=[⟨2,by decide⟩],length_le:=by decide}
private theorem fit : descriptor.labels.length<3:=by decide
private theorem free : (2 : Fin 3)∉(IntegralMixedChronologicalMidpoint.frame descriptor fit 0 1).frozen:=
  (IntegralMixedChronologicalMidpoint.free_iff descriptor fit 0 1 2).mpr (by decide)
private def values (i : Fin 3) : ℝ:=if i=0 then 7 else if i=1 then -4 else 2
private theorem mean_value : IntegralMixedChronologicalMeanCut.mean values (0 : Fin 3) 1=(-1 : ℝ):=by
  norm_num [IntegralMixedChronologicalMeanCut.mean,IntegralMixedChronologicalMidpoint.reference,values]
private abbrev ordinary:=IntegralMixedCutRecordConstructor.Data.rule
  (IntegralMixedChronologicalSweepFrame.data descriptor fit 2 2 free free) (-3) (by decide)
private abbrev centered:=IntegralMixedCutRecordConstructor.Data.rule
  (IntegralMixedChronologicalMeanCut.data descriptor fit 0 1 2 2 free free) (-3) (by decide)

-- A negative mean and negative CURRENT Q: the old frozen row is retained.
example : centered.slope=(-3 : ℤ):=rfl
example : centered.height.val=1:=rfl
example : centered.critical.offset.val=2:=by decide
example : (normalized centered values 0).eval 0=(normalized ordinary values 0).eval (-1):=by
  have H:=IntegralMixedChronologicalMeanCut.normalized_zero descriptor fit 0 1 2 2 free free (-3)
    (by decide) values 0
  simpa only [ordinary,centered,Fin.val_zero,Fin.val_one,mean_value] using H
example : (normalized centered values 1).eval 0=(normalized ordinary values 1).eval (-1):=by
  have H:=IntegralMixedChronologicalMeanCut.normalized_zero descriptor fit 0 1 2 2 free free (-3)
    (by decide) values 1
  simpa only [ordinary,centered,Fin.val_zero,Fin.val_one,mean_value] using H

-- Equal endpoint VALUES are allowed too; no open-interval assumption occurs.
example : (normalized centered (fun _ : Fin 3=>2) 1).eval 0=(normalized ordinary (fun _ : Fin 3=>2) 1).eval 2:=by
  have H:=IntegralMixedChronologicalMeanCut.normalized_zero descriptor fit 0 1 2 2 free free (-3)
    (by decide) (fun _ : Fin 3=>2) 1
  have HM : IntegralMixedChronologicalMeanCut.mean (fun _ : Fin 3=>2) (0 : Fin 3) 1=(2 : ℝ):=by
    norm_num [IntegralMixedChronologicalMeanCut.mean]
  simpa only [ordinary,centered,Fin.val_one,HM] using H

private def labels:=WordList.encode [BinaryNatCode.encode 2]
private abbrev cutData:=IntegralMixedChronologicalMeanCut.data descriptor fit 0 1 2 2 free free
private abbrev word:=cutData.code IntegralMixedCausalRecordBits.Tag.squarefree 7 5
private theorem word_raw : word=IntegralMixedChronologicalMeanCutCode.code 2 labels 0 1 2 2 1 7 5:=
  IntegralMixedChronologicalMeanCutCode.data_code descriptor fit 0 1 2 2 free free .squarefree 7 5

-- Use the public ABI field lemmas: do not expand an entire nested byte word.
example : IntegralMixedUnitRecordCode.field word 0=[]:=IntegralMixedCutRecordConstructor.field_0 _ _ _ _
example : Nat.fromBitsLE (IntegralMixedUnitRecordCode.field word 2)=1:=by
  rw [IntegralMixedCutRecordConstructor.field_2]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [IntegralMixedChronologicalMeanCut.data_offset]
  decide
example : Nat.fromBitsLE (IntegralMixedUnitRecordCode.field word 5)=1:=by
  rw [IntegralMixedCutRecordConstructor.field_5]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rfl
example : IntegralMixedUnitRecordCode.field word 10=[true]:=IntegralMixedCutRecordConstructor.field_10 _ _ _ _
example : Nat.fromBitsLE (IntegralMixedUnitRecordCode.field word 8)=7:=by
  rw [IntegralMixedCutRecordConstructor.field_8]
  exact Nat.fromBitsLE_bits 7
example : Nat.fromBitsLE (IntegralMixedUnitRecordCode.field word 9)=5:=by
  exact (congrArg Nat.fromBitsLE (IntegralMixedCausalRecordDegree.field_9
    (cutData.baseCode .squarefree 7) 5)).trans (Nat.fromBitsLE_bits 5)
example : Nat.fromBitsLE (IntegralMixedUnitRecordCode.field word 11)=1:=by
  rw [IntegralMixedCutRecordConstructor.field_11]
  exact Nat.fromBitsLE_bits 1
example : IntegralMixedUnitRecordCode.field word 13=[false,true,false]:=by
  rw [IntegralMixedCutRecordConstructor.field_13]
  change List.ofFn (IntegralMixedChronologicalMidpointCode.data descriptor fit 0 1 2 2 free free).double=_
  rw [IntegralMixedChronologicalMidpointCode.data_doubles]
  decide
example : WordList.get (IntegralMixedUnitRecordCode.field word 7) 0=
    pair [true] (BinaryNatCode.encode 2):=by
  rw [IntegralMixedCutRecordConstructor.field_7]
  change WordList.get (WordList.encode (List.ofFn (fun i=>
    ((IntegralMixedChronologicalMidpointCode.data descriptor fit 0 1 2 2 free free).rows i).base))) 0=_
  rw [IntegralMixedChronologicalMidpointCode.data_rows]
  decide
example : WordList.get (IntegralMixedUnitRecordCode.field word 15) 1=
    sumWord (pair [true] (BinaryNatCode.encode 0)) (pair [true] (BinaryNatCode.encode 1)):=by
  rw [IntegralMixedCutRecordConstructor.field_15]
  change WordList.get (WordList.encode (List.ofFn (fun i=>
    ((IntegralMixedChronologicalMidpointCode.data descriptor fit 0 1 2 2 free free).rows i).midpoint))) 1=_
  rw [IntegralMixedChronologicalMidpointCode.data_midRows]
  decide

-- Leading-zero producer bits normalize in the original row table.
example : IntegralMixedChronologicalFrameCode.row
    (WordList.encode [BinaryNatCode.encode 2++[false,false]]) 0=
    IntegralMixedChronologicalFrameCode.row labels 0:=by decide
example : word=IntegralMixedChronologicalMeanCutCode.code 2 labels 0 1 2 2 1 7 5:=word_raw
example : ¬IntegralMixedChronologicalMeanCutCode.Bounds 2 3 3 8 labels 0 1 2 2 3 7 5:=by
  intro H
  have HT:=H.2.1
  omega
example : (2 : ZMod 2)=0:=by decide

private def sphere : SpatialSource 2:=
  {low:=MvPolynomial.C (-8),leading:=1,degree:=2,degree_two:=by decide,
    low_degree:=by rw [MvPolynomial.totalDegree_C];decide,leading_ne_zero:=by decide}
-- At mean2 with the other frozen level2, the last fiber is z^2=0.
example (z : ℝ) :
    (FermatCriticalHomogenization.polynomial sphere.low sphere.leading sphere.degree).eval₂
      (Int.castRingHom ℝ) (fun i=>if i=0 then 2 else if i=1 then 2 else z)=z^2:=by
  norm_num [sphere,FermatCriticalHomogenization.polynomial,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,Fin.sum_univ_succ]
  ring
example : Polynomial.IsRoot ((Polynomial.X : Polynomial ℝ)^2) 0 ∧
    (Polynomial.derivative ((Polynomial.X : Polynomial ℝ)^2)).eval 0=0:=by simp [Polynomial.IsRoot]

#check IntegralMixedChronologicalMeanCutCode.code_FP
#check IntegralMixedChronologicalMeanCutCode.raw_command
#check IntegralMixedChronologicalMeanCut.selected_zero_roots
#check IntegralMixedChronologicalMeanCut.selected_zero_degree
#print axioms IntegralMixedChronologicalMeanCut.data_rule
#print axioms IntegralMixedChronologicalMeanCutCode.code_FP
#print axioms IntegralMixedChronologicalMeanCutCode.data_code
#print axioms IntegralMixedChronologicalMeanCutCode.command_decode
#print axioms IntegralMixedChronologicalMeanCutCode.code_size
#print axioms IntegralMixedChronologicalMeanCutCode.rawData_code
#print axioms IntegralMixedChronologicalMeanCutCode.raw_command
#print axioms IntegralMixedChronologicalMeanCutCode.bounds_FP
#print axioms IntegralMixedChronologicalMeanCut.normalized_zero
#print axioms IntegralMixedChronologicalMeanCut.coordinateAt_zero
#print axioms IntegralMixedChronologicalMeanCut.selected_zero_scaling
#print axioms IntegralMixedChronologicalMeanCut.selected_zero_roots
#print axioms IntegralMixedChronologicalMeanCut.selected_zero_degree
end ChronologicalMeanCutRegression
end
end RoadmapOriginsMeanCuts

namespace RoadmapOriginsReservedLast
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ReservedLastCodeRegression
private def Q : SpatialSource 2 where
 low:=1
 leading:=-2
 degree:=2
 degree_two:=by decide
 low_degree:=by simp
 leading_ne_zero:=by decide
private def d : IntegralMixedCutRecordConstructor.Data 2 3 where
 critical:={
  offset:=⟨1,by decide⟩
  objective:=⟨1,by decide⟩
  coordinate:=⟨0,by decide⟩
  double i:=decide (i.val=1)
  rows i:=if i.val=0 then .single (some ⟨2,by decide⟩) else
    if i.val=1 then .sum (some ⟨0,by decide⟩) (some ⟨2,by decide⟩) else .single none }
 positive:=by decide
 height:=⟨0,by decide⟩
 current:=true
private def prior : List (List Bool):=[[],[true],[false,true]]
private def root (tag : Tag) (c deg : ℕ):=pair [] (pair (WordList.encode (prior++[d.code tag c deg])) [])
private theorem table (tag : Tag) (c deg : ℕ) :
 IntegralMixedCausalRecordPlanBits.records (root tag c deg)=WordList.encode (prior++[d.code tag c deg]):=by
 simp only [root,IntegralMixedCausalRecordPlanBits.records,pairFst_pair,pairSnd_pair]
example (tag : Tag) (c deg : ℕ) : IntegralMixedCausalRecordPlanBits.count (root tag c deg)=4:=
 IntegralMixedSourceIntegerLastCode.count_last _ prior _ (table tag c deg)
example (tag : Tag) (c deg : ℕ) : IntegralMixedCausalRecordPlanBits.code (root tag c deg) 3=d.code tag c deg:=
 IntegralMixedSourceIntegerLastCode.code_last _ prior _ (table tag c deg)
example : ((d.cut Q .coordinate 1 0 (Nat.zero_le _) (show IntegralMixedExceptionalBounds.auxiliaryCap 3 Q.degree≤2^(IntegralMixedExceptionalBounds.auxiliaryCap 3 Q.degree).size from Nat.le_of_lt (Nat.lt_size_self _))).rule (-24) (by decide)).slope=-24:=rfl
example : (({d with current:=false} : IntegralMixedCutRecordConstructor.Data 2 3).rule (-24) (by decide)).slope=1:=rfl
example : d.critical.rule.heights ⟨1,by decide⟩=.add (.reference 0) (.reference 2):=rfl
example : ((-24:ℤ)%6)=0:=by decide
variable (B : ℕ) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap 3 Q.degree≤2^B)
example (tag : Tag) :
 (IntegralMixedCausalUnitRecordBits.record Q (by decide) 3 (d.code tag 1 0) hcap).template=
 .cut (d.cut Q tag 1 0 (Nat.zero_le _) hcap):=
 IntegralMixedReservedCutCode.template_decode d Q (by decide) tag 1 0 (Nat.zero_le _) hcap
example (tag : Tag) (deg : ℕ) (hd : deg≤IntegralMixedExceptionalBounds.auxiliaryCap 3 Q.degree) :
 (IntegralMixedCausalUnitRecordBits.record Q (by decide) 3 (d.code tag 1 deg) hcap).template=
 .cut (d.cut Q tag 1 deg hd hcap):=
 IntegralMixedReservedCutCode.template_decode d Q (by decide) tag 1 deg hd hcap
example {S m : ℕ} {ι : Type} (x : State Q S B m ι) (tag : Tag) :
 instantiate x (IntegralMixedCausalUnitRecordBits.record Q (by decide) 3 (d.code tag 1 0) hcap)=
 IntegralMixedReservedCutCode.instruction x d Q (by decide) tag 1 0 (Nat.zero_le _) hcap:=
 IntegralMixedReservedCutCode.instantiate_decode x d Q (by decide) tag 1 0 (Nat.zero_le _) hcap

example (tag : Tag) : ((d.cut Q tag 1 0 (Nat.zero_le _) hcap).rule (-48) (by decide)).slope=-48:=rfl
example (tag : Tag) : ((d.cut Q tag 1 0 (Nat.zero_le _) hcap).rule (-24) (by decide)).slope=-24:=rfl
example : IntegralMixedUnitRecordCode.field (d.code .coordinate 7 0) 11=BinaryNatCode.encode 0:=
 IntegralMixedCutRecordConstructor.field_11 _ _ _ _
example : IntegralMixedUnitRecordCode.field (d.code .squarefree 7 0) 11=BinaryNatCode.encode 1:=
 IntegralMixedCutRecordConstructor.field_11 _ _ _ _
example : IntegralMixedUnitRecordCode.field (d.code .value 7 0) 11=BinaryNatCode.encode 2:=
 IntegralMixedCutRecordConstructor.field_11 _ _ _ _
example : IntegralMixedUnitRecordCode.field (d.code .limitCoordinate 7 0) 11=BinaryNatCode.encode 3:=
 IntegralMixedCutRecordConstructor.field_11 _ _ _ _
example : IntegralMixedUnitRecordCode.field (d.code .value 7 0) 10=[true]:=
 IntegralMixedCutRecordConstructor.field_10 _ _ _ _
example (tag : Tag) : IntegralMixedCanonicalUnitRuleBits.writtenDegree Q (d.code tag 7 0)=0:=
 IntegralMixedCausalRecordDegree.writtenDegree Q _ 0 (Nat.zero_le _)
variable (A : Parameters) (N : List Bool→ℕ)
 (hr : ∀r,IntegralMixedCausalRecordPlanBits.count r+N r+2≤A.cap r+1)
example (tag : Tag) (c deg : ℕ) (aux : List Bool) :
 prefixLength A (keyAt (root tag c deg) (N (root tag c deg)+3) aux)=N (root tag c deg)+3:=
 IntegralMixedSourceIntegerLastCode.parent_key_prefix A N hr _ aux prior _ (table tag c deg)
example (tag : Tag) (c deg : ℕ) : N (root tag c deg)+3≤A.cap (root tag c deg)+1:=
 IntegralMixedSourceIntegerLastCode.parent_bound A N hr _ prior _ (table tag c deg)
example {n W labels : ℕ} (r : IntegralMixedRoadmapRecordChain.Records n W labels)
 (seed probe : IntegralMixedRoadmapRecordChain.Word W) :
 r.paddedWord seed probe=WordList.encode (IntegralMixedReservedProbePosition.beforeProbe r seed++[probe.val]):=
 IntegralMixedReservedProbePosition.paddedWord_last r seed probe
example {n W labels : ℕ} (r : IntegralMixedRoadmapRecordChain.Records n W labels)
 (seed : IntegralMixedRoadmapRecordChain.Word W) :
 (IntegralMixedReservedProbePosition.beforeProbe r seed).length=IntegralMixedRoadmapRecordChain.recordBound n:=
 IntegralMixedReservedProbePosition.beforeProbe_length r seed
#print axioms IntegralMixedSourceIntegerLastCode.count_last
#print axioms IntegralMixedSourceIntegerLastCode.code_last
#print axioms IntegralMixedSourceIntegerLastCode.rules_length_last
#print axioms IntegralMixedSourceIntegerLastCode.parent_bound
#print axioms IntegralMixedSourceIntegerLastCode.parent_key_prefix
#print axioms IntegralMixedSourceIntegerLastCode.last_instruction
#print axioms IntegralMixedSourceIntegerLastCode.rules_last
#print axioms IntegralMixedSourceIntegerLastCode.rules_last_instantiated
#print axioms IntegralMixedSourceIntegerLastCode.parent_currentQ
#print axioms IntegralMixedReservedCutCode.template_decode
#print axioms IntegralMixedReservedCutCode.instantiate_decode
#print axioms IntegralMixedReservedCutCode.rules_last_decoded
#print axioms IntegralMixedReservedCutVertex.child_positive
#print axioms IntegralMixedReservedCutVertex.exists_vertex
#print axioms IntegralMixedReservedProbePosition.paddedWord_last
#print axioms IntegralMixedReservedProbePosition.root_last
#print axioms IntegralMixedReservedProbePosition.checked_last
#print axioms IntegralMixedReservedCutPlanning.plan_eq
#print axioms IntegralMixedReservedCutPlanning.rules_eq
end ReservedLastCodeRegression
end
end RoadmapOriginsReservedLast

namespace RoadmapOriginsAnchorWindows
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Polynomial
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace AnchorWindowRegression
private noncomputable def p : ℝ[X]:=(X-C (-1))*(X-C 1)
private theorem roots : p.roots.toFinset={-1,1}:=by
 rw [p,Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
 rw [Polynomial.roots_X_sub_C,Polynomial.roots_X_sub_C]
 simp
private theorem degree : p.natDegree=2:=by
 rw [p,Polynomial.natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)]
 simp only [Polynomial.natDegree_X_sub_C]
example : ∀ε : ℝ,0<ε→IntegralMixedSelectedCoordinateWindow.Window p 0 (-1) ε:=by
 rw [IntegralMixedSelectedAnchorWindow.all_windows_iff,roots]
 norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : ∀ε : ℝ,0<ε→IntegralMixedSelectedCoordinateWindow.Window p 1 1 ε:=by
 rw [IntegralMixedSelectedAnchorWindow.all_windows_iff,roots]
 norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : ¬(∀ε : ℝ,0<ε→IntegralMixedSelectedCoordinateWindow.Window p 0 1 ε):=by
 rw [IntegralMixedSelectedAnchorWindow.all_windows_iff,roots]
 norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : IntegralMixedSelectedAnchorWindow.Test p 2 1 576 1:=by
 rw [IntegralMixedSelectedAnchorWindow.test_iff p 2 (by decide) degree 1 576 (by norm_num),roots]
 norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : ¬IntegralMixedSelectedAnchorWindow.Test p 2 1 576 0:=by
 rw [IntegralMixedSelectedAnchorWindow.test_iff p 2 (by decide) degree 1 576 (by norm_num),roots]
 norm_num [OrderedRealRootWindow.rank,Finset.filter_insert]
example : ¬(∀ε : ℝ,0<ε→IntegralMixedSelectedCoordinateWindow.Window (1 : ℝ[X]) 0 0 ε):=by
 rw [IntegralMixedSelectedAnchorWindow.all_windows_iff]
 simp
example : (PseudoRemainder.seed (p.map Polynomial.C)
    ((WindowTarskiSeedDegree.affineQuery (X-C (0 : ℝ)) 1)^1) 2 (2+2)).natDegree=1:=by
 exact WindowTarskiSeedDegree.ternary_seed_degree p (X-C 0) 1 one_ne_zero (1 : Fin 3)
   2 (by decide) degree (Polynomial.natDegree_X_sub_C_le _)
#print axioms IntegralMixedSelectedAnchorWindow.all_windows_iff
#print axioms IntegralMixedSelectedAnchorWindow.constant_window_iff_of_stable
#print axioms IntegralMixedSelectedAnchorWindow.window_stable
#print axioms IntegralMixedSelectedAnchorWindow.test_iff
#print axioms IntegralMixedSelectedAnchorWindow.captured_ordinal_iff
end AnchorWindowRegression
end RoadmapOriginsAnchorWindows

namespace RoadmapOriginsOwnHeight
open LeanCanny LeanCanny.Encoding
open scoped Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
namespace OwnHeightRegression
private def labels:=WordList.encode [BinaryNatCode.encode 7]
example : IntegralMixedChronologicalCompanionCode.codes 2 labels 1=
    [IntegralMixedChronologicalFrameCode.code 2 labels 1 2,
      IntegralMixedChronologicalFrameCode.code 2 labels 1 1]:=by
 simp only [IntegralMixedChronologicalCompanionCode.codes,labels,WordListRecords.count_encode,List.length_singleton]
 rfl
example : WordList.get (WordList.encode (IntegralMixedRoadmapChain.seedCodes 2)) 3=
    IntegralMixedChronologicalFrameCode.code 2 [] 0 0:=IntegralMixedRoadmapOwnHeightCode.seed_final 2
example {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q) (i : ℕ)
    (hi : i≤IntegralMixedRoadmapChain.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw q) (IntegralMixedRoadmapChain.rawStart n q i-1)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q i) i i:=
 IntegralMixedRoadmapOwnHeightCode.checked_own_height_record h i hi
#print axioms IntegralMixedRoadmapOwnHeightCode.companion_split_last
#print axioms IntegralMixedRoadmapOwnHeightCode.level_final
#print axioms IntegralMixedRoadmapOwnHeightCode.checked_next_height_record
#print axioms IntegralMixedRoadmapOwnHeightCode.checked_initial_height_record
#print axioms IntegralMixedRoadmapOwnHeightCode.checked_own_height_record
end OwnHeightRegression
end RoadmapOriginsOwnHeight

namespace RoadmapOriginsLocalPaths
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
#print axioms LeanCanny.Connectivity.IntegralMixedSpecializedSectionWordComparison.word_eq
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.MatchedSlabInterior.code_anchor
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.MatchedSlabInterior.joined_of_near
#print axioms LeanCanny.Geometry.IntegralMixedFrozenFrame.MatchedSlabInterior.joined_of_rank_near
end RoadmapOriginsLocalPaths
