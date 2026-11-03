/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarEmbeddedTarskiParameterTest
public import LeanCanny.Algebra.MvTwoParameterEvaluationDegree
public import LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
/-! # Ordered principal signs at the same full physical vertex

The smaller parameter is delta. Both scans use the original principal's
whole-output degree bound and retain the source, vertex and principal index.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleCompleteIndexedPolynomialTest.value
  SquareSampleCompleteSuffixPolynomialTest.test FixedWidthTarskiPrincipalBits.polynomial

def base (z : List Bool) :=pair (pairFst z) (pairFst (pairFst (pairSnd z)))
def delta (z : List Bool) :=Nat.fromBitsLE (pairSnd (pairFst (pairSnd z)))
def epsilon (z : List Bool) :=Nat.fromBitsLE (pairSnd (pairSnd z))
def datum (b d e : List Bool) :=pair (pair b d) e
-- u=(pair (pair source vertex) originalDatum); the two scan counters follow u.
def query (q : List Bool) :=
  pair (pairFst (pairFst (pairFst q)))
    (datum (pairSnd (pairFst (pairFst q))) (pairSnd (pairFst q)) (pairSnd q))
def inputContext (u : List Bool) :=pair (pairFst (pairFst u)) (pairSnd u)

theorem base_pair (c b : List Bool) : base (pair c b)=pair c (pairFst (pairFst b)) :=by
  simp only [base,pairFst_pair,pairSnd_pair]

theorem base_FP : base∈FP:=by polytime [base]
theorem delta_binary : BinaryFn delta:=BinaryFn.fromBits (by polytime)
theorem epsilon_binary : BinaryFn epsilon:=BinaryFn.fromBits (by polytime)
theorem query_FP : query∈FP:=by polytime [query,datum]
theorem inputContext_FP : inputContext∈FP:=by polytime [inputContext]

private theorem principal_cast_retarget (MF : FixedWidthTarskiPrincipalBits.Family)
    (read : List Bool→List Bool) (j : List Bool→ℕ) (M : ℕ) (z z' : List Bool) (hz : z=z')
    (h : MF.arity (read z)=M) (h' : MF.arity (read z')=M) :
    MvTwoParameterEncodedCoefficient.castPolynomial h (FixedWidthTarskiPrincipalBits.polynomial MF (read z) (j z))=
      MvTwoParameterEncodedCoefficient.castPolynomial h' (FixedWidthTarskiPrincipalBits.polynomial MF (read z') (j z')) :=by
  subst z'
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (j budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))).totalDegree≤budget (pair c b))
variable (hmass : ∀c b,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b)))≤2^height (pair c b))
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

noncomputable def source :=IntegralFramedScalarEmbeddedTarskiParameterTest.source P D H L F C hs key hpos O hc
  MF (read∘base) (j∘base) delta epsilon (budget∘base) (height∘base)
  (fun c b=>by simpa only [Function.comp_apply,base,pairFst_pair,pairSnd_pair] using dim c (pairFst (pairFst b)))
  (fun c b=> (congrArg (fun z=>(FixedWidthTarskiPrincipalBits.polynomial MF (read z) (j z)).totalDegree≤budget z)
    (base_pair c b)).mpr (hdegree c (pairFst (pairFst b))))
  (fun c b=> (congrArg (fun z=>MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read z) (j z))≤2^height z)
    (base_pair c b)).mpr (hmass c (pairFst (pairFst b))))

noncomputable def coefficientSign (q : List Bool) :=
  (SquareSampleCompleteIndexedPolynomialTest.value S (SquareSampleCompleteSuffixPolynomialTest.test
    (source P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass)) (query q)).take 2

noncomputable def value :=RealIteratedInfinitesimalSignSpace.value
  (coefficientSign P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass)
  (budget∘inputContext) (budget∘inputContext)

theorem coefficient_length (q : List Bool) :
    (coefficientSign P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass q).length≤2 :=
  List.length_take_le _ _

noncomputable def selected (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :=
  MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
    (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val
      (IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) (Fin.cast (hc c) i)))
    (MvTwoParameterEncodedCoefficient.castPolynomial (dim c b)
      (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))))

theorem coefficient_packet (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (d e : ℕ) :
    coefficientSign P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass
      (pair (pair (pair (pair c w) b) (BinaryNatCode.encode d)) (BinaryNatCode.encode e))=
      RealInfinitesimalSignSpace.tag
        (((selected P D H L F C hs key hpos O hc MF read j dim c w b hv).coeff d).coeff e) :=by
  unfold coefficientSign query datum
  simp only [pairFst_pair,pairSnd_pair]
  unfold source
  rw [IntegralFramedScalarEmbeddedTarskiParameterTest.packet (hv:=hv)]
  simp only [Function.comp_apply]
  have HB : base (pair c (pair (pair b (BinaryNatCode.encode d)) (BinaryNatCode.encode e)))=pair c b :=by
    simp only [base,pairFst_pair,pairSnd_pair]
  have HH : MF.arity (read (base (pair c (pair (pair b (BinaryNatCode.encode d)) (BinaryNatCode.encode e)))))=O.count c+2 :=by
    rw [HB]
    exact dim c b
  rw [principal_cast_retarget MF read j (O.count c+2) _ _ HB HH (dim c b)]
  simp only [delta,epsilon,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HT (s : SignType) : (InfinitesimalSign.encode s).take 2=InfinitesimalSign.encode s :=by cases s <;> rfl
  exact HT _

theorem value_at (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass (pair (pair c w) b)=
      RealIteratedInfinitesimalSignSpace.tag (selected P D H L F C hs key hpos O hc MF read j dim c w b hv) :=by
  unfold value
  refine RealIteratedInfinitesimalSignSpace.value_at _ _ _ _
    (selected P D H L F C hs key hpos O hc MF read j dim c w b hv) ?_ ?_ ?_
  · simp only [Function.comp_apply,inputContext,pairFst_pair,pairSnd_pair]
    exact (MvTwoParameterCoefficient.evaluate_degree _ _ _).trans
      ((MvTwoParameterEncodedCoefficient.cast_degree _ _).trans (hdegree c b))
  · intro d
    simp only [Function.comp_apply,inputContext,pairFst_pair,pairSnd_pair]
    exact (MvTwoParameterCoefficient.evaluate_coefficient_degree _ _ _ d).trans
      ((MvTwoParameterEncodedCoefficient.cast_degree _ _).trans (hdegree c b))
  · exact coefficient_packet P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass c w b hv

end LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
