/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteEmbeddedPolynomialTest
public import LeanCanny.Encoding.SquareSampleCompleteTarskiParameterTest
public import LeanCanny.Encoding.IntegralFramedPhysicalSquare
public import LeanCanny.Algebra.IntegralMixedFramedScalarEmbedding
/-! # Principal parameter signs on the raw scalar columns of a full vertex

Parameter extraction precedes the scalar-column embedding. The auxiliary
prefix input supplies only the integer polynomial's dimension; its roots
and evaluator are never used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarEmbeddedTarskiParameterTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedScalarEmbedding
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (j δ ε budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))).totalDegree≤budget (pair c b))
variable (hmass : ∀c b,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b)))≤2^height (pair c b))
local notation "R" => SquareSampleCompleteTarskiParameterTest.source O MF read j δ ε budget height dim hdegree hmass

noncomputable def columns (c _b : List Bool) : Fin ((R).arity c _b)→Fin ((S).count c) :=
  scalarMap P D H (key c) ∘ Fin.cast (hc c)

noncomputable def source :=SquareSampleCompleteEmbeddedPolynomialTest.source S R
  (columns P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass)

variable (T : IntegralMixedHeaderTablesBits.Tables) (hrT : IntegralMixedFramedHeaderBits.Represents P D H T)
include hrT in
theorem column_index (z : List Bool) (i : Fin ((R).arity (pairFst z) (pairSnd z))) :
    index P T (fun z=>key (pairFst z)) (pair z (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (columns P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass
        (pairFst z) (pairSnd z) i).val :=by
  exact index_map P D H T hrT (fun z=>key (pairFst z)) z (Fin.cast (hc (pairFst z)) i)

theorem columns_injective (c b : List Bool) : Function.Injective
    (columns P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass c b) :=
  (scalarMap_injective P D H (key c)).comp (Fin.cast_injective (hc c))

include hrT in
theorem access (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T) (hk : key∈FP)
    (hN : UnaryFn (S).count)
    (A : FixedWidthTarskiPrincipalBits.Access MF) (hW : UnaryFn MF.width)
    (hr : read∈FP) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (hD : BinaryFn budget) (hH : BinaryFn height)
    (hfit : ∀c b,budget (pair c b)<2^MF.width (read (pair c b))) :
    (source P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass).Access :=by
  have hO : UnaryFn O.count:=((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp hk).of_eq
    (fun c=>(hc c).symm)
  let RA:=SquareSampleCompleteTarskiParameterTest.access O MF read j δ ε budget height dim hdegree hmass
    A hO hW hr hj hδ hε hD hH hfit
  exact SquareSampleCompleteEmbeddedPolynomialTest.access S R _
    (index P T (fun z=>key (pairFst z)))
    (column_index P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass T hrT)
    (columns_injective P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass)
    RA (hO.comp pairFst_mem_FP) hN
    (index_FP P a T hT _ (mem_FP_comp pairFst_mem_FP hk))

include hrT in
theorem evaluator (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T) (hk : key∈FP)
    (hS : (S).Access) (A : FixedWidthTarskiPrincipalBits.Access MF) (hW : UnaryFn MF.width)
    (hr : read∈FP) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (hD : BinaryFn budget) (hH : BinaryFn height)
    (hfit : ∀c b,budget (pair c b)<2^MF.width (read (pair c b))) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.value S (SquareSampleCompleteSuffixPolynomialTest.test
      (source P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass))) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator hS _
    (access P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass T hrT
      a hT hk hS.count A hW hr hj hδ hε hD hH hfit)

theorem packet (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    SquareSampleCompleteIndexedPolynomialTest.value S (SquareSampleCompleteSuffixPolynomialTest.test
      (source P D H L F C hs key hpos O hc MF read j δ ε budget height dim hdegree hmass)) (pair (pair c w) b)=
      InfinitesimalSign.encode (SignType.sign
        (((MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
          (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val
            (scalarMap P D H (key c) (Fin.cast (hc c) i)))
          (MvTwoParameterEncodedCoefficient.castPolynomial (dim c b)
            (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))))).coeff
              (δ (pair c b))).coeff (ε (pair c b)))) :=by
  unfold source
  rw [SquareSampleCompleteEmbeddedPolynomialTest.packet]
  apply congrArg InfinitesimalSign.encode
  apply congrArg SignType.sign
  exact (MvTwoParameterCoefficient.selected_coefficient (Int.castRingHom ℝ) _ _ _ _).symm

end LeanCanny.Encoding.IntegralFramedScalarEmbeddedTarskiParameterTest
