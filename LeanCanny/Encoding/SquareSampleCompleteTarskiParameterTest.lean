/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthTarskiParameterCoefficientSpace
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
/-! # Principal parameter coefficients are tested at one complete terminal tuple

Original principal coefficient costs are charged. The sampler, candidate
word and terminal raw variables never change between parameter tests.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteTarskiParameterTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open MvTwoParameterEncodedCoefficient (castPolynomial)
open RationalSubstitution.IntegerBits (context context_mem_FP selectedDegree selectedDegree_mem_FP)
open scoped Classical

variable (S : SquareSampleInput.Inputs) (F : FixedWidthTarskiPrincipalBits.Family)
variable (read : List Bool→List Bool) (j δ ε budget height : List Bool→ℕ)
variable (dim : ∀ c d,F.arity (read (pair c d))=S.count c+2)
variable (hdegree : ∀ c d,(FixedWidthTarskiPrincipalBits.polynomial F (read (pair c d)) (j (pair c d))).totalDegree≤budget (pair c d))
variable (hmass : ∀ c d,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial F (read (pair c d)) (j (pair c d)))≤2^height (pair c d))

noncomputable abbrev source : SquareSampleCompleteSuffixPolynomialTest.Source S where
  arity c _:=S.count c
  newer _ _:=0
  polynomial c d:=MvTwoParameterCoefficient.slice
    (castPolynomial (dim c d) (FixedWidthTarskiPrincipalBits.polynomial F (read (pair c d)) (j (pair c d))))
    (δ (pair c d)) (ε (pair c d))
  degree c d:=budget (pair c d)
  mass c d:=height (pair c d)
  dimension _ _:=by simp
  polynomial_degree c d:=(MvTwoParameterCoefficient.degree _ _ _).trans
    ((MvTwoParameterEncodedCoefficient.cast_degree _ _).trans (hdegree c d))
  polynomial_mass c d:=(MvTwoParameterCoefficient.mass _ _ _).trans
    ((MvTwoParameterEncodedCoefficient.cast_mass _ _).trans (hmass c d))

def canonical (z : List Bool) :=pair (pairFst z) (pairSnd z)
def coefficientContext (q : List Bool) :=canonical (context q)

theorem canonical_FP : canonical∈FP:=mem_FP_pair pairFst_mem_FP pairSnd_mem_FP
theorem coefficientContext_FP : coefficientContext∈FP:=mem_FP_comp context_mem_FP canonical_FP

theorem access (A : FixedWidthTarskiPrincipalBits.Access F) (hCount : UnaryFn S.count)
    (hW : UnaryFn F.width) (hr : read∈FP) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (hD : BinaryFn budget) (hH : BinaryFn height)
    (hfit : ∀ c d,budget (pair c d)<2^F.width (read (pair c d))) :
    (source S F read j δ ε budget height dim hdegree hmass).Access where
  newer:=UnaryFn.const 0
  degree:=hD.comp canonical_FP
  mass:=hH.comp canonical_FP
  coefficient:=by
    let ctx:=coefficientContext
    let m:=fun q=>S.count (pairFst (context q))
    let V:=fun q=>(budget (ctx q)).size
    have HC : ctx∈FP:=coefficientContext_FP
    have HM : UnaryFn m:=hCount.comp (mem_FP_comp context_mem_FP pairFst_mem_FP)
    have HD : BinaryFn (budget ∘ ctx):=hD.comp HC
    have HV : UnaryFn V:=(UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
    have DM : ∀ q,F.arity ((read ∘ ctx) q)=m q+2:=fun q=>dim (pairFst (context q)) (pairSnd (context q))
    have HP : ∀ q,(FixedWidthTarskiPrincipalBits.polynomial F ((read ∘ ctx) q) ((j ∘ ctx) q)).totalDegree<
        2^F.width ((read ∘ ctx) q):=fun q=>
      (hdegree (pairFst (context q)) (pairSnd (context q))).trans_lt
        (hfit (pairFst (context q)) (pairSnd (context q)))
    have HW : ∀ q,V q≤F.width ((read ∘ ctx) q):=fun q=>Nat.size_le.mpr
      (hfit (pairFst (context q)) (pairSnd (context q)))
    have E:=FixedWidthTarskiParameterBits.coefficient_evaluator F (read ∘ ctx) m V (j ∘ ctx) (δ ∘ ctx) (ε ∘ ctx) DM A
      hW (mem_FP_comp HC hr) HM HV (hj.comp HC) (hδ.comp HC) (hε.comp HC) HP HW
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
    refine E.congr (funext fun q=>?_)
    unfold SquareSampleCompleteSuffixPolynomialTest.coefficient SquareSampleCompleteSuffixPolynomialTest.oldCoefficient
      FixedWidthRowBits.value FixedWidthTarskiParameterBits.polynomial
    simp only [source,ctx,coefficientContext,canonical,Function.comp_apply]
    rfl

theorem evaluator (hS : S.Access) (A : FixedWidthTarskiPrincipalBits.Access F)
    (hW : UnaryFn F.width) (hr : read∈FP) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (hD : BinaryFn budget) (hH : BinaryFn height) (hfit : ∀ c d,budget (pair c d)<2^F.width (read (pair c d))) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.value S
      (SquareSampleCompleteSuffixPolynomialTest.test (source S F read j δ ε budget height dim hdegree hmass))) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator hS _
    (access S F read j δ ε budget height dim hdegree hmass A hS.count hW hr hj hδ hε hD hH hfit)

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    SquareSampleCompleteIndexedPolynomialTest.value S
      (SquareSampleCompleteSuffixPolynomialTest.test (source S F read j δ ε budget height dim hdegree hmass))
      (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign
        (((MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
          (SquareSampleCompleteVertices.candidate S c w hv).val
          (castPolynomial (dim c d) (FixedWidthTarskiPrincipalBits.polynomial F (read (pair c d)) (j (pair c d))))).coeff (δ (pair c d))).coeff (ε (pair c d)))) :=by
  rw [SquareSampleCompleteSuffixPolynomialTest.packet _ c w d hv]
  have HI (i : Fin (S.count c)) :
      Fin.cast ((source S F read j δ ε budget height dim hdegree hmass).dimension c d)
        (FixedWidthSuffixLiftBits.shift ((source S F read j δ ε budget height dim hdegree hmass).newer c d) i)=i :=by
    apply Fin.ext
    exact (Fin.val_cast _ _).trans (Nat.zero_add i.val)
  have HH : (fun i : Fin (S.count c)=>
      (SquareSampleCompleteVertices.candidate S c w hv).val
        (Fin.cast ((source S F read j δ ε budget height dim hdegree hmass).dimension c d)
          (FixedWidthSuffixLiftBits.shift ((source S F read j δ ε budget height dim hdegree hmass).newer c d) i)))=
      (SquareSampleCompleteVertices.candidate S c w hv).val :=
    funext (fun i=>congrArg (SquareSampleCompleteVertices.candidate S c w hv).val (HI i))
  change InfinitesimalSign.encode (SignType.sign (MvPolynomial.eval₂ (Int.castRingHom ℝ) _
    (MvTwoParameterCoefficient.slice
      (castPolynomial (dim c d) (FixedWidthTarskiPrincipalBits.polynomial F (read (pair c d)) (j (pair c d))))
      (δ (pair c d)) (ε (pair c d)))))=_
  rw [HH]
  apply congrArg InfinitesimalSign.encode
  apply congrArg SignType.sign
  exact (MvTwoParameterCoefficient.selected_coefficient (Int.castRingHom ℝ)
    (SquareSampleCompleteVertices.candidate S c w hv).val _ _ _).symm

end LeanCanny.Encoding.SquareSampleCompleteTarskiParameterTest
