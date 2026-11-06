/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Encoding.SquareSampleSourceTest
/-! # Charged source queries on one unchanged complete sampler tuple -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleIndexedSourceTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def normalize (z : List Bool) := pair (pairFst z) (pairSnd z)
theorem normalize_FP : normalize∈FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def test (F : SquareSampleInput.Inputs) (S : Source) (read : List Bool→List Bool)
    (hd : ∀c d,S.arity (read (pair c d))=F.count c) : SquareSampleCompleteIndexedPolynomialTest.Test F where
  polynomial c d := SquareSampleSourceTest.castPolynomial (hd c d) (S.polynomial (read (pair c d)))
  degree z := S.degree (read (normalize z))
  mass z := S.mass (read (normalize z))
  polynomial_degree _z := (SquareSampleSourceTest.cast_degree _ _).le.trans (S.polynomial_degree _)
  polynomial_mass _z := (SquareSampleSourceTest.cast_mass _ _).le.trans (S.polynomial_mass _)

variable (F : SquareSampleInput.Inputs) (S : Source) (read : List Bool→List Bool)
  (hr : read∈FP) (hd : ∀c d,S.arity (read (pair c d))=F.count c)

def request (q : List Bool) := pair
  (pair (read (normalize (RationalSubstitution.IntegerBits.context q)))
    (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
include hr in
theorem request_FP : request read∈FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP normalize_FP) hr)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

include hr in
theorem access (A : IntegralFramedBankPolynomialModel.Access S) : (test F S read hd).Access := by
  have HV : UnaryFn (fun z=>(S.degree z).size) :=
    (UnaryFn.length A.degree.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have E:=(SquareSampleSourceTest.source_evaluator S A _ HV).precompose (request read) (request_FP read hr)
  refine ⟨A.degree.comp (mem_FP_comp normalize_FP hr),A.mass.comp (mem_FP_comp normalize_FP hr),?_⟩
  apply E.congr
  funext q
  let B (z t m : List Bool) := residueBits (((S.polynomial z).coeff
    (nativeExponent (Equiv.refl (Fin (S.arity z))) (S.degree z).size (Nat.fromBitsLE t)) :ℤ) :
      ZMod (Nat.fromBitsLE m+1))
  have HL : ((SquareSampleSourceTest.sourceValue S (fun z=>(S.degree z).size))∘request read) q=
      B (read (normalize (RationalSubstitution.IntegerBits.context q)))
        (RationalSubstitution.IntegerBits.selectedDegree q) (pairSnd q) := by
    change B (SquareSampleSourceTest.context (request read q))
      (SquareSampleSourceTest.target (request read q)) (pairSnd (request read q))=_
    simp only [request,SquareSampleSourceTest.context,SquareSampleSourceTest.target,
      RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]
  have HR : SquareSampleCompleteIndexedPolynomialTest.coefficient (test F S read hd) q=
      B (read (normalize (RationalSubstitution.IntegerBits.context q)))
        (RationalSubstitution.IntegerBits.selectedDegree q) (pairSnd q) := by
    unfold SquareSampleCompleteIndexedPolynomialTest.coefficient SquareSampleCompleteIndexedPolynomialTest.family
      FixedWidthRationalSubstitutionBits.Family.coefficient test
    simp only [SquareSampleCompleteIndexedPolynomialTest.width,←nativeExponent_refl]
    rw [SquareSampleSourceTest.cast_coefficient]
    rfl
  exact HL.trans HR.symm

noncomputable def value := SquareSampleCompleteIndexedPolynomialTest.value F (test F S read hd)
include hr in
theorem evaluator (hF : F.Access) (A : IntegralFramedBankPolynomialModel.Access S) :
    SpaceFunction (value F S read hd) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator hF (access F S read hr hd A)

theorem packet (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    value F S read hd (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((S.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate F c w hw).val (Fin.cast (hd c d) i)))) := by
  rw [value,SquareSampleCompleteIndexedPolynomialTest.packet F (test F S read hd) c w d hw]
  exact congrArg (fun r :ℝ=>InfinitesimalSign.encode (SignType.sign r))
    (SquareSampleSourceTest.cast_eval (hd c d) _ _)

end LeanCanny.Encoding.SquareSampleIndexedSourceTest
