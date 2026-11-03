/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace

/-! # Native polynomial tests on an explicit subset of one full tuple

Only the original polynomial coefficient interface is reused. No vertex,
root or evaluation from its old square input is used. The injective raw
column map retains the same complete target sampler and vertex word.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteEmbeddedPolynomialTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthEmbeddingBits.word

def canonical (z : List Bool) :=pair (pairFst z) (pairSnd z)
def context (q : List Bool) :=canonical (RationalSubstitution.IntegerBits.context q)
theorem canonical_FP : canonical∈FP:=mem_FP_pair pairFst_mem_FP pairSnd_mem_FP
theorem context_FP : context∈FP:=mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP canonical_FP

variable {O : SquareSampleInput.Inputs} (S : SquareSampleInput.Inputs)
variable (R : SquareSampleCompleteSuffixPolynomialTest.Source O)
variable (f : (c d : List Bool)→Fin (R.arity c d)→Fin (S.count c))

noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source S where
  arity c _:=S.count c
  newer _ _:=0
  polynomial c d:=MvPolynomial.rename (f c d) (R.polynomial c d)
  degree:=R.degree
  mass:=R.mass
  dimension _ _:=Nat.zero_add _
  polynomial_degree c d:=(MvPolynomial.totalDegree_rename_le _ _).trans (R.polynomial_degree c d)
  polynomial_mass c d:=(MvMass.rename_le _ _).trans (R.polynomial_mass c d)

variable (index : List Bool→List Bool)
variable (hindex : ∀z i,index (pair z (BinaryNatCode.encode i.val))=
  BinaryNatCode.encode (f (pairFst z) (pairSnd z) i).val)
variable (hf : ∀c d,Function.Injective (f c d))

noncomputable def embeddedCoefficient (c d target modulus : List Bool) : List Bool :=
  residueBits ((((MvPolynomial.rename (f c d) (R.polynomial c d)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (S.count c))) (R.degree c d).size
      (Nat.fromBitsLE target))):ℤ):ZMod (Nat.fromBitsLE modulus+1))

theorem old_coefficient_packet (z target modulus : List Bool) :
    SquareSampleCompleteSuffixPolynomialTest.coefficient R (pair (pair z target) modulus)=
      SquareSampleCompleteSuffixPolynomialTest.oldCoefficient R z target modulus := by
  unfold SquareSampleCompleteSuffixPolynomialTest.coefficient
  simp only [RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair]

include hindex hf in
theorem access (A : R.Access) (hA : UnaryFn (fun z=>R.arity (pairFst z) (pairSnd z)))
    (hN : UnaryFn S.count) (hi : index∈FP) : (source S R f).Access := by
  refine ⟨UnaryFn.const 0,A.degree,A.mass,?_⟩
  let oldA:=fun q=>R.arity (pairFst (context q)) (pairSnd (context q))
  let newA:=fun q=>S.count (pairFst (context q))
  let W:=fun q=>(R.degree (pairFst (context q)) (pairSnd (context q))).size
  let p:=fun q=>R.polynomial (pairFst (context q)) (pairSnd (context q))
  let g:=fun q=>f (pairFst (context q)) (pairSnd (context q))
  let idx:=fun q=>index (pair (context (pairFst q)) (pairSnd q))
  let target:=RationalSubstitution.IntegerBits.selectedDegree
  have HA : UnaryFn oldA:=hA.comp context_FP
  have HN : UnaryFn newA:=hN.comp (mem_FP_comp context_FP pairFst_mem_FP)
  have HD : BinaryFn (fun q=>R.degree (pairFst (context q)) (pairSnd (context q))):=A.degree.comp context_FP
  have HW : UnaryFn W:=(UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have HX : (fun q=>context (pairFst q))∈FP:=
    mem_FP_comp (f:=pairFst) (g:=context) pairFst_mem_FP context_FP
  have HI : idx∈FP:=mem_FP_comp (mem_FP_pair HX pairSnd_mem_FP) hi
  have HT : target∈FP:=RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  let word:=FixedWidthEmbeddingBits.word oldA newA W target idx
  have HWord : word∈FP:=FixedWidthEmbeddingBits.word_FP oldA newA W target idx HA HN HW HT HI
  let request:=fun q=>pair (pair (context q) (word q)) (pairSnd q)
  have HReq : request∈FP:=mem_FP_pair (mem_FP_pair context_FP HWord) pairSnd_mem_FP
  have Eold : SpaceFunction (FixedWidthRowBits.value oldA W p word pairSnd) :=
    (A.coefficient.precompose request HReq).congr (by
      funext q
      change SquareSampleCompleteSuffixPolynomialTest.coefficient R (pair (pair (context q) (word q)) (pairSnd q))=_
      rw [old_coefficient_packet R]
      rfl)
  have HG : ∀q,Function.Injective (g q):=fun q=>hf _ _
  have HIdx : ∀q i,idx (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (g q i).val :=by
    intro q i
    simp only [idx,pairFst_pair,pairSnd_pair]
    exact hindex _ i
  have E:=FixedWidthEmbeddingBits.evaluator oldA newA W target idx p g HG HIdx pairSnd HA HN HW HT HI Eold
  apply E.congr
  funext q
  change embeddedCoefficient S R f (pairFst (context q)) (pairSnd (context q)) (target q) (pairSnd q)=
    embeddedCoefficient S R f (pairFst (RationalSubstitution.IntegerBits.context q))
      (pairSnd (RationalSubstitution.IntegerBits.context q)) (target q) (pairSnd q)
  simp only [context,canonical,pairFst_pair,pairSnd_pair]

private theorem cast_shift_zero {a : ℕ} (h : 0+a=a) (i : Fin a) :
    Fin.cast h (FixedWidthSuffixLiftBits.shift 0 i)=i := by
  apply Fin.ext
  exact Nat.zero_add _

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    SquareSampleCompleteIndexedPolynomialTest.value S
      (SquareSampleCompleteSuffixPolynomialTest.test (source S R f)) (pair (pair c w) d)=
      InfinitesimalSign.encode (SignType.sign ((R.polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val (f c d i)))) := by
  rw [SquareSampleCompleteSuffixPolynomialTest.packet (source S R f) c w d hv]
  simp only [source,MvPolynomial.eval₂_rename,cast_shift_zero]
  rfl

include hindex hf in
theorem evaluator (hS : S.Access) (A : R.Access)
    (hA : UnaryFn (fun z=>R.arity (pairFst z) (pairSnd z))) (hi : index∈FP) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.value S
      (SquareSampleCompleteSuffixPolynomialTest.test (source S R f))) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator hS _ (access S R f index hindex hf A hA hS.count hi)

end LeanCanny.Encoding.SquareSampleCompleteEmbeddedPolynomialTest
