/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Algebra.FixedWidthSuffixLiftSpace
/-! # Indexed polynomial signs on one terminal suffix

An original integer-polynomial reader can be lifted to a longer complete
joint tuple. Every newer exponent is checked to be zero, and the one old
coefficient query drops exactly those blocks. The degree, mass and caller
modulus are retained. The sign theorem reads the literal suffix of the
same complete vertex.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source (F : SquareSampleInput.Inputs) where
  arity : List Bool→List Bool→ℕ
  newer : List Bool→List Bool→ℕ
  polynomial : (c d : List Bool)→MvPolynomial (Fin (arity c d)) ℤ
  degree : List Bool→List Bool→ℕ
  mass : List Bool→List Bool→ℕ
  dimension : ∀ c d,newer c d+arity c d=F.count c
  polynomial_degree : ∀ c d,(polynomial c d).totalDegree≤degree c d
  polynomial_mass : ∀ c d,MvMass.mass (polynomial c d)≤2^mass c d

noncomputable def test {F : SquareSampleInput.Inputs} (S : Source F) :
    SquareSampleCompleteIndexedPolynomialTest.Test F where
  polynomial c d:=MvPolynomial.rename (Fin.cast (S.dimension c d))
    (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (S.newer c d)) (S.polynomial c d))
  degree z:=S.degree (pairFst z) (pairSnd z)
  mass z:=S.mass (pairFst z) (pairSnd z)
  polynomial_degree _z := (MvPolynomial.totalDegree_rename_le _ _).trans
    ((MvPolynomial.totalDegree_rename_le _ _).trans (S.polynomial_degree _ _))
  polynomial_mass _z := (MvMass.rename_le _ _).trans
    ((MvMass.rename_le _ _).trans (S.polynomial_mass _ _))

noncomputable def oldCoefficient {F : SquareSampleInput.Inputs} (S : Source F)
    (z target modulus : List Bool) : List Bool :=
  residueBits (((S.polynomial (pairFst z) (pairSnd z)).coeff
    (nativeExponent (Equiv.refl (Fin (S.arity (pairFst z) (pairSnd z))))
      ((S.degree (pairFst z) (pairSnd z)).size) (Nat.fromBitsLE target)) :ℤ) : ZMod (Nat.fromBitsLE modulus+1))

noncomputable def coefficient {F : SquareSampleInput.Inputs} (S : Source F) (q : List Bool) : List Bool :=
  oldCoefficient S (RationalSubstitution.IntegerBits.context q)
    (RationalSubstitution.IntegerBits.selectedDegree q) (pairSnd q)

structure Source.Access {F : SquareSampleInput.Inputs} (S : Source F) : Prop where
  newer : UnaryFn (fun z=>S.newer (pairFst z) (pairSnd z))
  degree : BinaryFn (fun z=>S.degree (pairFst z) (pairSnd z))
  mass : BinaryFn (fun z=>S.mass (pairFst z) (pairSnd z))
  coefficient : SpaceFunction (coefficient S)

private theorem coefficient_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (W k : ℕ) :
    (MvPolynomial.rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl (Fin b)) W k)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W k) := by
  cases h
  rw [show (Fin.cast rfl : Fin a→Fin a)=id from by funext i; rfl,MvPolynomial.rename_id]
  rfl

theorem coefficient_evaluator {F : SquareSampleInput.Inputs} (S : Source F) (A : S.Access) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.coefficient (test S)) := by
  let ctx:=RationalSubstitution.IntegerBits.context
  let target:=RationalSubstitution.IntegerBits.selectedDegree
  let D:=fun q=>S.newer (pairFst (ctx q)) (pairSnd (ctx q))
  let oldA:=fun q=>S.arity (pairFst (ctx q)) (pairSnd (ctx q))
  let V:=fun q=>(S.degree (pairFst (ctx q)) (pairSnd (ctx q))).size
  let p:=fun q=>S.polynomial (pairFst (ctx q)) (pairSnd (ctx q))
  have hD : UnaryFn D:=A.newer.comp RationalSubstitution.IntegerBits.context_mem_FP
  have HD : BinaryFn (fun q=>S.degree (pairFst (ctx q)) (pairSnd (ctx q))) :=
    A.degree.comp RationalSubstitution.IntegerBits.context_mem_FP
  have hV : UnaryFn V := (UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have ht : target∈FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  let request:=fun q=>pair (pair (ctx q) (FixedWidthSuffixLiftBits.spatial D V target q)) (pairSnd q)
  have hreq : request∈FP:=mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    (FixedWidthSuffixLiftBits.spatial_FP D V target hD hV ht)) pairSnd_mem_FP
  have Eold : SpaceFunction (FixedWidthRowBits.value oldA V p (FixedWidthSuffixLiftBits.spatial D V target) pairSnd) :=
    (A.coefficient.precompose request hreq).congr (by
      funext q
      simp only [Function.comp_apply,coefficient,request,RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]
      rfl)
  have EH:=FixedWidthSuffixLiftBits.evaluator D oldA V p target pairSnd hD hV ht Eold
  apply EH.congr
  funext q
  unfold SquareSampleCompleteIndexedPolynomialTest.coefficient SquareSampleCompleteIndexedPolynomialTest.family
    FixedWidthRationalSubstitutionBits.Family.coefficient
  simp only [test,coefficient_cast,←nativeExponent_refl]
  rfl

theorem access {F : SquareSampleInput.Inputs} (S : Source F) (A : S.Access) : (test S).Access where
  degree:=A.degree
  mass:=A.mass
  coefficient:=coefficient_evaluator S A

theorem packet {F : SquareSampleInput.Inputs} (S : Source F) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleCompleteIndexedPolynomialTest.value F (test S) (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((S.polynomial c d).eval₂ (Int.castRingHom ℝ) (fun i=>
        (SquareSampleCompleteVertices.candidate F c w hv).val
          (Fin.cast (S.dimension c d) (FixedWidthSuffixLiftBits.shift (S.newer c d) i))))) := by
  rw [SquareSampleCompleteIndexedPolynomialTest.packet F (test S) c w d hv]
  unfold test
  simp only [MvPolynomial.eval₂_rename]
  rfl

theorem evaluator {F : SquareSampleInput.Inputs} (h : F.Access) (S : Source F) (A : S.Access) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.value F (test S)) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator h (access S A)

end LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
