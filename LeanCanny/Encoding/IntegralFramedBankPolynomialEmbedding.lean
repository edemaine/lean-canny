/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
/-! # Charged polynomial sources under explicit injective variable maps

The native reader checks foreign columns before repacking. Its source and
caller modulus stay fixed; no values at algebraic points are supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (S : Source) (read : List Bool → List Bool) (N : List Bool → ℕ)
  (f : (c : List Bool) → Fin (S.arity (read c)) → Fin (N c))
  (hfit : ∀ c, S.degree (read c)<2^S.width (read c))

noncomputable def source : Source where
  arity := N
  width c := S.width (read c)
  degree c := S.degree (read c)
  mass c := S.mass (read c)
  polynomial c := MvPolynomial.rename (f c) (S.polynomial (read c))
  fit c i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    (((MvPolynomial.totalDegree_rename_le _ _).trans (S.polynomial_degree _)).trans_lt (hfit c))
  polynomial_degree _c := (MvPolynomial.totalDegree_rename_le _ _).trans (S.polynomial_degree _)
  polynomial_mass _c := (MvMass.rename_le _ _).trans (S.polynomial_mass _)

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree
def indexQuery (index : List Bool → List Bool) (q : List Bool) :=
  index (pair (context (pairFst q)) (pairSnd q))
theorem context_FP : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem indexQuery_FP (index : List Bool → List Bool) (hi : index ∈ FP) : indexQuery index ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP context_FP) pairSnd_mem_FP) hi

noncomputable def value (q : List Bool) :=
  residueBits ((((source S read N f hfit).polynomial (context q)).coeff
    (nativeExponent (Equiv.refl _) ((source S read N f hfit).width (context q))
      (Nat.fromBitsLE (target q))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1))

theorem evaluator (A : Access S) (hr : read ∈ FP) (hN : UnaryFn N)
    (hf : ∀ c, Function.Injective (f c)) (index : List Bool → List Bool) (hi : index ∈ FP)
    (hindex : ∀ c i, index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f c i).val) :
    SpaceFunction (value S read N f hfit) := by
  let old := read ∘ context
  let a := S.arity ∘ old
  let w := S.width ∘ old
  let n := N ∘ context
  have HO : old ∈ FP := mem_FP_comp context_FP hr
  have HA : UnaryFn a := A.arity.comp HO
  have HW : UnaryFn w := A.width.comp HO
  have HN : UnaryFn n := hN.comp context_FP
  let bits := FixedWidthEmbeddingBits.word a n w target (indexQuery index)
  have HB : bits ∈ FP := FixedWidthEmbeddingBits.word_FP a n w target (indexQuery index)
    HA HN HW target_FP (indexQuery_FP index hi)
  let request := fun q => pair (pair (old q) (bits q)) (pairSnd q)
  have HQ : request ∈ FP := mem_FP_pair (mem_FP_pair HO HB) pairSnd_mem_FP
  have E := A.evaluator.precompose request HQ
  have EP : SpaceFunction (FixedWidthRowBits.value a w (fun q => S.polynomial (old q)) bits pairSnd) := by
    apply E.congr
    funext q
    exact A.packet _ _ _
  have EI : ∀ q i, indexQuery index (pair q (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (f (context q) i).val := by
    intro q i
    simpa only [indexQuery,pairFst_pair,pairSnd_pair] using hindex (context q) i
  exact FixedWidthEmbeddingBits.evaluator a n w target (indexQuery index) (fun q => S.polynomial (old q))
    (fun q => f (context q)) (fun q => hf (context q)) EI pairSnd HA HN HW target_FP (indexQuery_FP index hi) EP

noncomputable def access (A : Access S) (hr : read ∈ FP) (hN : UnaryFn N)
    (hf : ∀ c, Function.Injective (f c)) (index : List Bool → List Bool) (hi : index ∈ FP)
    (hindex : ∀ c i, index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f c i).val) :
    Access (source S read N f hfit) where
  arity := hN
  width := A.width.comp hr
  degree := A.degree.comp hr
  mass := A.mass.comp hr
  coefficient := value S read N f hfit
  evaluator := evaluator S read N f hfit A hr hN hf index hi hindex
  packet c bits modulus := by
    let H (c : List Bool) (r m : ℕ) := residueBits ((((source S read N f hfit).polynomial c).coeff
      (nativeExponent (Equiv.refl _) ((source S read N f hfit).width c) r) : ℤ) : ZMod (m+1))
    change H (context (pair (pair c bits) modulus)) (Nat.fromBitsLE (target (pair (pair c bits) modulus)))
      (Nat.fromBitsLE (pairSnd (pair (pair c bits) modulus))) = H c (Nat.fromBitsLE bits) (Nat.fromBitsLE modulus)
    congr 1 <;> simp only [context,target,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
