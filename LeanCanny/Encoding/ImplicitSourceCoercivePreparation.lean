/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.CoerciveBoxBounds
public import LeanCanny.Algebra.CoerciveHomogeneousLayout
public import LeanCanny.Algebra.FixedWidthBoxRepackSpace
public import LeanCanny.Algebra.FixedWidthKroneckerSpace
public import LeanCanny.Algebra.FixedWidthBivariateRowSpace
public import LeanCanny.Algebra.PolynomialBinaryProductSpace
public import LeanCanny.Algebra.FixedWidthBinaryDerivativeSpace
public import LeanCanny.Algebra.HomogenizationBinarySpace
/-! # Coercive preparation from implicit original polynomial coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem binary_size {f : List Bool → ℕ} (h : BinaryFn f) : UnaryFn (fun q => (f q).size) :=
  (UnaryFn.length h.bits_mem_FP).of_eq (fun q => BinaryNatCode.length_encode (f q))

noncomputable def reindex (S : Source) (f : List Bool → List Bool) : Source where
  arity := S.arity ∘ f
  width := S.width ∘ f
  degree := S.degree ∘ f
  mass := S.mass ∘ f
  polynomial q := S.polynomial (f q)
  fit q := S.fit (f q)
  polynomial_degree q := S.polynomial_degree (f q)
  polynomial_mass q := S.polynomial_mass (f q)

noncomputable def reindex_access (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (f : List Bool → List Bool) (hf : f ∈ FP) : IntegralFramedBankPolynomialModel.Access (reindex S f) where
  arity := A.arity.comp hf
  width := A.width.comp hf
  degree := A.degree.comp hf
  mass := A.mass.comp hf
  coefficient q := A.coefficient (pair (pair (f (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q))
  evaluator := A.evaluator.precompose _ (mem_FP_pair (mem_FP_pair
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP)
  packet q bits modulus := by simp only [pairFst_pair, pairSnd_pair]; exact A.packet _ _ _

def rowWidth (S : Source) (u : List Bool) := CoerciveCoordinateEliminant.width (S.arity u) (S.degree u)
def workWidth (S : Source) (u : List Bool) := max (rowWidth S u) (2*S.degree u+2).size
def squareDegree (S : Source) (u : List Bool) := 2*S.degree u+1
def degreeBound (S : Source) (u : List Bool) := CoerciveBoxGramEliminant.blockDimension (S.arity u) (S.degree u)
def massExponent (S : Source) (u : List Bool) :=
  CoerciveBoxGramEliminant.massExponent (S.arity u) (S.degree u) (S.mass u)

theorem rowWidth_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : UnaryFn (rowWidth S) := by
  have HL : BinaryFn (fun u => Macaulay.level (CoerciveCriticalHomogenization.finDegree (n := S.arity u) (S.degree u))) := by
    have H := ((BinaryFn.ofUnary A.arity).mul ((BinaryFn.const 2).mul A.degree)).add (BinaryFn.const 1)
    apply H.of_eq
    intro u
    unfold Macaulay.level CoerciveCriticalHomogenization.finDegree CoerciveCriticalHomogenization.nativeDegree
    rw [← Equiv.sum_comp CoerciveCriticalHomogenization.layout]
    simp only [Equiv.symm_apply_apply, Fintype.sum_option, Nat.sub_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel, zero_add]
  have HD := ((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1)
  exact binary_size ((BinaryFn.ite (HL.le HD) HD HL).of_eq (fun _ => (max_def _ _).symm))

theorem workWidth_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : UnaryFn (workWidth S) :=
  (rowWidth_unary S A).max (binary_size (((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 2)))

theorem work_fit (S : Source) (u : List Bool) : squareDegree S u < 2^workWidth S u :=
  (by unfold squareDegree; omega : squareDegree S u < 2*S.degree u+2).trans
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)))

theorem degreeBound_binary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : BinaryFn (degreeBound S) := by
  have HC : BinaryFn (fun u => FixedWidthPolynomial.count (S.arity u+1) (rowWidth S u)) :=
    ((BinaryFn.const 2).powUnary ((A.arity.add (UnaryFn.const 1)).mul (rowWidth_unary S A))).of_eq
      (fun u => by simp only [FixedWidthPolynomial.count, ←pow_mul, Nat.mul_comm])
  exact ((BinaryFn.ofUnary A.arity).add (BinaryFn.const 3)).mul HC

theorem massExponent_binary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : BinaryFn (massExponent S) :=
  ((degreeBound_binary S A).mul (((BinaryFn.const 2).mul (degreeBound_binary S A).size).add
    ((BinaryFn.const 2).mul (A.degree.size.add (((BinaryFn.const 2).mul A.mass).add (BinaryFn.const 3)))))).add (BinaryFn.const 1)

theorem source_row_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (V : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (hV : UnaryFn V) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value S.arity V S.polynomial target modulus) := by
  let bits := FixedWidthQuery.repack S.arity V S.arity S.width target
  have HB : bits ∈ FP := FixedWidthQuery.repack_mem_FP A.arity hV A.arity A.width ht
  have HE := A.evaluator.precompose (fun u => pair (pair u (bits u)) (modulus u))
    (mem_FP_pair (mem_FP_pair id_mem_FP HB) hm)
  have HN : SpaceFunction (FixedWidthRowBits.value S.arity S.width S.polynomial bits modulus) :=
    HE.congr (funext fun u => A.packet u (bits u) (modulus u))
  exact FixedWidthBoxRepackBits.evaluator S.arity S.width V S.polynomial
    (fun u e he i => (MvPolynomial.monomial_le_degreeOf i he).trans_lt (S.fit u i)) target modulus
    A.arity A.width hV ht HN

noncomputable def packed (S : Source) (u : List Bool) : ℤ[X] :=
  FixedWidthKronecker.encode (S.arity u) (workWidth S u) (S.polynomial u)

theorem packed_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) :
    SpaceFunction (PrimitivePairBits.coefficient (packed S)) := by
  let C := RationalSubstitution.IntegerBits.context
  let Q := reindex S C
  let H := reindex_access S A C RationalSubstitution.IntegerBits.context_mem_FP
  have HW := (workWidth_unary S A).comp RationalSubstitution.IntegerBits.context_mem_FP
  have ER := source_row_evaluator Q H (workWidth S ∘ C) RationalSubstitution.IntegerBits.selectedDegree pairSnd
    HW RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  have EK := FixedWidthKroneckerBits.evaluator Q.arity (workWidth S ∘ C) Q.degree Q.polynomial
    RationalSubstitution.IntegerBits.selectedDegree pairSnd H.arity HW
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP Q.polynomial_degree
    (fun u => (by unfold squareDegree; omega : S.degree (C u) ≤ squareDegree S (C u)).trans_lt (work_fit S (C u))) ER
  exact EK.congr (funext fun _ => rfl)

noncomputable def squareReader (S : Source) (q : List Bool) :=
  FixedWidthRowBits.value (S.arity ∘ RationalSubstitution.IntegerBits.context)
    (workWidth S ∘ RationalSubstitution.IntegerBits.context)
    (fun q => S.polynomial (RationalSubstitution.IntegerBits.context q)^2)
    RationalSubstitution.IntegerBits.selectedDegree pairSnd q

theorem square_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : SpaceFunction (squareReader S) := by
  let C := RationalSubstitution.IntegerBits.context
  let target := RationalSubstitution.IntegerBits.selectedDegree
  let bits := FixedWidthQuery.repack (S.arity ∘ C) (workWidth S ∘ C)
    (S.arity ∘ C) (workWidth S ∘ C) target
  have HB : bits ∈ FP := FixedWidthQuery.repack_mem_FP (A.arity.comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((workWidth_unary S A).comp RationalSubstitution.IntegerBits.context_mem_FP)
    (A.arity.comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((workWidth_unary S A).comp RationalSubstitution.IntegerBits.context_mem_FP) RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have E := (PolynomialBinaryProductBits.evaluator (packed S) (packed S) (packed_evaluator S A) (packed_evaluator S A)).precompose
    (fun q => pair (pair (C q) (bits q)) (pairSnd q))
    (mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP HB) pairSnd_mem_FP)
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair]
  change residueBits (((packed S (C q)*packed S (C q)).coeff (Nat.fromBitsLE (bits q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1)) = _
  have HE : packed S (C q)*packed S (C q) = FixedWidthKronecker.encode (S.arity (C q)) (workWidth S (C q)) (S.polynomial (C q)^2) := by
    rw [map_pow, pow_two]; rfl
  rw [HE]
  have HF : (S.polynomial (C q)^2).totalDegree < 2^workWidth S (C q) :=
    (MvPolynomial.totalDegree_pow _ 2).trans_lt
      ((Nat.mul_le_mul_left 2 (S.polynomial_degree _)).trans_lt ((by unfold squareDegree; omega : 2*S.degree (C q)<squareDegree S (C q)).trans (work_fit S (C q))))
  have HR := FixedWidthBivariateRowBits.coefficient_repack (S.arity ∘ C) (workWidth S ∘ C)
    (fun q => S.polynomial (C q)^2) target q HF
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q)+1))) HR

end LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
