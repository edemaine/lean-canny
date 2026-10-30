/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.IndexedIntegerDerivativeSpace
public import LeanCanny.Algebra.UnivariateRowSpace
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Algebra.PolynomialFamilyProductSpace

/-! # Native coordinate Thom signs at complete square-system labels

Binary query fields select a coordinate and derivative order. The original
system and its complete root label stay fixed. Equality of these streamed
signs identifies coordinates across different labels, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteCoordinateThom
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def coordinate (F : Inputs) (c d : List Bool) : Fin (F.count c) :=
  SquareSampleInput.selected F c (pairFst d)

theorem coordinate_unary {F : Inputs} (h : F.Access) :
    UnaryFn (fun z => (coordinate F (pairFst z) (pairSnd z)).val) :=
  UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    ((h.count.comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def baseAt (F : Inputs) (c d : List Bool) : ℤ[X] :=
  F.annihilator c (coordinate F c d)

noncomputable def base (F : Inputs) (z : List Bool) : ℤ[X] := baseAt F (pairFst z) (pairSnd z)

def order (z : List Bool) : List Bool := pairSnd (pairSnd z)
theorem order_FP : order ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

noncomputable def polynomial (F : Inputs) : List Bool → ℤ[X] :=
  IndexedIntegerDerivativeBits.polynomial (base F) order

theorem baseEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (base F)) := by
  have hc := RationalSubstitution.IntegerBits.context_mem_FP
  have E := SquareSampleInput.ann_evaluator h (mem_FP_comp hc pairFst_mem_FP)
    (fun q => coordinate F (pairFst (RationalSubstitution.IntegerBits.context q))
      (pairSnd (RationalSubstitution.IntegerBits.context q))) ((coordinate_unary h).comp hc)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  exact E.congr (funext fun _ => rfl)

theorem coefficientEvaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  IndexedIntegerDerivativeBits.evaluator (base F) (baseEvaluator h) order_FP

noncomputable def mass (F : Inputs) (z : List Bool) : ℕ :=
  IteratedDerivativeBits.massBudget (F.annDegree (pairFst z)) (F.annHeight (pairFst z))

theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  IteratedDerivativeBits.massBudget_binary (h.annDegree.comp pairFst_mem_FP) (h.annHeight.comp pairFst_mem_FP)

theorem polynomial_degree (F : Inputs) (z : List Bool) :
    (polynomial F z).natDegree ≤ F.annDegree (pairFst z) :=
  (Polynomial.natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans (F.ann_degree _ _))

theorem polynomial_mass (F : Inputs) (z : List Bool) : coefficientMass (polynomial F z) ≤ 2 ^ mass F z :=
  IteratedDerivativeBits.mass_bound _ _ _ (F.ann_degree _ _)
    (fun k => (Nat.size_le.mp (F.ann_height _ _ k)).le) _

noncomputable def test (F : Inputs) : SquareSampleCompleteIndexedPolynomialTest.Test F where
  polynomial c d := (polynomial F (pair c d)).toMvPolynomial (coordinate F c d)
  degree z := F.annDegree (pairFst z)
  mass := mass F
  polynomial_degree z := (DiagonalUnivariateSystem.degree_le _ _).trans (by
    simpa only [pairFst_pair] using polynomial_degree F (pair (pairFst z) (pairSnd z)))
  polynomial_mass z := (DiagonalUnivariateSystem.mass_le _ _).trans (by
    simpa only [mass, pairFst_pair] using polynomial_mass F (pair (pairFst z) (pairSnd z)))

def normalize (z : List Bool) : List Bool := pair (pairFst z) (pairSnd z)
theorem normalize_FP : normalize ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

theorem testAccess {F : Inputs} (h : F.Access) : (test F).Access := by
  have hc := RationalSubstitution.IntegerBits.context_mem_FP
  have hD : BinaryFn (fun z => F.annDegree (pairFst z)) := h.annDegree.comp pairFst_mem_FP
  have hW : UnaryFn (fun z => (F.annDegree (pairFst z)).size) :=
    (UnaryFn.length hD.bits_mem_FP).of_eq (fun z => BinaryNatCode.length_encode _)
  have P := PolynomialFamilyProductBits.reindexEvaluator (coefficientEvaluator h)
    (normalize ∘ RationalSubstitution.IntegerBits.context) (mem_FP_comp hc normalize_FP)
  have E := UnivariateRowBits.evaluator (h.count.comp (mem_FP_comp hc pairFst_mem_FP)) (hW.comp hc)
    (fun q => coordinate F (pairFst (RationalSubstitution.IntegerBits.context q))
      (pairSnd (RationalSubstitution.IntegerBits.context q))) ((coordinate_unary h).comp hc)
    (polynomial F ∘ normalize ∘ RationalSubstitution.IntegerBits.context) P
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨hD, mass_binary h, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

noncomputable def value (F : Inputs) : List Bool → List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value F (test F)

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator h (testAccess h)

theorem packet (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (i : Fin (F.count c)) (k : ℕ) :
    value F (pair (pair c w) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (ThomEncoding.sign ((F.annihilator c i).map (Int.castRingHom ℝ))
        ((SquareSampleCompleteVertices.candidate F c w hw).val i) k) := by
  rw [value, SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w _ hw]
  have hi : coordinate F c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)) = i := by
    simp only [coordinate, pairFst_pair, SquareSampleInput.selected_encode]
  have hp : polynomial F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (F.annihilator c i) := by
    unfold polynomial IndexedIntegerDerivativeBits.polynomial
    simp only [base, order, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change Polynomial.derivative^[k] (baseAt F c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) = _
    rw [baseAt, hi]
  change InfinitesimalSign.encode (SignType.sign (((polynomial F
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)))).toMvPolynomial
      (coordinate F c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)))).eval₂
        (Int.castRingHom ℝ) (SquareSampleCompleteVertices.candidate F c w hw).val)) = _
  rw [DiagonalUnivariateSystem.eval, hi, hp]
  simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]

end LeanCanny.Encoding.SquareSampleCompleteCoordinateThom
