/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConstraintIndexed
public import LeanCanny.Algebra.RationalSubstitutionResidue

/-! # Native rational substitution into the actual integer constraints

Only coordinate polynomial readers are supplied. The complete native constraint
reader, rank exponents, and clearing allowance instantiate the substitution
engine, with every child computation included in its space certificate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConstraintSubstitution
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MatrixPower RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet row : List Bool → List Bool)
variable (n d : List Bool → ℕ → Polynomial ℤ)

noncomputable def family : IntegerBits.Family where
  arity := TubeSampleCoefficient.A packet
  width c := 2 * TubeIndexed.degreeBound (pairFst (packet c))
  terms c := FixedWidthPolynomial.count (TubeSampleCoefficient.A packet c) (TubeConstraintIndexed.blockWidth packet c)
  exponent c := FixedWidthPolynomial.entry (TubeConstraintIndexed.blockWidth packet c)
  coefficient := TubeConstraintIndexed.coefficient packet row
  numerator := n
  denominator := d
  exponent_le _ _ _ _ _ := (FixedWidthPolynomial.entry_lt _ _ _).le.trans (TubeIndexed.clearingWidth_le _)

theorem polynomial_eq (c : List Bool) : (family packet row n d).polynomial c =
    clearedWith (fun _ => TubeIndexed.degreeBound (pairFst (packet c)))
      (integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c))
      (fun i => n c i.val) (fun i => d c i.val) := by
  unfold IntegerBits.Family.polynomial family
  rw [Indexed.cleared_eq_clearedWith_source, TubeConstraintIndexed.source_eq]
  rfl

noncomputable def arityCode (c : List Bool) : List Bool := BinaryNatCode.encode (TubeSampleCoefficient.A packet c)

noncomputable def widthCode (c : List Bool) : List Bool :=
  BinaryNatCode.encode (2 * TubeIndexed.degreeBound (pairFst (packet c)))

noncomputable def termsCode : List Bool → List Bool :=
  FixedWidthPolynomial.countCode (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)

noncomputable def exponentRead : List Bool → List Bool :=
  FixedWidthPolynomial.exponentRead (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)

theorem arityCode_FP (hp : packet ∈ FP) : arityCode packet ∈ FP :=
  bits_mem_FP (TubeSampleCoefficient.A_unary packet hp)

theorem widthCode_FP (hp : packet ∈ FP) : widthCode packet ∈ FP :=
  bits_mem_FP ((UnaryFn.const 2).mul (TubeIndexed.degreeBound_unary.comp (mem_FP_comp hp pairFst_mem_FP)))

theorem termsCode_FP (hp : packet ∈ FP) : termsCode packet ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP (TubeSampleCoefficient.A_unary packet hp) (TubeConstraintIndexed.blockWidth_unary packet hp)

theorem exponentRead_FP (hp : packet ∈ FP) : exponentRead packet ∈ FP :=
  FixedWidthPolynomial.exponentRead_mem_FP (TubeSampleCoefficient.A_unary packet hp) (TubeConstraintIndexed.blockWidth_unary packet hp)

structure CoordinateReaders where
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  numeratorEvaluator : SpaceFunction numerator
  denominatorEvaluator : SpaceFunction denominator
  numerator_eq : ∀ c i, i < TubeSampleCoefficient.A packet c → ∀ k m, 0 < m →
    numerator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((n c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < TubeSampleCoefficient.A packet c → ∀ k m, 0 < m →
    denominator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((d c i).coeff k : ℤ) : ZMod m)

/-- Reindex only the context, retaining the binary coordinate, degree, and modulus. -/
def coordinateQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (IntegerBits.context q)) (IntegerBits.selectedDegree q)) (pairSnd q)

theorem coordinateQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : coordinateQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp IntegerBits.context_mem_FP hf) IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

def CoordinateReaders.precompose (C : CoordinateReaders packet n d) (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateReaders (packet ∘ f) (fun c => n (f c)) (fun c => d (f c)) where
  numerator := C.numerator ∘ coordinateQuery f
  denominator := C.denominator ∘ coordinateQuery f
  numeratorEvaluator := C.numeratorEvaluator.precompose _ (coordinateQuery_FP f hf)
  denominatorEvaluator := C.denominatorEvaluator.precompose _ (coordinateQuery_FP f hf)
  numerator_eq c i hi k m hm := by
    simpa only [Function.comp_apply, coordinateQuery, IntegerBits.context, IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair] using C.numerator_eq (f c) i hi k m hm
  denominator_eq c i hi k m hm := by
    simpa only [Function.comp_apply, coordinateQuery, IntegerBits.context, IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair] using C.denominator_eq (f c) i hi k m hm

noncomputable def access (C : CoordinateReaders packet n d) : IntegerBits.Access (family packet row n d) where
  arity := arityCode packet
  width := widthCode packet
  terms := termsCode packet
  exponent := exponentRead packet
  coefficient := TubeConstraintIndexed.value packet row
  numerator := C.numerator
  denominator := C.denominator
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq _ := Nat.fromBitsLE_bits _
  terms_eq c := by
    simp only [termsCode, FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits, family]
  exponent_eq c r _ i hi := by
    change i < TubeSampleCoefficient.A packet c at hi
    have he := FixedWidthPolynomial.exponentRead_packet (TubeSampleCoefficient.A packet)
      (TubeConstraintIndexed.blockWidth packet) c r i hi
    exact (congrArg Nat.fromBitsLE he).trans (Nat.fromBitsLE_bits _)
  coefficient_eq c r _ m hm := TubeConstraintIndexed.value_packet packet row c r m hm
  numerator_eq := C.numerator_eq
  denominator_eq := C.denominator_eq

attribute [local irreducible] exponentRead

theorem access_controls (C : CoordinateReaders packet n d) (hp : packet ∈ FP) :
    (access packet row n d C).ControlsPolyTime := by
  constructor
  · exact arityCode_FP packet hp
  · exact widthCode_FP packet hp
  · exact termsCode_FP packet hp
  · exact exponentRead_FP packet hp

theorem evaluator (C : CoordinateReaders packet n d) (hp : packet ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family packet row n d).value :=
  (access packet row n d C).evaluator (access_controls packet row n d C hp)
    (TubeConstraintIndexed.evaluator packet row hp hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeConstraintSubstitution
