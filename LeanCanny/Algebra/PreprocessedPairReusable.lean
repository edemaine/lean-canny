/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairBounds
public import LeanCanny.Algebra.ValidatedPolynomialReaders

/-! # A computed primitive pair as a subsequent polynomial input

The original source controls supply an FP output-height bound. The actual
output degree and coefficients are computed in space, and checked contexts
provide the exact FP degree metadata required by the next algebraic stage.
-/

@[expose] public section

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

variable (F G : Family) (A : Readers F) (B : Readers G)
variable (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0)

theorem outputEvaluator : SpaceFunction (ValidatedDegreeBits.coefficient (outputFamily F G A B hF hG).polynomial) := by
  have E := (parameterEvaluator F G A B hF hG).precompose
    PrimitivePairBits.modularCoefficientQuery PrimitivePairBits.modularCoefficientQuery_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, PrimitivePairBits.coefficient, PrimitivePairBits.modularCoefficientQuery,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair,
    ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context, ValidatedDegreeBits.modulus, outputFamily]
  rfl

noncomputable def reusableFamily : Family := ValidatedDegreeBits.family (outputFamily F G A B hF hG)

noncomputable def reusableReaders : Readers (reusableFamily F G A B hF hG) :=
  ValidatedDegreeBits.readers _ (outputHeight_binary F G A B)
    (outputEvaluator F G A B hF hG) (degreeEvaluator F G A B hF hG)

noncomputable def reuseContext (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (parameter F G A B hF hG c).natDegree)

theorem reuseContextEvaluator : SpaceFunction (reuseContext F G A B hF hG) :=
  (degreeEvaluator F G A B hF hG).withInput

theorem reusable_packet (c : List Bool) :
    (reusableFamily F G A B hF hG).polynomial
        (pair c (BinaryNatCode.encode (parameter F G A B hF hG c).natDegree)) = parameter F G A B hF hG c :=
  ValidatedDegreeBits.family_packet (outputFamily F G A B hF hG) c

theorem reusable_separable {L : Type*} [Field L] [CharZero L] (c : List Bool) :
    (((reusableFamily F G A B hF hG).polynomial c).map (Int.castRingHom L)).Separable := by
  have hp : ∀ c, (((outputFamily F G A B hF hG).polynomial c).map (Int.castRingHom L)).Separable :=
    parameter_separable_in_field (L := L) F G A B hF hG
  exact ValidatedDegreeBits.family_separable (outputFamily F G A B hF hG) hp c

theorem reusable_ne_zero (c : List Bool) : (reusableFamily F G A B hF hG).polynomial c ≠ 0 :=
  ValidatedDegreeBits.family_ne_zero (outputFamily F G A B hF hG) (parameter_ne_zero F G A B hF hG) c

end LeanCanny.Algebra.PreprocessedPair
