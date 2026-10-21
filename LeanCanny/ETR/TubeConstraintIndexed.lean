/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConstraintCoefficientSource
public import LeanCanny.Algebra.RationalSubstitutionResidue
public import LeanCanny.Algebra.FixedWidthPolynomialFP
public import LeanCanny.ETR.TubeIndexedBounds

/-! # Streamed rank coefficients of the integer tube constraints

The degree bound determines fixed-width exponent blocks. Binary ranks cover
the complete polynomial, and the native coefficient reader supplies its actual
coefficients without storing the exponentially many monomials.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConstraintIndexed
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MatrixPower RationalSubstitution.Indexed
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet row : List Bool → List Bool)

noncomputable def blockWidth (c : List Bool) : ℕ := TubeIndexed.blockWidth (pairFst (packet c))

theorem blockWidth_unary (hp : packet ∈ FP) : UnaryFn (blockWidth packet) :=
  TubeIndexed.blockWidth_unary.comp (mem_FP_comp hp pairFst_mem_FP)

noncomputable def coefficientAt (p rowBits : List Bool) (r : ℕ) : ℤ :=
  (integerConstraint p (TubeConstraintCoefficient.decodedRow id (fun _ => rowBits) p)).coeff
    (exponentVector (TubeSampleCoefficient.A id p)
      (FixedWidthPolynomial.entry (blockWidth id p) r))

noncomputable def coefficient (c : List Bool) (r : ℕ) : ℤ :=
  coefficientAt (packet c) (row c) r

theorem coefficient_eq (c : List Bool) (r : ℕ) : coefficient packet row c r =
    (integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c)).coeff
      (exponentVector (TubeSampleCoefficient.A packet c) (FixedWidthPolynomial.entry (blockWidth packet c) r)) := rfl

theorem source_eq (c : List Bool) :
    source (TubeSampleCoefficient.A packet c)
      (FixedWidthPolynomial.count (TubeSampleCoefficient.A packet c) (blockWidth packet c))
      (coefficient packet row c) (FixedWidthPolynomial.entry (blockWidth packet c)) =
        integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c) := by
  apply FixedWidthPolynomial.indexed_source_eq
  intro e he j
  exact ((MvPolynomial.monomial_le_degreeOf j he).trans
    (integerConstraint_degreeOf _ _ j)).trans_lt (TubeIndexed.degreeBound_lt _)

noncomputable def value (q : List Bool) : List Bool :=
  RationalSubstitution.IntegerBits.coefficientResidue
    (coefficient packet row (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q))))
    (Nat.fromBitsLE (pairSnd q) + 1)

theorem evaluator (hp : packet ∈ FP) (hr : row ∈ FP) : SpaceFunction (value packet row) := by
  let ctx := fun q : List Bool => pairFst (pairFst q)
  have hctx : ctx ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  let target := fun q : List Bool => BinaryNat.normalize (pairSnd (pairFst q))
  have ht : target ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  let E := TubeConstraintCoefficient.encodedEvaluator (packet ∘ ctx) (row ∘ ctx) pairSnd
    (blockWidth packet ∘ ctx) target (mem_FP_comp hctx hp) (mem_FP_comp hctx hr)
    pairSnd_mem_FP ((blockWidth_unary packet hp).comp hctx) ht
  refine E.congr (funext fun q => ?_)
  have he : TubeSampleCoefficient.exponent (packet ∘ ctx) (blockWidth packet ∘ ctx) target q =
      exponentVector (TubeSampleCoefficient.A packet (ctx q))
        (FixedWidthPolynomial.entry (blockWidth packet (ctx q)) (Nat.fromBitsLE (pairSnd (pairFst q)))) := by
    dsimp +instances only [TubeSampleCoefficient.A, TubeParameter.spatialCount]
    ext j
    simp only [TubeSampleCoefficient.exponent, exponentVector, Finsupp.coe_equivFunOnFinite_symm,
      FixedWidthQuery.coordinate, target, BinaryNat.normalize_eq_bits, FixedWidthPolynomial.entry,
      Function.comp_apply]
    rfl
  rw [he]
  rfl

attribute [local irreducible] RationalSubstitution.IntegerBits.coefficientResidue

theorem value_packet (c : List Bool) (r m : ℕ) (hm : 0 < m) :
    value packet row (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      RationalSubstitution.IntegerBits.coefficientResidue (coefficient packet row c r) m := by
  simp only [value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.sub_add_cancel hm]

end LeanCanny.ETR.TubeConstraintIndexed
