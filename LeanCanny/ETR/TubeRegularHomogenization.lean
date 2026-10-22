/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularSpace

/-! # Partial homogenization of the full regular tube system

Both the reciprocal and point coordinates are homogenized. Direction and
perturbation coordinates remain coefficient parameters. The actual regular-row
reader supplies the homogenized coefficients with complete space certificates.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularHomogenization
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra LeanCanny.Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection
  TubeRegularBits.value

abbrev Native (bits : List Bool) := Option (TubeRegularSource.Variable bits)

def pointWeight (n : ℕ) : Option (TubeProjectionEncoding.Variable n) → ℕ :=
  HomogenizationLayout.prefixWeight (HomogenizationLayout.variableEquiv (variableEquiv n)) (pointCount n + 1)

theorem pointWeight_eq (n : ℕ) : pointWeight n = WeightedHomogenization.weights (TubeHomogenization.pointWeight n) :=
  (HomogenizationLayout.weights_prefix (variableEquiv n) (pointCount n)).symm

noncomputable def polynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) : MvPolynomial (Native bits) ℤ :=
  WeightedHomogenization.homogenize (pointWeight (CompactSource.term bits).arity) (TubeIndexed.degreeBound bits)
    (TubeRegularSource.polynomial bits s j)

theorem homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits) :
    (polynomial bits s j).IsWeightedHomogeneous (WeightedHomogenization.weights (pointWeight (CompactSource.term bits).arity))
      (TubeIndexed.degreeBound bits) := WeightedHomogenization.homogeneous _ _ _

theorem eval_chart {R : Type*} [CommSemiring R] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) (φ : ℤ →+* R) (x : TubeRegularSource.Variable bits → R) :
    (polynomial bits s j).eval₂ φ (fun i => i.elim 1 x) = (TubeRegularSource.polynomial bits s j).eval₂ φ x :=
  HomogenizationLayout.eval_chart _ _ _ _ (TubeRegularSource.degree_le bits s j) φ x

theorem support_fits (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits)
    (e : Native bits →₀ ℕ) (he : e ∈ (polynomial bits s j).support) (i : Native bits) :
    e i < 2 ^ TubeIndexed.blockWidth bits :=
  (WeightedHomogenization.support_coordinate_le _ _ _ (TubeRegularSource.degree_le bits s j) e he i).trans_lt
    (TubeIndexed.degreeBound_lt bits)

theorem coefficient_bound (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits)
    (e : Native bits →₀ ℕ) : ((polynomial bits s j).coeff e).natAbs ≤ 2 ^ TubeRegularSource.coefficientBudget bits := by
  rw [polynomial, WeightedHomogenization.coefficient]
  split_ifs
  · exact TubeRegularSource.coefficient_bound bits s j e.some
  · exact Nat.zero_le _

noncomputable def outputEquiv (bits : List Bool) : Native bits ≃ Fin (TubeIndexed.projectionDimension bits + 1 + 1) :=
  HomogenizationLayout.variableEquiv (TubeHomogenization.outputEquiv bits)

noncomputable def dimension (source : List Bool → List Bool) (c : List Bool) : ℕ := TubeIndexed.projectionDimension (source c) + 1
noncomputable def pointDimension (source : List Bool → List Bool) (c : List Bool) : ℕ := pointCount (TubeIndexed.arity (source c)) + 1

noncomputable def value (source active row modulus : List Bool → List Bool) : List Bool → List Bool :=
  HomogenizationBits.value (dimension source) (pointDimension source) (TubeHomogenization.width source)
    (TubeHomogenization.degree source) (TubeRegularBits.value source active row modulus)

theorem evaluator (source active row modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value source active row modulus) := by
  have hN : UnaryFn (dimension source) := (TubeIndexed.projectionDimension_unary.comp hs).add (UnaryFn.const 1)
  have hA0 := (TubeProjectionQuery.pointCount_unary (TubeIndexed.arity_unary.comp hs)).add (UnaryFn.const 1)
  have hA : UnaryFn (pointDimension source) := hA0.of_eq (fun _ => rfl)
  have hW : UnaryFn (TubeHomogenization.width source) := TubeIndexed.blockWidth_unary.comp hs
  have hD : UnaryFn (TubeHomogenization.degree source) := TubeIndexed.degreeBound_unary.comp hs
  have ER := TubeRegularBits.evaluator source active row modulus hs ha hr hm
  have ES := HomogenizationBits.evaluator hN hA hW hD ER
  exact ES.congr (funext fun q => rfl)

theorem value_packet (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value source active row modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((polynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
        (TubeRegularBits.decodedIndex source row c)).coeff
          (FixedWidthPolynomial.nativeExponent (outputEquiv (source c)) (TubeHomogenization.width source c) r) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  apply HomogenizationBits.value_packet (dimension source) (pointDimension source)
    (TubeHomogenization.width source) (TubeHomogenization.degree source) (TubeRegularBits.value source active row modulus) c
    (TubeHomogenization.outputEquiv (source c)) _
    (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1)))
  · simp [residueBits, BinaryNatCode.encode]
  · intro k
    exact TubeRegularBits.value_packet source active row modulus c k

end LeanCanny.ETR.TubeRegularHomogenization
