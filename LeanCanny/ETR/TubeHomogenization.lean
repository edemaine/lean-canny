/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationSpace
public import LeanCanny.ETR.TubeIndexedSpace
public import LeanCanny.ETR.TubeIndexedBounds

/-! # Partial homogenization of the actual tube projection rows

Only point coordinates have weight one. Direction and perturbation parameters
keep weight zero. Thus the affine chart with homogenizing coordinate one gives
exactly the original projection equations for every fixed parameter choice.
The degree, coordinate widths and coefficient budgets come from the actual
compiled ETR source. A complete residue evaluator reuses its coefficient reader.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeHomogenization
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra LeanCanny.Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection
  TubeIndexed.projectionResidue

abbrev Native (bits : List Bool) := Option (TubeSource.IntegerProjectionVariable bits)

def pointWeight (n : ℕ) : Variable n → ℕ :=
  HomogenizationLayout.prefixWeight (variableEquiv n) (pointCount n)

@[simp] theorem weight_point (n : ℕ) (i : Point n) : pointWeight n (.inl (.inl i)) = 1 := by
  simp [pointWeight, HomogenizationLayout.prefixWeight, (pointEquiv n i).isLt]

@[simp] theorem weight_direction (n : ℕ) (i : Point n) : pointWeight n (.inl (.inr i)) = 0 := by
  simp [pointWeight, HomogenizationLayout.prefixWeight]

@[simp] theorem weight_parameter (n : ℕ) (p : TubePolynomial.Parameter) : pointWeight n (.inr p) = 0 := by
  unfold pointWeight HomogenizationLayout.prefixWeight
  apply ite_eq_right
  rw [index_parameter]
  omega

noncomputable def polynomial (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) : MvPolynomial (Native bits) ℤ :=
  WeightedHomogenization.homogenize (pointWeight ((CompactSource.term bits).arity)) (TubeIndexed.degreeBound bits)
    (TubeSource.integerProjection bits s j)

theorem homogeneous (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) :
    (polynomial bits s j).IsWeightedHomogeneous (WeightedHomogenization.weights (pointWeight ((CompactSource.term bits).arity)))
      (TubeIndexed.degreeBound bits) := WeightedHomogenization.homogeneous _ _ _

theorem source_degree (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) : (TubeSource.integerProjection bits s j).totalDegree ≤ TubeIndexed.degreeBound bits := by
  have h := TubeSource.integer_projection_degree_le_code bits s j
  simpa only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, TubeIndexed.degreeBound] using h

theorem totalDegree_le (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) : (polynomial bits s j).totalDegree ≤ 2 * TubeIndexed.degreeBound bits := by
  have h := WeightedHomogenization.totalDegree_le (pointWeight ((CompactSource.term bits).arity)) (TubeIndexed.degreeBound bits)
    (TubeSource.integerProjection bits s j)
  exact h.trans ((Nat.add_le_add_left (source_degree bits s j) _).trans_eq (by omega))

theorem eval_chart {R : Type*} [CommSemiring R] (bits : List Bool)
    (s : Finset (Constraint ((CompactSource.term bits).arity))) (j : TubeSource.ProjectionIndex bits)
    (φ : ℤ →+* R) (x : TubeSource.IntegerProjectionVariable bits → R) :
    (polynomial bits s j).eval₂ φ (fun i => i.elim 1 x) = (TubeSource.integerProjection bits s j).eval₂ φ x :=
  HomogenizationLayout.eval_chart _ _ _ _ (source_degree bits s j) φ x

theorem eval_projection_chart (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) (epsilon delta alpha : ℝ) (x v : TubeSource.Coordinate bits → ℝ) :
    (polynomial bits s j).eval₂ (Int.castRingHom ℝ)
      (fun i => i.elim 1 (Sum.elim (Sum.elim x v) (TubePolynomial.parameters epsilon delta alpha))) =
      (TubeSource.projectionSystem bits s j).eval₂ (TubePolynomial.coefficientMap epsilon delta alpha) (Sum.elim x v) := by
  rw [eval_chart]
  exact TubeSource.eval_integerProjection bits s j epsilon delta alpha x v

theorem coefficient_bound (bits : List Bool) (s : Finset (Constraint ((CompactSource.term bits).arity)))
    (j : TubeSource.ProjectionIndex bits) (e : Native bits →₀ ℕ) :
    ((polynomial bits s j).coeff e).natAbs ≤ 2 ^ TubeSource.massBudget (CompactSource.size bits) := by
  rw [polynomial, WeightedHomogenization.coefficient]
  split_ifs
  · exact (Algebra.MvMass.coeff_le _ _).trans (TubeSource.integer_projection_mass_le bits s j)
  · exact Nat.zero_le _

theorem support_fits (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeSource.ProjectionIndex bits) (e : Native bits →₀ ℕ) (he : e ∈ (polynomial bits s j).support)
    (i : Native bits) : e i < 2 ^ TubeIndexed.blockWidth bits :=
  (WeightedHomogenization.support_coordinate_le _ _ _ (source_degree bits s j) e he i).trans_lt
    (TubeIndexed.degreeBound_lt bits)

noncomputable def outputEquiv (bits : List Bool) : Native bits ≃ Fin (TubeIndexed.projectionDimension bits + 1) :=
  HomogenizationLayout.variableEquiv (variableEquiv ((CompactSource.term bits).arity))

noncomputable def dimension (source : List Bool → List Bool) (c : List Bool) : ℕ := TubeIndexed.projectionDimension (source c)
noncomputable def pointDimension (source : List Bool → List Bool) (c : List Bool) : ℕ := pointCount (TubeIndexed.arity (source c))
def width (source : List Bool → List Bool) (c : List Bool) : ℕ := TubeIndexed.blockWidth (source c)
def degree (source : List Bool → List Bool) (c : List Bool) : ℕ := TubeIndexed.degreeBound (source c)

noncomputable def value (source active row modulus : List Bool → List Bool) : List Bool → List Bool :=
  HomogenizationBits.value (dimension source) (pointDimension source) (width source) (degree source)
    (TubeIndexed.projectionResidue source active row modulus)

noncomputable def evaluator (source active row modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value source active row modulus) := by
  have hN : UnaryFn (dimension source) := TubeIndexed.projectionDimension_unary.comp hs
  have hA0 := TubeProjectionQuery.pointCount_unary (TubeIndexed.arity_unary.comp hs)
  have hA : UnaryFn (pointDimension source) := hA0.of_eq (fun _ => rfl)
  have hW : UnaryFn (width source) := TubeIndexed.blockWidth_unary.comp hs
  have hD : UnaryFn (degree source) := TubeIndexed.degreeBound_unary.comp hs
  have EP := TubeIndexed.projectionResidueEvaluator source active row modulus hs ha hr hm
  have ES := HomogenizationBits.evaluator hN hA hW hD EP
  exact ES.congr (funext fun q => rfl)

theorem value_packet (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value source active row modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((polynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
        (TubeProjection.decodedRow (TubeIndexed.compiled source) row c)).coeff
          (FixedWidthPolynomial.nativeExponent (outputEquiv (source c)) (width source c) r) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  apply HomogenizationBits.value_packet
    (dimension source) (pointDimension source) (width source) (degree source)
    (TubeIndexed.projectionResidue source active row modulus) c
    (variableEquiv (TubeIndexed.arity (source c))) _
    (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1)))
  · simp [residueBits, BinaryNatCode.encode]
  · intro k
    change TubeIndexed.projectionResidue source active row modulus (pair c (BinaryNatCode.encode k)) =
      TubeIndexed.projectionAt source active row modulus c k
    exact TubeIndexed.projectionResidue_packet source active row modulus c k

end LeanCanny.ETR.TubeHomogenization
