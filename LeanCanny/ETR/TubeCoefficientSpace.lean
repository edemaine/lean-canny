/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDenseQuery
public import LeanCanny.ETR.TubeCombine

/-! # Polynomial-space coefficient access to the full integer tube

The source-square and two shifted-source children supply the dense terms.
The zero-source child supplies the sparse remainder. Sequential pairing and
FP modular arithmetic combine them according to the actual tube coefficient
identity. Source validation and all space-bounded work are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

-- Keep the child semantics and geometry behind their proved coefficient APIs.
attribute [local irreducible] TubeDense.value TubeZeroQuery.value TubeDense.polynomial
  TubePolynomial.integerPolynomial TubePolynomial.spatialCoefficient TubePolynomial.shiftedSpatialCoefficient
  TubeZeroQuery.exponent TubeCombine.finish

noncomputable def coefficient (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target : List Bool → List Bool) (c : List Bool) : ℤ :=
  (TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c))).coeff
    (TubeZeroQuery.exponent (TubeDense.arity base) W target c)

noncomputable def value (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((coefficient base W active target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def responses (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair (pair (TubeDense.value base 2 W target modulus none c) (TubeDense.value base 1 W target modulus (some false) c))
    (pair (TubeDense.value base 1 W target modulus (some true) c) (TubeZeroQuery.value (TubeDense.arity base) W active target modulus c))

theorem responseEvaluator (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (hb : base ∈ FP) (hW : UnaryFn W)
    (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (responses base W active target modulus) := by
  let A := TubeDense.evaluator base 2 (by decide) W target modulus none hb hW ht hm
  let F := TubeDense.evaluator base 1 (by decide) W target modulus (some false) hb hW ht hm
  let T := TubeDense.evaluator base 1 (by decide) W target modulus (some true) hb hW ht hm
  let Z := TubeZeroQuery.evaluator (TubeDense.arity base) W active target modulus (TubeDense.arity_unary hb) hW ha ht hm
  let E := (A.pairOutputs F).pairOutputs (T.pairOutputs Z)
  exact E.congr (funext fun _ => rfl)

theorem finish_responses (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (c : List Bool) :
    TubeCombine.finish active modulus (pair c (responses base W active target modulus c)) = value base W active target modulus c := by
  classical
  unfold responses TubeDense.value TubeZeroQuery.value
  rw [TubeCombine.finish_residueBits]
  unfold value
  apply congrArg residueBits
  simp only [TubeDense.coefficient_none, TubeDense.coefficient_some]
  rw [coefficient, TubePolynomial.coeff_integerPolynomial, TubePolynomial.squareMultiplicity_eq]
  simp only [TubeZeroQuery.coefficient, activeSet, Finset.mem_filter, Finset.mem_univ, true_and,
    constraintIndex_source_false, constraintIndex_source_true]
  split_ifs <;> push_cast <;> ring

theorem exponent_eq_of_encoded (base : List Bool → List Bool) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (c : List Bool) (m : Coordinate (TubeDense.arity base c) →₀ ℕ)
    (ht : target c = FixedWidthNatVector.encode (dimension (TubeDense.arity base c)) (W c)
      (TubeZero.paddedExponent (TubeDense.arity base c) m)) (hm : ∀ j, m j < 2 ^ W c) :
    TubeZeroQuery.exponent (TubeDense.arity base) W target c = m := by
  ext j
  have hpad : TubeZero.paddedExponent (TubeDense.arity base c) m (coordinateEquiv _ j).val = m j := by
    unfold TubeZero.paddedExponent
    rw [dite_eq_left (coordinateEquiv _ j).isLt]
    change m ((coordinateEquiv _).symm (coordinateEquiv _ j)) = m j
    rw [Equiv.symm_apply_apply]
  simp only [TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate]
  rw [ht, FixedWidthNatVector.decode_block _ _ _ _ (coordinateEquiv _ j).isLt (by rw [hpad]; exact hm j)]
  exact hpad

theorem coefficient_eq_native (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target : List Bool → List Bool) (c : List Bool) (m : Coordinate (TubeDense.arity base c) →₀ ℕ)
    (ht : target c = FixedWidthNatVector.encode (dimension (TubeDense.arity base c)) (W c)
      (TubeZero.paddedExponent (TubeDense.arity base c) m)) (hm : ∀ j, m j < 2 ^ W c) :
    coefficient base W active target c =
      (TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c))).coeff m := by
  unfold coefficient
  rw [exponent_eq_of_encoded base W target c m ht hm]

theorem evaluator (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (hb : base ∈ FP) (hW : UnaryFn W)
    (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (value base W active target modulus) := by
  let R := responseEvaluator base W active target modulus hb hW ha ht hm
  let E := R.withInput.postcompose (TubeCombine.finish active modulus) (TubeCombine.finish_mem_FP ha hm)
  exact E.congr (funext fun c => finish_responses base W active target modulus c)

end LeanCanny.ETR.TubeCoefficient
