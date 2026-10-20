/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionSpace

/-! # Native-coordinate round trips for projection coefficients -/

@[expose] public section

namespace LeanCanny.ETR.TubeProjection
open Complexity
open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

noncomputable def paddedExponent (n : ℕ) (m : Variable n →₀ ℕ) (i : ℕ) : ℕ :=
  if hi : i < TubeProjectionEncoding.dimension n then m ((variableEquiv n).symm ⟨i, hi⟩) else 0

noncomputable def exponentCode (n W : ℕ) (m : Variable n →₀ ℕ) : List Bool :=
  FixedWidthNatVector.encode (TubeProjectionEncoding.dimension n) W (paddedExponent n m)

@[simp] theorem exponentCode_length (n W : ℕ) (m : Variable n →₀ ℕ) :
    (exponentCode n W m).length = TubeProjectionEncoding.dimension n * W := FixedWidthNatVector.length_encode _ _ _

theorem exponent_eq_of_encoded (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool)
    (m : Variable (n c) →₀ ℕ) (ht : target c = exponentCode (n c) (W c) m) (hm : ∀ j, m j < 2 ^ W c) :
    TubeProjectionQuery.exponent n W target c = m := by
  ext j
  have hpad : paddedExponent (n c) m (variableEquiv (n c) j).val = m j := by
    unfold paddedExponent
    rw [dite_eq_left (variableEquiv (n c) j).isLt]
    change m ((variableEquiv (n c)).symm (variableEquiv (n c) j)) = m j
    rw [Equiv.symm_apply_apply]
  simp only [TubeProjectionQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate]
  rw [ht, exponentCode, FixedWidthNatVector.decode_block _ _ _ _ (variableEquiv (n c) j).isLt (by rw [hpad]; exact hm j)]
  exact hpad

attribute [local irreducible] TubeDense.polynomial TubePolynomial.integerProjection

noncomputable def coefficient (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active word target : List Bool → List Bool) (c : List Bool) : ℤ :=
  (TubePolynomial.integerProjection (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c))
    (decodedRow base word c)).coeff (TubeProjectionQuery.exponent (TubeDense.arity base) W target c)

theorem value_eq_coefficient (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active word target modulus : List Bool → List Bool) (c : List Bool) :
    value base W active word target modulus c = residueBits ((coefficient base W active word target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := rfl

theorem coefficient_eq_native (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active word target : List Bool → List Bool) (c : List Bool)
    (j : TubePolynomial.ProjectionIndex (Fin (TubeDense.arity base c))) (m : Variable (TubeDense.arity base c) →₀ ℕ)
    (hw : word c = BinaryNatCode.encode (TubeProjectionRow.code (TubeDense.arity base c) j))
    (ht : target c = exponentCode (TubeDense.arity base c) (W c) m) (hm : ∀ i, m i < 2 ^ W c) :
    coefficient base W active word target c =
      (TubePolynomial.integerProjection (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c)) j).coeff m := by
  unfold coefficient
  rw [decodedRow_of_code base word c j hw, exponent_eq_of_encoded (TubeDense.arity base) W target c m ht hm]

end LeanCanny.ETR.TubeProjection
