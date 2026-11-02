/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationSource
public import LeanCanny.Algebra.IntegralCoordinatePoweredSpace

/-! # Lower equation coefficients as actual old-algebra matrices

The complete old multiplication matrix of each lower monic coefficient is
read from the creating companion's last block column. Its canonical polynomial
representative is the literal coefficient of the extension equation.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCoordinateBasis FixedWidthPolynomial PaddedIntegralParameterExtension
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family (S : Source) : IntegralCoordinateCoefficientBits.Family where
  arity c := S.arity (pairFst c)
  width c := S.width (pairFst c)
  carrier c := S.carrier (pairFst c)
  ring c := S.ring (pairFst c)
  basis c := S.basis (pairFst c)
  element c := by
    let := S.ring (pairFst c)
    exact (PaddedIntegralNormalization.polynomial (S.polynomial (pairFst c))
      (S.degree (pairFst c)) (2 ^ S.width (pairFst c))).coeff
        (Nat.fromBitsLE (pairSnd c) % 2 ^ S.width (pairFst c))

def power (S : Source) (c : List Bool) : Fin (2^S.width (pairFst c)) :=
  ⟨Nat.fromBitsLE (pairSnd c) % 2^S.width (pairFst c), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem polynomial_eq (S : Source) (c : List Bool) :
    (family S).polynomial c = (S.equation (pairFst c)).coeff (power S c).val := by
  let := S.ring (pairFst c)
  let := S.nontrivial (pairFst c)
  exact (IntegralCoordinateBasis.polynomial_coefficient (S.basis (pairFst c))
    (PaddedIntegralNormalization.polynomial (S.polynomial (pairFst c))
      (S.degree (pairFst c)) (2^S.width (pairFst c))) (power S c).val).symm

attribute [local irreducible] Source.matrix

theorem matrix_eq (S : Source) (c : List Bool)
    (r t : Fin (count (S.arity (pairFst c)) (S.width (pairFst c)))) :
    (family S).matrix c r t =
      -S.matrix (pairFst c) (pairIndex (S.arity (pairFst c)) (S.width (pairFst c)) (r,power S c))
        (pairIndex (S.arity (pairFst c)) (S.width (pairFst c)) (t,lastDigit (S.width (pairFst c)))) := by
  let := S.ring (pairFst c)
  let := S.nontrivial (pairFst c)
  unfold Source.matrix
  change _ = -Algebra.leftMulMatrix ((S.basis (pairFst c)).step _ _ _).finBasis _ _ _
  rw [finBasis_root_matrix]
  have H : ¬(lastDigit (S.width (pairFst c))).val+1<2^S.width (pairFst c) := by
    dsimp only [lastDigit]
    have := Nat.two_pow_pos (S.width (pairFst c))
    omega
  rw [ite_eq_right H,neg_neg]
  rfl

end LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
