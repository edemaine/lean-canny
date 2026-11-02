/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationReadback
public import LeanCanny.Algebra.PaddedIntegralGeneratorSource

/-! # Literal equation coefficients of an original scalar source

No regularity or selected-leading-coefficient premise is needed. The equation
is the actual monic padded relation used to construct this source's extension.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorSource
open IntegralCoordinateBasis FixedWidthPolynomial PaddedIntegralParameterExtension
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.equation (S : Source) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (S.arity c)) ℤ) := by
  let := S.ring c
  let := S.nontrivial c
  exact PaddedIntegralParameterExtension.equation (S.basis c) (S.polynomial c) (S.degree c)

attribute [local irreducible] Source.matrix

theorem Source.equation_lower (S : Source) (c : List Bool)
    (r : Fin (count (S.arity c) (S.width c))) (i : Fin (2 ^ S.width c)) :
    ((S.equation c).coeff i.val).coeff (vector (S.arity c) (S.width c) r) =
      -S.matrix c (pairIndex (S.arity c) (S.width c) (r, i))
        (pairIndex (S.arity c) (S.width c) (zeroFin (S.arity c) (S.width c), lastDigit (S.width c))) := by
  let := S.ring c
  let := S.nontrivial c
  unfold Source.matrix
  exact equation_coefficient_companion (S.basis c) (S.polynomial c) (S.degree c) r i

theorem Source.equation_top (S : Source) (c : List Bool) :
    (S.equation c).coeff (2 ^ S.width c) = 1 := by
  let := S.ring c
  let := S.nontrivial c
  exact equation_coefficient_top (S.basis c) (S.polynomial c) (S.degree c)

theorem Source.equation_above (S : Source) (c : List Bool) (k : ℕ) (hk : 2 ^ S.width c < k) :
    (S.equation c).coeff k = 0 := by
  let := S.ring c
  let := S.nontrivial c
  exact equation_coefficient_above (S.basis c) (S.polynomial c) (S.degree c) k hk

theorem Source.equation_outside (S : Source) (c : List Bool) (k : ℕ)
    (v : Fin (S.arity c) →₀ ℕ) (hv : ∃ j, 2 ^ S.width c ≤ v j) :
    ((S.equation c).coeff k).coeff v = 0 := by
  let := S.ring c
  exact equation_coefficient_outside (S.basis c) (S.polynomial c) (S.degree c) k v hv

end LeanCanny.Algebra.PaddedIntegralGeneratorSource
