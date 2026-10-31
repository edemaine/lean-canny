/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDerivativeCorrect
public import LeanCanny.Algebra.IntegralClearedCoefficientSpace

/-! # Actual original derivatives cleared on frozen coordinate blocks

Differentiate the original polynomial before freezing coordinates. The
same original coefficient, integer denominator, and retained-height
readers construct every cleared derivative coefficient; the clearing
allowance remains the original spatial allowance.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (S : Source) (c : List Bool) :
    letI := S.ring c
    MvPolynomial (Fin (S.arity c)) (S.carrier c) := by
  letI := S.ring c
  exact MvPolynomial.pderiv (S.selected c) (S.polynomial c)

theorem support (S : Source) (c : List Bool) :
    letI := S.ring c
    ∀ e ∈ (polynomial S c).support, ∀ i, e i < 2 ^ S.sourceWidth c := by
  let := S.ring c
  intro e he i
  have H := MvPolynomial.mem_support_iff.mp he
  have HO : (S.polynomial c).coeff (e + Finsupp.single (S.selected c) 1) ≠ 0 := by
    intro h
    apply H
    rw [polynomial, MvPolynomial.coeff_pderiv, h, zero_mul]
  have HB := S.support c _ (MvPolynomial.mem_support_iff.mpr HO) i
  have HE : e i ≤ (e + Finsupp.single (S.selected c) 1 : Fin (S.arity c) →₀ ℕ) i := by
    rw [Finsupp.add_apply]
    exact Nat.le_add_right _ _
  exact HE.trans_lt HB

noncomputable def clearedSource (S : Source) : IntegralClearedCoefficientBits.Source :=
  { S.toSource with polynomial := polynomial S, support := support S }

noncomputable def clearedAccess (S : Source) (a : Access S) : IntegralClearedCoefficientBits.Access (clearedSource S) where
  arity := a.arity
  free := a.free
  offset := a.offset
  sourceWidth := a.sourceWidth
  targetWidth := a.targetWidth
  rank := a.rank
  allowance := a.allowance
  target := a.target
  row := a.row
  col := a.col
  modulus := a.modulus
  coefficient := value S a
  height := a.height
  denominator := a.denominator
  coefficient_eq := packet S a
  height_eq := a.height_eq
  denominator_eq := a.denominator_eq

theorem cleared_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (clearedSource S).value := by
  have ED : SpaceFunction (clearedAccess S a).coefficient := evaluator S a EC
  exact IntegralClearedCoefficientBits.evaluator (clearedSource S) (clearedAccess S a) ED EH EQ

end LeanCanny.Algebra.IntegralDerivativeBits
