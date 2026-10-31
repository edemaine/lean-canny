/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerLowerSpace

/-! # Saved-source queries for every actual cleared critical lower row

The original family, objective coordinate, and degree allowance are pulled
back through one saved-record map. Spatial targets and old basis outputs
are selected independently. The native row program charges only the same
four original readers through their explicit query writers.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.requery (S : Source) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c))) : Source where
  toGradient := {
    toFrozen := {
      toSource := S.toGradient.toFrozen.toSource.requery original target row col
      leading c := S.leading (original c) }
    free_pos c := S.free_pos (original c)
    degree c := S.degree (original c)
    degree_pos c := S.degree_pos (original c)
    degree_le c := S.degree_le (original c)
    degree_lt c := S.degree_lt (original c) }
  objective c := S.objective (original c)

noncomputable def Access.requery (S : Source) (a : Access S) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c)))
    (h : original ∈ FP) (ht : BinaryFn target) (hr : BinaryFn (fun c => (row c).val))
    (hc : BinaryFn (fun c => (col c).val)) : Access (S.requery original target row col) where
  toGradient := {
    toFrozen := {
      toAccess := IntegralClearedCoefficientBits.Access.requery S.toGradient.toFrozen.toSource
        a.toGradient.toFrozen.toAccess original target row col h ht hr hc
      leading := a.leading ∘ original
      leading_eq c := a.leading_eq (original c) }
    degree := a.degree.comp h }
  objective := a.objective.comp h

theorem requery_lower_polynomial (S : Source) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c)))
    (c : List Bool) (i : Fin (S.free (original c))) :
    letI := S.ring (original c)
    (S.requery original target row col).lowerPolynomial c i = S.lowerPolynomial (original c) i := by
  rfl

theorem requery_lower_evaluator (S : Source) (a : Access S) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c)))
    (i : ∀ c, Fin (S.free (original c))) (h : original ∈ FP) (ht : BinaryFn target)
    (hr : BinaryFn (fun c => (row c).val)) (hc : BinaryFn (fun c => (col c).val))
    (hi : BinaryFn (fun c => (i c).val)) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction ((S.requery original target row col).lowerValue i) :=
  lower_evaluator (S.requery original target row col) (a.requery S original target row col h ht hr hc) i hi
    (EC.precompose (IntegralClearedCoefficientBits.coefficientRequery original)
      (IntegralClearedCoefficientBits.coefficientRequery_FP original h))
    (EH.precompose (IntegralClearedCoefficientBits.heightRequery original)
      (IntegralClearedCoefficientBits.heightRequery_FP original h))
    (EQ.precompose original h) (EA.precompose original h)

end LeanCanny.Algebra.IntegralEulerBits
