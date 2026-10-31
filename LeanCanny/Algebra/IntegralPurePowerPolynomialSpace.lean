/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPurePowerActionSpace
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace

/-! # Native coefficients of the constructed relative coordinate annihilator

The original reduction-entry program and common integer leading-coefficient
reader construct the actual pure-power annihilator's multiplication-matrix
entries. Shifted action entries, relative characteristic coefficients, and
the rescaling factor are all computed internally. The polynomial degree
remains the spatial reduction dimension.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.polynomial (S : Source) (c : List Bool) :
    letI := S.ring c
    Polynomial (S.carrier c) := by
  letI := S.ring c
  exact PurePowerRelativeAnnihilator.polynomial (S.layout.coordinate c)
    (fun i => S.layout.degree c i.val) (S.low c) (S.leading c : S.carrier c)
    (S.layout.bound c) (S.layout.grid_le c) (S.layout.bound_lt c) (S.layout.coordinate c)

noncomputable def Source.value (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff (S.coefficient c))
    (S.basisRow c) (S.basisCol c) : ℤ) : ZMod (S.modulus c))

attribute [local irreducible] Matrix.charpoly PurePowerReductionMatrix.matrix
  IntegralReductionActionBits.Source.actionMatrix PurePowerRelativeAnnihilator.actionMatrix

theorem polynomial_value (S : Source) :
    IntegralScaledCharacteristicBits.value (IntegralReductionActionBits.actionSource (reductionSource S))
      S.leading (fun c => S.layout.bound c + 1) = S.value := by
  funext c
  let := S.ring c
  let := (reductionSource S).ring c
  have HP : ScaledGradedReductionAnnihilator.polynomial ((reductionSource S).actionMatrix c)
      (S.leading c : S.carrier c) (S.layout.bound c + 1) = S.polynomial c := by
    rw [action_matrix]
    rfl
  have H := congrArg (fun p : Polynomial (S.carrier c) => residueBits
    ((Algebra.leftMulMatrix (S.basis c) (p.coeff (S.coefficient c))
      (S.basisRow c) (S.basisCol c) : ℤ) : ZMod (S.modulus c))) HP
  dsimp only [IntegralScaledCharacteristicBits.value, Source.value,
    IntegralReductionActionBits.actionSource, reductionSource]
  exact H

attribute [local irreducible] Source.value IntegralScaledCharacteristicBits.value

theorem polynomial_evaluator (S : Source) (a : IntegralBerkowitzBlockBits.Access (reductionSource S).toSource)
    (h : S.layout.toLayout.PolyTime) (hc : UnaryFn (fun c => (S.layout.coordinate c).val))
    (hb : BinaryFn S.layout.bound) (E : SpaceFunction a.entry)
    (EC : SpaceFunction (fun c => residueBits (S.leading c : ZMod (S.modulus c)))) : SpaceFunction S.value := by
  have EA := IntegralReductionActionBits.entry_evaluator (reductionSource S) a (controls S h hc hb) E
  have HE : SpaceFunction (IntegralReductionActionBits.actionAccess (reductionSource S) a).entry := by
    change SpaceFunction (IntegralReductionActionBits.entryProgram (reductionSource S))
    exact EA
  exact (IntegralScaledCharacteristicBits.evaluator
    (IntegralReductionActionBits.actionSource (reductionSource S))
    (IntegralReductionActionBits.actionAccess (reductionSource S) a)
    S.leading (fun c => S.layout.bound c + 1) (hb.add (BinaryFn.const 1)) HE EC).congr (polynomial_value S)

end LeanCanny.Algebra.IntegralPurePowerActionBits
