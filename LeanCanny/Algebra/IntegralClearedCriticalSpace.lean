/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerLowReaderSpace
public import LeanCanny.Algebra.IntegralPurePowerReductionSpace
public import LeanCanny.Algebra.PurePowerFallbackInvariant

/-! # Actual cleared critical annihilators from four original readers

The original coefficient, retained-height, denominator, and integer-leading
readers construct every Euler lower coefficient and the common integer
leading coefficient. These feed the actual pure-power reduction, shifted
action, relative characteristic polynomial, and rescaling internally.
The relative degree is the spatial grid size, independent of the old rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def rowDegree (S : IntegralEulerBits.Source) (c : List Bool) (i : ℕ) : ℕ :=
  if i = IntegralEulerBits.objectiveRank S c then S.allowance c else S.allowance c - 1

structure Source extends toEuler : IntegralEulerBits.Source where
  bound : List Bool → ℕ
  grid_le : ∀ c, PurePowerReductionMatrix.gridBound (fun i : Fin (free c) => rowDegree toEuler c i.val) + 1 ≤ bound c
  bound_lt : ∀ c, bound c < 2 ^ targetWidth c
  coordinate : ∀ c, Fin (free c)
  coefficientIndex : List Bool → ℕ

structure Access (S : Source) extends toEuler : IntegralEulerBits.Access S.toEuler where
  bound : BinaryFn S.bound
  coordinate : BinaryFn (fun c => (S.coordinate c).val)
  coefficientIndex : BinaryFn S.coefficientIndex

noncomputable def layout (S : Source) : PurePowerReductionShiftBits.Layout where
  arity := S.free
  width := S.targetWidth
  degree := rowDegree S.toEuler
  bound := S.bound
  grid_le := S.grid_le
  bound_lt := S.bound_lt
  coordinate := S.coordinate

theorem layout_polyTime (S : Source) (a : Access S) : (layout S).toLayout.PolyTime := by
  refine ⟨a.free, a.targetWidth, ?_⟩
  have HI : BinaryFn (fun q => (pairSnd q).length) := BinaryFn.ofUnary UnaryFn.index
  have HO : BinaryFn (fun q => IntegralEulerBits.objectiveRank S.toEuler (pairFst q)) := a.objective.comp pairFst_mem_FP
  have HD : BinaryFn (fun q => S.allowance (pairFst q)) := a.allowance.comp pairFst_mem_FP
  exact BinaryFn.ite (HI.eq HO) HD (HD.sub (BinaryFn.const 1))

theorem coordinate_unary (S : Source) (a : Access S) : UnaryFn (fun c => (S.coordinate c).val) := by
  have H := UnaryFn.fromBitsLE_of_le a.coordinate.bits_mem_FP a.free
    (fun c => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (S.coordinate c).isLt.le)
  exact H.of_eq (fun _ => Nat.fromBitsLE_bits _)

noncomputable def relativeSource (S : Source) : IntegralPurePowerActionBits.Source where
  layout := layout S
  rank := S.rank
  carrier := S.carrier
  ring := S.ring
  nontrivial c := by
    let := S.ring c
    exact nontrivial_of_ne _ _ ((S.basis c).ne_zero (S.row c))
  basis := S.basis
  low := S.toEuler.lowerPolynomial
  leading c := S.leading c * S.denominator c ^ S.allowance c * (S.allowance c : ℤ)
  modulus := S.modulus
  modulus_ne_zero := S.modulus_ne_zero
  coefficient := S.coefficientIndex
  basisRow := S.row
  basisCol := S.col

noncomputable def relativeAccess (S : Source) (a : Access S) : IntegralPurePowerReductionBits.Access (relativeSource S) where
  layout := layout_polyTime S a
  coordinate := coordinate_unary S a
  bound := a.bound
  rank := a.rank
  modulus := a.modulus
  coefficient := a.coefficientIndex
  basisRow := a.row
  basisCol := a.col
  low := IntegralEulerLowBits.value S.toEuler
  leading := IntegralCriticalLeadingBits.value S.toEuler.toGradient.toFrozen
  leading_eq _ := rfl
  low_eq := IntegralEulerLowBits.packet S.toEuler

noncomputable def Source.annihilator (S : Source) (c : List Bool) :
    letI := S.ring c
    Polynomial (S.carrier c) := (relativeSource S).polynomial c

noncomputable def Source.value (S : Source) : List Bool → List Bool := (relativeSource S).value

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction S.value :=
  IntegralPurePowerReductionBits.evaluator (relativeSource S) (relativeAccess S a)
    (IntegralEulerLowBits.evaluator S.toEuler a.toEuler EC EH EQ EA)
    (IntegralCriticalLeadingBits.evaluator S.toEuler.toGradient.toFrozen a.toEuler.toGradient.toFrozen EQ EA)

theorem annihilator_eq (S : Source) (c : List Bool) :
    letI := S.ring c
    S.annihilator c = PurePowerRelativeAnnihilator.polynomial (S.objective c)
      (fun i => rowDegree S.toEuler c i.val) (S.toEuler.lowerPolynomial c)
      ((S.leading c * S.denominator c ^ S.allowance c * (S.allowance c : ℤ) : ℤ) : S.carrier c)
      (S.bound c) (S.grid_le c) (S.bound_lt c) (S.coordinate c) := by
  let := S.ring c
  dsimp only [Source.annihilator, IntegralPurePowerActionBits.Source.polynomial, relativeSource, layout]
  exact PurePowerRelativeAnnihilator.polynomial_fallback _ _ _ _ _ _ _ _ _

theorem specialized_degree (S : Source) (c : List Bool) {K : Type*} [Field K]
    (φ : letI := S.ring c; S.carrier c →+* K)
    (h : letI := S.ring c; φ ((S.leading c * S.denominator c ^ S.allowance c * (S.allowance c : ℤ) : ℤ) : S.carrier c) ≠ 0) :
    letI := S.ring c
    ((S.annihilator c).map φ).natDegree = FixedWidthPolynomial.count (S.free c) (S.targetWidth c) := by
  let := S.ring c
  rw [annihilator_eq]
  exact PurePowerRelativeAnnihilator.specialized_degree φ _ _ _ _ h _ _ _ _

end LeanCanny.Algebra.IntegralClearedCriticalBits
