/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCriticalSpace
public import LeanCanny.Algebra.PurePowerReductionBounds

/-! # Derived canonical spatial bounds for native critical annihilators

The free arity and original allowance construct the reduction bound and
fixed-width spatial layout. No width, grid-bound, or dimension oracle is
supplied. Changing this query layout leaves all actual Euler lower rows
unchanged. The relative degree is the existing canonical spatial bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCanonicalCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def normalized (S : IntegralEulerBits.Source) : IntegralEulerBits.Source :=
  { S with targetWidth := fun c => PurePowerReductionBounds.width (S.free c) (S.allowance c) }

noncomputable def normalizedAccess (S : IntegralEulerBits.Source) (a : IntegralEulerBits.Access S) :
    IntegralEulerBits.Access (normalized S) :=
  { a with targetWidth := PurePowerReductionBounds.width_unary a.free a.allowance }

theorem normalized_lower (S : IntegralEulerBits.Source) (c : List Bool) (i : Fin (S.free c)) :
    letI := S.ring c
    (normalized S).lowerPolynomial c i = S.lowerPolynomial c i := by rfl

noncomputable def source (S : IntegralEulerBits.Source) (coordinate : ∀ c, Fin (S.free c))
    (coefficientIndex : List Bool → ℕ) : IntegralClearedCriticalBits.Source where
  toEuler := normalized S
  bound c := PurePowerReductionBounds.bound (S.free c) (S.allowance c)
  grid_le c := PurePowerReductionBounds.grid_bound _ _ (by
    intro i
    unfold IntegralClearedCriticalBits.rowDegree
    split_ifs
    · exact Nat.le_refl _
    · exact Nat.sub_le _ _)
  bound_lt c := PurePowerReductionBounds.bound_lt (S.free c) (S.allowance c)
  coordinate := coordinate
  coefficientIndex := coefficientIndex

noncomputable def access (S : IntegralEulerBits.Source) (a : IntegralEulerBits.Access S)
    (coordinate : ∀ c, Fin (S.free c)) (coefficientIndex : List Bool → ℕ)
    (hi : BinaryFn (fun c => (coordinate c).val)) (hk : BinaryFn coefficientIndex) :
    IntegralClearedCriticalBits.Access (source S coordinate coefficientIndex) where
  toEuler := normalizedAccess S a
  bound := PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary a.free) a.allowance
  coordinate := hi
  coefficientIndex := hk

theorem evaluator (S : IntegralEulerBits.Source) (a : IntegralEulerBits.Access S)
    (coordinate : ∀ c, Fin (S.free c)) (coefficientIndex : List Bool → ℕ)
    (hi : BinaryFn (fun c => (coordinate c).val)) (hk : BinaryFn coefficientIndex)
    (EC : SpaceFunction a.coefficient) (EH : SpaceFunction a.height)
    (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction (source S coordinate coefficientIndex).value :=
  IntegralClearedCriticalBits.evaluator (source S coordinate coefficientIndex)
    (access S a coordinate coefficientIndex hi hk) EC EH EQ EA

theorem specialized_degree (S : IntegralEulerBits.Source) (coordinate : ∀ c, Fin (S.free c))
    (coefficientIndex : List Bool → ℕ) (c : List Bool) {K : Type*} [Field K]
    (φ : letI := S.ring c; S.carrier c →+* K)
    (h : letI := S.ring c; φ ((S.leading c * S.denominator c ^ S.allowance c * (S.allowance c : ℤ) : ℤ) : S.carrier c) ≠ 0) :
    letI := S.ring c
    (((source S coordinate coefficientIndex).annihilator c).map φ).natDegree =
      PurePowerReductionBounds.dimension (S.free c) (S.allowance c) :=
  IntegralClearedCriticalBits.specialized_degree (source S coordinate coefficientIndex) c φ h

end LeanCanny.Algebra.IntegralCanonicalCriticalBits
