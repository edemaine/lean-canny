/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReductionActionSpace
public import LeanCanny.Algebra.PurePowerReductionShiftControl
public import LeanCanny.Algebra.PurePowerRelativeAnnihilator

/-! # Constructed relative pure-power actions with derived native controls

The reduction matrix, normal mask, and coordinate shift all use the actual
fixed-width spatial layout. The relative characteristic-coefficient reader
charges only the original reduction-entry program. No action matrix,
normal-column oracle, or shifted-index oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Source where
  layout : PurePowerReductionShiftBits.Layout
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  nontrivial : ∀ c, Nontrivial (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  low : ∀ c, Fin (layout.arity c) → MvPolynomial (Fin (layout.arity c)) (carrier c)
  leading : List Bool → ℤ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  coefficient : List Bool → ℕ
  basisRow : ∀ c, Fin (rank c)
  basisCol : ∀ c, Fin (rank c)

noncomputable def reductionSource (S : Source) : IntegralReductionActionBits.Source where
  dimension c := FixedWidthPolynomial.count (S.layout.arity c) (S.layout.width c)
  rank := S.rank
  carrier := S.carrier
  ring := S.ring
  nontrivial := S.nontrivial
  basis := S.basis
  matrix c := by
    letI := S.ring c
    exact PurePowerReductionMatrix.matrix (S.layout.coordinate c)
      (fun i => S.layout.degree c i.val) (S.low c) (S.leading c : S.carrier c) (S.layout.bound c)
  modulus := S.modulus
  modulus_ne_zero := S.modulus_ne_zero
  coefficient := S.coefficient
  basisRow := S.basisRow
  basisCol := S.basisCol
  dimension_pos _ := pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _
  normal c := PurePowerReductionMatrix.Normal (fun i => S.layout.degree c i.val) ∘ FixedWidthPolynomial.vector _ _
  shift c := PurePowerReductionMatrix.shift (fun i => S.layout.degree c i.val)
    (S.layout.bound c) (S.layout.grid_le c) (S.layout.bound_lt c) (S.layout.coordinate c)
  bound := S.layout.bound

def columnQuery (p : List Bool) : List Bool :=
  pair (IntegralBerkowitzBlockBits.original p) (MatrixMoment.EntryBits.colIndex p)

theorem columnQuery_FP : columnQuery ∈ FP :=
  mem_FP_pair IntegralBerkowitzBlockBits.original_FP MatrixMoment.EntryBits.colIndex_mem_FP

theorem controls (S : Source) (h : S.layout.toLayout.PolyTime)
    (hc : UnaryFn (fun c => (S.layout.coordinate c).val)) (hb : BinaryFn S.layout.bound) :
    IntegralReductionActionBits.Controls (reductionSource S) where
  bound := hb
  shift := by
    have H : BinaryFn (fun p => PurePowerReductionShiftBits.shiftValue S.layout (columnQuery p)) :=
      (PurePowerReductionShiftBits.shiftValue_binary S.layout h hc).comp columnQuery_FP
    refine BinaryFn.of_eq H (fun p => ?_)
    rw [columnQuery, PurePowerReductionShiftBits.shiftValue_pair]
    rfl
  normal := by
    apply ((PurePowerReductionShiftBits.normal_fppred S.layout h).comp columnQuery_FP).of_iff
    intro p
    rw [columnQuery, PurePowerReductionShiftBits.normal_pair]
    rfl

theorem action_matrix (S : Source) (c : List Bool) :
    letI := S.ring c
    (reductionSource S).actionMatrix c = PurePowerRelativeAnnihilator.actionMatrix (S.layout.coordinate c)
      (fun i => S.layout.degree c i.val) (S.low c) (S.leading c : S.carrier c)
      (S.layout.bound c) (S.layout.grid_le c) (S.layout.bound_lt c) (S.layout.coordinate c) := rfl

theorem evaluator (S : Source) (a : IntegralBerkowitzBlockBits.Access (reductionSource S).toSource)
    (h : S.layout.toLayout.PolyTime) (hc : UnaryFn (fun c => (S.layout.coordinate c).val))
    (hb : BinaryFn S.layout.bound) (E : SpaceFunction a.entry) :
    SpaceFunction (IntegralReductionActionBits.actionSource (reductionSource S)).value :=
  IntegralReductionActionBits.evaluator (reductionSource S) a (controls S h hc hb) E

end LeanCanny.Algebra.IntegralPurePowerActionBits
