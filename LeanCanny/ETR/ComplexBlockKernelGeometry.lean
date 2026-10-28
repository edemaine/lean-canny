/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBlockKernel
public import LeanCanny.Encoding.BoundedCriticalSampleBlockScaling

/-! # Original-term semantics of the native block kernel validator

Frozen inputs keep the original parent values, including their zero extension.
The circuit specialization is exactly the original frozen-coordinate term
polynomial. This is a polynomial identity, so its derivatives and the full
critical regularity predicate agree with those used by child-sample geometry.
Selecting the actual parent tuples in the constraint formula remains separate.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BlockKernel
open LeanCanny.Algebra LeanCanny.Encoding MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem specialize_term_congr (t : Term) (frozen : ℕ → ℝ) (parent : Fin N → ℝ) (offset dim : ℕ)
    (hf : ∀ i < t.arity, frozen i = Formula.extend parent i) :
    FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) frozen
      (CircuitBlock.substitution offset dim t.toPolynomial) =
        BoundedCriticalSampleBlockScaling.original t parent offset dim := by
  unfold BoundedCriticalSampleBlockScaling.original
  let ψ := (FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) frozen).comp
    (CircuitBlock.substitution offset dim)
  change ψ t.toPolynomial = _
  rw [← Source.eval_variables, Term.eval_hom]
  apply Term.eval_congr
  intro i hiScope
  change FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) frozen
    (rename (CircuitBlock.input offset dim) (X i)) = _
  rw [rename_X]
  by_cases hi : BoundedCriticalSampleBlockSource.InBlock offset dim i
  · have hp : offset ≤ i ∧ i < offset + dim := hi
    have hh : i - offset < dim := by omega
    have hInput : CircuitBlock.input offset dim i = i - offset := ite_eq_left hp
    rw [hInput, FreeCoordinateSpecialization.specialize, eval₂Hom_X', dite_eq_left hh, dite_eq_left hi]
  · have hh : ¬dim + i < dim := by omega
    have hp : ¬(offset ≤ i ∧ i < offset + dim) := hi
    rw [CircuitBlock.input_frozen _ _ _ hp, FreeCoordinateSpecialization.specialize, eval₂Hom_X',
      dite_eq_right hh, Nat.add_sub_cancel_left, hf i hiScope, dite_eq_right hi]

theorem specialize_term (t : Term) (parent : Fin N → ℝ) (offset dim : ℕ) :
    FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) (Formula.extend parent)
      (CircuitBlock.substitution offset dim t.toPolynomial) =
        BoundedCriticalSampleBlockScaling.original t parent offset dim :=
  specialize_term_congr t (Formula.extend parent) parent offset dim (fun _ _ => rfl)

theorem slice_eq_original_bounded (F : Inputs) (c : List Bool) (x : ℕ → ℝ) (parent : Fin N → ℝ)
    (hparent : ∀ i < (term F c).arity, x (dim F c + i) = Formula.extend parent i) :
    slice F c x = BoundedCriticalSampleBlockScaling.original (term F c) parent (F.offset c) (dim F c) :=
  specialize_term_congr (term F c) (fun i => x (dim F c + i)) parent (F.offset c) (dim F c) hparent

theorem slice_eq_original (F : Inputs) (c : List Bool) (x : ℕ → ℝ) (parent : Fin N → ℝ)
    (hparent : ∀ i, x (dim F c + i) = Formula.extend parent i) :
    slice F c x = BoundedCriticalSampleBlockScaling.original (term F c) parent (F.offset c) (dim F c) := by
  have hp : (fun i => x (F.free c + 1 + i)) = Formula.extend parent := funext hparent
  unfold slice CriticalKernel.realSlice
  rw [hp]
  exact specialize_term (term F c) parent (F.offset c) (dim F c)

end LeanCanny.ETR.ComplexCircuit.BlockKernel
