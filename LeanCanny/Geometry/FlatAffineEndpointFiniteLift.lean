/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteFrame

/-! # Joint finite lifts of actual midpoint comparisons

Every original current point and every pair of endpoint candidates lift to
the same finite integer system once the sample height is a derivative root.
The renamed integer midpoint has exactly the original comparison value.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineEndpointFiniteLift
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def point (F : Inputs) (s : List Bool) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ) : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
  FrozenAffineCopies.point t (fun _ : Fin 1 => FrozenAffineCopies.point a ![current, left, right])

theorem lift (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineEndpointFiniteFrame.retained F height (pairFst s)) = 0)
    (hc : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) current =
      if i = height (pairFst (pairFst s)) then t else 0)
    (hl : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) left =
      if i = height (pairFst (pairFst s)) then a else 0)
    (hr : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) right =
      if i = height (pairFst (pairFst s)) then a else 0) :
    ∀ i, (FlatAffineEndpointFiniteFrame.system F height s i).eval₂ (Int.castRingHom ℝ) (point F s a t current left right) = 0 := by
  let rho := SymbolicScaledSquarefree.scalarEvaluation t
  let z := FrozenAffineCopies.point a ![current, left, right]
  have H := FrozenAffineCopies.lift (FlatAffinePowerPositive.system F (pairFst (pairFst s)))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) (height (pairFst (pairFst s)))
    rho a current left right ha (by simpa only [rho, SymbolicScaledSquarefree.scalarEvaluation,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hc) hl hr
  have hz := (AffineConstantParameterShift.roots_iff (FlatAffineEndpointPreparation.system F height (pairFst s))
    (fun j => if j = FlatAffineEndpointGram.active F height (pairFst s) then Polynomial.X else 0) rho z).mp H
  apply (FrozenAffineCopies.zero_iff (Int.castRingHom ℝ)
    (FlatAffineEndpointPreparation.system F height (pairFst s)) (FlatAffineEndpointFiniteFrame.retained F height (pairFst s))
    (FlatAffineEndpointGram.active F height (pairFst s)) (fun _ : Fin 1 => true) (point F s a t current left right)).mpr
  constructor
  · simpa only [point, FrozenAffineCopies.point_zero, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom] using ht
  · intro k i
    have he : point F s a t current left right ∘ FrozenAffineCopies.block k = z := by
      funext j
      exact FrozenAffineCopies.point_block t (fun _ : Fin 1 => z) k j
    rw [he]
    simp only [point, FrozenAffineCopies.point_zero, true_and]
    have hi := hz i
    by_cases heq : i = FlatAffineEndpointGram.active F height (pairFst s)
    · simpa only [heq, ite_true, rho, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hi
    · simpa only [heq, ite_false, rho, map_zero] using hi

noncomputable def midpoint (F : Inputs) (s : List Bool) (i : Fin (count F (pairFst (pairFst s)))) :
    MvPolynomial (Fin (FlatAffineEndpointFiniteFrame.arity F s)) ℤ :=
  MvPolynomial.rename (FrozenAffineCopies.block (0 : Fin 1)) (FrozenAffineCopies.midpoint i)

theorem midpoint_eval (F : Inputs) (s : List Bool) (i : Fin (count F (pairFst (pairFst s)))) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ) :
    (midpoint F s i).eval₂ (Int.castRingHom ℝ) (point F s a t current left right) =
      2 * current i - left i - right i := by
  have H := MvPolynomial.eval₂_rename (f := Int.castRingHom ℝ) (g := point F s a t current left right)
    (k := FrozenAffineCopies.block (0 : Fin 1)) (p := FrozenAffineCopies.midpoint i)
  refine H.trans ((FrozenAffineCopies.midpoint_eval (Int.castRingHom ℝ) i _).trans ?_)
  simp [point]

end LeanCanny.Geometry.FlatAffineEndpointFiniteLift
