/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenAffineCopies
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native integer midpoint tests on the frozen endpoint system

Three coordinate reads and modular addition/subtraction compute
`2 * current - firstEndpoint - secondEndpoint`. No algebraic coordinate
digits or expanded rational midpoint is an input.
-/

@[expose] public section
namespace LeanCanny.Algebra.FrozenAffineMidpointBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem block_unary {N : List Bool → ℕ} (hN : UnaryFn N)
    (i : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (i c).val)) (k : Fin 3) :
    UnaryFn (fun c => (FrozenAffineCopies.block k (i c)).val) :=
  (hi.add (hN.mul (UnaryFn.const k.val))).add (UnaryFn.const 1)

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (i : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (i c).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c => 3 * N c + 1) W
      (fun c => FrozenAffineCopies.midpoint (i c)) target modulus) := by
  let A := fun c => 3 * N c + 1
  have hA : UnaryFn A := ((UnaryFn.const 3).mul hN).add (UnaryFn.const 1)
  have V (k : Fin 3) := FixedWidthRowBits.variable_evaluator A W (fun c => FrozenAffineCopies.block k (i c))
    target modulus hA hW (block_unary hN i hi k) ht hm
  have D := FixedWidthRowBits.add_evaluator A W _ _ target modulus hm (V 0) (V 0)
  have L := FixedWidthRowBits.sub_evaluator A W _ _ target modulus hm D (V 1)
  have H := FixedWidthRowBits.sub_evaluator A W _ _ target modulus hm L (V 2)
  refine H.congr (funext fun c => ?_)
  have he : (X (FrozenAffineCopies.block (0 : Fin 3) (i c)) + X (FrozenAffineCopies.block (0 : Fin 3) (i c)) -
      X (FrozenAffineCopies.block (1 : Fin 3) (i c)) - X (FrozenAffineCopies.block (2 : Fin 3) (i c)) :
      MvPolynomial (Fin (A c)) ℤ) = FrozenAffineCopies.midpoint (i c) := by
    simp only [FrozenAffineCopies.midpoint, map_ofNat, two_mul]
  simp only [FixedWidthRowBits.value, he]
  rfl

end LeanCanny.Algebra.FrozenAffineMidpointBits
