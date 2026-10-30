/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenRetainedMidpointSpace

/-! # Native comparison of the two retained endpoint coordinates -/

@[expose] public section
namespace LeanCanny.Algebra.FrozenRetainedComparisonBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def block {n : ℕ} (k : Fin 3) (i : Fin n) : Fin (1 * (3 * n + 1) + 1) :=
  FrozenAffineCopies.block (0 : Fin 1) (FrozenAffineCopies.block k i)

noncomputable def polynomial {n : ℕ} (i : Fin n) : MvPolynomial (Fin (1 * (3 * n + 1) + 1)) ℤ :=
  X (block 1 i) - X (block 2 i)

theorem degree_le {n : ℕ} (i : Fin n) : (polynomial i).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (by simp)

theorem mass_le {n : ℕ} (i : Fin n) : MvMass.mass (polynomial i) ≤ 2 :=
  (MvMass.sub_le _ _).trans (by simp)

theorem block_unary {N : List Bool → ℕ} (hN : UnaryFn N)
    (i : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (i c).val)) (k : Fin 3) :
    UnaryFn (fun c => (block k (i c)).val) := by
  have H := ((FrozenAffineMidpointBits.block_unary hN i hi k).add (UnaryFn.const 1))
  exact H.of_eq (fun c => by
    change (FrozenAffineCopies.block k (i c)).val + 1 =
      (FrozenAffineCopies.block k (i c)).val + (3 * N c + 1) * 0 + 1
    omega)

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (i : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (i c).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c => 1 * (3 * N c + 1) + 1) W
      (fun c => polynomial (i c)) target modulus) := by
  have hA := ((UnaryFn.const 1).mul (((UnaryFn.const 3).mul hN).add (UnaryFn.const 1))).add (UnaryFn.const 1)
  have V (k : Fin 3) := FixedWidthRowBits.variable_evaluator _ _ (fun c => block k (i c))
    target modulus hA hW (block_unary hN i hi k) ht hm
  exact (FixedWidthRowBits.sub_evaluator _ _ _ _ target modulus hm (V 1) (V 2)).congr (funext fun _ => rfl)

theorem eval_point {n : ℕ} (i : Fin n) (a t : ℝ) (current left right : Fin n → ℝ) :
    (polynomial i).eval₂ (Int.castRingHom ℝ)
      (FrozenAffineCopies.point t (fun _ : Fin 1 => FrozenAffineCopies.point a ![current, left, right])) =
        left i - right i := by
  simp only [polynomial, eval₂_sub, eval₂_X, block, FrozenAffineCopies.point_block,
    Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

end LeanCanny.Algebra.FrozenRetainedComparisonBits
