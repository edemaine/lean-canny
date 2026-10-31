/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerRelativeAnnihilator
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Explicit binary dimensions for relative pure-power reductions

Only the free spatial arity and the original local degree enter these
bounds. In particular, neither old parameter-algebra rank nor previously
chosen coordinate powers occur in the reduction dimension.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBounds
open scoped Classical

def bound (n D : ℕ) : ℕ := n * (D - 1) + 1
def width (n D : ℕ) : ℕ := (bound n D + 1).size
def dimension (n D : ℕ) : ℕ := FixedWidthPolynomial.count n (width n D)

theorem grid_bound {n : ℕ} (d : Fin n → ℕ) (D : ℕ) (hd : ∀ i, d i ≤ D) :
    PurePowerReductionMatrix.gridBound d + 1 ≤ bound n D := by
  have H : PurePowerReductionMatrix.gridBound d ≤ n * (D - 1) := by
    unfold PurePowerReductionMatrix.gridBound
    calc
      _ ≤ Finset.univ.sum (fun _i : Fin n => D - 1) := Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_right (hd i) 1)
      _ = n * (D - 1) := by simp
  exact Nat.add_le_add_right H 1

theorem bound_lt (n D : ℕ) : bound n D < 2 ^ width n D :=
  (Nat.lt_succ_self _).trans (Nat.lt_size_self (bound n D + 1))

theorem bound_binary {n D : List Bool → ℕ} (hn : BinaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun c => bound (n c) (D c)) := (hn.mul (hD.sub (BinaryFn.const 1))).add (BinaryFn.const 1)

theorem width_unary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    UnaryFn (fun c => width (n c) (D c)) := by
  have H := (bound_binary (BinaryFn.ofUnary hn) hD).add (BinaryFn.const 1)
  have HL : UnaryFn (fun c => (BinaryNatCode.encode (bound (n c) (D c) + 1)).length) :=
    UnaryFn.length H.bits_mem_FP
  exact UnaryFn.of_eq HL (fun _ => by exact BinaryNatCode.length_encode _)

theorem dimension_binary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun c => dimension (n c) (D c)) := by
  have H : BinaryFn (fun c => 2 ^ width (n c) (D c)) := (BinaryFn.const 2).powUnary (width_unary hn hD)
  exact H.powUnary hn

theorem dimension_bits (n D : ℕ) : (dimension n D).size = width n D * n + 1 := by
  simp only [dimension, FixedWidthPolynomial.count, ← pow_mul, Nat.size_pow]

theorem width_bound (n D : ℕ) : width n D ≤ n.size + D.size + 3 := by
  have HM : n * D ≤ 2 ^ (n.size + D.size) := by
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self n).le (Nat.lt_size_self D).le
  have HP : 1 ≤ 2 ^ (n.size + D.size) := Nat.one_le_two_pow
  have H : bound n D + 1 ≤ 2 ^ (n.size + D.size + 2) := by
    calc
      _ ≤ n * D + 2 := by unfold bound; have := Nat.mul_le_mul_left n (Nat.sub_le D 1); omega
      _ ≤ 2 ^ (n.size + D.size) + 2 := Nat.add_le_add_right HM 2
      _ ≤ 2 ^ (n.size + D.size) * 4 := by omega
      _ = 2 ^ (n.size + D.size + 2) := by simp only [pow_add]; norm_num
  have HS := Nat.size_le_size H
  simpa only [width, Nat.size_pow, Nat.add_assoc] using HS

theorem dimension_bits_bound (n D : ℕ) :
    (dimension n D).size ≤ n * (n.size + D.size + 3) + 1 := by
  rw [dimension_bits, Nat.mul_comm (width n D) n]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (width_bound n D)) 1

end LeanCanny.Algebra.PurePowerReductionBounds
