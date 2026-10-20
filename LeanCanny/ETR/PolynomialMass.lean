/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomial
public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Geometry.CubePolynomialMass
import Mathlib.Tactic.Linarith

/-! # Integer polynomial coefficient mass from encoded term size

Binary constant payloads and expression-tree size bound the coefficient mass
of the finite-variable source polynomial, before rational compactification.
-/

@[expose] public section

namespace LeanCanny.ETR
open Complexity

theorem Codec.bits_length_le_size (bits : List Bool) :
    bits.length ≤ (Data.l (bits.map Codec.bit)).size := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons, Data.cons_size, Codec.bit, Bool.false_eq_true,
      ite_false, ite_true, Data.size_empty, List.length_cons] <;> omega

theorem Codec.natural_payload_le_size (n : ℕ) : n.size ≤ (Codec.natural n).size := by
  simpa only [Codec.natural, Nat.size_eq_bits_len] using Codec.bits_length_le_size n.bits

theorem Codec.integer_natAbs_le_pow_size (z : ℤ) : z.natAbs ≤ 2 ^ (Codec.integer z).size := by
  cases z with
  | ofNat n =>
    apply (Nat.lt_size_self n).le.trans
    apply Nat.pow_le_pow_right (by decide)
    have h := Codec.natural_payload_le_size n
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega
  | negSucc n =>
    have hn : n + 1 ≤ 2 ^ n.size := Nat.lt_size_self n
    apply hn.trans
    apply Nat.pow_le_pow_right (by decide)
    have h := Codec.natural_payload_le_size n
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega

namespace Term

theorem finitePolynomial_mass (t : Term) (n : ℕ) :
    Algebra.MvMass.mass (finitePolynomial n t) ≤ 2 ^ t.toData.size := by
  induction t with
  | const z =>
    rw [finitePolynomial, Algebra.MvMass.C]
    apply (Codec.integer_natAbs_le_pow_size z).trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [toData, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega
  | var i =>
    simp only [finitePolynomial]
    split_ifs
    · rw [Algebra.MvMass.X]
      exact Nat.one_le_pow _ _ (by decide)
    · simp
  | add t u ht hu =>
    apply (Algebra.MvMass.add_le _ _).trans (Nat.add_le_add ht hu) |>.trans
    calc
      2 ^ t.toData.size + 2 ^ u.toData.size ≤
          2 ^ (t.toData.size + u.toData.size) + 2 ^ (t.toData.size + u.toData.size) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
      _ = 2 ^ (t.toData.size + u.toData.size + 1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simp only [dataSize_add]; omega)
  | mul t u ht hu =>
    apply (Algebra.MvMass.mul_le _ _).trans (Nat.mul_le_mul ht hu) |>.trans
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    simp only [dataSize_mul]
    omega

theorem compactPolynomial_mass (t : Term) :
    Algebra.MvMass.mass t.compactPolynomial ≤ 2 ^ (t.toData.size + 2 * t.toData.size ^ 2) := by
  apply (Geometry.CubePolynomial.cleared_mass_of_degree (finitePolynomial t.arity t)).trans
  have hdeg := totalDegree_finitePolynomial t t.arity
  have hdim := t.arity_le_dataSize
  have hsize := t.degreeBound_le_dataSize
  have he : 2 * Fintype.card (Fin t.arity) * (finitePolynomial t.arity t).totalDegree ≤ 2 * t.toData.size ^ 2 := by
    rw [Fintype.card_fin, pow_two]
    have h := Nat.mul_le_mul hdim (hdeg.trans hsize)
    nlinarith
  apply (Nat.mul_le_mul (finitePolynomial_mass t t.arity)
    (Nat.pow_le_pow_right (by decide) he)).trans
  rw [← pow_add]

end Term
end LeanCanny.ETR
