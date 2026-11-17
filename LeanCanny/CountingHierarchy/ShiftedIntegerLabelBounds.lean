/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SparseRootProductCriterion

/-! # Uniform degree and mass bounds for the bounded integer root-label shift -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra

theorem shiftedIntegerLabel_degree_le (D e : ℕ) (L : Polynomial ℤ) :
    (shiftedIntegerLabel D e L).natDegree ≤ L.natDegree := by
  rw [shiftedIntegerLabel]
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_C, zero_add]
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le _

theorem shiftedIntegerLabel_mass_le (D e b : ℕ) (L : Polynomial ℤ)
    (he : e ≤ D) (hL : coefficientMass L ≤ 2 ^ b) :
    coefficientMass (shiftedIntegerLabel D e L) ≤ 2 ^ (b + D.size + 3) := by
  apply (coefficientMass_add_le _ _).trans
  have hmul : coefficientMass (Polynomial.C (-4 * (D : ℤ)) * L) ≤ 4 * D * 2 ^ b := by
    apply (coefficientMass_mul_le _ _).trans
    simpa only [coefficientMass_C, Int.natAbs_mul, Int.natAbs_neg, show (4 : ℤ).natAbs = 4 from rfl,
      Int.natAbs_natCast] using Nat.mul_le_mul_left (4 * D) hL
  have heval : coefficientMass (Polynomial.C (e : ℤ)) = e := by
    rw [coefficientMass_C, Int.natAbs_natCast]
  have hD : D ≤ 2 ^ D.size := (Nat.lt_size_self D).le
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [heval]
  calc
    _ ≤ 4 * D * 2 ^ b + e := Nat.add_le_add_right hmul e
    _ ≤ 8 * (2 ^ D.size * 2 ^ b) := by nlinarith
    _ = _ := by rw [← pow_add, show 8 = 2 ^ 3 by decide, ← pow_add]; congr 1; omega

end LeanCanny.CountingHierarchy
