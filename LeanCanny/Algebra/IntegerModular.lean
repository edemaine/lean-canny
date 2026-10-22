/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Data.ZMod.Basic
public import LeanCanny.Algebra.CoefficientBounds

/-!
# Detecting integer zero through small moduli

An integer with at most `B` magnitude bits is zero exactly when all its residues
modulo `1,...,2*B+4` vanish. The LCM grows exponentially, so the scan length is
linear in the bit budget, rather than in the integer's magnitude. In particular,
an exponential bit budget still requires only polynomial-length modulus words.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerModular

theorem linear_le_two_pow (B : ℕ) : 2 * B + 5 ≤ 2 ^ (B + 3) := by
  induction B with
  | zero => decide
  | succ B ih =>
    rw [show B + 1 + 3 = (B + 3) + 1 by omega, pow_succ]
    omega

theorem two_pow_lt_lcmUpto (B : ℕ) : 2 ^ B < Nat.lcmUpto (2 * B + 4) := by
  by_contra h
  have hL : Nat.lcmUpto (2 * B + 4) ≤ 2 ^ B := Nat.le_of_not_gt h
  have hsmall : (2 * B + 4 + 1) * Nat.lcmUpto (2 * B + 4) ≤ 2 ^ (2 * B + 3) := by
    calc
      _ ≤ 2 ^ (B + 3) * 2 ^ B := Nat.mul_le_mul (by have := linear_le_two_pow B; omega) hL
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbig := Chebyshev.two_pow_le_mul_lcmUpto (2 * B + 4)
  have hlt : (2 : ℕ) ^ (2 * B + 3) < 2 ^ (2 * B + 4) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

theorem eq_zero_iff_residues (z : ℤ) (B : ℕ) (hb : z.natAbs.size ≤ B) :
    z = 0 ↔ ∀ m : ℕ, 1 ≤ m → m ≤ 2 * B + 4 → (z : ZMod m) = 0 := by
  constructor
  · rintro rfl m _ _
    exact Int.cast_zero
  · intro h
    have hdiv : Nat.lcmUpto (2 * B + 4) ∣ z.natAbs := by
      rw [Nat.lcmUpto, Finset.lcm_dvd_iff]
      intro m hm
      have hr := h m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
      exact Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd z m).mp hr)
    have hlt := (Nat.size_le.mp hb).trans (two_pow_lt_lcmUpto B)
    by_contra hz
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hdiv
    omega

theorem det_eq_zero_iff_residues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℕ) (hb : A.det.natAbs.size ≤ B) :
    A.det = 0 ↔ ∀ m : ℕ, 1 ≤ m → m ≤ 2 * B + 4 →
      (A.map (Int.castRingHom (ZMod m))).det = 0 := by
  have hm (m : ℕ) : (A.map (Int.castRingHom (ZMod m))).det = (A.det : ZMod m) :=
    ((Int.castRingHom (ZMod m)).map_det A).symm
  simp only [hm]
  exact eq_zero_iff_residues A.det B hb

theorem det_natAbs_size_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (b : ι → ℕ) (hb : ∀ i j, (A i j).natAbs ≤ 2 ^ b j) :
    A.det.natAbs.size ≤ (Fintype.card ι).size * Fintype.card ι + (∑ j, b j) + 1 := by
  have h := det_coeff_size_le (A.map Polynomial.C) b
    (by intro i j; simpa only [Matrix.map_apply, coefficientMass_C] using hb i j) 0
  have heq : (A.map Polynomial.C).det = Polynomial.C A.det := (Polynomial.C.map_det A).symm
  simpa only [heq, Polynomial.coeff_C_zero] using h

theorem det_natAbs_size_le_uniform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hb : ∀ i j, (A i j).natAbs ≤ 2 ^ b) :
    A.det.natAbs.size ≤ n.size * n + n * b + 1 := by
  simpa only [Fintype.card_fin, Fin.sum_const, smul_eq_mul] using
    det_natAbs_size_le A (fun _ => b) hb

end LeanCanny.Algebra.IntegerModular
