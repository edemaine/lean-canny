/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatScaledCoordinateCone

/-! # Coordinate cone exclusion with three independent positive powers

Parameter scaling raises physical coordinates and multipliers by different
powers. The source, gradient, and height exponents need not differ by one.
An unused coordinate objective still excludes every nonzero common root.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatScaledPowerCone
open scoped Classical BigOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem root_zero (P Q W : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hW : 0 < W)
    (a g b : K) (ha : a ≠ 0) (hg0 : g ≠ 0) (hb : b ≠ 0)
    (c : Fin n → K) (hc : ∀ i, c i ≠ 0) (s : Finset (Fin n)) (r : Fin n) (hr : r ∉ s)
    (x : Fin n → K) (mu : Fin (n + 1) → K)
    (hp : a * ∑ i, x i ^ P = 0)
    (hl : ∀ i ∈ s, c i * x i ^ W = 0)
    (hgrad : ∀ i, g * x i ^ Q = (if i = r then b * mu 0 ^ Q else 0) + c i * mu i.succ ^ Q)
    (hu : ∀ i, i ∉ s → mu i.succ = 0) : x = 0 ∧ mu = 0 := by
  have hactive (i : Fin n) (hi : i ∈ s) : x i = 0 :=
    (pow_eq_zero_iff hW.ne').mp ((mul_eq_zero.mp (hl i hi)).resolve_left (hc i))
  have hother (i : Fin n) (hi : i ≠ r) : x i = 0 := by
    by_cases hs : i ∈ s
    · exact hactive i hs
    · have H := hgrad i
      rw [ite_eq_right hi, hu i hs, zero_pow hQ.ne', mul_zero, zero_add] at H
      exact (pow_eq_zero_iff hQ.ne').mp ((mul_eq_zero.mp H).resolve_left hg0)
  have hxr : x r = 0 := by
    have HS : (∑ i, x i ^ P) = x r ^ P := by
      apply Finset.sum_eq_single r
      · intro i _ hi
        rw [hother i hi, zero_pow hP.ne']
      · simp
    rw [HS] at hp
    exact (pow_eq_zero_iff hP.ne').mp ((mul_eq_zero.mp hp).resolve_left ha)
  have hx : x = 0 := by
    funext i
    by_cases hi : i = r
    · simpa only [hi, Pi.zero_apply] using hxr
    · exact hother i hi
  have hm : mu 0 = 0 := by
    have H := hgrad r
    rw [hxr, zero_pow hQ.ne', mul_zero, ite_eq_left rfl, hu r hr, zero_pow hQ.ne', mul_zero, add_zero] at H
    exact (pow_eq_zero_iff hQ.ne').mp ((mul_eq_zero.mp H.symm).resolve_left hb)
  refine ⟨hx, ?_⟩
  funext j
  refine Fin.cases hm (fun i => ?_) j
  have H := hgrad i
  have H' : c i * mu i.succ ^ Q = 0 := by
    simpa only [hx, Pi.zero_apply, zero_pow hQ.ne', mul_zero, hm, ite_self, zero_add] using H.symm
  exact (pow_eq_zero_iff hQ.ne').mp ((mul_eq_zero.mp H').resolve_left (hc i))

end LeanCanny.Algebra.FermatScaledPowerCone
