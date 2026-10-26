/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateRecoveryMap
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Projection resultants without square-free hypotheses

Repeated roots do not make the projected-pair polynomial vanish identically.
Its roots still lie in a finite set of projected pairs. This avoids square-free
preprocessing when using resultants solely for root-separation estimates.
-/

@[expose] public section
namespace LeanCanny.Algebra.ResultantNonvanishing
open Polynomial
open scoped Classical

theorem field_ne_zero {K L : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]
    (p q : K[X]) (c : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (hs : (q.map (algebraMap K L)).Splits) :
    cannyResultant p q c ≠ 0 := by
  obtain ⟨z, hz⟩ := ((rootPairs (L := L) p q).image (shear c)).exists_notMem
  intro hr
  have he : Polynomial.aeval z (cannyResultant p q c) = 0 := by rw [hr, map_zero]
  obtain ⟨a, b, ha, hb, he⟩ := (cannyResultant_roots p q c z hq hs).mp he
  exact hz (Finset.mem_image.mpr ⟨(a, b), (mem_rootPairs p q hp hq _).mpr ⟨ha, hb⟩, he.symm⟩)

theorem integer_ne_zero (p q : ℤ[X]) (c : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : cannyResultant p q c ≠ 0 := by
  have hi : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hp' := (Polynomial.map_ne_zero_iff hi).mpr hp
  have hq' := (Polynomial.map_ne_zero_iff hi).mpr hq
  have hs : ((q.map (Int.castRingHom ℂ)).map (algebraMap ℂ ℂ)).Splits := IsAlgClosed.splits _
  have hn := field_ne_zero (L := ℂ) (p.map (Int.castRingHom ℂ)) (q.map (Int.castRingHom ℂ)) c hp' hq' hs
  intro hz
  apply hn
  rw [← CoordinateRecoveryMap.resultant (Int.castRingHom ℂ) hi, hz, Polynomial.map_zero]

theorem eval_complex_ofReal (p : ℤ[X]) (x : ℝ) :
    p.eval₂ (Int.castRingHom ℂ) (x : ℂ) = Complex.ofReal (p.eval₂ (Int.castRingHom ℝ) x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, hp, hq, Complex.ofReal_add]
  | monomial n a => simp [Polynomial.eval₂_monomial]

theorem integer_sum_root (p q : ℤ[X]) (c : ℕ) (a b : ℝ) (hq : q ≠ 0)
    (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) (hb : q.eval₂ (Int.castRingHom ℝ) b = 0) :
    (cannyResultant p q c).eval₂ (Int.castRingHom ℝ) (a + (c : ℝ) * b) = 0 := by
  have hi : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hq' := (Polynomial.map_ne_zero_iff hi).mpr hq
  have hs : ((q.map (Int.castRingHom ℂ)).map (algebraMap ℂ ℂ)).Splits := IsAlgClosed.splits _
  have ha' : Polynomial.aeval (a : ℂ) (p.map (Int.castRingHom ℂ)) = 0 := by
    simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, eval_complex_ofReal, ha, Complex.ofReal_zero]
  have hb' : Polynomial.aeval (b : ℂ) (q.map (Int.castRingHom ℂ)) = 0 := by
    simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, eval_complex_ofReal, hb, Complex.ofReal_zero]
  have hr := (cannyResultant_roots (p.map (Int.castRingHom ℂ)) (q.map (Int.castRingHom ℂ)) c
    ((a : ℂ) + (c : ℂ) * (b : ℂ)) hq' hs).mpr ⟨(a : ℂ), (b : ℂ), ha', hb', rfl⟩
  rw [← CoordinateRecoveryMap.resultant (Int.castRingHom ℂ) hi] at hr
  simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map] at hr
  have he : ((a + (c : ℝ) * b : ℝ) : ℂ) = (a : ℂ) + (c : ℂ) * (b : ℂ) := by push_cast; rfl
  rw [← he, eval_complex_ofReal] at hr
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using hr)

end LeanCanny.Algebra.ResultantNonvanishing
