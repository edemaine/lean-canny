/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairInteger
public import LeanCanny.Algebra.SeparableResultant

/-! # Recognizing separating directions by the actual integer resultant

For split separable source polynomials, the unnormalized resultant is nonzero
for every direction. It is separable exactly when the shear is injective on the
Cartesian product of root sets. Thus testing its derivative resultant is an
effective test of the geometric condition used by coordinate recovery.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePair
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]

theorem resultant_separable_iff (p q : K[X]) (c : ℕ)
    (hp : p.Separable) (hq : q.Separable)
    (hsp : (p.map (algebraMap K L)).Splits) (hsq : (q.map (algebraMap K L)).Splits) :
    (cannyResultant p q c).Separable ↔
      Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L)) := by
  refine ⟨fun h => ?_, resultant_separable p q c hp hq hsp hsq⟩
  have hm := (Polynomial.separable_map (algebraMap K L)).mpr h
  rw [cannyResultant_eq_sign_mul, Polynomial.map_mul, Polynomial.map_C,
    projectionResultant_map_eq p q c hp hq hsp hsq, ← mul_assoc] at hm
  exact separable_prod_X_sub_C_iff'.mp (hm.of_dvd (dvd_mul_left _ _))

theorem resultant_ne_zero (p q : K[X]) (c : ℕ)
    (hp : p.Separable) (hq : q.Separable)
    (hsp : (p.map (algebraMap K L)).Splits) (hsq : (q.map (algebraMap K L)).Splits) :
    cannyResultant p q c ≠ 0 := by
  intro hz
  have hm := congrArg (fun r : K[X] => r.map (algebraMap K L)) hz
  rw [cannyResultant_eq_sign_mul, Polynomial.map_mul, Polynomial.map_C,
    projectionResultant_map_eq p q c hp hq hsp hsq, Polynomial.map_zero] at hm
  have hs : algebraMap K L ((-1 : K) ^ (p.natDegree * q.natDegree)) ≠ 0 := by simp
  have hscale : algebraMap K L (resultantScale p q) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne (resultantScale_ne_zero p q hp.ne_zero hq.ne_zero)
  exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hs)
    (mul_ne_zero (Polynomial.C_ne_zero.mpr hscale) Lagrange.nodal_ne_zero)) hm

section Integer
variable [CharZero L]

theorem integer_resultant_ne_zero (p q : ℤ[X]) (c : ℕ)
    (hp : (p.map (Int.castRingHom L)).Separable) (hq : (q.map (Int.castRingHom L)).Separable)
    (hsp : (p.map (Int.castRingHom L)).Splits) (hsq : (q.map (Int.castRingHom L)).Splits) :
    cannyResultant p q c ≠ 0 := by
  have hi : Function.Injective (Int.castRingHom L) := Int.cast_injective
  have hsp' : ((p.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsp
  have hsq' : ((q.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsq
  have hn := resultant_ne_zero _ _ c hp hq hsp' hsq'
  intro hz
  apply hn
  rw [← CoordinateRecoveryMap.resultant (Int.castRingHom L) hi, hz, Polynomial.map_zero]

theorem integer_resultant_test (p q : ℤ[X]) (c : ℕ)
    (hp : (p.map (Int.castRingHom L)).Separable) (hq : (q.map (Int.castRingHom L)).Separable)
    (hsp : (p.map (Int.castRingHom L)).Splits) (hsq : (q.map (Int.castRingHom L)).Splits) :
    (cannyResultant p q c).resultant (cannyResultant p q c).derivative ≠ 0 ↔
      Set.InjOn (shear c)
        (rootPairs (L := L) (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) : Set (L × L)) := by
  have hi : Function.Injective (Int.castRingHom L) := Int.cast_injective
  have hsp' : ((p.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsp
  have hsq' : ((q.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsq
  have hn' := integer_resultant_ne_zero p q c hp hq hsp hsq
  rw [← integer_separable_iff_resultant_ne_zero (K := L) _ hn',
    CoordinateRecoveryMap.resultant (Int.castRingHom L) hi]
  exact resultant_separable_iff _ _ c hp hq hsp' hsq'

theorem integer_separable_iff_separating (p q : ℤ[X]) (c : ℕ)
    (hp : (p.map (Int.castRingHom L)).Separable) (hq : (q.map (Int.castRingHom L)).Separable)
    (hsp : (p.map (Int.castRingHom L)).Splits) (hsq : (q.map (Int.castRingHom L)).Splits) :
    ((cannyResultant p q c).map (Int.castRingHom ℚ)).Separable ↔
      Set.InjOn (shear c)
        (rootPairs (L := L) (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) : Set (L × L)) :=
  (integer_separable_iff_resultant_ne_zero _ (integer_resultant_ne_zero p q c hp hq hsp hsq)).trans
    (integer_resultant_test p q c hp hq hsp hsq)

end Integer
end LeanCanny.Algebra.PrimitivePair
