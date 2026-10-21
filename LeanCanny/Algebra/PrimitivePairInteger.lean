/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateRecoveryMap

/-! # Correctness of the integer primitive-pair polynomials

The integer polynomials evaluated by the native readers decode every resultant
root over a characteristic-zero splitting field. The common denominator is
nonzero at every such root under the separating-direction hypothesis.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePair
open Polynomial
variable {L : Type*} [Field L] [CharZero L]

noncomputable def decodeInteger (p q : ℤ[X]) (c : ℕ) (theta : L) : L × L :=
  ((leftNumerator p q c).eval₂ (Int.castRingHom L) theta / (denominator p q c).eval₂ (Int.castRingHom L) theta,
    (rightNumerator p q c).eval₂ (Int.castRingHom L) theta / (denominator p q c).eval₂ (Int.castRingHom L) theta)

theorem decodeInteger_eq (p q : ℤ[X]) (c : ℕ) (theta : L) :
    decodeInteger p q c theta = decode (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) c theta := by
  have hi : Function.Injective (Int.castRingHom L) := Int.cast_injective
  simp only [decodeInteger, decode, Polynomial.coe_aeval_eq_eval,
    ← CoordinateRecoveryMap.leftNumerator (Int.castRingHom L) hi p q c,
    ← CoordinateRecoveryMap.rightNumerator (Int.castRingHom L) hi p q c,
    ← CoordinateRecoveryMap.denominator (Int.castRingHom L) hi p q c, Polynomial.eval_map]

theorem decodeInteger_root (p q : ℤ[X]) (c : ℕ) (theta : L) (hp : p ≠ 0)
    (hq : (q.map (Int.castRingHom L)).Separable) (hs : (q.map (Int.castRingHom L)).Splits)
    (hi : Set.InjOn (shear c) (rootPairs (L := L) (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) : Set (L × L)))
    (ht : (cannyResultant p q c).eval₂ (Int.castRingHom L) theta = 0) :
    p.eval₂ (Int.castRingHom L) (decodeInteger p q c theta).1 = 0 ∧
      q.eval₂ (Int.castRingHom L) (decodeInteger p q c theta).2 = 0 ∧
      shear c (decodeInteger p q c theta) = theta ∧
      (denominator p q c).eval₂ (Int.castRingHom L) theta ≠ 0 := by
  have hcast : Function.Injective (Int.castRingHom L) := Int.cast_injective
  have hp' : p.map (Int.castRingHom L) ≠ 0 := (Polynomial.map_ne_zero_iff hcast).mpr hp
  have hs' : ((q.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hs
  have ht' : Polynomial.aeval theta (cannyResultant (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) c) = 0 := by
    rw [← CoordinateRecoveryMap.resultant (Int.castRingHom L) hcast]
    simpa only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map] using ht
  have he := decode_root (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) c theta hp' hq hs' hi ht'
  rw [← decodeInteger_eq] at he
  simpa only [Polynomial.coe_aeval_eq_eval,
    ← CoordinateRecoveryMap.denominator (Int.castRingHom L) hcast p q c, Polynomial.eval_map] using he

/-- The exact degree has a binary product writer when the two inputs are separable. -/
theorem resultant_natDegree (p q : ℤ[X]) (c : ℕ)
    (hp : (p.map (Int.castRingHom L)).Separable) (hq : (q.map (Int.castRingHom L)).Separable)
    (hsp : (p.map (Int.castRingHom L)).Splits) (hsq : (q.map (Int.castRingHom L)).Splits) :
    (cannyResultant p q c).natDegree = p.natDegree * q.natDegree := by
  have hcast : Function.Injective (Int.castRingHom L) := Int.cast_injective
  have hsp' : ((p.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsp
  have hsq' : ((q.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsq
  calc
    _ = ((cannyResultant p q c).map (Int.castRingHom L)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective hcast _).symm
    _ = (cannyResultant (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) c).natDegree :=
      congrArg Polynomial.natDegree (CoordinateRecoveryMap.resultant (Int.castRingHom L) hcast p q c)
    _ = (p.map (Int.castRingHom L)).natDegree * (q.map (Int.castRingHom L)).natDegree :=
      cannyResultant_natDegree _ _ c hp hq hsp' hsq'
    _ = _ := by rw [Polynomial.natDegree_map_eq_of_injective hcast, Polynomial.natDegree_map_eq_of_injective hcast]

end LeanCanny.Algebra.PrimitivePair
