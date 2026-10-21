/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantCoordinates
public import LeanCanny.Algebra.CoordinateRecoveryBounds

/-! # Explicit polynomial coordinates for the Cartesian product of root sets

The report's resultant is the parameter polynomial. The common coordinate
denominator is D, with numerators theta*D+c*N and -N, where N,D are the actual
piecewise coordinate-recovery polynomials. No interpolated coordinate polynomial
or coefficient descent is used in these formulas.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePair
open Polynomial

variable {R : Type*} [CommRing R]

noncomputable def denominator (p q : R[X]) (c : ℕ) : R[X] := coordinateDenominator p q c
noncomputable def rightNumerator (p q : R[X]) (c : ℕ) : R[X] := -coordinateNumerator p q c
noncomputable def leftNumerator (p q : R[X]) (c : ℕ) : R[X] :=
  X * denominator p q c + C (c : R) * coordinateNumerator p q c

theorem denominator_degree (p q : R[X]) (c : ℕ) :
    (denominator p q c).natDegree ≤ max 1 ((q.natDegree - 1) * p.natDegree) :=
  coordinateDenominator_natDegree_le p q c

theorem rightNumerator_degree (p q : R[X]) (c : ℕ) :
    (rightNumerator p q c).natDegree ≤ max 1 ((q.natDegree - 1) * p.natDegree) := by
  rw [rightNumerator, Polynomial.natDegree_neg]
  exact coordinateNumerator_natDegree_le p q c

theorem leftNumerator_degree (p q : R[X]) (c : ℕ) :
    (leftNumerator p q c).natDegree ≤ 1 + max 1 ((q.natDegree - 1) * p.natDegree) := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le (denominator_degree p q c))
  · exact (natDegree_C_mul_le _ _).trans ((coordinateNumerator_natDegree_le p q c).trans (by omega))

theorem leftNumerator_coeff (p q : R[X]) (c k : ℕ) :
    (leftNumerator p q c).coeff k =
      (if 1 ≤ k then (denominator p q c).coeff (k - 1) else 0) +
        (c : R) * (coordinateNumerator p q c).coeff k := by
  rw [leftNumerator, coeff_add, coeff_C_mul]
  simpa only [pow_one] using congrArg (fun z => z + (c : R) * (coordinateNumerator p q c).coeff k)
    (coeff_X_pow_mul' (denominator p q c) 1 k)

section Field
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def decode (p q : K[X]) (c : ℕ) (theta : L) : L × L :=
  (Polynomial.aeval theta (leftNumerator p q c) / Polynomial.aeval theta (denominator p q c),
    Polynomial.aeval theta (rightNumerator p q c) / Polynomial.aeval theta (denominator p q c))

theorem decode_shear (p q : K[X]) (c : ℕ) (a b : L)
    (hp : p ≠ 0) (hq : q.Separable) (hs : (q.map (algebraMap K L)).Splits)
    (hi : Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L)))
    (ha : Polynomial.aeval a p = 0) (hb : Polynomial.aeval b q = 0) :
    decode p q c (shear c (a, b)) = (a, b) := by
  have hr := coordinate_recovery_spec p q c a b hp hq hs hi ha hb
  apply Prod.ext
  · change Polynomial.aeval _ (leftNumerator p q c) / Polynomial.aeval _ (denominator p q c) = a
    rw [leftNumerator, map_add, map_mul, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    simp only [denominator, map_natCast]
    rw [add_div, mul_div_cancel_right₀ _ hr.1, mul_div_assoc]
    exact hr.2.2.symm
  · change Polynomial.aeval _ (rightNumerator p q c) / Polynomial.aeval _ (denominator p q c) = b
    simp only [rightNumerator, denominator, map_neg]
    exact hr.2.1.symm

theorem decode_root (p q : K[X]) (c : ℕ) (theta : L)
    (hp : p ≠ 0) (hq : q.Separable) (hs : (q.map (algebraMap K L)).Splits)
    (hi : Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L)))
    (ht : Polynomial.aeval theta (cannyResultant p q c) = 0) :
    Polynomial.aeval (decode p q c theta).1 p = 0 ∧
      Polynomial.aeval (decode p q c theta).2 q = 0 ∧
      shear c (decode p q c theta) = theta ∧ Polynomial.aeval theta (denominator p q c) ≠ 0 := by
  obtain ⟨a, b, ha, hb, he⟩ := (cannyResultant_roots p q c theta hq.ne_zero hs).mp ht
  change theta = shear c (a, b) at he
  rw [he, decode_shear p q c a b hp hq hs hi ha hb]
  exact ⟨ha, hb, rfl, (coordinate_recovery_spec p q c a b hp hq hs hi ha hb).1⟩

noncomputable def rootEquiv (p q : K[X]) (c : ℕ)
    (hp : p ≠ 0) (hq : q.Separable) (hs : (q.map (algebraMap K L)).Splits)
    (hi : Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L))) :
    {theta : L // Polynomial.aeval theta (cannyResultant p q c) = 0} ≃
      (rootPairs (L := L) p q : Set (L × L)) where
  toFun theta := ⟨decode p q c theta.val,
    (mem_rootPairs p q hp hq.ne_zero _).mpr
      ⟨(decode_root p q c theta.val hp hq hs hi theta.property).1,
        (decode_root p q c theta.val hp hq hs hi theta.property).2.1⟩⟩
  invFun x := ⟨shear c x.val, (cannyResultant_roots p q c _ hq.ne_zero hs).mpr
    ⟨x.val.1, x.val.2, ((mem_rootPairs p q hp hq.ne_zero _).mp x.property).1,
      ((mem_rootPairs p q hp hq.ne_zero _).mp x.property).2, rfl⟩⟩
  left_inv theta := Subtype.ext (decode_root p q c theta.val hp hq hs hi theta.property).2.2.1
  right_inv x := Subtype.ext (decode_shear p q c x.val.1 x.val.2 hp hq hs hi
    ((mem_rootPairs p q hp hq.ne_zero _).mp x.property).1 ((mem_rootPairs p q hp hq.ne_zero _).mp x.property).2)

/-- The unnormalized integer-friendly parameter polynomial preserves separability. -/
theorem resultant_separable [Infinite L] (p q : K[X]) (c : ℕ)
    (hp : p.Separable) (hq : q.Separable)
    (hsp : (p.map (algebraMap K L)).Splits) (hsq : (q.map (algebraMap K L)).Splits)
    (hi : Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L))) :
    (cannyResultant p q c).Separable := by
  apply (Polynomial.separable_map (algebraMap K L)).mp
  rw [cannyResultant_eq_sign_mul, Polynomial.map_mul, Polynomial.map_C,
    projectionResultant_map_eq p q c hp hq hsp hsq, ← mul_assoc, ← Polynomial.C_mul]
  have hs : algebraMap K L ((-1 : K) ^ (p.natDegree * q.natDegree)) ≠ 0 := by simp
  have hscale : algebraMap K L (resultantScale p q) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne (resultantScale_ne_zero p q hp.ne_zero hq.ne_zero)
  apply Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero hs hscale)))
  exact separable_prod_X_sub_C_iff'.mpr hi

/-- A finite candidate interval suffices for the explicit formulas above. -/
theorem exists_bounded_direction [CharZero L] (p q : K[X])
    (hp : p.Separable) (hq : q.Separable)
    (hsp : (p.map (algebraMap K L)).Splits) (hsq : (q.map (algebraMap K L)).Splits) :
    ∃ c : ℕ, c ≤ (p.natDegree * q.natDegree) ^ 2 ∧
      Set.InjOn (shear c) (rootPairs (L := L) p q : Set (L × L)) := by
  obtain ⟨c, hc, hi⟩ := exists_bounded_separating_shear (rootPairs (L := L) p q)
  rw [rootPairs_card p q hp hq hsp hsq] at hc
  exact ⟨c, hc, hi⟩

end Field
end LeanCanny.Algebra.PrimitivePair
