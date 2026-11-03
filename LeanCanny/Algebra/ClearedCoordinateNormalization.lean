/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedCriticalCommonScaling
public import LeanCanny.Algebra.CoordinateFrozenCriticalElimination
/-! # Numerical frozen heights remove the actual integer clearing product

The constant scale is computed from every actual integer coordinate scale.
No literal prefix relation or common scalar algebra is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateNormalization
open Polynomial
open scoped Classical
variable {n k : ℕ} {R : Type*} [Field R] [CharZero R]

noncomputable def normalized (c : Fin (n+1)→ℤ)
    (H : Fin (n+1)→Polynomial R) (i : ℕ) : Polynomial R :=
  if hi : i<n+1 then C ((c ⟨i,hi⟩:R)⁻¹)*H ⟨i,hi⟩ else 0

theorem numerator (c : Fin (n+1)→ℤ) (hc : ∀i,c i≠0)
    (H : Fin (n+1)→Polynomial R) (i : ℕ) :
    CoordinateFrozenCriticalElimination.numerators c H i=
      C (CoordinateFrozenCriticalElimination.denominator c:R)*normalized c H i :=by
  unfold CoordinateFrozenCriticalElimination.numerators normalized
  split_ifs with hi
  · let j : Fin (n+1):=⟨i,hi⟩
    have HC : (c j:R)≠0:=Int.cast_ne_zero.mpr (hc j)
    have HE : (CoordinateFrozenCriticalElimination.denominator c:R)*(c j:R)⁻¹=
        (CommonIntegerDenominator.denominator (Finset.univ.erase j) c:R) :=by
      change (CommonIntegerDenominator.denominator Finset.univ c:R)*_=_
      rw [CommonIntegerDenominator.denominator_split _ _ j (Finset.mem_univ j),Int.cast_mul]
      field_simp
    change H j*(CommonIntegerDenominator.denominator (Finset.univ.erase j) c:Polynomial R)=_
    rw [←C_eq_intCast,←mul_assoc,←C_mul,HE]
    exact mul_comm _ _
  · exact (mul_zero _).symm

theorem specialize (D : ℕ) (c : Fin (n+1)→ℤ) (hc : ∀i,c i≠0)
    (H : Fin (n+1)→Polynomial R) (offset dim : ℕ)
    (p : MvPolynomial (Fin (n+1)) (Polynomial R)) (hp : p.totalDegree≤D) :
    ClearedCoordinateBlock.specialize D
        (CoordinateFrozenCriticalElimination.denominator c:Polynomial R)
        (CoordinateFrozenCriticalElimination.numerators c H) offset dim p=
      MvPolynomial.C (C ((CoordinateFrozenCriticalElimination.denominator c:R)^D))*
        ClearedCoordinateBlock.specialize D 1 (normalized c H) offset dim p :=by
  have HH : CoordinateFrozenCriticalElimination.numerators c H=
      fun i=>C (CoordinateFrozenCriticalElimination.denominator c:R)*normalized c H i:=by
    funext i
    exact numerator c hc H i
  rw [HH,←C_eq_intCast]
  simpa only [mul_one,←map_pow] using
    ClearedCoordinateCommonScaling.specialize D (1:Polynomial R)
      (C (CoordinateFrozenCriticalElimination.denominator c:R)) (normalized c H)
      offset dim p hp

theorem annihilator (D : ℕ) (c : Fin (n+1)→ℤ) (hc : ∀i,c i≠0)
    (H : Fin (n+1)→Polynomial R) (offset : ℕ)
    (hfit : offset+(k+1)≤n+1) (p : MvPolynomial (Fin (n+1)) (Polynomial R))
    (a : Polynomial R) (hp : p.totalDegree≤D) (r j : Fin (k+1)) :
    ClearedCoordinateCritical.annihilator D
        (CoordinateFrozenCriticalElimination.denominator c:Polynomial R)
        (CoordinateFrozenCriticalElimination.numerators c H) offset hfit p a r j=
      C (C (((CoordinateFrozenCriticalElimination.denominator c:R)^D)^
        ((PurePowerReductionBounds.bound (k+1) D+1)*PurePowerReductionBounds.dimension (k+1) D)))*
        ClearedCoordinateCritical.annihilator D 1 (normalized c H) offset hfit p a r j :=by
  have HH : CoordinateFrozenCriticalElimination.numerators c H=
      fun i=>C (CoordinateFrozenCriticalElimination.denominator c:R)*normalized c H i:=by
    funext i
    exact numerator c hc H i
  rw [HH,←C_eq_intCast]
  simpa only [mul_one,←map_pow] using
    ClearedCriticalCommonScaling.annihilator D (1:Polynomial R)
      (C (CoordinateFrozenCriticalElimination.denominator c:R)) (normalized c H)
      offset hfit p a hp r j

end LeanCanny.Algebra.ClearedCoordinateNormalization
