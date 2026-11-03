/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedCoordinateCommonScaling
public import LeanCanny.Algebra.ClearedCoordinateCriticalBounds
/-! # A common frozen clearing factor gives the exact critical annihilator scale -/
@[expose] public section
namespace LeanCanny.Algebra.ClearedCriticalCommonScaling
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {R : Type*} [CommRing R]
attribute [local irreducible] PurePowerRelativeAnnihilator.polynomial ClearedCoordinateBlock.specialize

theorem euler (s : R) (p : MvPolynomial (Fin (k+1)) R)
    (g : Fin (k+1)→MvPolynomial (Fin (k+1)) R) (D : ℕ) (r j : Fin (k+1)) :
    PurePowerEulerReduction.lower (C s*p) (fun i=>C s*g i) D r j=
      C s*PurePowerEulerReduction.lower p g D r j :=by
  unfold PurePowerEulerReduction.lower
  split_ifs
  · unfold PurePowerEulerReduction.objectiveLower
    rw [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  · rfl

theorem gradient (D : ℕ) (q s : R) (H : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)≤n+1) (p : MvPolynomial (Fin (n+1)) R)
    (hp : p.totalDegree≤D) (j : Fin (k+1)) :
    ClearedCoordinateCritical.gradientLower D (s*q) (fun i=>s*H i) offset hfit p j=
      C (s^D)*ClearedCoordinateCritical.gradientLower D q H offset hfit p j :=by
  exact ClearedCoordinateCommonScaling.specialize D q s H offset (k+1) _
    ((PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans hp))

theorem lower (D : ℕ) (q s : R) (H : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)≤n+1) (p : MvPolynomial (Fin (n+1)) R)
    (a : R) (hp : p.totalDegree≤D) (r j : Fin (k+1)) :
    ClearedCoordinateCritical.lower D (s*q) (fun i=>s*H i) offset hfit p a r j=
      C (s^D)*ClearedCoordinateCritical.lower D q H offset hfit p a r j :=by
  have HG : ClearedCoordinateCritical.gradientLower D (s*q) (fun i=>s*H i) offset hfit p=
      fun j=>C (s^D)*ClearedCoordinateCritical.gradientLower D q H offset hfit p j:=by
    funext j
    exact gradient D q s H offset hfit p hp j
  unfold ClearedCoordinateCritical.lower
  rw [ClearedCoordinateCommonScaling.block_lower D q s H offset (k+1) p a hp,HG]
  exact euler (s^D) (ClearedCoordinateBlock.lower D q H offset (k+1) p a)
    (ClearedCoordinateCritical.gradientLower D q H offset hfit p) D r j

theorem annihilator (D : ℕ) (q s : R) (H : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)≤n+1) (p : MvPolynomial (Fin (n+1)) R)
    (a : R) (hp : p.totalDegree≤D) (r j : Fin (k+1)) :
    ClearedCoordinateCritical.annihilator D (s*q) (fun i=>s*H i) offset hfit p a r j=
      Polynomial.C ((s^D)^((PurePowerReductionBounds.bound (k+1) D+1)*
        PurePowerReductionBounds.dimension (k+1) D))*
        ClearedCoordinateCritical.annihilator D q H offset hfit p a r j :=by
  unfold ClearedCoordinateCritical.annihilator
  have HG : ClearedCoordinateCritical.lower D (s*q) (fun i=>s*H i) offset hfit p a r=
      fun j=>C (s^D)*ClearedCoordinateCritical.lower D q H offset hfit p a r j:=by
    funext j
    exact lower D q s H offset hfit p a hp r j
  rw [HG]
  have HL : (a*(s*q)^D)*(D:R)=s^D*((a*q^D)*(D:R)):=by rw [mul_pow]; ring
  rw [HL,PurePowerCommonScaling.polynomial]
  rfl

end LeanCanny.Algebra.ClearedCriticalCommonScaling
