/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedRegularComponents
public import LeanCanny.Encoding.BoundedRegularControls
public import LeanCanny.Geometry.BoundedRegularRadiusExponents

/-! # Explicit integer outer-coordinate cuts for the actual regular source

The nonnegative squared energy bounds every even-power coordinate term.
The resulting strict dyadic cutoff needs only the original penalty exponent.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularCoordinateCutoff
open LeanCanny.Algebra LeanCanny.Encoding MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ}
def exponent (n D R : ℕ) := BoundedZeroSource.penaltyExponent n D R+2

theorem power_sum_le (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : Fin (n+4)→ℝ)
    (hw : (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℝ) w=0) :
    ∑ i,w i^BoundedZeroSource.powerDegree D≤(2 : ℝ)^BoundedZeroSource.penaltyExponent n D R+1 := by
  change (FermatCriticalHomogenization.polynomial _ _ _).eval₂ _ _=0 at hw
  rw [IntegerRegularSource.polynomial_eq] at hw
  simp only [FermatCriticalHomogenization.polynomial,BoundedRegularSource.lower,eval₂_sub,eval₂_mul,
    eval₂_add,eval₂_C,eval₂_one,eval₂_rename,Function.comp_def,eval₂_sum,eval₂_pow,eval₂_X,
    IntegerRegularSource.scale,Int.coe_castRingHom,
    Int.cast_pow,Int.cast_ofNat,Int.cast_one,one_mul] at hw
  have HZ:=BoundedZeroSource.nonneg q R (fun i=>w (i.castAdd 2))
  have HE : 0≤(2 : ℝ)^BoundedZeroSource.perturbationExponent n D b R*
      (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) (fun i=>w (i.castAdd 2)) :=
    mul_nonneg (by positivity) HZ
  have HS : (1 : ℝ)≤2^IntegerRegularSource.exponent (n+3) (BoundedZeroSource.powerDegree D)
      (BoundedRegularSource.sourceMassExponent n D b R) := one_le_pow₀ (by norm_num)
  have HA : (2 : ℝ)^BoundedZeroSource.perturbationExponent n D b R*
      (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) (fun i=>w (i.castAdd 2))-
      (2 : ℝ)^BoundedZeroSource.penaltyExponent n D R+∑ i,w i^BoundedZeroSource.powerDegree D≤1 := by
    nlinarith
  linarith

theorem coordinate_lt (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : Fin (n+4)→ℝ)
    (hw : (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℝ) w=0) (j : Fin (n+4)) :
    |w j|<(2 : ℝ)^exponent n D R := by
  have HS:=power_sum_le q D b R w hw
  have HP : (1 : ℝ)≤2^BoundedZeroSource.penaltyExponent n D R := one_le_pow₀ (by norm_num)
  have HC : |w j|≤(2 : ℝ)^BoundedZeroSource.penaltyExponent n D R+1 := by
    by_cases HJ : |w j|≤1
    · linarith
    · have HD : BoundedZeroSource.powerDegree D≠0 := by have H:=BoundedRegularSource.powerDegree_gt_one D; omega
      have Hpow : |w j|≤|w j|^BoundedZeroSource.powerDegree D:=le_self_pow₀ (le_of_not_ge HJ) HD
      have HE : |w j|^BoundedZeroSource.powerDegree D=w j^BoundedZeroSource.powerDegree D := by
        rw [←abs_pow,abs_of_nonneg ((BoundedZeroSource.powerDegree_even D).pow_nonneg _)]
      rw [HE] at Hpow
      exact Hpow.trans ((Finset.single_le_sum
        (fun i _=>(BoundedZeroSource.powerDegree_even D).pow_nonneg (w i)) (Finset.mem_univ j)).trans HS)
  unfold exponent
  rw [pow_add]
  norm_num only [pow_two] at *
  nlinarith

theorem exponent_affine (n D R : ℕ) :
    exponent n D R=exponent n D 0+BoundedZeroSource.powerDegree D*R := by
  unfold exponent
  rw [BoundedRegularRadius.penalty_affine n D R]
  omega

theorem as_radius_power (n D R : ℕ) :
    (2 : ℝ)^exponent n D R=(2 : ℝ)^exponent n D 0*((2 : ℝ)^R)^BoundedZeroSource.powerDegree D := by
  rw [exponent_affine,pow_add,←pow_mul,Nat.mul_comm R]

theorem exponent_binary {n D R : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) (hR : BinaryFn R) :
    BinaryFn (fun q=>exponent (n q) (D q) (R q)) := by
  unfold exponent
  exact ((hR.mul (BoundedZeroControls.powerDegree_binary hD)).add
    ((BinaryFn.ofUnary (hn.add (UnaryFn.const 2))).size)).add (BinaryFn.const 2)

end LeanCanny.Geometry.BoundedRegularCoordinateCutoff
