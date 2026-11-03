/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.BoundedMarkedParameterTerm
public import LeanCanny.Geometry.BoundedMarkedComponents
/-! # Parameter-variable tests are the literal regular and marking equations -/
@[expose] public section
namespace LeanCanny.Geometry.BoundedMarkedParameterSemantics
open LeanCanny.Algebra LeanCanny.ETR MvPolynomial
open BoundedMarkedParameterTerm
open scoped BigOperators

theorem mark_eval (t : Term) (n R : ℕ) (ht : t.arity≤n) (v : ℕ→ℝ)
    (hr : v (n+4)=(2:ℝ)^R) :
    (mark t n).eval v=(BoundedRegularSource.markPolynomial (t.finitePolynomial n) R).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val) := by
  rw [eval_mark]
  simp only [BoundedRegularSource.markPolynomial,BoundedZeroSource.polynomial,BoundedZeroSource.sphere,
    eval₂_rename,Function.comp_def,eval₂_add,eval₂_pow,eval₂_sub,eval₂_sum,eval₂_X,eval₂_C,Int.coe_castRingHom,
    BoundedZeroSource.radiusSquared,Int.cast_pow,Int.cast_ofNat,Fin.val_castAdd]
  have H:=PartialHomogenization.finite_eval t n v ht
  have HP : (2:ℝ)^(2*R)=((2:ℝ)^R)^2 := by rw [Nat.mul_comm 2 R,pow_mul]
  rw [H,hr,HP]

theorem source_eval {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Fin (n+4)→ℝ) :
    (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℝ) x=
      (2:ℝ)^BoundedRegularSource.regularizationExponent n D b R*
        ((2:ℝ)^BoundedZeroSource.perturbationExponent n D b R*
          (BoundedRegularSource.markPolynomial q R).eval₂ (Int.castRingHom ℝ) x-
          (2:ℝ)^BoundedZeroSource.penaltyExponent n D R+∑ i,x i^BoundedZeroSource.powerDegree D)-1 := by
  simp only [BoundedRegularSource.polynomial,BoundedRegularSource.lower,FermatCriticalHomogenization.polynomial,
    IntegerRegularSource.lower,IntegerRegularSource.leading,IntegerRegularSource.scale,BoundedRegularSource.regularizationExponent,
    BoundedRegularSource.markPolynomial,eval₂_sub,eval₂_mul,eval₂_C,eval₂_add,Int.coe_castRingHom,
    Int.cast_pow,Int.cast_ofNat,mul_one,eval₂_one,eval₂_sum,eval₂_pow,eval₂_X]
  ring


theorem regular_eval (t : Term) (n D R : ℕ) (ht : t.arity≤n) (v : ℕ→ℝ)
    (hr : v (n+4)=(2:ℝ)^R)
    (hL : v (n+5)=(2:ℝ)^BoundedRegularSource.regularizationExponent n D D R)
    (hB : v (n+6)=(2:ℝ)^BoundedZeroSource.perturbationExponent n D D R)
    (hK : v (n+7)=(2:ℝ)^BoundedZeroSource.penaltyExponent n D R) :
    (regular t n (BoundedZeroSource.powerDegree D)).eval v=
      (BoundedRegularSource.polynomial (t.finitePolynomial n) D D R).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val) := by
  rw [eval_regular _ _ _ (Nat.zero_lt_of_lt (BoundedRegularSource.powerDegree_gt_one D)),source_eval]
  rw [hL,hB,hK,mark_eval t n R ht v hr]

end LeanCanny.Geometry.BoundedMarkedParameterSemantics
