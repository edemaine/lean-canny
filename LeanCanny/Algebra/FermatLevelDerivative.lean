/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelLift

/-! # The appended free level derivative and its sign on the bounded lift

This is hypersurface regularity in the level direction. It makes no claim that
the critical-coordinate Hessian or the whole critical curve is nonsingular.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelLift
open MvPolynomial
variable {n : ℕ}

theorem derivative_last_rename (p : MvPolynomial (Fin (n+1)) ℤ) :
    pderiv (Fin.last (n+1)) (rename Fin.castSucc p)=0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp,pderiv_X,Fin.castSucc_ne_last]

theorem derivative_last (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) :
    pderiv (Fin.last (n+1)) (polynomial (source P A))=
      C (P.leading*(P.degree:ℤ))*X (Fin.last (n+1))^(P.degree-1)-C A := by
  rw [polynomial_eq]
  simp only [map_sub,map_add,derivative_last_rename,zero_add,pderiv_C_mul,Derivation.leibniz_pow,
    pderiv_X,Pi.single_apply,ite_true,mul_one]
  simp only [nsmul_eq_mul,C_mul,map_natCast]
  ring

theorem eval_derivative_last (P : IntegralMixedHistory.SpatialSource n) (A : ℤ)
    (x : Fin (n+1) → ℝ) (v : ℝ) :
    (pderiv (Fin.last (n+1)) (polynomial (source P A))).eval₂ (Int.castRingHom ℝ) (Fin.snoc x v)=
      (P.leading:ℝ)*(P.degree:ℝ)*v^(P.degree-1)-(A:ℝ) := by
  rw [derivative_last]
  simp only [eval₂_sub,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,Fin.snoc_last,Int.cast_mul,Int.cast_natCast,
    Int.coe_castRingHom]

theorem eval_derivative_last_neg (P : IntegralMixedHistory.SpatialSource n) (A : ℤ)
    (hP : P.leading=1) (hA : (P.degree:ℝ)<(A:ℝ)) (x : Fin (n+1) → ℝ) (v : ℝ)
    (hv : v∈Set.Icc (-1:ℝ) 1) :
    (pderiv (Fin.last (n+1)) (polynomial (source P A))).eval₂ (Int.castRingHom ℝ) (Fin.snoc x v)<0 := by
  have HV : |v|≤1 := abs_le.mpr hv
  have HP : v^(P.degree-1)≤1 := (le_abs_self _).trans (by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg v) HV (P.degree-1))
  have HM := mul_le_mul_of_nonneg_left HP (Nat.cast_nonneg (α:=ℝ) P.degree)
  rw [eval_derivative_last,hP,Int.cast_one,one_mul]
  nlinarith only [HM,hA]

end LeanCanny.Algebra.FermatLevelLift
