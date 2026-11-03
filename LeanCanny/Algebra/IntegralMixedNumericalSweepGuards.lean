/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepComparison
public import LeanCanny.Algebra.IntegralMixedCurrentQValueCuts
public import LeanCanny.Algebra.IntegralMixedCurrentQPrincipalScaling
/-! # Actual coordinate and principal guards across independent histories

The real constant ratios are derived from numerical frozen equations, rather
than supplied as a factor-covariance hypothesis.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m T C l : ℕ} {P : SpatialSource n} {ι κ : Type}
variable (x : State P S B m ι) (hm : m≤S) (y : State P T C l κ) (hl : l≤T) (r s : Rule n)
    (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset) (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (j : Fin (n-r.critical.offset.val+1))
include hr hs hoff hobj H K HN

theorem coefficient_scaling (i : ℕ) :
    ((IntegralMixedCriticalSweep.coordinate y hl s (indexCast r s hoff j)).coeff i).map ψ.toRingHom=
      Polynomial.C (coordinateScale y hl s/coordinateScale x hm r)*
        ((IntegralMixedCriticalSweep.coordinate x hm r j).coeff i).map φ.toRingHom :=by
  simpa only [selected,Polynomial.coeff_map,Polynomial.coeff_C_mul,Polynomial.coe_mapRingHom] using
    congrArg (fun p : Polynomial (Polynomial ℝ)=>p.coeff i)
      (selected_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j)

theorem coefficient_zero_iff (i : ℕ) :
    ((IntegralMixedCriticalSweep.coordinate y hl s (indexCast r s hoff j)).coeff i).map ψ.toRingHom=0 ↔
      ((IntegralMixedCriticalSweep.coordinate x hm r j).coeff i).map φ.toRingHom=0 :=by
  rw [coefficient_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j i]
  have HE : Polynomial.C (coordinateScale y hl s/coordinateScale x hm r)≠(0:Polynomial ℝ):=
    Polynomial.C_ne_zero.mpr (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r))
  exact mul_eq_zero.trans (or_iff_right HE)

theorem coefficient_root_iff (i : ℕ) (t : ℝ) :
    ((IntegralMixedCriticalSweep.coordinate y hl s (indexCast r s hoff j)).coeff i).eval₂ ψ.toRingHom t=0 ↔
      ((IntegralMixedCriticalSweep.coordinate x hm r j).coeff i).eval₂ φ.toRingHom t=0 :=by
  rw [←Polynomial.eval_map,←Polynomial.eval_map,
    coefficient_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j i]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,mul_eq_zero,
    div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r),false_or]

theorem principal_scaling (i : ℕ) :
    (IntegralMixedCoordinateSquarefree.principal y hl s (indexCast r s hoff j) i).map ψ.toRingHom=
      Polynomial.C ((coordinateScale y hl s/coordinateScale x hm r)^
        ((IntegralMixedCoordinateSquarefree.coordinateDegree P r-1-i)+
          (IntegralMixedCoordinateSquarefree.coordinateDegree P r-i)))*
        (IntegralMixedCoordinateSquarefree.principal x hm r j i).map φ.toRingHom :=by
  rw [IntegralMixedCurrentQCoordinateScaling.selected_principal,
    IntegralMixedCurrentQCoordinateScaling.selected_principal,
    selected_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j,
    Polynomial.derivative_C_mul,PrincipalSubresultant.psc_C_mul_left,PrincipalSubresultant.psc_C_mul_right]
  have HD : IntegralMixedCoordinateSquarefree.coordinateDegree P s=
      IntegralMixedCoordinateSquarefree.coordinateDegree P r:=by
    unfold IntegralMixedCoordinateSquarefree.coordinateDegree
    rw [hoff]
  rw [HD,←mul_assoc,←map_pow,←map_pow,←map_mul,←pow_add]

theorem principal_zero_iff (i : ℕ) :
    (IntegralMixedCoordinateSquarefree.principal y hl s (indexCast r s hoff j) i).map ψ.toRingHom=0 ↔
      (IntegralMixedCoordinateSquarefree.principal x hm r j i).map φ.toRingHom=0 :=by
  rw [principal_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j i]
  have HE : Polynomial.C ((coordinateScale y hl s/coordinateScale x hm r)^
        ((IntegralMixedCoordinateSquarefree.coordinateDegree P r-1-i)+
          (IntegralMixedCoordinateSquarefree.coordinateDegree P r-i)))≠(0:Polynomial ℝ):=
    Polynomial.C_ne_zero.mpr (pow_ne_zero _
      (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r)))
  exact mul_eq_zero.trans (or_iff_right HE)

theorem principal_root_iff (i : ℕ) (t : ℝ) :
    (IntegralMixedCoordinateSquarefree.principal y hl s (indexCast r s hoff j) i).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedCoordinateSquarefree.principal x hm r j i).eval₂ φ.toRingHom t=0 :=by
  rw [←Polynomial.eval_map,←Polynomial.eval_map,
    principal_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K HN j i]
  have HE := pow_ne_zero
    ((IntegralMixedCoordinateSquarefree.coordinateDegree P r-1-i)+
      (IntegralMixedCoordinateSquarefree.coordinateDegree P r-i))
    (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r))
  simp only [Polynomial.eval_mul,Polynomial.eval_C,mul_eq_zero,HE,false_or]

end LeanCanny.Algebra.IntegralMixedNumericalSweep
