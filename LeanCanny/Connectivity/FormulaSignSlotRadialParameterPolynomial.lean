/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotTiltedRadialGrid
public import LeanCanny.Algebra.ParametricTiltedCoerciveSpecialization
public import LeanCanny.Algebra.TrailingCoefficientMap
/-! # One radius-parameter polynomial for the actual fixed-center radial slices -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialParameterPolynomial
open ETR Set Polynomial MvPolynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (a : Fin (d c) → ℝ) :
    MvPolynomial (Fin (N c+d c+1)) (Polynomial ℝ) :=
  ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c+d c+1)).map
    (Polynomial.C.comp (Int.castRingHom ℝ))+
    (∑ i, (MvPolynomial.X (centerIndex c i)-MvPolynomial.C (Polynomial.C (a i)))^2)+
    (MvPolynomial.X (radiusIndex c)-MvPolynomial.C Polynomial.X)^2

theorem specialization (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    (polynomial c a).map (Polynomial.evalRingHom r)=FormulaSignSlotCenteredRadialLimits.polynomial c a r := by
  have HC : (Polynomial.evalRingHom r).comp (Polynomial.C.comp (Int.castRingHom ℝ))=Int.castRingHom ℝ := by
    ext x
    simp
  simp only [polynomial,FormulaSignSlotCenteredRadialLimits.polynomial,map_add,map_pow,map_sub,map_sum,
    MvPolynomial.map_X,MvPolynomial.map_C,MvPolynomial.map_map,HC,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X]

private theorem square_degree {m : ℕ} (i : Fin m) (a : Polynomial ℝ) :
    ((MvPolynomial.X i-MvPolynomial.C a : MvPolynomial (Fin m) (Polynomial ℝ))^2).totalDegree≤2 := by
  apply (totalDegree_pow _ _).trans
  have H : (MvPolynomial.X i-MvPolynomial.C a : MvPolynomial (Fin m) (Polynomial ℝ)).totalDegree≤1 :=
    (totalDegree_sub _ _).trans (by simp)
  exact Nat.mul_le_mul_left 2 H

theorem degree (c : List Bool) (a : Fin (d c) → ℝ) : (polynomial c a).totalDegree≤degreeBudget c := by
  have H2 : 2≤degreeBudget c := by unfold degreeBudget; omega
  unfold polynomial
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (PolynomialMapDegree.degree_le _ _).trans
        ((Term.totalDegree_finitePolynomial _ _).trans ((Term.degreeBound_le_dataSize _).trans (Nat.le_add_right _ 2)))
    · exact (totalDegree_finsetSum_le (fun i _ => square_degree (centerIndex c i) (Polynomial.C (a i)))).trans H2
  · exact (square_degree _ _).trans H2

end LeanCanny.Connectivity.FormulaSignSlotRadialParameterPolynomial
