/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialParameterPolynomial
/-! # Integer formal centers for the actual radius-parameter spatial polynomial -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialFormalCenter
open ETR LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Center (c :List Bool):=MvPolynomial (Fin (d c)) ℤ
noncomputable abbrev Radius (c :List Bool):=Polynomial (Center c)
noncomputable def constants (c :List Bool):ℤ→+*Radius c:=Polynomial.C.comp MvPolynomial.C
noncomputable def centerMap (c :List Bool) (a :Fin (d c)→ℝ):Center c→+*ℝ:=
  MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a
noncomputable def radiusMap (c :List Bool) (a :Fin (d c)→ℝ):Radius c→+*Polynomial ℝ:=
  Polynomial.mapRingHom (centerMap c a)

noncomputable def polynomial (c :List Bool):MvPolynomial (Fin (N c+d c+1)) (Radius c):=
  ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c+d c+1)).map (constants c)+
    (∑i,(MvPolynomial.X (centerIndex c i)-MvPolynomial.C (Polynomial.C (MvPolynomial.X i)))^2)+
    (MvPolynomial.X (radiusIndex c)-MvPolynomial.C Polynomial.X)^2

theorem polynomial_specialization (c :List Bool) (a :Fin (d c)→ℝ):
    (polynomial c).map (radiusMap c a)=FormulaSignSlotRadialParameterPolynomial.polynomial c a:=by
  have HC:(radiusMap c a).comp (constants c)=Polynomial.C.comp (Int.castRingHom ℝ):=by
    ext x
    simp [constants,radiusMap,centerMap]
  have HR (z :Center c):radiusMap c a (Polynomial.C z)=Polynomial.C (centerMap c a z):=by
    simp [radiusMap]
  have HX:radiusMap c a Polynomial.X=Polynomial.X:=by simp [radiusMap]
  have HA (i :Fin (d c)):centerMap c a (MvPolynomial.X i)=a i:=by simp [centerMap]
  simp only [polynomial,FormulaSignSlotRadialParameterPolynomial.polynomial,map_add,map_pow,map_sub,map_sum,
    MvPolynomial.map_X,MvPolynomial.map_C,MvPolynomial.map_map,HC,HR,HX,HA]

/-- Center specialization followed by radius evaluation is the exact original
frozen radial polynomial, not a substitute regularized source. -/
theorem radius_specialization (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ):
    ((polynomial c).map (radiusMap c a)).map (Polynomial.evalRingHom r)=
      FormulaSignSlotCenteredRadialLimits.polynomial c a r:=by
  rw [polynomial_specialization,FormulaSignSlotRadialParameterPolynomial.specialization]

private theorem square_degree {R :Type*} [CommRing R] [Nontrivial R] {m :ℕ} (i :Fin m) (a :R):
    ((MvPolynomial.X i-MvPolynomial.C a :MvPolynomial (Fin m) R)^2).totalDegree≤2:=by
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have H:(MvPolynomial.X i-MvPolynomial.C a :MvPolynomial (Fin m) R).totalDegree≤1:=
    (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  exact Nat.mul_le_mul_left 2 H

/-- The same original-only spatial degree budget holds before center evaluation.
This is a spatial degree statement; no eliminant height bound is asserted. -/
theorem spatial_degree (c :List Bool):(polynomial c).totalDegree≤degreeBudget c:=by
  have H2:2≤degreeBudget c:=by unfold degreeBudget;omega
  unfold polynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (PolynomialMapDegree.degree_le _ _).trans
        ((Term.totalDegree_finitePolynomial _ _).trans ((Term.degreeBound_le_dataSize _).trans (Nat.le_add_right _ 2)))
    · exact (MvPolynomial.totalDegree_finsetSum_le (fun i _=>square_degree (R:=Radius c) (centerIndex c i)
        (Polynomial.C (MvPolynomial.X i :Center c)))).trans H2
  · exact (square_degree (R:=Radius c) (radiusIndex c) Polynomial.X).trans H2

end LeanCanny.Connectivity.FormulaSignSlotRadialFormalCenter
