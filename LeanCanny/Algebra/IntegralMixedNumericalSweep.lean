/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedCoordinateNormalization
public import LeanCanny.Algebra.ClearedCoordinateFrozenCongruence
public import LeanCanny.Algebra.IntegralMixedCurrentQSelectedCoordinate
public import LeanCanny.Algebra.IntegralMixedCurrentQSelectedRows
/-! # An actual mixed sweep factors through its numerical frozen heights

The quotient interpretation determines the normalized real frozen equations.
The actual state contributes a nonzero constant clearing scale. Independent
histories need not have the same scalar algebra or complete sample labels.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def numericalHeights (r : Rule n) (values : Fin m→ℝ)
    (i : Fin (n+1)) : Polynomial ℝ :=
  C ((r.critical.heights i).evaluate values)+if i=r.height then X else 0

noncomputable def normalized (r : Rule n) (values : Fin m→ℝ) : ℕ→Polynomial ℝ :=
  ClearedCoordinateNormalization.normalized r.critical.scales (numericalHeights r values)

theorem heights_eq (x : State P S B m ι) (r : Rule n)
    (hr : r.slope=commonDenominator x) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (i : Fin (n+1)) :
    (heights x r i).map φ.toRingHom=C (commonDenominator x:ℝ)*numericalHeights r values i :=by
  have HC (u : ℤ) : (C (u:x.sampler.scalarPrefix.carrier)).map φ.toRingHom=C (u:ℝ):=by
    rw [Polynomial.map_C,map_intCast]
  unfold heights numericalHeights
  simp only [Polynomial.map_add,Polynomial.map_C]
  have HE : φ.toRingHom (expression x (r.critical.heights i))=
      (commonDenominator x:ℝ)*(r.critical.heights i).evaluate values:=
    expression_recover x φ values H _
  rw [HE]
  by_cases hi : i=r.height
  · simp only [hi,ite_true,Polynomial.map_mul,Polynomial.map_X,HC,hr,C_mul]
    ring
  · simp only [ite_eq_right hi,Polynomial.map_zero,add_zero,C_mul]

theorem normalized_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (hr : r.slope=commonDenominator x) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    ClearedCoordinateNormalization.normalized (data x hm r.critical).scales
      (fun i=>(heights x r i).map φ.toRingHom)=normalized r values :=by
  funext i
  unfold normalized ClearedCoordinateNormalization.normalized
  split_ifs with hi
  · let j : Fin (n+1):=⟨i,hi⟩
    change C (((data x hm r.critical).scales j:ℝ)⁻¹)*(heights x r j).map φ.toRingHom=
      C ((r.critical.scales j:ℝ)⁻¹)*numericalHeights r values j
    have HS : ((data x hm r.critical).scales j:ℝ)=
        (commonDenominator x:ℝ)*(r.critical.scales j:ℝ):=Int.cast_mul _ _
    rw [HS,heights_eq x r hr φ values H j]
    have HQ : (commonDenominator x:ℝ)≠0:=Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
    have HC : (r.critical.scales j:ℝ)≠0:=Int.cast_ne_zero.mpr (r.critical.scales_ne_zero j)
    have HE : ((commonDenominator x:ℝ)*(r.critical.scales j:ℝ))⁻¹*
        (commonDenominator x:ℝ)=(r.critical.scales j:ℝ)⁻¹:=by field_simp
    rw [←mul_assoc,←C_mul,HE]
  · rfl

noncomputable def coordinateScale (x : State P S B m ι) (hm : m≤S) (r : Rule n) : ℝ :=
  ((CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:ℝ)^P.degree)^
    ((PurePowerReductionBounds.bound (n-r.critical.offset.val+1) P.degree+1)*
      PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree)

theorem coordinateScale_ne_zero (x : State P S B m ι) (hm : m≤S) (r : Rule n) :
    coordinateScale x hm r≠0 :=by
  exact pow_ne_zero _ (pow_ne_zero _ (Int.cast_ne_zero.mpr
    (CoordinateFrozenCriticalElimination.denominator_ne_zero _ (data x hm r.critical).scales_ne)))

noncomputable def coordinate (P : SpatialSource n) (r : Rule n) (values : Fin m→ℝ)
    (j : Fin (n-r.critical.offset.val+1)) : Polynomial (Polynomial ℝ) :=
  ClearedCoordinateCritical.annihilator P.degree 1 (normalized r values)
    r.critical.offset.val (fit r).le (P.low.map (Int.castRingHom (Polynomial ℝ)))
    (P.leading:Polynomial ℝ) (objective r) j

theorem selected_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (hr : r.slope=commonDenominator x) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (j : Fin (n-r.critical.offset.val+1)) :
    selected x hm r j φ=C (C (coordinateScale x hm r))*coordinate P r values j :=by
  rw [IntegralMixedCurrentQCoordinateScaling.selected_coordinate]
  have HH : (fun i=>(CoordinateFrozenCriticalElimination.numerators
      (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)=
      CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales
        (fun i=>(heights x r i).map φ.toRingHom):=by
    funext i
    exact IntegralMixedCurrentQCoordinateScaling.map_numerators (Polynomial.mapRingHom φ.toRingHom) _ _ i
  rw [HH,ClearedCoordinateNormalization.annihilator P.degree _ (data x hm r.critical).scales_ne]
  · rw [normalized_eq x hm r hr φ values H]
    rfl
  · exact (PolynomialMapDegree.degree_le _ _).trans P.low_degree.le

end LeanCanny.Algebra.IntegralMixedNumericalSweep
