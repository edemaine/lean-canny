/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQNumerators
public import LeanCanny.Algebra.IntegralMixedCoordinateTrailing
/-! # Actual selected coordinate covariance under one retained command

The common scalar is derived from the actual new bank denominator and
retained quotient values. The source, horizon, width and sweep parameter
are fixed; no covariance or root-persistence premise is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def coordinateScale (x : State P S B m ι) (hm : m≤S) (c : Command P B) (r : Rule n) : ℝ :=
  (((leading x hm c:ℝ)^(n+1))^P.degree)^((PurePowerReductionBounds.bound
    (n-r.critical.offset.val+1) P.degree+1)*PurePowerReductionBounds.dimension
      (n-r.critical.offset.val+1) P.degree)

omit [Fintype ι] in
theorem coordinateScale_ne_zero (x : State P S B m ι) (hm : m≤S) (c : Command P B) (r : Rule n) :
    coordinateScale x hm c r ≠ 0 :=by
  exact pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (Int.cast_ne_zero.mpr (leading_ne_zero x hm c))))

theorem selected_scaling (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (j : Fin (n-r.critical.offset.val+1)) :
    selected (step x hm c) hn (shiftRule x hm c r) j ψ=
      C (C (coordinateScale x hm c r))*selected x hm r j φ :=by
  rw [selected_coordinate,selected_coordinate]
  have HD : (CoordinateFrozenCriticalElimination.denominator
      (data (step x hm c) hn (shiftRule x hm c r).critical).scales:Polynomial ℝ)=
      C ((leading x hm c:ℝ)^(n+1))*
        (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:Polynomial ℝ) :=by
    rw [denominator]
    simp only [Int.cast_mul,Int.cast_pow]
    rw [map_pow,Polynomial.C_eq_intCast]
  have HH : (fun i=>(CoordinateFrozenCriticalElimination.numerators
      (data (step x hm c) hn (shiftRule x hm c r).critical).scales
      (heights (step x hm c) (shiftRule x hm c r)) i).map ψ.toRingHom)=
      fun i=>C ((leading x hm c:ℝ)^(n+1))*
        (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom:=by
    funext i
    exact selected_numerators x hm c hn r hr φ ψ values a H HN i
  rw [HD,HH]
  have HP : (P.low.map (Int.castRingHom (Polynomial ℝ))).totalDegree≤P.degree :=
    (PolynomialMapDegree.degree_le _ _).trans P.low_degree.le
  simpa only [coordinateScale,←map_pow,shiftRule,objective] using
    ClearedCriticalCommonScaling.annihilator P.degree
      (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:Polynomial ℝ)
      (C ((leading x hm c:ℝ)^(n+1)))
      (fun i=>(CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)
      r.critical.offset.val (fit r).le (P.low.map (Int.castRingHom (Polynomial ℝ)))
      (P.leading:Polynomial ℝ) HP (objective r) j

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
