/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQNumerators
public import LeanCanny.Algebra.IntegralMixedSweepRows
/-! # Actual tested source and gradient rows share the retained clearing scale -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (j : Fin (n-r.critical.offset.val+1))



omit [Fintype ι] in
theorem selected_row :
    (IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom)=
      ClearedCoordinateBlock.specialize P.degree
        (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:Polynomial ℝ)
        (fun i=>(CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)
        r.critical.offset.val (n-r.critical.offset.val+1)
        ((IntegralMixedSweepRows.integerRow P r j).map (Int.castRingHom (Polynomial ℝ))) :=by
  unfold IntegralMixedSweepRows.row IntegralMixedSweepRows.denominator IntegralMixedSweepRows.numerators
  rw [ClearedCoordinateMap.specialize]
  simp only [Polynomial.coe_mapRingHom,Polynomial.map_intCast]
  congr 1
  rw [MvPolynomial.map_map]
  apply congrArg (fun f : ℤ→+*Polynomial ℝ=>(IntegralMixedSweepRows.integerRow P r j).map f)
  exact RingHom.ext_int _ _

noncomputable def rowScale : ℝ := ((leading x hm c:ℝ)^(n+1))^P.degree

omit [Fintype ι] in
theorem rowScale_ne_zero : rowScale x hm c ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ (Int.cast_ne_zero.mpr (leading_ne_zero x hm c)))

include hr H HN

theorem selected_row_scaling :
    (IntegralMixedSweepRows.row (step x hm c) hn (shiftRule x hm c r) j).map (Polynomial.mapRingHom ψ.toRingHom)=
      MvPolynomial.C (C (rowScale x hm c))*(IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom) :=by
  rw [selected_row,selected_row]
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
  have HP : ((IntegralMixedSweepRows.integerRow P r j).map (Int.castRingHom (Polynomial ℝ))).totalDegree≤P.degree :=
    (PolynomialMapDegree.degree_le _ _).trans (IntegralMixedSweepRows.integerRow_degree P r j)
  simpa only [rowScale,←map_pow,IntegralMixedSweepRows.integerRow,shiftRule,objective] using
    ClearedCoordinateCommonScaling.specialize P.degree
      (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:Polynomial ℝ)
      (C ((leading x hm c:ℝ)^(n+1)))
      (fun i=>(CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)
      r.critical.offset.val (n-r.critical.offset.val+1)
      ((IntegralMixedSweepRows.integerRow P r j).map (Int.castRingHom (Polynomial ℝ))) HP

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
