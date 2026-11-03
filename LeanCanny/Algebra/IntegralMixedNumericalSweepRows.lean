/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweep
/-! # The actual source and gradient rows have the numerical frozen form -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def rowScale (x : State P S B m ι) (hm : m≤S) (r : Rule n) : ℝ :=
  (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:ℝ)^P.degree

theorem rowScale_ne_zero (x : State P S B m ι) (hm : m≤S) (r : Rule n) : rowScale x hm r≠0 :=
  pow_ne_zero _ (Int.cast_ne_zero.mpr
    (CoordinateFrozenCriticalElimination.denominator_ne_zero _ (data x hm r.critical).scales_ne))

noncomputable def row (P : SpatialSource n) (r : Rule n) (values : Fin m→ℝ)
    (j : Fin (n-r.critical.offset.val+1)) :
    MvPolynomial (Fin (n-r.critical.offset.val+1)) (Polynomial ℝ) :=
  ClearedCoordinateBlock.specialize P.degree 1 (normalized r values)
    r.critical.offset.val (n-r.critical.offset.val+1)
    ((IntegralMixedSweepRows.integerRow P r j).map (Int.castRingHom (Polynomial ℝ)))

theorem selected_row_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (hr : r.slope=commonDenominator x) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (j : Fin (n-r.critical.offset.val+1)) :
    (IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom)=
      MvPolynomial.C (C (rowScale x hm r))*row P r values j :=by
  rw [IntegralMixedCurrentQCoordinateScaling.selected_row]
  have HH : (fun i=>(CoordinateFrozenCriticalElimination.numerators
      (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)=
      CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales
        (fun i=>(heights x r i).map φ.toRingHom):=by
    funext i
    exact IntegralMixedCurrentQCoordinateScaling.map_numerators (Polynomial.mapRingHom φ.toRingHom) _ _ i
  rw [HH,ClearedCoordinateNormalization.specialize P.degree _ (data x hm r.critical).scales_ne]
  · rw [normalized_eq x hm r hr φ values H]
    rfl
  · exact (PolynomialMapDegree.degree_le _ _).trans (IntegralMixedSweepRows.integerRow_degree P r j)

end LeanCanny.Algebra.IntegralMixedNumericalSweep
