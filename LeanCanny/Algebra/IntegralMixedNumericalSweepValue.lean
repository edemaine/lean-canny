/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepGuards
/-! # Actual value-Gram guards across independent realized histories

Independent nonzero coordinate and tested-row scales reach the actual
weighted Gram certificate. No equality of the Gram polynomials is assumed.
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

theorem value_trailing_degree :
    (IntegralMixedValueTrailing.selectedValue y hl s (indexCast r s hoff j) ψ).natTrailingDegree=
      (IntegralMixedValueTrailing.selectedValue x hm r j φ).natTrailingDegree :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  let r : Rule n:=⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  let s : Rule n:=⟨⟨o,b,c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  change (IntegralMixedValueTrailing.selectedValue y hl s j ψ).natTrailingDegree=
    (IntegralMixedValueTrailing.selectedValue x hm r j φ).natTrailingDegree
  have HC : (fun i=>selected y hl s i ψ)=
      fun i=>Polynomial.C (Polynomial.C (coordinateScale y hl s/coordinateScale x hm r))*selected x hm r i φ:=by
    funext i
    exact selected_scaling x hm y hl r s hr hs rfl rfl φ ψ values other H K HN i
  have HR := eq_of_heq (row_scaling x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j)
  change (IntegralMixedSweepRows.row y hl s j).map (Polynomial.mapRingHom ψ.toRingHom)=
    MvPolynomial.C (Polynomial.C (rowScale y hl s/rowScale x hm r))*
      (IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom) at HR
  rw [IntegralMixedCurrentQCoordinateScaling.selected_value_eq,
    IntegralMixedCurrentQCoordinateScaling.selected_value_eq,HC,HR]
  exact RelativeAffineGridValueScaling.trailing_degree_scale _ _ _ _
    (coordinateScale y hl s/coordinateScale x hm r) (rowScale y hl s/rowScale x hm r)
    (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r))
    (div_ne_zero (rowScale_ne_zero y hl s) (rowScale_ne_zero x hm r))
    (IntegralMixedCurrentQCoordinateScaling.selected_value_gram_nonzero x hm r φ j)

theorem value_trailing_zero (t : ℝ) :
    (IntegralMixedValueTrailing.selectedValue y hl s (indexCast r s hoff j) ψ).trailingCoeff.eval t=0 ↔
      (IntegralMixedValueTrailing.selectedValue x hm r j φ).trailingCoeff.eval t=0 :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  let r : Rule n:=⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  let s : Rule n:=⟨⟨o,b,c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  change (IntegralMixedValueTrailing.selectedValue y hl s j ψ).trailingCoeff.eval t=0 ↔
    (IntegralMixedValueTrailing.selectedValue x hm r j φ).trailingCoeff.eval t=0
  have HC : (fun i=>selected y hl s i ψ)=
      fun i=>Polynomial.C (Polynomial.C (coordinateScale y hl s/coordinateScale x hm r))*selected x hm r i φ:=by
    funext i
    exact selected_scaling x hm y hl r s hr hs rfl rfl φ ψ values other H K HN i
  have HR := eq_of_heq (row_scaling x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j)
  change (IntegralMixedSweepRows.row y hl s j).map (Polynomial.mapRingHom ψ.toRingHom)=
    MvPolynomial.C (Polynomial.C (rowScale y hl s/rowScale x hm r))*
      (IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom) at HR
  rw [IntegralMixedCurrentQCoordinateScaling.selected_value_eq,
    IntegralMixedCurrentQCoordinateScaling.selected_value_eq,HC,HR]
  exact RelativeAffineGridValueScaling.trailing_zero_scale _ _ _ _
    (coordinateScale y hl s/coordinateScale x hm r) (rowScale y hl s/rowScale x hm r)
    (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r))
    (div_ne_zero (rowScale_ne_zero y hl s) (rowScale_ne_zero x hm r))
    (IntegralMixedCurrentQCoordinateScaling.selected_value_gram_nonzero x hm r φ j) t

end LeanCanny.Algebra.IntegralMixedNumericalSweep
