/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepCongruence
/-! # Independent realized sweeps have explicit constant scaling

The two states may have different banks, scalar algebras, horizons and
widths. Equal normalized frozen equations and equal projection data supply
the comparison. There is no common-prefix or root-label premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m T C l : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem selected_scaling (x : State P S B m ι) (hm : m≤S)
    (y : State P T C l κ) (hl : l≤T) (r s : Rule n)
    (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (j : Fin (n-r.critical.offset.val+1)) :
    selected y hl s (indexCast r s hoff j) ψ=
      Polynomial.C (Polynomial.C (coordinateScale y hl s/coordinateScale x hm r))*selected x hm r j φ :=by
  rw [selected_eq y hl s hs ψ other K,selected_eq x hm r hr φ values H,
    ←coordinate_congr P r s hoff hobj values other HN j]
  rw [←mul_assoc,←map_mul,←map_mul,div_mul_cancel₀ _ (coordinateScale_ne_zero x hm r)]

theorem row_scaling (x : State P S B m ι) (hm : m≤S)
    (y : State P T C l κ) (hl : l≤T) (r s : Rule n)
    (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (j : Fin (n-r.critical.offset.val+1)) :
    HEq ((IntegralMixedSweepRows.row y hl s (indexCast r s hoff j)).map (Polynomial.mapRingHom ψ.toRingHom))
      (MvPolynomial.C (Polynomial.C (rowScale y hl s/rowScale x hm r))*
        (IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom)) :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  apply heq_of_eq
  rw [selected_row_eq y hl _ hs ψ other K,selected_row_eq x hm _ hr φ values H]
  have HE := eq_of_heq (row_congr P
    ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
    ⟨⟨o,b,c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
    rfl rfl values other HN j)
  rw [←HE]
  rw [←mul_assoc,←map_mul,←map_mul,div_mul_cancel₀ _ (rowScale_ne_zero x hm _)]

end LeanCanny.Algebra.IntegralMixedNumericalSweep
