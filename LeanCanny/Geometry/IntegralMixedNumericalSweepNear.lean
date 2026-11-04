/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepSpecialization
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
/-! # Ordered roots and Near depend only on the numerical frozen sweep -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open LeanCanny.Geometry LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m T C l :ℕ} {P :SpatialSource n} {ι κ :Type}
variable (x :State P S B m ι) (hm :m≤S) (y :State P T C l κ) (hl :l≤T)
  (r s :Rule n) (hr :r.slope=commonDenominator x) (hs :s.slope=commonDenominator y)
  (hoff :r.critical.offset=s.critical.offset) (hobj :r.critical.objective=s.critical.objective)
  (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ :y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (values :Fin m→ℝ) (other :Fin l→ℝ)
  (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
  (K :∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
  (HN :∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)

include hr hs hobj H K HN

theorem root_set_eq_of_levels (t :ℝ) (j :Fin (n-r.critical.offset.val+1)):
    IntegralMixedFrozenFrameSectionCode.roots y hl s ψ t (indexCast r s hoff j)=
      IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j:=by
  unfold IntegralMixedFrozenFrameSectionCode.roots IntegralMixedFrozenFrameSectionCode.polynomial
  exact congrArg Multiset.toFinset (specialized_selected_roots x hm y hl r s hr hs hoff hobj φ ψ
    values other H K t t (fun i hi=>congrArg (fun p :Polynomial ℝ=>p.eval t) (HN i hi)) j)

theorem rank_eq_of_levels (t z :ℝ) (j :Fin (n-r.critical.offset.val+1)):
    IntegralMixedSelectedRootRank.rank y hl s ψ t (indexCast r s hoff j) z=
      IntegralMixedSelectedRootRank.rank x hm r φ t j z:=by
  unfold IntegralMixedSelectedRootRank.rank
  rw [root_set_eq_of_levels x hm y hl r s hr hs hoff hobj φ ψ values other H K HN]

/-- This compares different histories and even different horizons/widths.
Only the normalized numerical sweep is shared; no tuple or ordinal is moved. -/
theorem near_iff_of_levels (a b endpoint z :ℝ) (j :Fin (n-r.critical.offset.val+1)) (code :ℕ):
    IntegralMixedSelectedCoordinateEndpoint.Near y hl s ψ a b endpoint (indexCast r s hoff j) code z↔
      IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b endpoint j code z:=by
  unfold IntegralMixedSelectedCoordinateEndpoint.Near
  have HR:=root_set_eq_of_levels x hm y hl r s hr hs hoff hobj φ ψ values other H K HN
  have HK:=rank_eq_of_levels x hm y hl r s hr hs hoff hobj φ ψ values other H K HN
  simp only [HR,HK]

theorem anchored_near_iff_of_levels (a b endpoint t mid child :ℝ)
    (j :Fin (n-r.critical.offset.val+1)):
    IntegralMixedSelectedCoordinateEndpoint.Near y hl s ψ a b endpoint (indexCast r s hoff j)
      (IntegralMixedSelectedRootRank.rank y hl s ψ t (indexCast r s hoff j) mid) child↔
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b endpoint j
      (IntegralMixedSelectedRootRank.rank x hm r φ t j mid) child:=by
  rw [rank_eq_of_levels x hm y hl r s hr hs hoff hobj φ ψ values other H K HN]
  exact near_iff_of_levels x hm y hl r s hr hs hoff hobj φ ψ values other H K HN a b endpoint child j _

end LeanCanny.Algebra.IntegralMixedNumericalSweep
