/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepSpecialization
public import LeanCanny.Connectivity.IntegralMixedSelectedRootRank
/-! # Actual coordinate ranks agree on equal specialized frozen slices

This compares ranks among all real coordinate roots, including ghost roots.
It does not identify independent complete sampler words or their ordinals.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSpecializedRootRankComparison
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep
open IntegralMixedSelectedRootRank IntegralMixedFrozenFrameSectionCode
open scoped Classical
variable {n S B m T C l : ℕ} {P : SpatialSource n} {ι κ : Type}
variable (x : State P S B m ι) (hm : m≤S) (y : State P T C l κ) (hl : l≤T)
variable (r s : Rule n) (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
variable (hoff : r.critical.offset=s.critical.offset) (hobj : r.critical.objective=s.critical.objective)
variable (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
variable (values : Fin m→ℝ) (other : Fin l→ℝ)
variable (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
variable (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
variable (t u : ℝ) (HN : ∀i,i<r.critical.offset.val→
  (normalized r values i).eval t=(normalized s other i).eval u)
variable (j : IntegralMixedSelectedGeometry.Free r)

include hr hs hobj H K HN in
theorem root_sets :
    roots y hl s ψ u (indexCast r s hoff j)=roots x hm r φ t j :=by
  exact congrArg Multiset.toFinset
    (specialized_selected_roots x hm y hl r s hr hs hoff hobj φ ψ values other H K t u HN j)

include hr hs hobj H K HN in
theorem ranks (z : ℝ) :
    rank y hl s ψ u (indexCast r s hoff j) z=rank x hm r φ t j z :=by
  unfold rank
  rw [root_sets x hm y hl r s hr hs hoff hobj φ ψ values other H K t u HN j]

include hr hs hobj H K HN in
theorem ordinals (a : IntegralMixedSelectedPhysicalFiber.physical x hm r φ t)
    (b : IntegralMixedSelectedPhysicalFiber.physical y hl s ψ u)
    (hcoord : b.val (ClearedCoordinateCritical.freeIndex s.critical.offset.val (fit s).le (indexCast r s hoff j))=
      a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)) :
    (ordinal y hl s ψ u b (indexCast r s hoff j)).val=(ordinal x hm r φ t a j).val :=by
  rw [ordinal_rank,ordinal_rank,hcoord]
  exact ranks x hm y hl r s hr hs hoff hobj φ ψ values other H K t u HN j _

end LeanCanny.Connectivity.IntegralMixedSpecializedRootRankComparison
