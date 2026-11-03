/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSpecializedRootRankComparison
/-! # The same physical anchor has the same section word on equal slices

This compares coordinate-rank words at the same declared digit width.
It does not compare or transport complete sampler words.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSpecializedSectionWordComparison
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep
open IntegralMixedFrozenFrameSectionCode
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m T l : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem word_eq (x : State P S B m ι) (hm : m≤S) (y : State P T B l κ) (hl : l≤T)
    (r s : Rule n) (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset) (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (t u : ℝ) (HN : ∀i,i<r.critical.offset.val→
      (normalized r values i).eval t=(normalized s other i).eval u)
    (a : IntegralMixedSelectedPhysicalFiber.physical x hm r φ t)
    (b : IntegralMixedSelectedPhysicalFiber.physical y hl s ψ u) (Hab : a.val=b.val) :
    word x hm r φ t a=word y hl s ψ u b :=by
  unfold word
  apply congrArg (LeanCanny.Encoding.FixedWidthNatVector.encode (n+1) B)
  funext i
  by_cases hi : i<n-r.critical.offset.val+1
  · have hi' : i<n-s.critical.offset.val+1:=by rw [←hoff];exact hi
    rw [dite_eq_left hi,dite_eq_left hi']
    let j : IntegralMixedSelectedGeometry.Free r:=⟨i,hi⟩
    have HJ : indexCast r s hoff j=⟨i,hi'⟩:=Fin.ext rfl
    have HC : b.val (ClearedCoordinateCritical.freeIndex s.critical.offset.val (fit s).le (indexCast r s hoff j))=
        a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) :=by
      rw [←Hab]
      apply congrArg a.val
      apply Fin.ext
      change s.critical.offset.val+i=r.critical.offset.val+i
      rw [hoff]
    have HO:=IntegralMixedSpecializedRootRankComparison.ordinals x hm y hl r s hr hs hoff hobj
      φ ψ values other H K t u HN j a b HC
    rw [HJ] at HO
    exact HO.symm
  · have hi' : ¬i<n-s.critical.offset.val+1:=by rw [←hoff];exact hi
    rw [dite_eq_right hi,dite_eq_right hi']

end LeanCanny.Connectivity.IntegralMixedSpecializedSectionWordComparison
