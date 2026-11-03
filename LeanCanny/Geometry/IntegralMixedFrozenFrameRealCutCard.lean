/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealSweepStep
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutCard
/-! # The real-critical sweep retains the original cut-count bound -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem realCriticalValues_ncard (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    (realCriticalValues P F values h).ncard≤2^B :=
  (Set.ncard_le_ncard (realCriticalValues_subset x hm φ F h hh values H)
    (heightCut_finite x hm F h φ)).trans (height_cut_roots_ncard x hm φ F h)

theorem sweepBadReal_ncard (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h g : Fin (n+1))
    (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (sweepBadReal x hm φ F h g hg values c).ncard≤(3*(n+1)+1)*2^B := by
  apply (Set.ncard_union_le _ _).trans
  have HC:=selected_bad_ncard (cutSource x F h) hm (cutRule x F h g hg) φ c hcap
  have HR:=realCriticalValues_ncard x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) values H
  calc
    _≤3*(n+1)*2^B+2^B:=Nat.add_le_add HC HR
    _=(3*(n+1)+1)*2^B:=by ring

end LeanCanny.Geometry.IntegralMixedFrozenFrame
