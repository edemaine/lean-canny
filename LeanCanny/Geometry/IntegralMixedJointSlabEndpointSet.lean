/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedRetainedSweep
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealSweepStep
/-! # One parent endpoint set survives either kind of retained endpoint birth -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open IntegralMixedFullHistoryScript IntegralMixedCurrentQCoordinateScaling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def jointEndpointSet (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h g : Fin (n+1))
    (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) : Set ℝ :=
  IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x F h g hg) φ old ∪
    realCriticalValues P (line F h) values h

noncomputable def retainedFrameChoices (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) :
    IntegralMixedRelativeCuts.Choices (step x hm c) hn (cutRule (step x hm c) (retained F) h g hg) ψ :=
  retainedChoices x hm c hn (cutRule x F h g hg) rfl φ ψ values a H HN old

theorem jointEndpointSet_retained_iff (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ) (t : ℝ) :
    t∈jointEndpointSet (step x hm c) hn ψ (retained F) h g hg (Fin.cons a values)
      (retainedFrameChoices x hm c hn φ ψ F h g hg values a H HN old) ↔
      t∈jointEndpointSet x hm φ F h g hg values old :=by
  unfold jointEndpointSet
  rw [realCriticalValues_retained]
  exact or_congr (retained_bad_iff x hm c hn (cutRule x F h g hg) rfl φ ψ values a H HN old t) Iff.rfl

omit [Fintype ι] in
theorem PrefixFrozen.sweepBadReal_eq {F : Frame n} (h : Fin (n+1)) (HP : PrefixFrozen (line F h))
    (x : State P S B m ι) (hm : m≤S) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (old : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ) :
    sweepBadReal x hm φ F h g hg values old=jointEndpointSet x hm φ F h g hg values
      (IntegralMixedCutSourceCast.choices
        (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen))
        x hm x.critical_cap (HP.spatial P) _ φ old) :=by
  unfold sweepBadReal jointEndpointSet
  rw [HP.cut_bad h x hm g hg φ old]

end LeanCanny.Geometry.IntegralMixedFrozenFrame
