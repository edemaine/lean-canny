/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOriginalSweepRecord
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutContinue
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
public import LeanCanny.Algebra.IntegralMixedCurrentQBadCuts
public import LeanCanny.Algebra.IntegralMixedCutSourceCast
/-! # Retained original frames give the exact shifted current-Q sweep -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedCurrentQCoordinateScaling
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
set_option backward.isDefEq.respectTransparency false

theorem retained_sweep (x : State P S B m ι) (hm : m≤S) (c : Command P B)
    (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) :
    sweep (step x hm c) (retained F) h hh g hg=shiftRule x hm c (sweep x F h hh g hg) :=rfl

theorem retained_cutRule (x : State P S B m ι) (hm : m≤S) (c : Command P B)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen) :
    cutRule (step x hm c) (retained F) h g hg=shiftRule x hm c (cutRule x F h g hg) :=rfl

omit [Fintype ι] in
theorem PrefixFrozen.cut_factor {F : Frame n} (h : Fin (n+1)) (HP : PrefixFrozen (line F h))
    (x : State P S B m ι) (hm : m≤S) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Kind
      (IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) (cutRule x F h g hg)) :
    IntegralMixedRelativeCuts.factor (cutSource x F h) hm (cutRule x F h g hg) c=
      IntegralMixedRelativeCuts.factor x hm (cutRule x F h g hg)
        (IntegralMixedCutSourceCast.kind (HP.spatial P) _ c) :=
  IntegralMixedCutSourceCast.factor (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) x hm x.critical_cap (HP.spatial P) _ c

omit [Fintype ι] in
private theorem bad_reframe {Q : SpatialSource n} (x : State P S B m ι) (hm : m≤S)
    (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ : Q=P) (r : Rule n) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : IntegralMixedRelativeCuts.Choices (reframe x Q hc) hm r φ) :
    LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad (reframe x Q hc) hm r φ old=
      LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ
        (IntegralMixedCutSourceCast.choices x hm hc hQ r φ old) :=by
  subst Q
  cases x
  rfl

omit [Fintype ι] in
theorem PrefixFrozen.cut_bad {F : Frame n} (h : Fin (n+1)) (HP : PrefixFrozen (line F h))
    (x : State P S B m ι) (hm : m≤S) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ) :
    LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad (cutSource x F h) hm (cutRule x F h g hg) φ old=
      LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x F h g hg) φ
        (IntegralMixedCutSourceCast.choices (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) x hm x.critical_cap (HP.spatial P) _ φ old) :=
  bad_reframe (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) x hm x.critical_cap (HP.spatial P) _ φ old

omit [Fintype ι] in
theorem realCriticalValues_retained (F : Frame n) (values : Fin m→ℝ) (a : ℝ) (h : Fin (n+1)) :
    realCriticalValues P (line (retained F) h) (Fin.cons a values) h=
      realCriticalValues P (line F h) values h :=by
  ext t
  simp only [realCriticalValues,shiftedSlice,retained,line,evaluate_later]

end LeanCanny.Geometry.IntegralMixedFrozenFrame
