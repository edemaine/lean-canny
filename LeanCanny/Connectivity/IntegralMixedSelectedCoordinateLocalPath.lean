/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
public import Mathlib.Analysis.Convex.PathConnected
/-! # An anchored physical midpoint and coordinate Near tests give a source path -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
open Set LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

/-- Selected bad-cut avoidance alone supplies the closed physical arc.
No component-cover or no-critical-value hypothesis is needed for this direction. -/
theorem joined_source_of_near (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    {a b : ℝ} (t₀ : Ioo a b)
    (havoid : ∀t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c)
    (mid : physical x hm r φ t₀.val) (endpoint : ℝ) (he : endpoint∈Icc a b)
    (child : Fin (n+1)→ℝ) (hf : Frozen x hm r φ endpoint child)
    (hn : ∀i : Free r,Near x hm r φ a b endpoint i
      (IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i
        (mid.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)))
      (child (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i))) :
    JoinedIn {y : Fin (n+1)→ℝ |
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0}
      child mid.val :=by
  obtain ⟨_,curve,HA,HC,HR,_,_⟩:=
    IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs x hm r φ c a b t₀ havoid
  have HE : curve mid endpoint=child:=
    (point_near_iff x hm r φ c t₀ havoid (curve mid) (HC mid) (HR mid)
      endpoint he child hf).mp (by simpa only [HA] using hn)
  have HI : IsPathConnected (Icc a b):=
    (convex_Icc a b).isPathConnected ⟨t₀.val,Ioo_subset_Icc_self t₀.property⟩
  have HJ : JoinedIn {y : Fin (n+1)→ℝ |
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0}
      (curve mid endpoint) (curve mid t₀.val) :=by
    apply ((HI.joinedIn endpoint he t₀.val (Ioo_subset_Icc_self t₀.property)).map (HC mid)).mono
    rintro y ⟨t,ht,rfl⟩
    have HZ:=(HR mid t ht).2 (objective r)
    simpa only [Set.mem_ofPred_eq,IntegralMixedSweepRows.integerRow,ite_true] using HZ
  simpa only [HE,HA] using HJ

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
