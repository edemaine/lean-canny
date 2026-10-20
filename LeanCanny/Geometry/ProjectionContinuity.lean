/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactSupportingProjection
public import Mathlib.Topology.Compactness.Compact

/-! # Uniform control of projection changes on compact sets

Joint continuity in direction and point makes a small direction change
uniformly small on any fixed compact point set.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

theorem continuous_projection_joint : Continuous (fun q : (ι → ℝ) × (ι → ℝ) => projection q.1 q.2) := by
  simp only [CompactSupportingProjection.projection_apply]
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd))

theorem close_on_compact (K : Set (ι → ℝ)) (hK : IsCompact K) (v : ι → ℝ)
    (e : ℝ) (he : 0 < e) : ∀ᶠ w in nhds v, ∀ x ∈ K, |projection w x - projection v x| < e := by
  apply hK.eventually_forall_of_forall_eventually
  intro x _
  have hc : Continuous (fun q : (ι → ℝ) × (ι → ℝ) => |projection q.1 q.2 - projection v q.2|) :=
    (continuous_projection_joint.sub ((projection v).continuous.comp continuous_snd)).abs
  exact hc.continuousAt.eventually (Iio_mem_nhds (by simpa only [sub_self, abs_zero] using he))

end LeanCanny.Geometry.ProjectionCritical
