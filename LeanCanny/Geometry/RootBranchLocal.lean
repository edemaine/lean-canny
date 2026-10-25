/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Local branches of regular root systems

The implicit function theorem supplies a continuous branch on an actual closed
parameter interval, together with local completeness of that branch. The
branch and its interval are conclusions, rather than supplied curve data.
No effective bound for the interval radius is asserted here.
-/

@[expose] public section

namespace LeanCanny.Geometry.RootBranchLocal
open Set Filter Metric
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A regular root belongs to a continuous family of roots on a closed
interval. All roots sufficiently near the original pair lie on that family. -/
theorem exists_branch (f : ℝ × E → F) (t₀ : ℝ) (a : E)
    (hf : ContDiffAt ℝ 1 f (t₀, a)) (hz : f (t₀, a) = 0)
    (hJac : (fderiv ℝ f (t₀, a) ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ curve : ℝ → E,
      curve t₀ = a ∧ ContinuousOn curve (Icc (t₀ - δ) (t₀ + δ)) ∧
      (∀ t ∈ Icc (t₀ - δ) (t₀ + δ), f (t, curve t) = 0) ∧
      ∀ᶠ z in 𝓝 (t₀, a), f z = 0 ↔ curve z.1 = z.2 := by
  let curve := hf.implicitFunction (by norm_num) hJac
  have hc0 : curve t₀ = a := hf.implicitFunction_apply_self _ _
  have hc : ContDiffAt ℝ 1 curve t₀ := hf.contDiffAt_implicitFunction _ _
  obtain ⟨C, s, hs, hLip⟩ := hc.exists_lipschitzOnWith
  have hroots : ∀ᶠ t in 𝓝 t₀, f (t, curve t) = 0 := by
    simpa only [hz] using hf.eventually_apply_implicitFunction (by norm_num) hJac
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hroots)
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsub : Icc (t₀ - δ) (t₀ + δ) ⊆ ball t₀ ε := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |t - t₀| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact habs.trans_lt (by dsimp [δ]; linarith)
  refine ⟨δ, hδ, curve, hc0, hLip.continuousOn.mono (fun t ht => (hball (hsub ht)).1),
    fun t ht => (hball (hsub ht)).2, ?_⟩
  simpa only [hz] using hf.eventually_apply_eq_iff_implicitFunction (by norm_num) hJac

end LeanCanny.Geometry.RootBranchLocal
