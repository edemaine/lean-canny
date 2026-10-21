/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import LeanCanny.Algebra.DeformationLowestCoefficient

/-! # Root curves at regular points

The implicit function theorem constructs a local continuous family of roots
when the derivative in the unknowns is invertible. If those roots annihilate
a polynomial in the deformation parameter, its lowest coefficient vanishes
at the limiting coefficient parameters. No root family is supplied as a
hypothesis; invertibility remains essential to this regular-point result.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LeanCanny.Geometry.ImplicitRootPersistence
variable {K E F : Type*} [RCLike K]
  [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

theorem exists_curve (f : K × E → F) (a : E)
    (hf : ContDiffAt K 1 f (0, a)) (hz : f (0, a) = 0)
    (hJac : (fderiv K f (0, a) ∘L ContinuousLinearMap.inr K K E).IsInvertible) :
    ∃ curve : K → E, curve 0 = a ∧ ContinuousAt curve 0 ∧
      ∀ᶠ s in 𝓝 (0 : K), f (s, curve s) = 0 := by
  let curve := hf.implicitFunction (by norm_num) hJac
  refine ⟨curve, hf.implicitFunction_apply_self _ _, ?_, ?_⟩
  · exact (hf.hasStrictFDerivAt_implicitFunction (by norm_num) hJac).continuousAt
  · simpa only [hz] using hf.eventually_apply_implicitFunction (by norm_num) hJac

variable {R : Type*} [CommRing R]

theorem trailingCoeff_eq_zero (p : Polynomial R) (φ : E → R →+* K)
    (hφ : ∀ r, Continuous (fun a => φ a r)) (f : K × E → F) (a : E)
    (hf : ContDiffAt K 1 f (0, a)) (hz : f (0, a) = 0)
    (hJac : (fderiv K f (0, a) ∘L ContinuousLinearMap.inr K K E).IsInvertible)
    (hroot : ∀ s z, f (s, z) = 0 → p.eval₂ (φ z) s = 0) :
    φ a p.trailingCoeff = 0 := by
  obtain ⟨curve, hc0, hc, hcurve⟩ := exists_curve f a hf hz hJac
  apply LeanCanny.Algebra.DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto
    p φ hφ (𝓝[≠] (0 : K)) curve id a
  · exact hc0 ▸ hc.tendsto.mono_left nhdsWithin_le_nhds
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · exact self_mem_nhdsWithin
  · filter_upwards [hcurve.filter_mono nhdsWithin_le_nhds] with s hs
    exact hroot s (curve s) hs

end LeanCanny.Geometry.ImplicitRootPersistence
