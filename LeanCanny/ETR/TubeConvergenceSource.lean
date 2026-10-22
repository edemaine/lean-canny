/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSource
public import LeanCanny.Geometry.TubeSigns

/-! # Tube critical points near strict projection maxima of encoded ETR

At a feasible point with a strict local projection maximum on its active zero
locus, every neighborhood contains local maxima on all sufficiently small
positive tubes. They satisfy the integer projection equations and preserve
positivity of all inactive constraints. The strict-maximum hypothesis is
explicit: existence of suitable generic directions remains unproved.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConvergenceSource
open Geometry

theorem approximation_of_strict_maximum (bits : List Bool) (epsilon delta : ℝ)
    (z : PerturbedSource.Point bits) (v : TubeSource.Coordinate bits → ℝ)
    (hd : 0 < delta) (hz : z ∈ PerturbedSource.feasible bits epsilon delta)
    (hv : v (TubePolynomial.base (Fin (CompactSource.term bits).arity)) = 1)
    (hstrict : TubePolynomial.StrictLocalMaximum (CompactSource.polynomial bits)
      (CriticalPointSource.activeSet bits epsilon z) epsilon delta v z) :
    TubePolynomial.CriticalApproximationWithPositiveInactive (CompactSource.polynomial bits)
      (CriticalPointSource.activeSet bits epsilon z) epsilon delta v z := by
  have h := TubePolynomial.active_approximation_of_strict (CompactSource.polynomial bits) epsilon delta v z hd hz hv hstrict
  exact h

end LeanCanny.ETR.TubeConvergenceSource
