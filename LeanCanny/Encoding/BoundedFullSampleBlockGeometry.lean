/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleBlockScaling
public import LeanCanny.Geometry.CoordinateBlockCompactness

/-! # Properness of full-source blocks at actual parents

Contained free blocks inherit properness from the constructed full source.
Every real level is compact, including singular levels and the empty block.
The actual parent coordinates need no additional bounds.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleBlockGeometry
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.ETR MvPolynomial
open BoundedFullSampleBlock BoundedFullSampleBlockScaling
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem proper_original (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hfit : F.offset u + F.dim u ≤ F.source.dim u + 4) :
    IsProperMap (fun y : Fin (F.dim u) → ℝ => (original F u p).eval y) := by
  unfold original
  apply CoordinateBlockCompactness.proper_finite (Int.castRingHom ℝ) (Formula.extend p.val)
    (F.offset u) (F.dim u) ((family F).source u) hfit
  exact BoundedFullGeometry.proper (BoundedFullWriter.original F.source u)
    (BoundedFullWriter.size F.source u) (BoundedFullWriter.size F.source u) (F.source.radius u)

theorem compact_level (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hfit : F.offset u + F.dim u ≤ F.source.dim u + 4) (t : ℝ) :
    IsCompact {y : Fin (F.dim u) → ℝ | (original F u p).eval y = t} :=
  (proper_original F u p hfit).isCompact_preimage isCompact_singleton

end LeanCanny.Encoding.BoundedFullSampleBlockGeometry
