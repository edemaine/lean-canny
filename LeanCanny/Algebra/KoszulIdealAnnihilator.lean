/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulExterior
public import Mathlib.RingTheory.Ideal.Operations

/-! # The input ideal annihilates positive Koszul homology

The exterior multiplication homotopy works for every linear combination
of the inputs. Thus every element of the generated ideal sends cycles to
boundaries and annihilates the positive homology modules.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulExterior
open scoped Classical BigOperators
variable {R I : Type*} [CommRing R] [Fintype I]

theorem ideal_smul_mem_range_of_mem_ker (p : I → R) (k : ℕ) (f : R) (hf : f ∈ Ideal.span (Set.range p))
    (x : ExteriorAlgebra.exteriorPower R (k + 1) (I → R)) (hx : gradedDifferential p k x = 0) :
    f • x ∈ LinearMap.range (gradedDifferential p (k + 1)) := by
  obtain ⟨v, hv⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  have hz : differential p x.val = 0 := congrArg Subtype.val hx
  refine ⟨⟨wedge v x.val, wedge_mem v (k + 1) x.val x.property⟩, ?_⟩
  apply Subtype.ext
  change differential p (wedge v x.val) = f • x.val
  have he := homotopy_identity p v x.val
  change differential p (wedge v x.val) + wedge v (differential p x.val) = (∑ i, v i * p i) • x.val at he
  simpa only [hz, map_zero, add_zero, hv] using he

theorem ideal_smul_ker_le_range (p : I → R) (k : ℕ) :
    Ideal.span (Set.range p) • LinearMap.ker (gradedDifferential p k) ≤
      LinearMap.range (gradedDifferential p (k + 1)) := by
  apply Submodule.smul_le.mpr
  intro f hf x hx
  exact ideal_smul_mem_range_of_mem_ker p k f hf x hx

end LeanCanny.Algebra.KoszulExterior
