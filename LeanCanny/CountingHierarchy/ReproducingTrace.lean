/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.Ring

/-!
# A finite reproducing identity determines multiplication traces

The trace of a rank-one map `x ↦ f(x) • c` is `f(c)`. Consequently a
finite reproducing kernel for a functional identifies every multiplication
trace with that functional applied to the kernel's diagonal. This linear
algebra step requires no assumptions about roots or separability.
-/

public section

namespace LeanCanny.CountingHierarchy

open Module
open scoped Classical BigOperators

variable {S A ι κ : Type*} [CommRing S] [CommRing A] [Algebra S A] [Fintype ι]

theorem trace_eq_of_reproducing (b : Basis ι S A) (L : A →ₗ[S] S)
    (s : Finset κ) (c m : κ → A)
    (h : ∀ x : A, ∑ i ∈ s, L (m i * x) • c i = x) (v : A) :
    Algebra.trace S A v = L (v * ∑ i ∈ s, c i * m i) := by
  let : Module.Free S A := Module.Free.of_basis b
  let : Module.Finite S A := Module.Finite.of_basis b
  have hdecomp : Algebra.lmul S A v =
      ∑ i ∈ s, (L.comp (Algebra.lmul S A (m i * v))).smulRight (c i) := by
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_assoc] using (h (v * x)).symm
  rw [Algebra.trace_apply, hdecomp, map_sum]
  simp only [LinearMap.trace_smulRight, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [← map_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end LeanCanny.CountingHierarchy
