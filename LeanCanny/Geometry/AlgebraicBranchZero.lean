/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AlgebraicBranchLimit
public import Mathlib.Topology.Connected.Clopen

/-! # Zero tests along continuous algebraic branches

Factor out the lowest power of the value variable from an annihilator.
Where its remaining constant coefficient is nonzero, the zero values form a
clopen set. On a connected parameter space a single sample decides whether
the test vanishes on the entire branch. Multiple roots are allowed.
-/

@[expose] public section
namespace LeanCanny.Geometry.AlgebraicBranchZero
open Set Polynomial Topology

lemma continuous_evaluation (p : Polynomial (Polynomial ℝ)) :
    Continuous (fun z : ℝ × ℝ => p.eval₂ (Polynomial.evalRingHom z.1) z.2) :=
  (AlgebraicBranchLimit.continuous_value p).comp (continuous_snd.prodMk continuous_fst)

/-- A nonzero value annihilator has only finitely many excluded parameters. -/
theorem finite_exceptional (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0) :
    {t : ℝ | p.trailingCoeff.eval t = 0}.Finite :=
  Polynomial.finite_setOfPred_isRoot (Polynomial.trailingCoeff_ne_zero.mpr hp)

variable {X : Type*} [TopologicalSpace X]

/-- The trailing coefficient is a parameter polynomial. Its nonvanishing
prevents a nonzero test value from approaching zero along the root set. -/
theorem isClopen_zeroSet (p : Polynomial (Polynomial ℝ)) (r f : X → ℝ)
    (hr : Continuous r) (hf : Continuous f)
    (hroot : ∀ x, p.eval₂ (Polynomial.evalRingHom (r x)) (f x) = 0)
    (htrail : ∀ x, p.trailingCoeff.eval (r x) ≠ 0) :
    IsClopen {x | f x = 0} := by
  obtain ⟨q, hq, hq0⟩ := LeanCanny.Algebra.InfinitesimalSign.factor_at_trailingDegree p
  have hfactor (x : X) : f x ^ p.natTrailingDegree *
      q.eval₂ (Polynomial.evalRingHom (r x)) (f x) = 0 := by
    have H := hroot x
    rw [hq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at H
    exact H
  have hcont : Continuous (fun x => q.eval₂ (Polynomial.evalRingHom (r x)) (f x)) :=
    (continuous_evaluation q).comp (hr.prodMk hf)
  refine ⟨isClosed_eq hf continuous_const, isOpen_iff_mem_nhds.mpr ?_⟩
  intro x hx
  change f x = 0 at hx
  have hqnonzero : q.eval₂ (Polynomial.evalRingHom (r x)) (f x) ≠ 0 := by
    simpa only [hx, Polynomial.eval₂_at_zero, hq0, Polynomial.coe_evalRingHom] using htrail x
  have hne := (isOpen_ne.preimage hcont).mem_nhds hqnonzero
  apply Filter.mem_of_superset hne
  intro y hy
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp (hfactor y)).resolve_right hy)

variable [PreconnectedSpace X]

theorem zero_iff (p : Polynomial (Polynomial ℝ)) (r f : X → ℝ)
    (hr : Continuous r) (hf : Continuous f)
    (hroot : ∀ x, p.eval₂ (Polynomial.evalRingHom (r x)) (f x) = 0)
    (htrail : ∀ x, p.trailingCoeff.eval (r x) ≠ 0) (x y : X) :
    f x = 0 ↔ f y = 0 := by
  have hc := isClopen_zeroSet p r f hr hf hroot htrail
  constructor
  · intro hx
    have H : y ∈ {x | f x = 0} := by rw [hc.eq_univ ⟨x, hx⟩]; trivial
    exact H
  · intro hy
    have H : x ∈ {x | f x = 0} := by rw [hc.eq_univ ⟨y, hy⟩]; trivial
    exact H

end LeanCanny.Geometry.AlgebraicBranchZero
