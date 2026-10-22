/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ActiveExtremum
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Separation.Basic

/-! # Finite critical sets make local maxima strict

A point tied with a local maximum in a sufficiently small neighborhood is
itself a local maximum. Isolation among local maxima therefore implies
strictness. On a regular smooth fiber, normalized Lagrange multipliers put
every local maximum in the critical set, so finiteness of that set suffices.
-/

@[expose] public section

namespace LeanCanny.Geometry.IsolatedCriticalMaximum
open Set Filter
open scoped Topology

section Topology
variable {X : Type*} [TopologicalSpace X]

theorem strict_of_isolated_local_maxima (φ : X → ℝ) (S : Set X) (p : X)
    (hmax : IsLocalMaxOn φ S p)
    (hisolated : ∀ᶠ x in nhds p, x ∈ S → IsLocalMaxOn φ S x → x = p) :
    ∀ᶠ x in nhds p, x ∈ S → x ≠ p → φ x < φ p := by
  have hbound : ∀ᶠ x in nhds p, x ∈ S → φ x ≤ φ p := eventually_nhdsWithin_iff.mp hmax
  have hnear := eventually_eventually_nhds.mpr hbound
  filter_upwards [hbound, hnear, hisolated] with x hx hnearx hiso hxS hne
  apply lt_of_le_of_ne (hx hxS)
  intro heq
  have hmaxx : IsLocalMaxOn φ S x := eventually_nhdsWithin_iff.mpr (by
    filter_upwards [hnearx] with y hy hyS
    rw [heq]
    exact hy hyS)
  exact hne (hiso hxS hmaxx)

theorem strict_of_finite_candidates [T1Space X] (φ : X → ℝ) (S C : Set X) (p : X)
    (hmax : IsLocalMaxOn φ S p) (hC : C.Finite)
    (hcandidate : ∀ᶠ x in nhds p, x ∈ S → IsLocalMaxOn φ S x → x ∈ C) :
    ∀ᶠ x in nhds p, x ∈ S → x ≠ p → φ x < φ p := by
  have havoid : ∀ᶠ x in nhds p, x ∉ C \ {p} :=
    hC.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  apply strict_of_isolated_local_maxima φ S p hmax
  filter_upwards [havoid, hcandidate] with x hx hc hxS hxmax
  by_contra hne
  exact hx ⟨hc hxS hxmax, hne⟩

end Topology

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def NormalizedCritical (f : E → F) (L : E →L[ℝ] ℝ) (x : E) : Prop :=
  ∃ Λ : Module.Dual ℝ F, ∀ h, L h = Λ (fderiv ℝ f x h)

def criticalFiber (f : E → F) (L : E →L[ℝ] ℝ) (c : F) : Set E :=
  {x | f x = c ∧ NormalizedCritical f L x}

theorem strict_of_finite_critical (f : E → F) (L : E →L[ℝ] ℝ) (p : E)
    (hf : ContDiff ℝ ⊤ f)
    (hregular : ∀ x, f x = f p → Function.Surjective (fderiv ℝ f x))
    (hfinite : (criticalFiber f L (f p)).Finite)
    (hmax : IsLocalMaxOn L {x | f x = f p} p) :
    ∀ᶠ x in nhds p, f x = f p → x ≠ p → L x < L p := by
  apply strict_of_finite_candidates L {x | f x = f p} (criticalFiber f L (f p)) p hmax hfinite
  refine Eventually.of_forall (fun x hx hm => ⟨hx, ?_⟩)
  apply ActiveExtremum.exists_normalized f L x _ L ?_
    (hf.hasStrictFDerivAt (by simp)) L.hasStrictFDerivAt (hregular x hx)
  rw [hx]
  exact hm

end Calculus
end LeanCanny.Geometry.IsolatedCriticalMaximum
