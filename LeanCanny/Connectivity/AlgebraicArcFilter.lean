/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AlgebraicBranchZero
public import LeanCanny.Geometry.PolynomialGridValues
public import LeanCanny.Connectivity.AccessibleArc

/-! # Filtering algebraic arcs at one indexing fiber

Coordinate root grids may contain points outside the original equation set.
An annihilator for each equation value, with nonvanishing trailing coefficient
on the open interval, makes its zero test constant along every branch.
Testing the original equations in one fiber then selects complete original
arcs, whose endpoints also satisfy the original equations.

The value annihilators and their nonvanishing interval are explicit inputs.
This module does not construct those certificates or their native readers.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicArcFilter
open Set Geometry
variable {E J κ : Type*} [TopologicalSpace E]

/-- A retained label is tested against the original equations at the anchor. -/
def Label (f : ℝ × E → κ → ℝ) (curve : J → ℝ → E) (t₀ : ℝ) :=
  {j : J // f (t₀, curve j t₀) = 0}

theorem root_iff_anchor (f : ℝ × E → κ → ℝ) (hcont : Continuous f)
    (a b : ℝ) (t₀ t : Ioo a b) (curve : ℝ → E) (hc : ContinuousOn curve (Icc a b))
    (p : κ → Polynomial (Polynomial ℝ))
    (hrel : ∀ k s, s ∈ Ioo a b →
      (p k).eval₂ (Polynomial.evalRingHom s) (f (s, curve s) k) = 0)
    (htrail : ∀ k s, s ∈ Ioo a b → (p k).trailingCoeff.eval s ≠ 0) :
    f (t.val, curve t.val) = 0 ↔ f (t₀.val, curve t₀.val) = 0 := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hcurve : Continuous (fun s : Ioo a b => (s.val, curve s.val)) :=
    continuous_subtype_val.prodMk
      (continuousOn_iff_continuous_domRestrict.mp (hc.mono Ioo_subset_Icc_self))
  have hz (k : κ) : f (t.val, curve t.val) k = 0 ↔ f (t₀.val, curve t₀.val) k = 0 :=
    AlgebraicBranchZero.zero_iff (p k) Subtype.val (fun s : Ioo a b => f (s.val, curve s.val) k)
      continuous_subtype_val ((continuous_apply k).comp (hcont.comp hcurve))
      (fun s => hrel k s.val s.property) (fun s => htrail k s.val s.property) t t₀
  constructor <;> intro h <;> funext k
  · exact (hz k).mp (congrFun h k)
  · exact (hz k).mpr (congrFun h k)

variable [T2Space E]

/-- Restricting labels by the original equations gives complete disjoint
interior arcs and preserves their actual original endpoint roots. The labels
are finite whenever the supplied branch labels are finite. -/
theorem filtered_arcs (f : ℝ × E → κ → ℝ) (hcont : Continuous f)
    (a b : ℝ) (t₀ : Ioo a b) (curve : J → ℝ → E)
    (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
    (hcomplete : ∀ t : Ioo a b, ∀ x, f (t.val, x) = 0 → ∃! j, curve j t.val = x)
    (p : κ → Polynomial (Polynomial ℝ))
    (hrel : ∀ j k t, t ∈ Ioo a b →
      (p k).eval₂ (Polynomial.evalRingHom t) (f (t, curve j t) k) = 0)
    (htrail : ∀ k t, t ∈ Ioo a b → (p k).trailingCoeff.eval t ≠ 0) :
    (∀ j : Label f curve t₀.val, ContinuousOn (curve j.val) (Icc a b)) ∧
    (∀ (j : Label f curve t₀.val) t, t ∈ Icc a b → f (t, curve j.val t) = 0) ∧
    (∀ t : Ioo a b, ∀ x, f (t.val, x) = 0 ↔
      ∃! j : Label f curve t₀.val, curve j.val t.val = x) ∧
    ∀ j : Label f curve t₀.val,
      FrontierCover.Accessible ((fun t => (t, curve j.val t)) '' Ioo a b) := by
  have hab : a < b := t₀.property.1.trans t₀.property.2
  have hroot (j : Label f curve t₀.val) (t : ℝ) (ht : t ∈ Ioo a b) :
      f (t, curve j.val t) = 0 :=
    (root_iff_anchor f hcont a b t₀ ⟨t, ht⟩ (curve j.val) (hc j.val) p (hrel j.val) htrail).mpr j.property
  have hfull (j : Label f curve t₀.val) (t : ℝ) (ht : t ∈ Icc a b) :
      f (t, curve j.val t) = 0 := by
    have hclosed : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have hcontinuous : ContinuousWithinAt (fun s => f (s, curve j.val s)) (Ioo a b) t :=
      hcont.continuousAt.comp_continuousWithinAt
        ((continuousWithinAt_id.prodMk (hc j.val t ht)).mono Ioo_subset_Icc_self)
    exact hcontinuous.eq_const_of_mem_closure hclosed (hroot j)
  refine ⟨(fun j => hc j.val), hfull, ?_, ?_⟩
  · intro t x
    constructor
    · intro hx
      obtain ⟨j, hj, huniq⟩ := hcomplete t x hx
      have hanchor : f (t₀.val, curve j t₀.val) = 0 :=
        (root_iff_anchor f hcont a b t₀ t (curve j) (hc j) p (hrel j) htrail).mp (hj ▸ hx)
      refine ⟨⟨j, hanchor⟩, hj, ?_⟩
      intro k hk
      exact Subtype.ext (huniq k.val hk)
    · rintro ⟨j, hj, _⟩
      rw [← hj]
      exact hroot j t.val t.property
  · intro j
    exact FrontierCover.accessible_open_arc (continuous_id.continuousOn.prodMk (hc j.val))

end LeanCanny.Connectivity.AlgebraicArcFilter
