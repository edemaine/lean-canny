/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootBranches
public import LeanCanny.Geometry.AlgebraicBranchSign

/-! # Persistent equality and order of scalar root branches

Uniqueness of covering lifts makes equality of two continuous root curves
independent of the parameter. For scalar roots, continuity then makes their
strict order independent of the parameter as well. The curves may come from
different grid labels; distinctness of the labels is not assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.RootBranches
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem curves_eq_of_anchor (H : ℝ × E → F) {a b : ℝ}
    (hcover : IsCoveringMap (projection H a b)) (f g : C(Ioo a b, E))
    (hf : ∀ t, H (t.val, f t) = 0) (hg : ∀ t, H (t.val, g t) = 0)
    (t₀ : Ioo a b) (he : f t₀ = g t₀) : f = g := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  let lf : Ioo a b → IntervalSpace H a b := fun t => ⟨⟨(t.val, f t), hf t⟩, t.property⟩
  let lg : Ioo a b → IntervalSpace H a b := fun t => ⟨⟨(t.val, g t), hg t⟩, t.property⟩
  have hlf : Continuous lf :=
    ((continuous_subtype_val.prodMk f.continuous).subtype_mk hf).subtype_mk (fun t => t.property)
  have hlg : Continuous lg :=
    ((continuous_subtype_val.prodMk g.continuous).subtype_mk hg).subtype_mk (fun t => t.property)
  have hstart : lf t₀ = lg t₀ := Subtype.ext (Subtype.ext (Prod.ext rfl he))
  have hl := hcover.eq_of_comp_eq hlf hlg rfl t₀ hstart
  apply ContinuousMap.ext
  intro t
  exact congrArg (fun z : IntervalSpace H a b => z.val.val.2) (congrFun hl t)

theorem curves_eq_iff (H : ℝ × E → F) {a b : ℝ}
    (hcover : IsCoveringMap (projection H a b)) (f g : C(Ioo a b, E))
    (hf : ∀ t, H (t.val, f t) = 0) (hg : ∀ t, H (t.val, g t) = 0)
    (s t : Ioo a b) : f s = g s ↔ f t = g t := by
  constructor <;> intro he
  · exact congrArg (fun h : C(Ioo a b, E) => h t) (curves_eq_of_anchor H hcover f g hf hg s he)
  · exact congrArg (fun h : C(Ioo a b, E) => h s) (curves_eq_of_anchor H hcover f g hf hg t he)

theorem scalar_order_iff (H : ℝ × (Fin 1 → ℝ) → F) {a b : ℝ}
    (hcover : IsCoveringMap (projection H a b)) (f g : C(Ioo a b, Fin 1 → ℝ))
    (hf : ∀ t, H (t.val, f t) = 0) (hg : ∀ t, H (t.val, g t) = 0)
    (s t : Ioo a b) : f s 0 < g s 0 ↔ f t 0 < g t 0 := by
  classical
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  by_cases he : f = g
  · subst g
    simp
  · have hne (u : Ioo a b) : f u 0 ≠ g u 0 := by
      intro hu
      apply he
      apply curves_eq_of_anchor H hcover f g hf hg u
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hu
    exact AlgebraicBranchSign.order_iff (fun u => f u 0) (fun u => g u 0)
      ((continuous_apply 0).comp f.continuous) ((continuous_apply 0).comp g.continuous) hne s t

/-- Full grid branches may share a coordinate. For each coordinate, both
equality and strict order persist once its scalar root projection is a covering. -/
theorem coordinate_comparison_iff {ι : Type*} (H : ℝ × (Fin 1 → ℝ) → F) {a b : ℝ}
    (hcover : IsCoveringMap (projection H a b)) (f g : C(Ioo a b, ι → ℝ)) (i : ι)
    (hf : ∀ t, H (t.val, fun _ => f t i) = 0) (hg : ∀ t, H (t.val, fun _ => g t i) = 0)
    (s t : Ioo a b) :
    (f s i = g s i ↔ f t i = g t i) ∧ (f s i < g s i ↔ f t i < g t i) := by
  let fi : C(Ioo a b, Fin 1 → ℝ) :=
    ⟨fun u _ => f u i, continuous_pi (fun _ => (continuous_apply i).comp f.continuous)⟩
  let gi : C(Ioo a b, Fin 1 → ℝ) :=
    ⟨fun u _ => g u i, continuous_pi (fun _ => (continuous_apply i).comp g.continuous)⟩
  have he := curves_eq_iff H hcover fi gi hf hg s t
  constructor
  · constructor <;> intro h
    · have hfg : fi s = gi s := funext (fun _ => h)
      exact congrFun (he.mp hfg) 0
    · have hfg : fi t = gi t := funext (fun _ => h)
      exact congrFun (he.mpr hfg) 0
  · exact scalar_order_iff H hcover fi gi hf hg s t

end LeanCanny.Geometry.RootBranches
