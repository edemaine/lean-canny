/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedCircularCoordinates
/-! # Positive Boolean weak witnesses with bounded slack coordinates -/
@[expose] public section
namespace LeanCanny.Geometry.BoundedWeakBooleanWitness
open CircularWitness BoundedCircularCoordinates Set
open scoped Classical
variable {X I : Type*} [TopologicalSpace X]
abbrev Base (f : I → X → ℝ) (P : (I → Prop) → Prop) := WeakBooleanWitness.Base f P
abbrev Space (B : X → ℝ) (f : I → X → ℝ) (P : (I → Prop) → Prop) :=
  {z : X × (I → Pair) // (∀ i, ‖(z.2 i).1‖^2+‖(z.2 i).2‖^2=B z.1) ∧
    P (fun i => f i z.1=‖(z.2 i).1‖^2)}
variable (B : X → ℝ) (f : I → X → ℝ) (P : (I → Prop) → Prop)
  (HM : ∀ a b : I → Prop, (∀ i, a i → b i) → P a → P b)
  (HB : ∀ x i, max (f i x) 0 ≤ B x)

def projection (z : Space B f P) : Base f P :=
  ⟨z.val.1,HM _ _ (fun i H => by rw [H]; exact sq_nonneg _) z.property.2⟩

noncomputable def centerSection (x : Base f P) : Space B f P :=
  ⟨(x.val,fun i => center (B x.val) (f i x.val)),
    ⟨fun i => center_sum _ _ (HB x.val i),
      HM _ _ (fun _i H => (center_atom _ _).mpr H) x.property⟩⟩

theorem continuous_projection : Continuous (projection B f P HM) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem continuous_section (hB : Continuous B) (hf : ∀ i, Continuous (f i)) :
    Continuous (centerSection B f P HM HB) :=
  (continuous_subtype_val.prodMk (continuous_pi (fun i =>
    (continuous_center B (f i) hB (hf i)).comp continuous_subtype_val))).subtype_mk _

theorem fiber_joined (z : Space B f P) :
    JoinedIn univ z (centerSection B f P HM HB (projection B f P HM z)) := by
  choose γ hγ using fun i => coordinate_joined (B z.val.1) (f i z.val.1) (z.val.2 i)
    (z.property.1 i) (HB z.val.1 i)
  let path : Path z (centerSection B f P HM HB (projection B f P HM z)) :=
    { toFun := fun t => ⟨(z.val.1,fun i => γ i t),
        ⟨fun i => (hγ i t).1,HM _ _ (fun i H => (hγ i t).2 H) z.property.2⟩⟩
      continuous_toFun := (continuous_const.prodMk (continuous_pi (fun i =>
        (γ i).continuous))).subtype_mk _
      source' := by
        apply Subtype.ext
        change (z.val.1,fun i => γ i 0) = (z.val.1,z.val.2)
        apply Prod.ext
        · rfl
        · funext i; exact (γ i).source
      target' := by
        apply Subtype.ext
        change (z.val.1,fun i => γ i 1) = (z.val.1,fun i => center (B z.val.1) (f i z.val.1))
        apply Prod.ext
        · rfl
        · funext i; exact (γ i).target }
  exact ⟨path,fun _ => mem_univ _⟩

include HB in
theorem joined_iff (hB : Continuous B) (hf : ∀ i, Continuous (f i)) (y z : Space B f P) :
    JoinedIn univ y z ↔ JoinedIn univ (projection B f P HM y) (projection B f P HM z) :=
  ConnectedWitnessProjection.joined_iff (projection B f P HM) (centerSection B f P HM HB)
    (continuous_projection B f P HM) (continuous_section B f P HM HB hB hf)
    (fiber_joined B f P HM HB) y z

include HM HB in
theorem preconnected_iff (hB : Continuous B) (hf : ∀ i, Continuous (f i)) :
    IsPreconnected (univ : Set (Space B f P)) ↔ IsPreconnected (univ : Set (Base f P)) :=
  ConnectedWitnessProjection.preconnected_iff (projection B f P HM) (centerSection B f P HM HB)
    (continuous_projection B f P HM) (continuous_section B f P HM HB hB hf)
    (fun _ => rfl) (fiber_joined B f P HM HB)

end LeanCanny.Geometry.BoundedWeakBooleanWitness
