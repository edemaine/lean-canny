/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ConnectedWitnessProjection
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-! # Circular fibers preserve paths and connectedness, including radius zero -/
@[expose] public section
namespace LeanCanny.Geometry.CircularWitness
open Set Metric
open scoped Classical
variable {X : Type*} [TopologicalSpace X]
abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev Space (ρ : X → ℝ) := {z : X × Plane // ‖z.2‖ = ρ z.1}

def projection (ρ : X → ℝ) (z : Space ρ) : X := z.val.1

noncomputable def unit : Plane := PiLp.single 2 0 1

theorem unit_norm : ‖unit‖ = 1 := by simp [unit,PiLp.norm_single]

noncomputable def centerSection (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (x : X) : Space ρ :=
  ⟨(x,ρ x • unit),by simp [norm_smul,unit_norm,Real.norm_eq_abs,abs_of_nonneg (hρ x)]⟩

theorem continuous_projection (ρ : X → ℝ) : Continuous (projection ρ) := continuous_fst.comp continuous_subtype_val

theorem continuous_section (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (Hρ : Continuous ρ) :
    Continuous (centerSection ρ hρ) :=
  (continuous_id.prodMk (Hρ.smul continuous_const)).subtype_mk _

theorem fiber_joined (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (z : Space ρ) :
    JoinedIn univ z (centerSection ρ hρ (projection ρ z)) := by
  have Hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have HC := isPathConnected_sphere Hrank (0 : Plane) (hρ z.val.1)
  have Hleft : z.val.2 ∈ sphere (0 : Plane) (ρ z.val.1) := by simpa using z.property
  have Hright : ρ z.val.1 • unit ∈ sphere (0 : Plane) (ρ z.val.1) := by
    simp [norm_smul,unit_norm,Real.norm_eq_abs,abs_of_nonneg (hρ z.val.1)]
  let lift : sphere (0 : Plane) (ρ z.val.1) → Space ρ := fun w =>
    ⟨(z.val.1,w.val),by simpa only [Metric.mem_sphere,dist_zero_right] using w.property⟩
  have HL : Continuous lift := (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have HJ : JoinedIn univ (⟨z.val.2,Hleft⟩ : sphere (0 : Plane) (ρ z.val.1)) ⟨ρ z.val.1 • unit,Hright⟩ :=
    joinedIn_univ.mpr ((joinedIn_iff_joined Hleft Hright).mp (HC.joinedIn _ Hleft _ Hright))
  exact ((HJ.map HL.continuousOn).mono (subset_univ _))

theorem joined_iff (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (Hρ : Continuous ρ) (y z : Space ρ) :
    JoinedIn univ y z ↔ JoinedIn univ (projection ρ y) (projection ρ z) :=
  ConnectedWitnessProjection.joined_iff (projection ρ) (centerSection ρ hρ) (continuous_projection ρ)
    (continuous_section ρ hρ Hρ) (fiber_joined ρ hρ) y z

theorem preconnected_iff (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (Hρ : Continuous ρ) :
    IsPreconnected (univ : Set (Space ρ)) ↔ IsPreconnected (univ : Set X) :=
  ConnectedWitnessProjection.preconnected_iff (projection ρ) (centerSection ρ hρ) (continuous_projection ρ)
    (continuous_section ρ hρ Hρ) (fun _ => rfl) (fiber_joined ρ hρ)

end LeanCanny.Geometry.CircularWitness
