/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CircularWitness
public import Mathlib.Analysis.Real.Sqrt
/-! # Boundary-aware connected witnesses for positive Boolean combinations of weak inequalities

Each weak atom fᵢ(x)≥0 is replaced by fᵢ(x)=uᵢ²+vᵢ². Its canonical
witness √max(fᵢ(x),0) is continuous on the whole ambient space. All active
clauses therefore share the same witness, including at their boundaries.
No selector variable or disjoint-union interpretation of OR is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.WeakBooleanWitness
open Set CircularWitness Metric
open scoped Classical
variable {X I : Type*} [TopologicalSpace X]

noncomputable def canonical (a : ℝ) : Plane := Real.sqrt (max a 0) • unit

theorem canonical_norm (a : ℝ) : ‖canonical a‖ = Real.sqrt (max a 0) := by
  simp [canonical,norm_smul,unit_norm,Real.norm_eq_abs]

theorem canonical_equation (a : ℝ) : a=‖canonical a‖^2 ↔ 0≤a := by
  rw [canonical_norm,Real.sq_sqrt (le_max_right a 0)]
  constructor
  · intro H
    rw [H]
    exact le_max_right _ _
  · intro H
    exact (max_eq_left H).symm

theorem coordinate_path (a : ℝ) (w : Plane) :
    ∃ γ : Path w (canonical a), ∀ t, a=‖w‖^2 → a=‖γ t‖^2 := by
  by_cases HA : a=‖w‖^2
  · have Hnonneg : 0≤a := HA ▸ sq_nonneg ‖w‖
    have Hrank : 1 < Module.rank ℝ Plane := by rw [← Module.finrank_eq_rank]; norm_num
    have HC := isPathConnected_sphere Hrank (0 : Plane) (Real.sqrt_nonneg a)
    have HW : w ∈ sphere (0 : Plane) (Real.sqrt a) := by
      simp only [mem_sphere,dist_zero_right]
      rw [HA,Real.sqrt_sq (norm_nonneg w)]
    have HT : canonical a ∈ sphere (0 : Plane) (Real.sqrt a) := by
      simp only [mem_sphere,dist_zero_right,canonical_norm,max_eq_left Hnonneg]
    obtain ⟨γ,Hγ⟩ := HC.joinedIn w HW (canonical a) HT
    refine ⟨γ,fun t _ => ?_⟩
    have HN : ‖γ t‖ = Real.sqrt a := by simpa only [mem_sphere,dist_zero_right] using Hγ t
    rw [HN,Real.sq_sqrt Hnonneg]
  · exact ⟨(PathConnectedSpace.joined w (canonical a)).somePath,fun _ H => (HA H).elim⟩

abbrev Base (f : I → X → ℝ) (P : (I → Prop) → Prop) := {x : X // P (fun i => 0≤f i x)}
abbrev Space (f : I → X → ℝ) (P : (I → Prop) → Prop) :=
  {z : X × (I → Plane) // P (fun i => f i z.1=‖z.2 i‖^2)}

variable (f : I → X → ℝ) (P : (I → Prop) → Prop)
  (HM : ∀ a b : I → Prop, (∀ i, a i → b i) → P a → P b)

def projection (z : Space f P) : Base f P :=
  ⟨z.val.1,HM (fun i => f i z.val.1=‖z.val.2 i‖^2) (fun i => 0≤f i z.val.1)
    (fun i H => by rw [H]; exact sq_nonneg ‖z.val.2 i‖) z.property⟩

noncomputable def centerSection (x : Base f P) : Space f P :=
  ⟨(x.val,fun i => canonical (f i x.val)),HM (fun i => 0≤f i x.val)
    (fun i => f i x.val=‖canonical (f i x.val)‖^2)
    (fun i H => (canonical_equation (f i x.val)).mpr H) x.property⟩

theorem continuous_projection : Continuous (projection f P HM) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem continuous_section (hf : ∀ i, Continuous (f i)) : Continuous (centerSection f P HM) := by
  have HC (i : I) : Continuous (fun x : Base f P => canonical (f i x.val)) :=
    (((hf i).comp continuous_subtype_val).max continuous_const).sqrt.smul continuous_const
  exact (continuous_subtype_val.prodMk (continuous_pi HC)).subtype_mk _

theorem fiber_joined (z : Space f P) : JoinedIn univ z (centerSection f P HM (projection f P HM z)) := by
  choose γ Hγ using (fun i => coordinate_path (f i z.val.1) (z.val.2 i))
  let path : Path z (centerSection f P HM (projection f P HM z)) :=
    { toFun := fun t => ⟨(z.val.1,fun i => γ i t),HM _ _ (fun i H => Hγ i t H) z.property⟩
      continuous_toFun := (continuous_const.prodMk (continuous_pi (fun i => (γ i).continuous))).subtype_mk _
      source' := by
        apply Subtype.ext
        change (z.val.1,fun i => γ i 0) = (z.val.1,z.val.2)
        apply Prod.ext
        · rfl
        · funext i; exact (γ i).source
      target' := by
        apply Subtype.ext
        change (z.val.1,fun i => γ i 1) = (z.val.1,fun i => canonical (f i z.val.1))
        apply Prod.ext
        · rfl
        · funext i; exact (γ i).target }
  exact ⟨path,fun _ => mem_univ _⟩

theorem joined_iff (hf : ∀ i, Continuous (f i)) (y z : Space f P) :
    JoinedIn univ y z ↔ JoinedIn univ (projection f P HM y) (projection f P HM z) :=
  ConnectedWitnessProjection.joined_iff (projection f P HM) (centerSection f P HM)
    (continuous_projection f P HM) (continuous_section f P HM hf) (fiber_joined f P HM) y z

include HM in
theorem preconnected_iff (hf : ∀ i, Continuous (f i)) :
    IsPreconnected (univ : Set (Space f P)) ↔ IsPreconnected (univ : Set (Base f P)) :=
  ConnectedWitnessProjection.preconnected_iff (projection f P HM) (centerSection f P HM)
    (continuous_projection f P HM) (continuous_section f P HM hf) (fun _ => rfl) (fiber_joined f P HM)

end LeanCanny.Geometry.WeakBooleanWitness
