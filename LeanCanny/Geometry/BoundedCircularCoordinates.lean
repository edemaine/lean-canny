/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakBooleanWitness
/-! # Bounded circular coordinates with a slack circle

The sum of the two squared radii is fixed. A satisfied weak atom is retained
along a path to the canonical coordinates; inactive atoms impose no constraint.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedCircularCoordinates
open CircularWitness WeakBooleanWitness Set
open scoped Classical
abbrev Pair := Plane × Plane
noncomputable def center (B a : ℝ) : Pair := (canonical a,canonical (B-max a 0))

theorem canonical_sq (a : ℝ) : ‖canonical a‖^2=max a 0 := by
  rw [canonical_norm,Real.sq_sqrt (le_max_right a 0)]

theorem center_sum (B a : ℝ) (h : max a 0 ≤ B) :
    ‖(center B a).1‖^2+‖(center B a).2‖^2=B := by
  simp only [center,canonical_sq,max_eq_left (sub_nonneg.mpr h)]
  ring

theorem center_atom (B a : ℝ) : a=‖(center B a).1‖^2 ↔ 0≤a := canonical_equation a

theorem continuous_center {X : Type*} [TopologicalSpace X] (B a : X → ℝ)
    (hB : Continuous B) (ha : Continuous a) : Continuous (fun x => center (B x) (a x)) := by
  exact (((ha.max continuous_const).sqrt.smul continuous_const).prodMk
    ((((hB.sub (ha.max continuous_const)).max continuous_const).sqrt).smul continuous_const))

theorem coordinate_joined (B a : ℝ) (p : Pair)
    (hB : ‖p.1‖^2+‖p.2‖^2=B) (ha : max a 0 ≤ B) :
    JoinedIn {q : Pair | ‖q.1‖^2+‖q.2‖^2=B ∧ (a=‖p.1‖^2 → a=‖q.1‖^2)}
      p (center B a) := by
  obtain ⟨γ,hγ⟩ := coordinate_path (‖p.1‖^2) p.1
  obtain ⟨δ,hδ⟩ := coordinate_path (‖p.2‖^2) p.2
  have Hfirst : JoinedIn {q : Pair | ‖q.1‖^2+‖q.2‖^2=B ∧ (a=‖p.1‖^2 → a=‖q.1‖^2)}
      p (canonical (‖p.1‖^2),canonical (‖p.2‖^2)) := by
    refine ⟨γ.prod δ,fun t => ?_⟩
    change ‖γ t‖^2+‖δ t‖^2=B ∧ (a=‖p.1‖^2 → a=‖γ t‖^2)
    rw [← hγ t rfl,← hδ t rfl]
    exact ⟨hB,id⟩
  let r : unitInterval → ℝ := fun t => (1-(t : ℝ))*‖p.1‖^2+(t : ℝ)*max a 0
  have hr0 (t : unitInterval) : 0≤r t :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (sq_nonneg _))
      (mul_nonneg t.property.1 (le_max_right a 0))
  have hrB (t : unitInterval) : r t≤B := by
    have H := mul_nonneg (sub_nonneg.mpr t.property.2) (sq_nonneg ‖p.2‖)
    have H' := mul_nonneg t.property.1 (sub_nonneg.mpr ha)
    rw [← hB] at H' ⊢
    dsimp [r]
    nlinarith
  let η : Path (canonical (‖p.1‖^2),canonical (‖p.2‖^2)) (center B a) :=
    { toFun := fun t => (canonical (r t),canonical (B-r t))
      continuous_toFun := by
        have HR : Continuous r := ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
          (continuous_subtype_val.mul continuous_const)
        exact ((HR.max continuous_const).sqrt.smul continuous_const).prodMk
          ((((continuous_const.sub HR).max continuous_const).sqrt).smul continuous_const)
      source' := by
        simp only [r, Set.Icc.coe_zero,sub_zero,one_mul,zero_mul,add_zero]
        rw [← hB]
        congr 2
        ring
      target' := by simp [r,center,canonical] }
  apply Hfirst.trans
  refine ⟨η,fun t => ?_⟩
  change ‖canonical (r t)‖^2+‖canonical (B-r t)‖^2=B ∧ _
  rw [canonical_sq,canonical_sq,max_eq_left (hr0 t),max_eq_left (sub_nonneg.mpr (hrB t))]
  refine ⟨by ring,fun H => ?_⟩
  have HN : 0≤a := H ▸ sq_nonneg _
  change a=‖canonical (r t)‖^2
  rw [canonical_sq,max_eq_left (hr0 t)]
  dsimp [r]
  rw [← H,max_eq_left HN]
  ring

end LeanCanny.Geometry.BoundedCircularCoordinates
