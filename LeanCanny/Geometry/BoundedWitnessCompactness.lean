/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedWitnessBudget
public import LeanCanny.Geometry.FiniteMonotoneClosed
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
/-! # Properness of bounded slack-circle projections over closed Boolean witnesses -/
@[expose] public section
namespace LeanCanny.Geometry.BoundedWeakBooleanWitness
open CircularWitness BoundedCircularCoordinates Set Metric
open scoped Classical
variable {X I : Type*} [TopologicalSpace X] [T2Space X]

theorem compact_circles (B : X → ℝ) (hB : Continuous B) (K : Set X) (hK : IsCompact K) :
    IsCompact {z : X × (I → Pair) | z.1 ∈ K ∧ ∀ i, ‖(z.2 i).1‖^2+‖(z.2 i).2‖^2=B z.1} := by
  obtain ⟨R,hR⟩ := hK.bddAbove_image hB.continuousOn
  let ball := closedBall (0 : Plane) (Real.sqrt (max R 0))
  have HC : IsCompact (univ.pi (fun _ : I => ball ×ˢ ball)) :=
    isCompact_univ_pi (fun _ => (isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  apply (hK.prod HC).of_isClosed_subset
  · rw [ofPred_and,ofPred_forall]
    apply IsClosed.inter (hK.isClosed.preimage continuous_fst)
    apply isClosed_iInter
    intro i
    exact isClosed_eq
      (((continuous_fst.comp ((continuous_apply i).comp continuous_snd)).norm.pow 2).add
        ((continuous_snd.comp ((continuous_apply i).comp continuous_snd)).norm.pow 2))
      (hB.comp continuous_fst)
  · intro z hz
    refine ⟨hz.1,fun i _ => ?_⟩
    have HR : B z.1≤max R 0 := (hR (mem_image_of_mem B hz.1)).trans (le_max_left _ _)
    have H1 : ‖(z.2 i).1‖≤Real.sqrt (max R 0) := by
      nlinarith [hz.2 i,sq_nonneg ‖(z.2 i).2‖,norm_nonneg (z.2 i).1,
        Real.sqrt_nonneg (max R 0),Real.sq_sqrt (le_max_right R 0)]
    have H2 : ‖(z.2 i).2‖≤Real.sqrt (max R 0) := by
      nlinarith [hz.2 i,sq_nonneg ‖(z.2 i).1‖,norm_nonneg (z.2 i).2,
        Real.sqrt_nonneg (max R 0),Real.sq_sqrt (le_max_right R 0)]
    exact ⟨by simpa only [ball,mem_closedBall,dist_zero_right] using H1,
      by simpa only [ball,mem_closedBall,dist_zero_right] using H2⟩

theorem compact_space_over (B : X → ℝ) (f : I → X → ℝ) (P : (I → Prop) → Prop)
    (hB : Continuous B)
    (hP : IsClosed {z : X × (I → Pair) | P (fun i => f i z.1=‖(z.2 i).1‖^2)})
    (K : Set X) (hK : IsCompact K) :
    IsCompact {z : Space B f P | z.val.1 ∈ K} := by
  rw [Subtype.isCompact_iff]
  have HE : (Subtype.val '' {z : Space B f P | z.val.1 ∈ K}) =
      {z : X × (I → Pair) | z.1 ∈ K ∧ ∀ i, ‖(z.2 i).1‖^2+‖(z.2 i).2‖^2=B z.1} ∩
      {z | P (fun i => f i z.1=‖(z.2 i).1‖^2)} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨hw,w.property.1⟩,w.property.2⟩
    · rintro ⟨⟨hK',hB'⟩,hP'⟩
      exact ⟨⟨z,⟨hB',hP'⟩⟩,hK',rfl⟩
  rw [HE]
  exact (compact_circles B hB K hK).inter_right hP

theorem proper_projection [FirstCountableTopology X] (B : X → ℝ) (f : I → X → ℝ) (P : (I → Prop) → Prop)
    (HM : ∀ a b : I → Prop, (∀ i, a i → b i) → P a → P b)
    (hB : Continuous B)
    (hP : IsClosed {z : X × (I → Pair) | P (fun i => f i z.1=‖(z.2 i).1‖^2)}) :
    IsProperMap (projection B f P HM) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_projection B f P HM,?_⟩
  intro K hK
  have HK := hK.image (continuous_subtype_val : Continuous (Subtype.val : Base f P → X))
  apply (compact_space_over B f P hB hP _ HK).of_isClosed_subset
    (hK.isClosed.preimage (continuous_projection B f P HM))
  intro z hz
  exact ⟨projection B f P HM z,hz,rfl⟩

theorem proper_budget_projection [FirstCountableTopology X] [Fintype I]
    (f : I → X → ℝ) (P : (I → Prop) → Prop)
    (HM : ∀ a b : I → Prop, (∀ i, a i → b i) → P a → P b)
    (hf : ∀ i, Continuous (f i)) :
    IsProperMap (projection (budget f) f P HM) := by
  apply proper_projection (budget f) f P HM (continuous_budget f hf)
  exact FiniteMonotoneClosed.isClosed _ (fun i => isClosed_eq
    ((hf i).comp continuous_fst)
    (((continuous_fst.comp ((continuous_apply i).comp continuous_snd)).norm).pow 2)) P HM

end LeanCanny.Geometry.BoundedWeakBooleanWitness
