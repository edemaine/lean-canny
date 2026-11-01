/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalArcs
public import LeanCanny.Connectivity.SlabCover
public import Mathlib.Topology.Algebra.MvPolynomial
/-! # Gluing the selected-parent physical critical arcs to recursive endpoint covers

The remaining recursive inputs are covers of the exact two physical
endpoint fibers over the same old homomorphism. The interior arcs and
their original endpoint equations are already constructed.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedSlabCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedCriticalArcs
open IntegralMixedSelectedCriticalCuts IntegralMixedSelectedPhysicalFiber IntegralMixedSelectedPhysicalArcs
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem physical_closed (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) : IsClosed (physical x hm r φ t) := by
  have HF : IsClosed {y : Fin (n+1) → ℝ | ∀ i, i.val < r.critical.offset.val →
      ((data x hm r.critical).scales i : ℝ) * y i = heightValue x r φ t i} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((continuous_apply i).const_mul _) continuous_const
  have HR : IsClosed {y : Fin (n+1) → ℝ | ∀ j,
      (IntegralMixedSweepRows.integerRow P r j).eval₂ (Int.castRingHom ℝ) y = 0} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_eq _ continuous_const
    simpa only [MvPolynomial.eval₂_eq_eval_map] using
      MvPolynomial.continuous_eval ((IntegralMixedSweepRows.integerRow P r j).map (Int.castRingHom ℝ))
  exact HF.inter HR

noncomputable def endpointCover {J : Type} (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (C : ClopenPathCover (physical x hm r φ t) J) :
    SlabCover.FiberCover (fun s y => y ∈ physical x hm r φ s) t J where
  piece := C.imagePiece
  subset j _ hy := C.imagePiece_subset j hy
  cover := C.imagePiece_cover
  accessible j y hy z hz := by
    have HC := C.imagePiece_closed (physical_closed x hm r φ t) j
    have HY : y ∈ C.imagePiece j := HC.closure_eq ▸ hy
    simpa only [insert_eq_of_mem HY] using C.imagePiece_paths j y HY z hz

theorem exists_slab_cover {L R : Type} [Finite L] [Finite R]
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b) (havoid : ∀ t ∈ Ioo a b, t ∉ bad x hm r φ c)
    (left : ClopenPathCover (physical x hm r φ a) L) (right : ClopenPathCover (physical x hm r φ b) R) :
    Finite (physical x hm r φ t₀.val) ∧
    ∃ curve : physical x hm r φ t₀.val → ℝ → Fin (n+1) → ℝ,
      let p := SlabCover.piece (fun t y => y ∈ physical x hm r φ t)
        curve left.imagePiece right.imagePiece a b
      (∀ z, ∃ i, z ∈ p i) ∧ (∀ i, FrontierCover.Accessible (p i)) ∧
      (∀ j l, FrontierCover.Incident p (.inl j) (.inr (.inl l)) ↔ curve j a ∈ left.imagePiece l) ∧
      (∀ j k, FrontierCover.Incident p (.inl j) (.inr (.inr k)) ↔ curve j b ∈ right.imagePiece k) ∧
      Nonempty (ClopenPathCover (SlabCover.Space (fun t y => y ∈ physical x hm r φ t) a b)
        (SlabCover.Index (physical x hm r φ t₀.val) L R)) := by
  obtain ⟨Hfinite, curve, _, HC, HR, HE, _⟩ := anchored_physical_arcs x hm r φ c a b t₀ havoid
  let : Finite (physical x hm r φ t₀.val) := Hfinite
  let l := endpointCover x hm r φ a left
  let k := endpointCover x hm r φ b right
  let H := fun t y => y ∈ physical x hm r φ t
  have Hab := t₀.property.1.trans t₀.property.2
  have Hcomplete := fun t ht y hy => (HE ⟨t,ht⟩ y).mp hy |>.exists
  have Hcover := SlabCover.cover H curve Hcomplete l.piece k.piece l.cover k.cover
  have Haccess := SlabCover.accessible H Hab curve HC HR l.piece k.piece l.subset k.subset l.accessible k.accessible
  exact ⟨Hfinite, curve, Hcover, Haccess,
    SlabCover.incident_arc_left_iff H Hab curve HC HR l.piece k.piece l.subset k.subset,
    SlabCover.incident_arc_right_iff H Hab curve HC HR l.piece k.piece l.subset k.subset,
    ⟨ClopenPathCover.ofAccessible _ Hcover Haccess⟩⟩

end LeanCanny.Connectivity.IntegralMixedSelectedSlabCover
