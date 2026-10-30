/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompactComponentSamples
public import LeanCanny.Encoding.FlatAffineCompleteChildGeometry
public import LeanCanny.Geometry.FiniteComponentCover

/-! # Compact slice component covers indexed by native complete children

Accepted child labels index the connected components containing their actual
spatial points. Invalid words denote empty pieces. Compactness and independent
affine normals give a complete clopen connected cover, including singular
components. Testing overlap still requires the recursive slice connection
test; no path connectivity of singular components is assumed here.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineCompactComponentCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (active direction slice)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def Valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v w : List Bool) : Prop := pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language F cone

noncomputable def Slice (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v) : Set (Fin (arity F u) → ℝ) :=
  slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)

noncomputable def root (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v w : List Bool) (hw : Valid F cone u v w) : FlatAffinePowerSampleInput.OriginalRoots (next F) u :=
  FlatAffineCompleteVertices.vertexEquiv (next F) cone u
    ⟨w, (FlatAffineCompleteChildLabels.valid F cone u w v hw).1⟩

theorem root_prefix (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (w : List Bool) (hw : Valid F cone u v w) :
    FlatAffineCompleteRootStages.project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u)
      (root F cone u v w hw) = FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩ :=
  (FlatAffineCompleteChildLabels.packet F cone u w v (FlatAffineCompleteChildLabels.valid F cone u w v hw).1 hv).mp hw

noncomputable def point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (w : List Bool) (hw : Valid F cone u v w) : Slice F cone u v hv := by
  refine ⟨newest F u (root F cone u v w hw).val ∘ Sum.inl, ?_⟩
  have H := FlatAffineCompleteChildGeometry.newest_slice F u (root F cone u v w hw)
  rwa [root_prefix F cone u v hv w hw] at H

noncomputable def piece (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (w : List Bool) : Set (Slice F cone u v hv) :=
  if hw : Valid F cone u v w then connectedComponent (point F cone u v hv w hw) else ∅

attribute [local irreducible] point root

theorem piece_nonempty_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v) (w : List Bool) :
    (piece F cone u v hv w).Nonempty ↔ Valid F cone u v w := by
  by_cases hw : Valid F cone u v w
  · rw [piece, dite_eq_left hw]
    exact iff_of_true ⟨_, mem_connectedComponent⟩ hw
  · rw [piece, dite_eq_right hw]
    exact iff_of_false Set.not_nonempty_empty hw

theorem valid_width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v w : List Bool) (hw : Valid F cone u v w) :
    w.length = FlatAffineCompleteVertices.width (next F) cone u :=
  FlatAffineCompleteVertices.word_length (next F) cone u w (FlatAffineCompleteChildLabels.valid F cone u w v hw).1

theorem finite_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u v : List Bool) :
    Finite {w : List Bool // Valid F cone u v w} := by
  let I := FlatAffinePowerSampleInput.input (next F) cone
  let : Finite (SquareSampleComplete.Roots I u) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete (next F) cone) u).1
  let f : {w : List Bool // Valid F cone u v w} → SquareSampleComplete.Roots I u :=
    fun w => SquareSampleCompleteVertices.candidate I u w.val (FlatAffineCompleteChildLabels.valid F cone u w.val v w.property).1
  apply Finite.of_injective f
  intro w z h
  apply Subtype.ext
  exact SquareSampleCompleteVertices.candidate_injective I u w.val z.val _ _ h

theorem piece_preconnected (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v) (w : List Bool) :
    IsPreconnected (piece F cone u v hv w) := by
  unfold piece
  split_ifs
  · exact isPreconnected_connectedComponent
  · exact isPreconnected_empty

theorem overlap_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (w z : List Bool) (hw : Valid F cone u v w) (hz : Valid F cone u v z) :
    (piece F cone u v hv w ∩ piece F cone u v hv z).Nonempty ↔
      (point F cone u v hv z hz).val ∈ connectedComponentIn (Slice F cone u v hv)
        (point F cone u v hv w hw).val := by
  rw [piece, dite_eq_left hw, piece, dite_eq_left hz,
    connectedComponentIn_eq_image (point F cone u v hv w hw).property]
  constructor
  · rintro ⟨x, hx, hy⟩
    have HE : connectedComponent (point F cone u v hv z hz) = connectedComponent (point F cone u v hv w hw) :=
      (connectedComponent_eq hy).trans (connectedComponent_eq hx).symm
    refine ⟨point F cone u v hv z hz, ?_, rfl⟩
    rw [← HE]
    exact mem_connectedComponent
  · rintro ⟨x, hx, he⟩
    have HE : x = point F cone u v hv z hz := Subtype.ext he
    rw [HE] at hx
    exact ⟨_, hx, mem_connectedComponent⟩

section Compact
variable (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
  (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
  (hcompact : IsCompact (Slice F cone u v hv))
  (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
  (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
    (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ))

include hcompact hheights hindependent in
theorem piece_isClopen (w : List Bool) : IsClopen (piece F cone u v hv w) := by
  let : Finite (ConnectedComponents (Slice F cone u v hv)) :=
    (FlatAffineCompactComponentSamples.finite_card_le F cone u
      (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩) hcompact hheights hindependent).1
  unfold piece
  split_ifs
  · exact FiniteComponentCover.isClopen_component _
  · exact isClopen_empty

include hcompact hheights hindependent in
theorem cover (z : Slice F cone u v hv) : ∃ w, Valid F cone u v w ∧ z ∈ piece F cone u v hv w := by
  obtain ⟨w, ha, hc⟩ := FlatAffineCompactComponentSamples.exists_accepted F cone u v hv hcompact hheights hindependent z.val z.property
  have HA : Valid F cone u v w.val := ha
  have HP : (point F cone u v hv w.val HA).val ∈ connectedComponentIn (Slice F cone u v hv) z.val := by
    unfold point root
    exact hc
  rw [connectedComponentIn_eq_image z.property] at HP
  obtain ⟨y, hy, he⟩ := HP
  have HY : point F cone u v hv w.val HA = y := Subtype.ext he.symm
  refine ⟨w.val, HA, ?_⟩
  rw [piece, dite_eq_left HA, HY]
  exact ConnectedComponents.coe_eq_coe'.mp ((ConnectedComponents.coe_eq_coe'.mpr hy).symm)

include hcompact hheights hindependent in
theorem connected_iff_sample_connections :
    IsPreconnected (Slice F cone u v hv) ↔
      ∀ (w z : List Bool) (hw : Valid F cone u v w) (hz : Valid F cone u v z),
        (point F cone u v hv z hz).val ∈ connectedComponentIn (Slice F cone u v hv)
          (point F cone u v hv w hw).val := by
  constructor
  · intro H w z hw hz
    let : PreconnectedSpace (Slice F cone u v hv) := isPreconnected_iff_preconnectedSpace.mp H
    rw [connectedComponentIn_eq_image (point F cone u v hv w hw).property]
    refine ⟨point F cone u v hv z hz, ?_, rfl⟩
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  · intro H
    apply isPreconnected_iff_preconnectedSpace.mpr
    constructor
    apply isPreconnected_of_forall_pair
    intro x _ y _
    obtain ⟨w, hw, hx⟩ := cover F cone u v hv hcompact hheights hindependent x
    obtain ⟨z, hz, hy⟩ := cover F cone u v hv hcompact hheights hindependent y
    have HE := (overlap_iff F cone u v hv w z hw hz).mpr (H w z hw hz)
    exact ⟨piece F cone u v hv w ∪ piece F cone u v hv z, subset_univ _,
      Or.inl hx, Or.inr hy, IsPreconnected.union' HE
        (piece_preconnected F cone u v hv w) (piece_preconnected F cone u v hv z)⟩

end Compact
end LeanCanny.Connectivity.FlatAffineCompactComponentCover
