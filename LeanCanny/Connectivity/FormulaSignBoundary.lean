/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignEnvelopes
public import LeanCanny.Connectivity.FrontierCover
/-! # Relative boundaries of the actual permitted mixed-Boolean sign strata

A frontier witness belongs to an accepted stratum. A common excluded limit
point of two strata therefore creates no incidence.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignPartition
open ETR Set
open scoped Classical

noncomputable def piece (d : Description) (σ : {σ : Pattern d.formula // accepted σ}) : Set d.realization :=
  {x | x.val∈Stratum d.dimension σ.val}

theorem piece_cover (d : Description) : ∀ x : d.realization, ∃ σ, x∈piece d σ := by
  intro x
  let σ := ofPoint d.formula (Formula.extend x.val)
  have H := point_stratum d.formula d.dimension x.val
  exact ⟨⟨σ,(stratum_truth d.dimension σ H).mpr x.property⟩,H⟩

theorem piece_image (d : Description) (σ : {σ : Pattern d.formula // accepted σ}) :
    Subtype.val '' piece d σ=Stratum d.dimension σ.val := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,(stratum_truth d.dimension σ.val hx).mp σ.property⟩,hx,rfl⟩

theorem closure_piece (d : Description) (σ : {σ : Pattern d.formula // accepted σ}) :
    closure (piece d σ)=Subtype.val ⁻¹' closure (Stratum d.dimension σ.val) := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,piece_image]

theorem boundary_envelope (d : Description) (σ : {σ : Pattern d.formula // accepted σ})
    {x : d.realization} (hx : x∈closure (piece d σ)) :
    (envelope σ.val).Holds (Formula.extend x.val) := by
  rw [closure_piece] at hx
  exact closure_stratum_envelope d.dimension σ.val hx

theorem incidence_iff (d : Description) (σ τ : {σ : Pattern d.formula // accepted σ}) :
    FrontierCover.Incident (piece d) σ τ ↔
      (∃ x : Fin d.dimension → ℝ, x∈Stratum d.dimension σ.val ∧ x∈closure (Stratum d.dimension τ.val)) ∨
      (∃ x : Fin d.dimension → ℝ, x∈Stratum d.dimension τ.val ∧ x∈closure (Stratum d.dimension σ.val)) := by
  have HE (a b : {σ : Pattern d.formula // accepted σ}) :
      (piece d a ∩ closure (piece d b)).Nonempty ↔
        ∃ x : Fin d.dimension → ℝ, x∈Stratum d.dimension a.val ∧ x∈closure (Stratum d.dimension b.val) := by
    rw [closure_piece]
    constructor
    · rintro ⟨x,hx,hb⟩
      exact ⟨x.val,hx,hb⟩
    · rintro ⟨x,hx,hb⟩
      exact ⟨⟨x,(stratum_truth d.dimension a.val hx).mp a.property⟩,hx,hb⟩
  exact or_congr (HE _ _) (HE _ _)

theorem necessary_walk (d : Description) (σ τ : {σ : Pattern d.formula // accepted σ})
    {x y : d.realization} (hx : x∈piece d σ) (hy : y∈piece d τ) (H : JoinedIn univ x y) :
    Relation.ReflTransGen (FrontierCover.Incident (piece d)) σ τ :=
  FrontierCover.reachable_of_joinedIn (piece d) (piece_cover d) hx hy H

end LeanCanny.Connectivity.FormulaSignPartition
