/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaBoundedFrontier
public import LeanCanny.Connectivity.FormulaSignBoundary
/-! # Exact bounded-source lifts of sign-stratum boundary points

Properness supplies a lift in the closure of the selected sign stratum,
with the same original tuple. This is a lift through the actual witness
compiler, not a claim about lifting arbitrary absolute annihilator roots.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignPartition
open ETR Set LeanCanny.Encoding
open ClosedFormulaGateTruth ClosedFormulaBoundedFrontier
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

variable {p : Formula} (σ : Pattern p) (c : List Bool)
  (hc : FormulaView.normalize (Input.field 2 c)=(envelope σ).encode)
  (hs : (envelope σ).arity≤F.dimension c)

noncomputable def selectedTarget : Set (Target (envelope σ) c) :=
  {x | x.val∈Stratum (F.dimension c) σ}
noncomputable def selectedSource : Set (Source c) :=
  ClosedFormulaBoundedGate.projection (envelope_closed σ) c hc hs ⁻¹' selectedTarget σ c

theorem selectedTarget_image :
    Subtype.val '' selectedTarget σ c=Stratum (F.dimension c) σ := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,stratum_envelope (F.dimension c) σ hx⟩,hx,rfl⟩

theorem selectedTarget_closure :
    closure (selectedTarget σ c)=Subtype.val ⁻¹' closure (Stratum (F.dimension c) σ) := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,selectedTarget_image]

theorem selectedSource_image :
    projected (envelope_closed σ) c hc hs (selectedSource σ c hc hs)=selectedTarget σ c :=
  image_preimage_eq _ (projection_surjective (envelope_closed σ) c hc hs)

theorem boundary_lift {x : Fin (F.dimension c) → ℝ} (hx : x∈closure (Stratum (F.dimension c) σ)) :
    ∃ y : Source c, y∈closure (selectedSource σ c hc hs) ∧ oldCoordinates c y=x := by
  let z : Target (envelope σ) c := ⟨x,closure_stratum_envelope (F.dimension c) σ hx⟩
  have HZ : z∈closure (selectedTarget σ c) := by rw [selectedTarget_closure]; exact hx
  rw [← selectedSource_image σ c hc hs,closure_projected] at HZ
  obtain ⟨y,hy,HE⟩ := HZ
  refine ⟨y,hy,?_⟩
  have HC := congrArg Subtype.val HE
  rw [projection_coordinates] at HC
  exact HC

end LeanCanny.Connectivity.FormulaSignPartition
