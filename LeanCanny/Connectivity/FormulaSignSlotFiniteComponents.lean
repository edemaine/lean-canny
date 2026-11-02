/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalSignFiniteComponents
public import Mathlib.Topology.Connected.TotallyDisconnected
/-! # Actual positive and selected sign strata have finitely many components

Continuous surjective projections from the constructed closed circular source
establish finiteness without recursive-cover data. This does not assert path
connectivity or identify a native bounded component-label algorithm.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotFiniteComponents
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension pair Input.field
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count FormulaSignSlotMargin.prepared

noncomputable def projection (c : List Bool) : FormulaSignSlotCircularBoundedCover.Source c → Positive c :=
  FormulaSignSlotCircularInterior.projection c ∘ FormulaSignSlotCircularBoundedCover.projection c

theorem continuous_projection (c : List Bool) : Continuous (projection c) :=
  (FormulaSignSlotCircularInterior.continuous_projection c).comp (FormulaSignSlotCircularBoundedCover.proper_projection c).continuous

theorem projection_surjective (c : List Bool) : Function.Surjective (projection c) := by
  have H : Function.Surjective (FormulaSignSlotCircularInterior.projection c) :=
    fun y => ⟨FormulaSignSlotCircularInterior.sectionPoint c y,FormulaSignSlotCircularInterior.projection_section c y⟩
  exact H.comp (FormulaSignSlotCircularBoundedCover.projection_surjective c)

theorem positive_components_finite (c : List Bool) : Finite (ConnectedComponents (Positive c)) := by
  let : Finite (ConnectedComponents (FormulaSignSlotCircularBoundedCover.Source c)) := CanonicalSignFiniteComponents.components_finite c
  exact Finite.of_surjective _ ((continuous_projection c).connectedComponentsMap_surjective (projection_surjective c))

theorem positive_component_clopen (c : List Bool) (x : Positive c) : IsClopen (connectedComponent x) := by
  let : Finite (ConnectedComponents (Positive c)) := positive_components_finite c
  exact FiniteComponentCover.isClopen_component x

noncomputable def Stratum (c : List Bool) :=
  {x : Fin (FormulaSignSlotSource.dimension c) → ℝ | (FormulaSignSlotSource.stratum c).Holds (Formula.extend x)}
noncomputable def stratumProjection (c : List Bool) (x : Positive c) : Stratum c :=
  ⟨(FormulaSignSlotMarginProjection.projection c x.val).val,(value_positive_iff c x.val).mp x.property⟩

theorem continuous_stratumProjection (c : List Bool) : Continuous (stratumProjection c) :=
  (continuous_subtype_val.comp ((proper_projection c).continuous.comp continuous_subtype_val)).subtype_mk _

theorem stratumProjection_surjective (c : List Bool) : Function.Surjective (stratumProjection c) := by
  intro z
  let t : Target c := ⟨z.val,FormulaSignSlotSource.stratum_implies_envelope c _ z.property⟩
  obtain ⟨y,HY⟩ := FormulaSignSlotMarginProjection.projection_surjective c t
  have HP : 0 < value c y := (value_positive_iff c y).mpr (by rw [HY]; exact z.property)
  have HE : (FormulaSignSlotMarginProjection.projection c y).val=z.val := congrArg (fun t : Target c => t.val) HY
  exact ⟨⟨y,HP⟩,Subtype.ext HE⟩

theorem stratum_components_finite (c : List Bool) : Finite (ConnectedComponents (Stratum c)) := by
  let : Finite (ConnectedComponents (Positive c)) := positive_components_finite c
  exact Finite.of_surjective _ ((continuous_stratumProjection c).connectedComponentsMap_surjective (stratumProjection_surjective c))
end LeanCanny.Connectivity.FormulaSignSlotFiniteComponents
