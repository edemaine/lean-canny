/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotPartition
public import LeanCanny.Connectivity.ClosedFormulaBoundedFrontier
/-! # Selected strict-stratum boundaries in the native bounded weak-envelope source -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotFrontier
open ETR Set LeanCanny.Encoding LeanCanny.Geometry ClosedFormulaGateTruth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotBounded.prepared

noncomputable abbrev root (c : List Bool) := FormulaSignSlotBounded.prepared c
noncomputable abbrev Source (c : List Bool) := ClosedFormulaBoundedFrontier.Source (root c)
noncomputable abbrev Target (c : List Bool) :=
  ClosedFormulaBoundedFrontier.Target (FormulaSignSlotSource.envelope c) (root c)

theorem root_formula (c : List Bool) : FormulaView.normalize (Input.field 2 (root c))=
    (FormulaSignSlotSource.envelope c).encode := by
  simp only [root,FormulaSignSlotBounded.prepared,Input.field_whole_space,
    FormulaView.normalize_encode,FormulaSignSlotSource.description]

theorem root_dimension (c : List Bool) : F.dimension (root c)=FormulaSignSlotSource.dimension c := by
  unfold root FormulaSignSlotBounded.prepared
  rw [dimension_whole]
  rfl

theorem root_scope (c : List Bool) : (FormulaSignSlotSource.envelope c).arity≤F.dimension (root c) := by
  rw [root_dimension]
  exact FormulaSignSlotSource.envelope_scope c

noncomputable def projection (c : List Bool) : Source c → Target c :=
  ClosedFormulaBoundedGate.projection (FormulaSignSlotSource.envelope_closed c) (root c)
    (root_formula c) (root_scope c)

theorem proper_projection (c : List Bool) : IsProperMap (projection c) :=
  ClosedFormulaBoundedGate.proper_projection (FormulaSignSlotSource.envelope_closed c) (root c)
    (root_formula c) (root_scope c)
theorem projection_surjective (c : List Bool) : Function.Surjective (projection c) :=
  ClosedFormulaBoundedFrontier.projection_surjective (FormulaSignSlotSource.envelope_closed c) (root c)
    (root_formula c) (root_scope c)

noncomputable def selectedTarget (c : List Bool) : Set (Target c) :=
  {x | (FormulaSignSlotSource.stratum c).Holds (Formula.extend x.val)}
noncomputable def selectedSource (c : List Bool) : Set (Source c) := projection c ⁻¹' selectedTarget c

theorem selectedTarget_image (c : List Bool) :
    Subtype.val '' selectedTarget c={x : Fin (F.dimension (root c)) → ℝ |
      (FormulaSignSlotSource.stratum c).Holds (Formula.extend x)} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,FormulaSignSlotSource.stratum_implies_envelope c _ hx⟩,hx,rfl⟩

theorem selectedTarget_closure (c : List Bool) : closure (selectedTarget c)=Subtype.val ⁻¹'
    closure {x : Fin (F.dimension (root c)) → ℝ | (FormulaSignSlotSource.stratum c).Holds (Formula.extend x)} := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,selectedTarget_image]

theorem selectedSource_image (c : List Bool) : projection c '' selectedSource c=selectedTarget c :=
  image_preimage_eq _ (projection_surjective c)

theorem boundary_lift (c : List Bool) {x : Fin (F.dimension (root c)) → ℝ}
    (hx : x∈closure {x : Fin (F.dimension (root c)) → ℝ |
      (FormulaSignSlotSource.stratum c).Holds (Formula.extend x)}) :
    ∃ y : Source c, y∈closure (selectedSource c) ∧
      ClosedFormulaBoundedFrontier.oldCoordinates (root c) y=x := by
  have HE : (FormulaSignSlotSource.envelope c).Holds (Formula.extend x) :=
    (FormulaSignPartition.closed_holds (FormulaSignSlotSource.envelope_closed c) _).closure_subset_iff.mpr
      (fun z hz => FormulaSignSlotSource.stratum_implies_envelope c _ hz) hx
  let z : Target c := ⟨x,HE⟩
  have HZ : z∈closure (selectedTarget c) := by rw [selectedTarget_closure]; exact hx
  rw [← selectedSource_image] at HZ
  rw [(proper_projection c).isClosedMap.closure_image_eq_of_continuous (proper_projection c).continuous] at HZ
  obtain ⟨y,hy,HY⟩ := HZ
  refine ⟨y,hy,?_⟩
  have HC := congrArg Subtype.val HY
  change (ClosedFormulaBoundedGate.projection (FormulaSignSlotSource.envelope_closed c) (root c)
    (root_formula c) (root_scope c) y).val=x at HC
  rw [ClosedFormulaBoundedFrontier.projection_coordinates] at HC
  exact HC

theorem selected_accessible (c : List Bool) (H : FrontierCover.Accessible (selectedSource c)) :
    FrontierCover.Accessible (selectedTarget c) := by
  rw [← selectedSource_image]
  exact H.image (proper_projection c).continuous (proper_projection c).isClosedMap

end LeanCanny.Connectivity.FormulaSignSlotFrontier
