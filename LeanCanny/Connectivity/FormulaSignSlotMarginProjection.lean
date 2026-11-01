/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotMarginGraph
public import LeanCanny.Connectivity.ClosedFormulaBoundedFrontier
/-! # The native margin equation source projects properly and retains a literal coordinate objective -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotMarginProjection
open ETR Set LeanCanny.Encoding LeanCanny.Geometry ClosedFormulaGateTruth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared

noncomputable abbrev root (c : List Bool) := FormulaSignSlotMargin.prepared c
noncomputable abbrev Source (c : List Bool) := ClosedFormulaBoundedFrontier.Source (root c)
noncomputable abbrev Target (c : List Bool) := (FormulaSignSlotSource.description c).realization

theorem root_formula (c : List Bool) : FormulaView.normalize (Input.field 2 (root c))=
    (FormulaSignSlotMargin.graphDescription c).formula.encode := by
  simp only [root,FormulaSignSlotMargin.prepared,Input.field_whole_space,FormulaView.normalize_encode]
theorem root_dimension (c : List Bool) : F.dimension (root c)=(FormulaSignSlotMargin.graphDescription c).dimension := by
  unfold root FormulaSignSlotMargin.prepared
  exact dimension_whole _
theorem root_scope (c : List Bool) : (FormulaSignSlotMargin.graphDescription c).formula.arity≤F.dimension (root c) := by
  rw [root_dimension]
  exact FormulaSignSlotMargin.graph_wellFormed c

noncomputable def equalityHomeomorph {d e : Description} (H : d=e) : d.realization ≃ₜ e.realization := by
  cases H
  exact Homeomorph.refl _
private theorem equality_coordinate {d e : Description} (H : d=e) (x : d.realization) (i : ℕ)
    (hd : i < d.dimension) (he : i < e.dimension) :
    (equalityHomeomorph H x).val ⟨i,he⟩=x.val ⟨i,hd⟩ := by
  cases H
  rfl

theorem rootDescriptionEq (c : List Bool) :
    Description.mk (F.dimension (root c)) (FormulaSignSlotMargin.graphDescription c).formula=
      FormulaSignSlotMargin.graphDescription c := by rw [root_dimension]

noncomputable def targetHomeomorph (c : List Bool) :
    ClosedFormulaBoundedFrontier.Target (FormulaSignSlotMargin.graphDescription c).formula (root c) ≃ₜ
      (FormulaSignSlotMargin.graphDescription c).realization :=
  equalityHomeomorph (rootDescriptionEq c)

noncomputable def projection (c : List Bool) : Source c → Target c := fun y =>
  FormulaSignSlotMargin.graphHomeomorph c (targetHomeomorph c
    (ClosedFormulaBoundedGate.projection (FormulaSignSlotMargin.graph_closed c) (root c)
      (root_formula c) (root_scope c) y))

theorem proper_projection (c : List Bool) : IsProperMap (projection c) :=
  (FormulaSignSlotMargin.graphHomeomorph c).isProperMap.comp
    ((targetHomeomorph c).isProperMap.comp
      (ClosedFormulaBoundedGate.proper_projection (FormulaSignSlotMargin.graph_closed c) (root c)
        (root_formula c) (root_scope c)))
theorem projection_surjective (c : List Bool) : Function.Surjective (projection c) :=
  (FormulaSignSlotMargin.graphHomeomorph c).surjective.comp ((targetHomeomorph c).surjective.comp
    (ClosedFormulaBoundedFrontier.projection_surjective (FormulaSignSlotMargin.graph_closed c) (root c)
      (root_formula c) (root_scope c)))

theorem objective_lt (c : List Bool) : FormulaSignSlotMargin.objective c < F.dimension (root c) := by
  rw [root_dimension]
  change FormulaSignSlotSource.dimension c < FormulaSignSlotSource.dimension c+1
  omega

noncomputable def objectiveIndex (c : List Bool) : Fin (BoundedMonotoneGateSource.total F (root c)) :=
  ⟨FormulaSignSlotMargin.objective c,by
    have H := objective_lt c
    change FormulaSignSlotMargin.objective c < F.dimension (root c)+2*F.count (root c)+F.count (root c)+2*F.count (root c)
    omega⟩
noncomputable def oldIndex (c : List Bool) (i : Fin (FormulaSignSlotSource.dimension c)) :
    Fin (BoundedMonotoneGateSource.total F (root c)) :=
  ⟨i.val,i.isLt.trans (objectiveIndex c).isLt⟩

theorem projection_coordinate (c : List Bool) (y : Source c) (i : Fin (FormulaSignSlotSource.dimension c)) :
    (projection c y).val i=y.val (oldIndex c i) := by
  let z := ClosedFormulaBoundedGate.projection (FormulaSignSlotMargin.graph_closed c) (root c)
    (root_formula c) (root_scope c) y
  have HI : i.val < (FormulaSignSlotMargin.graphDescription c).dimension := by
    change i.val < FormulaSignSlotSource.dimension c+1
    exact Nat.lt_succ_of_lt i.isLt
  have HR : i.val < F.dimension (root c) := by rw [root_dimension]; exact HI
  have HG : (projection c y).val i=(targetHomeomorph c z).val (Fin.castAdd 1 i) :=
    TermCoordinateGraph.old_coordinate _ _ _ (FormulaSignSlotSource.envelope_scope c)
      (FormulaSignSlotMargin.margin_scope c) (targetHomeomorph c z) i
  have HE := equality_coordinate (rootDescriptionEq c) z i.val HR HI
  have HO := congrFun (ClosedFormulaBoundedFrontier.projection_coordinates
    (FormulaSignSlotMargin.graph_closed c) (root c) (root_formula c) (root_scope c) y) ⟨i.val,HR⟩
  exact HG.trans (HE.trans HO)

noncomputable def value (c : List Bool) (y : Source c) : ℝ := y.val (objectiveIndex c)

theorem continuous_value (c : List Bool) : Continuous (value c) :=
  (continuous_apply (objectiveIndex c)).comp continuous_subtype_val

theorem value_eq (c : List Bool) (y : Source c) :
    value c y=(FormulaSignSlotMargin.margin c).eval (Formula.extend (projection c y).val) := by
  let z := ClosedFormulaBoundedGate.projection (FormulaSignSlotMargin.graph_closed c) (root c)
    (root_formula c) (root_scope c) y
  have HO := congrFun (ClosedFormulaBoundedFrontier.projection_coordinates
    (FormulaSignSlotMargin.graph_closed c) (root c) (root_formula c) (root_scope c) y)
    ⟨FormulaSignSlotMargin.objective c,objective_lt c⟩
  have HE : (targetHomeomorph c z).val ⟨FormulaSignSlotMargin.objective c,by
      change FormulaSignSlotSource.dimension c < FormulaSignSlotSource.dimension c+1; omega⟩=
      z.val ⟨FormulaSignSlotMargin.objective c,objective_lt c⟩ :=
    equality_coordinate (rootDescriptionEq c) z _ _ _
  have HG := FormulaSignSlotMargin.graph_objective c (targetHomeomorph c z)
  rw [HE] at HG
  exact HO.symm.trans HG

theorem value_nonneg (c : List Bool) (y : Source c) : 0≤value c y := by
  rw [value_eq]
  exact FormulaSignSlotMargin.margin_nonneg _ _ (projection c y).property

theorem value_positive_iff (c : List Bool) (y : Source c) : 0 < value c y ↔
    (FormulaSignSlotSource.stratum c).Holds (Formula.extend (projection c y).val) := by
  rw [value_eq]
  exact FormulaSignSlotMargin.margin_positive_iff _ _ (projection c y).property

end LeanCanny.Connectivity.FormulaSignSlotMarginProjection
