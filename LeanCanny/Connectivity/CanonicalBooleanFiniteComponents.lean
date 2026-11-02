/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotFiniteComponents
public import LeanCanny.Geometry.FiniteComponentImages
public import LeanCanny.Connectivity.CanonicalSignRefinement
/-! # Every well-formed canonical Boolean realization has finitely many components

Native accepted sign words give an exact finite continuous image cover. Each
selected stratum has finite components by the actual closed circular source
and unbounded coercive sampling. This theorem has NO recursive-cover, compactness,
smoothness or evaluator premise. It does not assert a path-cover algorithm.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalBooleanFiniteComponents
open ETR Set LeanCanny.Encoding LeanCanny.Geometry CanonicalSignRefinement
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotCircularBoundedCover.root

noncomputable def map (d : Description) (hd : d.WellFormed) (l : Label d)
    (z : FormulaSignSlotFiniteComponents.Stratum (source d l)) : d.realization :=
  ⟨tuple d l z.val,by
    apply (FormulaSignSlotTruth.canonical_selected_iff d hd _).mpr
    refine ⟨l.val,l.property.1,l.property.2,?_⟩
    rw [extend_tuple]
    exact z.property⟩

theorem continuous_map (d : Description) (hd : d.WellFormed) (l : Label d) : Continuous (map d hd l) :=
  ((tuple d l).continuous.comp continuous_subtype_val).subtype_mk _

theorem cover (d : Description) (hd : d.WellFormed) (x : d.realization) :
    ∃ l z, map d hd l z=x := by
  obtain ⟨w,HW,HA,HX⟩ := (FormulaSignSlotTruth.canonical_selected_iff d hd x.val).mp x.property
  let l : Label d := ⟨w,HW,HA⟩
  let y := (tuple d l).symm x.val
  have HY : (FormulaSignSlotSource.stratum (source d l)).Holds (Formula.extend y) := by
    have HE := extend_tuple d l y
    rw [Homeomorph.apply_symm_apply] at HE
    rw [← HE]
    exact HX
  exact ⟨l,⟨y,HY⟩,Subtype.ext ((tuple d l).apply_symm_apply x.val)⟩

theorem components_finite (d : Description) (hd : d.WellFormed) : Finite (ConnectedComponents d.realization) := by
  let _ (l : Label d) : Finite (ConnectedComponents (FormulaSignSlotFiniteComponents.Stratum (source d l))) :=
    FormulaSignSlotFiniteComponents.stratum_components_finite (source d l)
  exact FiniteComponentImages.components_finite (map d hd) (continuous_map d hd) (cover d hd)

theorem component_clopen (d : Description) (hd : d.WellFormed) (x : d.realization) : IsClopen (connectedComponent x) := by
  let : Finite (ConnectedComponents d.realization) := components_finite d hd
  exact FiniteComponentCover.isClopen_component x
end LeanCanny.Connectivity.CanonicalBooleanFiniteComponents
