/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateProjection
public import LeanCanny.Connectivity.ClosedFormulaGateLanguages
/-! # Proper native single-equation reduction for actual closed Boolean formulas -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaBoundedGate
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open ClosedFormulaGateTruth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

noncomputable def projection {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (z : BoundedGateCoordinates.NativeZero F c) : (Description.mk (F.dimension c) p).realization :=
  baseHomeomorph hp c hc hs
    (BoundedGateCoordinates.projection F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three z)

theorem proper_projection {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c) :
    IsProperMap (projection hp c hc hs) :=
  (baseHomeomorph hp c hc hs).isProperMap.comp
    (BoundedGateCoordinates.proper_projection F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three)

theorem joined_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (y z : BoundedGateCoordinates.NativeZero F c) :
    JoinedIn univ y z ↔ JoinedIn univ (projection hp c hc hs y) (projection hp c hc hs z) := by
  rw [BoundedGateCoordinates.joined_iff F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three]
  constructor
  · intro H
    exact (H.map (baseHomeomorph hp c hc hs).continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [projection,Homeomorph.symm_apply_apply] using
      (H.map (baseHomeomorph hp c hc hs).symm.continuous.continuousOn).mono (subset_univ _)

theorem connected_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c) :
    (BoundedMonotoneGateSource.description F c).Connected ↔ (Description.mk (F.dimension c) p).Connected := by
  have HW := BoundedMonotoneGateSource.description_wellFormed F c (source_scope c)
  simp only [Description.Connected,HW,true_and,show (Description.mk (F.dimension c) p).WellFormed from hs]
  have HL : IsPreconnected (BoundedMonotoneGateSource.description F c).realization ↔
      IsPreconnected (univ : Set (BoundedGateCoordinates.NativeZero F c)) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  have HR : IsPreconnected (Description.mk (F.dimension c) p).realization ↔
      IsPreconnected (univ : Set (Description.mk (F.dimension c) p).realization) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  have HE := (baseHomeomorph hp c hc hs).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (baseHomeomorph hp c hc hs).surjective] at HE
  exact HL.trans ((BoundedGateCoordinates.preconnected_iff F c (source_scope c)
    ClosedFormulaGateMetadata.kind_ne_three).trans (HE.symm.trans HR.symm))

noncomputable def writer (c : List Bool) : List Bool :=
  (Input.whole (BoundedMonotoneGateSource.description F c)).encode

theorem writer_FP : writer ∈ FP :=
  BoundedMonotoneGateSource.whole_record_FP F ClosedFormulaGateMetadata.access

theorem language_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c) :
    writer c∈connectedLanguage ↔ (Input.whole (Description.mk (F.dimension c) p)).encode∈connectedLanguage := by
  simp only [writer,whole_encode_mem_iff]
  exact connected_iff hp c hc hs

theorem canonical_language_iff (d : Description) (hp : ClosedFormulaWitness.Closed d.formula)
    (hd : d.WellFormed) : writer (Input.whole d).encode∈connectedLanguage ↔ (Input.whole d).encode∈connectedLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.whole d).encode)=d.formula.encode := by
    rw [Input.field_whole_space,FormulaView.normalize_encode]
  have HS : d.formula.arity≤F.dimension (Input.whole d).encode := by rw [dimension_whole]; exact hd
  have H := language_iff hp (Input.whole d).encode HC HS
  have HE : Description.mk (F.dimension (Input.whole d).encode) d.formula=d := by rw [dimension_whole]
  rw [HE] at H
  exact H

end LeanCanny.Connectivity.ClosedFormulaBoundedGate
