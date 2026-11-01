/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaGateTruth
public import LeanCanny.Encoding.ClosedFormulaGateReaders
/-! # Native single-equation component reduction for actual closed formula inputs -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaGateTruth
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

 theorem source_scope (c : List Bool) :
    ∀ i < ClosedFormulaGateMetadata.count c, (F.atom (pair c (List.replicate i true))).arity≤ClosedFormulaGateMetadata.dimension c := by
  intro i _
  simpa only [F,ClosedFormulaGateMetadata.family,pairFst_pair] using
    ClosedFormulaGateMetadata.atom_scope (pair c (List.replicate i true))

 theorem predicate_holds {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    MonotoneGateCircles.predicate F c (statuses c x) ↔ p.Holds (Formula.extend x) := by
  have HP : 0 < ClosedFormulaGateMetadata.count c := by
    unfold ClosedFormulaGateMetadata.count
    rw [hc]
    simp [Formula.encode]
  change BooleanCircuitSpace.value circuit (atom c x) c=true ↔ _
  rw [BooleanCircuitSpace.value_eq_wireValue circuit (atom c x) c HP]
  have HW := wire_formula hp c [] [] x (by simpa only [List.nil_append,List.append_nil] using hc) hs
  have HW' : BooleanCircuitSpace.wireValue circuit (atom c x) c (ClosedFormulaGateMetadata.count c-1)=decide (p.Holds (Formula.extend x)) := by
    simpa only [wire,FormulaBooleanCircuitSource.wire,ClosedFormulaGateMetadata.count,List.length_nil,Nat.sub_zero] using HW
  have HCount : circuit.count c=ClosedFormulaGateMetadata.count c := rfl
  rw [HCount,HW',decide_eq_true_eq]

noncomputable def baseHomeomorph {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c) ≃ₜ
      (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization where
  toFun x := ⟨x.val,(predicate_holds hp c x.val hc hs).mp x.property⟩
  invFun x := ⟨x.val,(predicate_holds hp c x.val hc hs).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

noncomputable def originalProjection {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (z : MonotoneGateGraph.ZeroSet F c) : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization :=
  baseHomeomorph hp c hc hs (MonotoneGateCircles.projection F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three z)

private theorem homeomorph_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem original_joined_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (y z : MonotoneGateGraph.ZeroSet F c) :
    JoinedIn univ y z ↔ JoinedIn univ (originalProjection hp c hc hs y) (originalProjection hp c hc hs z) :=
  (MonotoneGateCircles.joined_iff F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three y z).trans
    (homeomorph_joined (baseHomeomorph hp c hc hs) _ _)

theorem original_connected_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    (MonotoneGateGraph.description F c).Connected ↔ (Description.mk (ClosedFormulaGateMetadata.dimension c) p).Connected := by
  have HE := (baseHomeomorph hp c hc hs).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (baseHomeomorph hp c hc hs).surjective] at HE
  have HZ := MonotoneGateCircles.preconnected_iff F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three
  have HB : IsPreconnected (univ : Set (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization) ↔
      IsPreconnected (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization :=
    (isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ).symm
  have HW := MonotoneGateGraph.description_wellFormed F c (source_scope c)
  simp only [Description.Connected,HW,true_and,show (Description.mk (ClosedFormulaGateMetadata.dimension c) p).WellFormed from hs]
  exact HZ.trans (HE.symm.trans HB)

end LeanCanny.Connectivity.ClosedFormulaGateTruth
