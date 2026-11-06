/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalPoints
/-! # Accepted successor histories define the actual old height fiber -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "levels" => FormulaSignSlotRadialProviderAtomic.levels
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.levels FormulaSignSlotRadialProviderAtomic.point
  FormulaSignSlotRadialProviderAtomicGeometry.source FormulaSignSlotRadialProviderMarkedGeometry.zeroSet

noncomputable def childCoordinate (c parent : List Bool) (hv : A parent) (hc : provider parent=c) :
    Fin (num c+4) :=
  ⟨depth parent,by have H := (pointAt_occurrence c parent hv hc).depth_le;omega⟩

theorem childCoordinate_val (c parent : List Bool) (hv : A parent) (hc : provider parent=c) :
    (childCoordinate c parent hv hc).val=depth parent := rfl

theorem child_frozenSlice_eq (c parent child : List Bool) (ha : A parent) (hb : A child)
    (hca : provider parent=c) (hcb : provider child=c) (hs : depth child=depth parent+1)
    (HF : pointAt c child hb hcb∈frozenSlice c (depth parent) (levels parent ha))
    (height : ℝ) (HH : pointAt c child hb hcb (childCoordinate c parent ha hca)=height) :
    frozenSlice c (depth child) (levels child hb)=
      frozenSlice c (depth parent) (levels parent ha)∩{p |p (childCoordinate c parent ha hca)=height} := by
  let coord := childCoordinate c parent ha hca
  have HVal : coord.val=depth parent := rfl
  have HO := pointAt_occurrence c child hb hcb
  have HOwn : ∀i : Fin (num c+4),i.val<depth child→pointAt c child hb hcb i=levels child hb i.val :=
    @IntegralMixedAtomicOccurrence.Occurrence.frozen (num c+3)
      (FormulaSignSlotRadialProviderAtomicGeometry.source c) (depth child) (levels child hb)
      (pointAt c child hb hcb) HO
  have HL (i : Fin (num c+4)) (hi : i.val<depth parent) :
      levels child hb i.val=levels parent ha i.val :=
    (HOwn i (by omega)).symm.trans (HF.2 i hi)
  have HG : levels child hb coord.val=height := (HOwn coord (by omega)).symm.trans HH
  ext p
  constructor
  · intro HP
    refine ⟨⟨HP.1,fun i hi=>(HP.2 i (by omega)).trans (HL i hi)⟩,?_⟩
    exact (HP.2 coord (by omega)).trans HG
  · rintro ⟨HP,HT⟩
    refine ⟨HP.1,?_⟩
    intro i hi
    by_cases HI : i.val<depth parent
    · exact (HP.2 i HI).trans (HL i HI).symm
    · have HE : i=coord := Fin.ext (by omega)
      subst i
      exact HT.trans HG.symm

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
