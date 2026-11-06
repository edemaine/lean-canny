/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendIdentity
/-! # Equal entire points glue actual native graph representatives -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.point

theorem identity_language_iff_pointAt_eq (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) :
    LeanCanny.pair a b∈FormulaSignSlotRadialProviderIdentity.language ↔ pointAt c a ha hca=pointAt c b hb hcb := by
  constructor
  · exact identity_pointAt_eq c a b ha hb hca hcb
  · intro HE
    have HN : HEq (FormulaSignSlotRadialProviderAtomic.point a ha) (FormulaSignSlotRadialProviderAtomic.point b hb) :=
      (native_pointAt_heq c a ha hca).trans ((heq_of_eq HE).trans (native_pointAt_heq c b hb hcb).symm)
    exact FormulaSignSlotRadialProviderRetainedAppend.identity_of_atomic_point_heq a b ha hb
      (hca.trans hcb.symm) HN

theorem raw_reachable_refl (c a : List Bool) (ha : A a) (hca : provider a=c) : RawReachable c a a :=
  ⟨ha,ha,hca,hca,Relation.ReflTransGen.refl⟩

theorem raw_reachable_trans {c a b d : List Bool} (h : RawReachable c a b) (k : RawReachable c b d) :
    RawReachable c a d := ⟨h.1,k.2.1,h.2.2.1,k.2.2.2.1,h.2.2.2.2.trans k.2.2.2.2⟩

theorem raw_reachable_of_pointAt_eq (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) (HE : pointAt c a ha hca=pointAt c b hb hcb) :
    RawReachable c a b :=
  ⟨ha,hb,hca,hcb,Relation.ReflTransGen.single
    (Or.inl ((identity_language_iff_pointAt_eq c a b ha hb hca hcb).mpr HE))⟩

noncomputable def PointReachable (c : List Bool) (p q : Fin (num c+4)→ℝ) : Prop :=
  ∃a b,∃ha : A a,∃hb : A b,∃hca : provider a=c,∃hcb : provider b=c,
    pointAt c a ha hca=p ∧ pointAt c b hb hcb=q ∧ RawReachable c a b

theorem point_reachable_iff_raw (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) :
    PointReachable c (pointAt c a ha hca) (pointAt c b hb hcb) ↔ RawReachable c a b := by
  constructor
  · rintro ⟨u,v,hu,hv,hcu,hcv,HEu,HEv,H⟩
    exact raw_reachable_trans (raw_reachable_trans
      (raw_reachable_of_pointAt_eq c a u ha hu hca hcu HEu.symm) H)
      (raw_reachable_of_pointAt_eq c v b hv hb hcv hcb HEv)
  · intro H
    exact ⟨a,b,ha,hb,hca,hcb,rfl,rfl,H⟩

theorem point_reachable_trans {c : List Bool} {p q r : Fin (num c+4)→ℝ}
    (h : PointReachable c p q) (k : PointReachable c q r) : PointReachable c p r := by
  obtain ⟨a,b,ha,hb,hca,hcb,HA,HB,H⟩ := h
  obtain ⟨u,v,hu,hv,hcu,hcv,HU,HV,K⟩ := k
  refine ⟨a,v,ha,hv,hca,hcv,HA,HV,?_⟩
  exact raw_reachable_trans (raw_reachable_trans H
    (raw_reachable_of_pointAt_eq c b u hb hu hcb hcu (HB.trans HU.symm))) K

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
