/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalGeometry
/-! # Arbitrary canonical points and paths in the fixed provider coordinates -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderRetainedAppend (preparedRoot parentDescriptor parentValues)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem reverse_cast_heq {n m : ℕ} (h : n=m) (p : Fin n→ℝ) :
    HEq (fun i : Fin m=>p (Fin.cast h.symm i)) p := by cases h;rfl

private theorem cast_inverse {n m : ℕ} (h : n=m) (p : Fin n→ℝ) :
    (fun i : Fin n=>p (Fin.cast h.symm (Fin.cast h i)))=p := by cases h;rfl

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "dim" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentValues

noncomputable def providerPoint (old : List Bool)
    (p : Fin ((P).ambient (preparedRoot old (E old))+1)→ℝ) : Fin (num (provider old)+4)→ℝ :=
  fun i=>p (Fin.cast (parent_point_dimension old).symm i)

theorem providerPoint_heq (old : List Bool)
    (p : Fin ((P).ambient (preparedRoot old (E old))+1)→ℝ) : HEq (providerPoint old p) p :=
  reverse_cast_heq (parent_point_dimension old) p

theorem parentPoint_providerPoint (old : List Bool)
    (p : Fin ((P).ambient (preparedRoot old (E old))+1)→ℝ) : parentPoint old (providerPoint old p)=p :=
  cast_inverse (parent_point_dimension old) p

theorem providerPoint_parentPoint (old : List Bool) (p : Fin (num (provider old)+4)→ℝ) :
    providerPoint old (parentPoint old p)=p :=
  cast_inverse (parent_point_dimension old).symm p

theorem providerPoint_continuous (old : List Bool) : Continuous (providerPoint old) :=
  continuous_pi (fun _=>continuous_apply _)

variable (old : List Bool) (hv : A old) (hd : depth old<dim old)
local notation "r" => preparedRoot old (E old)
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "d" => parentDescriptor old hv hd (E old) he
local notation "V" => parentValues old hv hd (E old) he

theorem providerPoint_slice_iff (p : Fin ((P).ambient r+1)→ℝ) :
    providerPoint old p∈frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv) ↔
      p∈slice (Q r) (d).frame V := by
  simpa only [parentPoint_providerPoint] using (parent_slice_iff old hv hd (providerPoint old p)).symm

theorem providerPoint_slice_image :
    providerPoint old '' slice (Q r) (d).frame V=
      frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv) := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (providerPoint_slice_iff old hv hd q).mpr hq
  · intro hp
    exact ⟨parentPoint old p,(parent_slice_iff old hv hd p).mpr hp,providerPoint_parentPoint old p⟩

theorem providerPoint_joined_iff (p q : Fin ((P).ambient r+1)→ℝ) :
    JoinedIn (frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv))
      (providerPoint old p) (providerPoint old q) ↔ JoinedIn (slice (Q r) (d).frame V) p q := by
  constructor
  · intro H
    simpa only [parentPoint_providerPoint] using parent_joinedIn old hv hd _ _ H
  · intro H
    apply (H.map (providerPoint_continuous old).continuousOn).mono
    rintro _ ⟨x,hx,rfl⟩
    exact (providerPoint_slice_iff old hv hd x).mpr hx

theorem providerPoint_eq_pointAt_of_native_heq (q : List Bool) (hq : A q)
    (hp : provider q=provider old) (p : Fin ((P).ambient r+1)→ℝ)
    (HE : HEq (FormulaSignSlotRadialProviderAtomic.point q hq) p) :
    providerPoint old p=pointAt (provider old) q hq hp := by
  exact eq_of_heq ((providerPoint_heq old p).trans (HE.symm.trans (native_pointAt_heq _ q hq hp)))

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
