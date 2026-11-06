/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCoding
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAtomicGeometry
/-! # Entire provider graph points in one common spatial source -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem graph_cast_point_heq {n m : ℕ} (h : n=m) (p : Fin m→ℝ) :
    HEq (fun i : Fin n=>p (Fin.cast h i)) p := by cases h;rfl

local notation "Geo" => FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomicGeometry.source
  FormulaSignSlotRadialProviderAtomicGeometry.point

noncomputable def pointAt (c q : List Bool) (hq : A q) (hc : provider q=c) : Fin (num c+4)→ℝ := fun i=>
  FormulaSignSlotRadialProviderAtomicGeometry.point q hq
    (Fin.cast (congrArg (fun r=>num r+4) hc).symm i)

theorem pointAt_heq (c q : List Bool) (hq : A q) (hc : provider q=c) :
    HEq (FormulaSignSlotRadialProviderAtomicGeometry.point q hq) (pointAt c q hq hc) :=
  (graph_cast_point_heq (congrArg (fun r=>num r+4) hc).symm _).symm

theorem native_pointAt_heq (c q : List Bool) (hq : A q) (hc : provider q=c) :
    HEq (FormulaSignSlotRadialProviderAtomic.point q hq) (pointAt c q hq hc) :=
  (FormulaSignSlotRadialProviderAtomicGeometry.point_heq q hq).trans (pointAt_heq c q hq hc)

theorem pointAt_occurrence (c q : List Bool) (hq : A q) (hc : provider q=c) :
    IntegralMixedAtomicOccurrence.Occurrence (FormulaSignSlotRadialProviderAtomicGeometry.source c)
      (FormulaSignSlotRadialProviderAtomic.depth q) (FormulaSignSlotRadialProviderAtomic.levels q hq)
      (pointAt c q hq hc) := by
  subst c
  have HP := eq_of_heq (pointAt_heq (provider q) q hq rfl)
  exact (congrArg (fun p=>IntegralMixedAtomicOccurrence.Occurrence
    (FormulaSignSlotRadialProviderAtomicGeometry.source (provider q))
      (FormulaSignSlotRadialProviderAtomic.depth q) (FormulaSignSlotRadialProviderAtomic.levels q hq) p) HP).mp
    (FormulaSignSlotRadialProviderAtomicGeometry.occurrence q hq)

theorem pointAt_zero (c q : List Bool) (hq : A q) (hc : provider q=c) : pointAt c q hq hc∈Geo c := by
  subst c
  have HP := eq_of_heq (pointAt_heq (provider q) q hq rfl)
  exact (congrArg (fun p=>p∈Geo (provider q)) HP).mp
    (FormulaSignSlotRadialProviderAtomicGeometry.point_mem q hq)

theorem pointAt_eq_of_native_heq (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c)
    (hp : HEq (FormulaSignSlotRadialProviderAtomic.point a ha) (FormulaSignSlotRadialProviderAtomic.point b hb)) :
    pointAt c a ha hca=pointAt c b hb hcb :=
  eq_of_heq ((native_pointAt_heq c a ha hca).symm.trans (hp.trans (native_pointAt_heq c b hb hcb)))

private theorem identity_native_point_heq (q : List Bool) (hq : A q) :
    HEq (FormulaSignSlotRadialProviderIdentity.point q hq) (FormulaSignSlotRadialProviderAtomic.point q hq) := by
  unfold FormulaSignSlotRadialProviderIdentity.point
  exact graph_cast_point_heq (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm _

theorem identity_pointAt_eq (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c)
    (hi : LeanCanny.pair a b∈FormulaSignSlotRadialProviderIdentity.language) :
    pointAt c a ha hca=pointAt c b hb hcb := by
  have HE := (FormulaSignSlotRadialProviderIdentity.language_iff a b ha hb (hca.trans hcb.symm)).mp hi
  exact pointAt_eq_of_native_heq c a b ha hb hca hcb
    ((identity_native_point_heq a ha).symm.trans (HE.trans (identity_native_point_heq b hb)))

theorem identity_joined (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c)
    (hi : LeanCanny.pair a b∈FormulaSignSlotRadialProviderIdentity.language) :
    JoinedIn (Geo c) (pointAt c a ha hca) (pointAt c b hb hcb) := by
  rw [identity_pointAt_eq c a b ha hb hca hcb hi]
  exact JoinedIn.refl (pointAt_zero c b hb hcb)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
