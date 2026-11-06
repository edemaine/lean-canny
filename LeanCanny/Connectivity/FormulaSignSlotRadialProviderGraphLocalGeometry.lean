/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphParentSlice
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
/-! # Actual ordinary-parent paths in the original fixed-provider source -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem local_family_source (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (a : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (key : List Bool) (Q : SpatialSource (p.ambient (pairFst key)))
    (hs : (IntegralMixedFramedHistoryFamilyBits.instruction p d key).source=d.initialSource (pairFst key))
    (hq : d.initialSource (pairFst key)=Q) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family p d a).spatial key) Q := heq_of_eq (hs.trans hq)

private theorem local_cast_heq {n m : ℕ} (h : n=m) (p : Fin m→ℝ) :
    HEq (fun i : Fin n=>p (Fin.cast h i)) p := by cases h;rfl

private theorem local_source_path {n m : ℕ} (Q : SpatialSource n) (R : SpatialSource m)
    (hd : n=m) (hs : HEq Q R) (p q : Fin (n+1)→ℝ) (r s : Fin (m+1)→ℝ)
    (hp : HEq p r) (hq : HEq q s)
    (H : JoinedIn {x |(FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) x=0} p q) :
    JoinedIn {x |(FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) x=0} r s := by
  cases hd
  cases eq_of_heq hs
  cases eq_of_heq hp
  cases eq_of_heq hq
  exact H

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "LF" => FormulaSignSlotRadialProviderProperLocalFrame.ambient
local notation "K" => FormulaSignSlotRadialProviderProperLocalFrame.oldKey
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomicGeometry.source
  FormulaSignSlotRadialProviderIdentity.point

theorem local_dimension_provider (q : List Bool) : LF q=num (provider q)+3 :=
  (FormulaSignSlotRadialProviderProperLocalFrame.ambient_eq q).trans (FormulaSignSlotRadialProviderAtomic.dimension_provider q)

theorem local_source_provider (q : List Bool) (hv : A q) :
    HEq ((G).spatial (K q)) (FormulaSignSlotRadialProviderAtomicGeometry.source (provider q)) := by
  have HP := local_family_source P D H (K q) _
    (FormulaSignSlotRadialProviderRecordPrefix.instruction_initial (K q))
    (FormulaSignSlotRadialProviderRecordPrefix.initial_source (pairFst (K q)))
  have HC : FormulaSignSlotRadialProviderRecordPlan.providerContext (pairFst (K q))=
      FormulaSignSlotRadialProviderRecordPlan.providerContext
        (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot q (FormulaSignSlotRadialProviderAtomic.ownBirth q)) := by
    unfold FormulaSignSlotRadialProviderProperLocalFrame.oldKey
    rw [FormulaSignSlotRadialProviderProperRow.parentKey_root,FormulaSignSlotRadialProviderProperRow.root_provider,
      FormulaSignSlotRadialProviderRetainedAppend.prepared_provider,FormulaSignSlotRadialProviderAtomic.root_provider]
    simp only [FormulaSignSlotRadialProviderProperRow.atomic,FormulaSignSlotRadialProviderProperLocalFrame.rowKey,pairFst_pair]
  exact HP.trans ((FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ HC).trans (parent_source_provider q hv))

theorem local_point_dimension (c q : List Bool) (hc : provider q=c) : LF q+1=num c+4 := by
  have HN := local_dimension_provider q
  rw [hc] at HN
  omega

noncomputable def midpointAt (c q : List Bool) (hv : A q) (hc : provider q=c) : Fin (num c+4)→ℝ := fun i=>
  FormulaSignSlotRadialProviderProperLocalFrame.midpoint q hv (Fin.cast (local_point_dimension c q hc).symm i)

theorem midpointAt_heq (c q : List Bool) (hv : A q) (hc : provider q=c) :
    HEq (FormulaSignSlotRadialProviderProperLocalFrame.midpoint q hv) (midpointAt c q hv hc) :=
  (local_cast_heq (local_point_dimension c q hc).symm _).symm

theorem local_child_native_heq (q : List Bool) (hv : A q) :
    HEq (FormulaSignSlotRadialProviderProperLocalFrame.child q hv) (FormulaSignSlotRadialProviderAtomic.point q hv) := by
  have HC : HEq (FormulaSignSlotRadialProviderProperLocalFrame.child q hv)
      (FormulaSignSlotRadialProviderIdentity.point q hv) := by
    unfold FormulaSignSlotRadialProviderProperLocalFrame.child
    exact local_cast_heq (congrArg (·+1) (FormulaSignSlotRadialProviderProperLocalFrame.ambient_eq q)) _
  have HI : HEq (FormulaSignSlotRadialProviderIdentity.point q hv) (FormulaSignSlotRadialProviderAtomic.point q hv) := by
    unfold FormulaSignSlotRadialProviderIdentity.point
    exact local_cast_heq (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm _
  exact HC.trans HI

theorem prepared_path_provider (q : List Bool) (hv : A q)
    (HP : JoinedIn {p |(FermatCriticalHomogenization.polynomial ((G).spatial (K q)).low
      ((G).spatial (K q)).leading ((G).spatial (K q)).degree).eval₂ (Int.castRingHom ℝ) p=0}
      (FormulaSignSlotRadialProviderProperLocalFrame.child q hv)
      (FormulaSignSlotRadialProviderProperLocalFrame.midpoint q hv)) :
    JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet (provider q))
      (pointAt (provider q) q hv rfl) (midpointAt (provider q) q hv rfl) := by
  have HG := local_source_path ((G).spatial (K q))
    (FormulaSignSlotRadialProviderAtomicGeometry.source (provider q)) (local_dimension_provider q)
    (local_source_provider q hv) _ _ _ _
    ((local_child_native_heq q hv).trans (native_pointAt_heq _ q hv rfl)) (midpointAt_heq _ q hv rfl) HP
  simpa only [FormulaSignSlotRadialProviderAtomicGeometry.source,
    FormulaSignSlotRadialProviderMarkedGeometry.zeroSet,FormulaSignSlotRadialProviderMarkedGeometry.polynomial] using HG

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
