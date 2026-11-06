/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphLocalGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphSymmetry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderProperLocalPath
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointEquality
/-! # Actual native proper edges and paths lie in one original provider component -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "Geo" => FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderProperLocalFrame.midpoint midpointAt

theorem proper_midpointAt_eq (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) (H : FormulaSignSlotRadialProviderEdge.Proper (LeanCanny.pair a b)) :
    midpointAt c a ha hca=midpointAt c b hb hcb :=
  eq_of_heq ((midpointAt_heq c a ha hca).symm.trans
    ((FormulaSignSlotRadialProviderProperMidSignature.proper_midpoint_eq a b ha hb H).trans (midpointAt_heq c b hb hcb)))

theorem local_joinedAt (c q : List Bool) (hv : A q) (hc : provider q=c)
    (H : FormulaSignSlotRadialProviderLocalEdge.Local q) :
    JoinedIn (Geo c) (pointAt c q hv hc) (midpointAt c q hv hc) := by
  subst c
  exact prepared_path_provider q hv (FormulaSignSlotRadialProviderProperLocalFrame.local_joined q H)

theorem proper_joined (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) (H : FormulaSignSlotRadialProviderEdge.Proper (LeanCanny.pair a b)) :
    JoinedIn (Geo c) (pointAt c a ha hca) (pointAt c b hb hcb) := by
  have HL : FormulaSignSlotRadialProviderLocalEdge.Local a := by simpa only [pairFst_pair] using H.2.1
  have HR : FormulaSignSlotRadialProviderLocalEdge.Local b := by simpa only [pairSnd_pair] using H.2.2.1
  have HA := local_joinedAt c a ha hca HL
  have HB := local_joinedAt c b hb hcb HR
  rw [proper_midpointAt_eq c a b ha hb hca hcb H] at HA
  exact HA.trans HB.symm

theorem adjacent_joined (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : provider a=c) (hcb : provider b=c) (H : FormulaSignSlotRadialProviderEdge.Adjacent a b) :
    JoinedIn (Geo c) (pointAt c a ha hca) (pointAt c b hb hcb) := by
  rcases H with HI|HP
  · exact identity_joined c a b ha hb hca hcb HI
  · exact proper_joined c a b ha hb hca hcb HP

theorem path_joined (c a b : List Bool) (ha : A a) (hca : provider a=c)
    (H : Relation.ReflTransGen FormulaSignSlotRadialProviderEdge.Adjacent a b) (hb : A b) (hcb : provider b=c) :
    JoinedIn (Geo c) (pointAt c a ha hca) (pointAt c b hb hcb) := by
  revert hb hcb
  induction H with
  | refl => intro _ _;exact JoinedIn.refl (pointAt_zero c a ha hca)
  | @tail b d _ HE IH =>
    intro hd hcd
    have HB := (FormulaSignSlotRadialProviderEdge.valid b d HE).1
    have HC := (FormulaSignSlotRadialProviderEdge.provider_eq b d HE).trans hcd
    exact (IH HB HC).trans (adjacent_joined c b d HB hd HC hcd HE)

theorem raw_reachable_joined (c a b : List Bool) (H : RawReachable c a b) :
    JoinedIn (Geo c) (pointAt c a H.1 H.2.2.1) (pointAt c b H.2.1 H.2.2.2.1) :=
  path_joined c a b H.1 H.2.2.1 H.2.2.2.2 H.2.1 H.2.2.2.1

theorem PointReachable.joined {c : List Bool} {p q : Fin (num c+4)→ℝ} (H : PointReachable c p q) :
    JoinedIn (Geo c) p q := by
  obtain ⟨a,b,ha,hb,hca,hcb,rfl,rfl,HP⟩ := H
  exact raw_reachable_joined c a b HP

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
