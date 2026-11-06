/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCriticalEndpoints
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint
/-! # Actual external points in the paired OLD provider's canonical source -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderPairGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderRetainedAppend (preparedRoot parentDescriptor parentValues)
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def castPoint {n m :ℕ} (h :n=m) (p :Fin m→ℝ) :Fin n→ℝ:=fun i=>p (Fin.cast h i)
private theorem cast_heq {n m :ℕ} (h :n=m) (p :Fin m→ℝ) :
    HEq (castPoint h p) p:=by cases h;rfl
attribute [local irreducible] castPoint

private theorem source_congr (c d :List Bool) (h :c=d) :
    HEq (FormulaSignSlotRadialProviderAtomicGeometry.source c)
      (FormulaSignSlotRadialProviderAtomicGeometry.source d):=by cases h;rfl

private theorem occurrence_transport {n m :ℕ} (Q :SpatialSource n) (R :SpatialSource m)
    (hd :n=m) (hs :HEq Q R) (p :Fin (n+1)→ℝ) (q :Fin (m+1)→ℝ) (hp :HEq p q)
    (k :ℕ) (values :ℕ→ℝ) (ho :IntegralMixedAtomicOccurrence.Occurrence Q k values p) :
    IntegralMixedAtomicOccurrence.Occurrence R k values q:=by
  cases hd
  cases eq_of_heq hs
  cases eq_of_heq hp
  exact ho

local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "depth"=>FormulaSignSlotRadialProviderAtomic.depth
local notation "dim"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q"=>FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "E"=>FormulaSignSlotRadialProviderAtomic.ownBirth
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderAtomicGeometry.source
  FormulaSignSlotRadialProviderAtomicGeometry.point FormulaSignSlotRadialProviderAtomic.point
  FormulaSignSlotRadialProviderAtomic.levels FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues

theorem number_oldOf (c :List Bool) :num (FormulaSignSlotRadialProviderPair.oldOf c)=num c:=by
  exact congrArg CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialProviderPair.original_oldOf c)

theorem number_pair (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :num (provider old)=num (provider ext):=
  (congrArg num hp).trans (number_oldOf (provider ext))

theorem source_pair (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    HEq (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old))
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider ext)):=
  (source_congr _ _ hp).trans
    ((FormulaSignSlotRadialProviderAtomicGeometry.source_heq _).trans
      ((FormulaSignSlotRadialProviderPair.spatial_shared _).trans
        (FormulaSignSlotRadialProviderAtomicGeometry.source_heq _).symm))

noncomputable def externalPoint (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext) :
    Fin (num (provider old)+4)→ℝ:=
  castPoint (congrArg (·+4) (number_pair old ext hp)) (FormulaSignSlotRadialProviderAtomicGeometry.point ext he)

theorem externalPoint_heq (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext) :
    HEq (externalPoint old ext hp he) (FormulaSignSlotRadialProviderAtomicGeometry.point ext he):=
  cast_heq (congrArg (·+4) (number_pair old ext hp)) _

theorem externalPoint_native_heq (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext) :
    HEq (FormulaSignSlotRadialProviderAtomic.point ext he) (externalPoint old ext hp he):=
  (FormulaSignSlotRadialProviderAtomicGeometry.point_heq ext he).trans (externalPoint_heq old ext hp he).symm

attribute [local irreducible] externalPoint

theorem external_occurrence (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext) :
    IntegralMixedAtomicOccurrence.Occurrence (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old))
      (depth ext) (FormulaSignSlotRadialProviderAtomic.levels ext he) (externalPoint old ext hp he):=
  occurrence_transport _ _ (congrArg (·+3) (number_pair old ext hp)).symm (source_pair old ext hp).symm
    _ _ (externalPoint_heq old ext hp he).symm _ _ (FormulaSignSlotRadialProviderAtomicGeometry.occurrence ext he)

theorem external_mem (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext) :
    externalPoint old ext hp he∈FormulaSignSlotRadialProviderMarkedGeometry.zeroSet (provider old):=by
  simpa only [FormulaSignSlotRadialProviderAtomicGeometry.source,
    FormulaSignSlotRadialProviderMarkedGeometry.zeroSet,FormulaSignSlotRadialProviderMarkedGeometry.polynomial,
    Set.mem_ofPred_eq] using (external_occurrence old ext hp he).zero

theorem depth_zero_room (old :List Bool) (h0 :depth old=0) :depth old<dim old:=by
  have HD:dim old=num (provider old)+3:=FormulaSignSlotRadialProviderAtomic.dimension_provider old
  omega

theorem external_frozen (old :List Bool) (hv :A old) (h0 :depth old=0) (ext :List Bool)
    (he :A ext) (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    externalPoint old ext hp he∈frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv):=by
  refine ⟨external_mem old ext hp he,?_⟩
  intro i hi
  omega

noncomputable def externalCanonicalPoint (old ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he :A ext):=
  parentPoint old (externalPoint old ext hp he)

theorem external_canonical_occurrence (old :List Bool) (hv :A old) (ext :List Bool) (he :A ext)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    IntegralMixedAtomicOccurrence.Occurrence (Q (preparedRoot old (E old))) (depth ext)
      (FormulaSignSlotRadialProviderAtomic.levels ext he) (externalCanonicalPoint old ext hp he):=
  parentPoint_occurrence old hv _ _ _ (external_occurrence old ext hp he)

variable (old :List Bool) (hv :A old) (h0 :depth old=0)
local notation "hd"=>depth_zero_room old h0
local notation "he0"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "r"=>preparedRoot old (E old)
local notation "d"=>parentDescriptor old hv hd (E old) he0
local notation "V"=>parentValues old hv hd (E old) he0
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd (E old) he0
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk

include hv h0 in
theorem external_canonical_slice (ext :List Bool) (he :A ext)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    externalCanonicalPoint old ext hp he∈slice (Q r) (d).frame V:=
  (parent_slice_iff old hv hd _).mpr (external_frozen old hv h0 ext he hp)

theorem external_height_mem_realCriticalValues (ext :List Bool) (he :A ext) (hExt0 :depth ext=0)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    externalCanonicalPoint old ext hp he h∈realCriticalValues (Q r) (line (d).frame h) V h:=by
  have HO:=external_canonical_occurrence old hv ext he hp
  have HL:=FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old) he0
  apply (line_realCriticalValues_iff (Q r) (d).frame V h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).free_normal _).mpr
  refine ⟨externalCanonicalPoint old ext hp he,external_canonical_slice old hv h0 ext he hp,rfl,?_⟩
  intro i _ hih
  apply HO.critical i (by omega)
  intro HI
  apply hih
  apply Fin.ext
  exact (HI.trans hExt0).trans (h0.symm.trans HL.symm)

theorem external_child_partials (ext :List Bool) (he :A ext) (hExt0 :depth ext=0)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    ∀i,i∉(line (d).frame h).frozen→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) (externalCanonicalPoint old ext hp he)=0:=by
  have HO:=external_canonical_occurrence old hv ext he hp
  have HL:=FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old) he0
  intro i hi
  have HF:=(IntegralMixedChronologicalSweepFrame.free_iff d hk i).mp hi
  have HI:depth ext < i.val:=by omega
  exact HO.critical i HI.le (Nat.ne_of_gt HI)

local notation "x"=>FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd (E old) he0
local notation "hm"=>FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd (E old) he0
local notation "phi"=>FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd (E old) he0
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd (E old) he0
local notation "hg"=>FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd (E old) he0
local notation "choices"=>FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd (E old) he0

theorem external_height_mem_jointEndpointSet (ext :List Bool) (he :A ext) (hExt0 :depth ext=0)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    externalCanonicalPoint old ext hp he h∈jointEndpointSet x hm phi (d).frame h g hg V choices:=
  Or.inr (external_height_mem_realCriticalValues old hv h0 ext he hExt0 hp)

omit hv h0 in
theorem compatible_representative (ext :List Bool)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext))
    (q :List Bool) (hq :provider q=provider old) :
    FormulaSignSlotRadialProviderCrossPoint.Compatible (pair q ext):=by
  constructor
  · have HO:FormulaSignSlotRadialProviderIntegerPlan.original (provider q)=
        FormulaSignSlotRadialProviderIntegerPlan.original (provider ext):=by
      rw [hq,hp]
      exact FormulaSignSlotRadialProviderPair.original_oldOf _
    simpa only [FormulaSignSlotRadialProviderCrossPoint.SameOriginal,pairFst_pair,pairSnd_pair,
      FormulaSignSlotRadialProviderAtomic.original] using HO
  · have HR:FormulaSignSlotRadialExternalPrelude.radius (provider q)=
        FormulaSignSlotRadialExternalPrelude.radius (provider ext):=by
      rw [hq,hp]
      exact FormulaSignSlotRadialProviderPair.radius_oldOf _
    simpa only [FormulaSignSlotRadialProviderCrossPoint.SameRadius,FormulaSignSlotRadialProviderCrossPoint.radius,
      pairFst_pair,pairSnd_pair] using HR

omit hv h0 in
theorem crossPoint_iff (ext :List Bool) (he :A ext)
    (hp :provider old=FormulaSignSlotRadialProviderPair.oldOf (provider ext))
    (q :List Bool) (hq :A q) (hprovider :provider q=provider old) :
    pair q ext∈FormulaSignSlotRadialProviderCrossPoint.language ↔
      pointAt (provider old) q hq hprovider=externalPoint old ext hp he:=by
  rw [FormulaSignSlotRadialProviderCrossPoint.language_native_iff q ext hq he
    (compatible_representative old ext hp q hprovider)]
  have HL:=native_pointAt_heq (provider old) q hq hprovider
  have HR:=externalPoint_native_heq old ext hp he
  constructor
  · intro HE
    exact eq_of_heq (HL.symm.trans (HE.trans HR))
  · intro HE
    exact HL.trans ((heq_of_eq HE).trans HR.symm)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderPairGeometry
