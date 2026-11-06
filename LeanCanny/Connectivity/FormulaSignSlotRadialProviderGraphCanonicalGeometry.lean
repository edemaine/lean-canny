/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphParentSlice
public import LeanCanny.Geometry.IntegralMixedJointSlabEndpointSet
/-! # Actual accepted points are critical points of the canonical parent slice -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderRetainedAppend (preparedRoot parentDescriptor parentValues)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem canonical_proper_transport {n m : ℕ} (Q : SpatialSource n) (R : SpatialSource m)
    (hn : n=m) (hs : HEq Q R)
    (h : IsProperMap (fun p : Fin (m+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) p)) :
    IsProperMap (fun p : Fin (n+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p) := by
  cases hn
  cases eq_of_heq hs
  exact h

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "dim" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderAtomicGeometry.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot

theorem parent_source_proper (old : List Bool) (hv : A old) :
    IsProperMap (fun p : Fin ((P).ambient (preparedRoot old (E old))+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot old (E old))).low
        (Q (preparedRoot old (E old))).leading (Q (preparedRoot old (E old))).degree).eval₂ (Int.castRingHom ℝ) p) := by
  apply canonical_proper_transport (Q (preparedRoot old (E old)))
    (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old))
    (parent_dimension_provider old) (parent_source_provider old hv)
  simpa only [FormulaSignSlotRadialProviderAtomicGeometry.source,FormulaSignSlotRadialProviderMarkedGeometry.polynomial]
    using FormulaSignSlotRadialProviderMarkedGeometry.proper (provider old)

variable (old : List Bool) (hv : A old) (hd : depth old<dim old)
local notation "r" => preparedRoot old (E old)
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "d" => parentDescriptor old hv hd (E old) he
local notation "V" => parentValues old hv hd (E old) he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd (E old) he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk

include hv in
theorem canonical_occurrence_of_pointAt (q : List Bool) (hq : A q)
    (hp : provider q=provider old) (ht : depth q=depth old) :
    IntegralMixedAtomicOccurrence.Occurrence (Q r) (depth old) (FormulaSignSlotRadialProviderAtomic.levels q hq)
      (parentPoint old (pointAt (provider old) q hq hp)) := by
  have H := parentPoint_occurrence old hv (pointAt (provider old) q hq hp) (depth q)
    (FormulaSignSlotRadialProviderAtomic.levels q hq) (pointAt_occurrence (provider old) q hq hp)
  simpa only [ht] using H

theorem canonical_height_mem_realCriticalValues (q : List Bool) (hq : A q)
    (hp : provider q=provider old) (ht : depth q=depth old)
    (HS : pointAt (provider old) q hq hp∈frozenSlice (provider old) (depth old)
      (FormulaSignSlotRadialProviderAtomic.levels old hv)) :
    parentPoint old (pointAt (provider old) q hq hp) h∈realCriticalValues (Q r) (line (d).frame h) V h := by
  have HO := canonical_occurrence_of_pointAt old hv q hq hp ht
  have HL := FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old) he
  apply (line_realCriticalValues_iff (Q r) (d).frame V h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).free_normal _).mpr
  refine ⟨parentPoint old (pointAt (provider old) q hq hp),(parent_slice_iff old hv hd _).mpr HS,rfl,?_⟩
  intro i hi hih
  have HI : depth old≤ i.val := by
    have HF : ¬i.val<(d).labels.length := fun H=>hi (((d).frozen_mem i).mpr H)
    omega
  have HNe : i.val≠depth old := by
    intro HE
    apply hih
    apply Fin.ext
    exact HE.trans HL.symm
  exact HO.critical i HI HNe

theorem canonical_child_partials (q : List Bool) (hq : A q)
    (hp : provider q=provider old) (ht : depth q=depth old) :
    ∀i,i∉(line (d).frame h).frozen→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) (parentPoint old (pointAt (provider old) q hq hp))=0 := by
  have HO := canonical_occurrence_of_pointAt old hv q hq hp ht
  have HL := FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old) he
  intro i hi
  have HF := (IntegralMixedChronologicalSweepFrame.free_iff d hk i).mp hi
  have HI : depth old< i.val := by omega
  exact HO.critical i HI.le (Nat.ne_of_gt HI)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
