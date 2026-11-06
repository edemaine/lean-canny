/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphFiberInduction
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
/-! # The actual canonical parent slice is the provider's original frozen slice -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderRetainedAppend (preparedRoot parentDescriptor parentValues)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem descriptor_frozen_iff {n b : ℕ} (Q : SpatialSource n)
    (d : IntegralMixedChronologicalFrame.Descriptor n b) (v : Fin b→ℝ) (k : ℕ) (levels : ℕ→ℝ)
    (hk : d.labels.length=k) (hv : ∀i,v (d.reference i)=levels i.val) (p : Fin (n+1)→ℝ) :
    p∈slice Q d.frame v ↔
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
        ∀i : Fin (n+1),i.val<k→p i=levels i.val := by
  rw [d.slice_iff]
  constructor
  · rintro ⟨hz,hf⟩
    refine ⟨hz,fun i hi=>?_⟩
    have HI : i.val<d.labels.length := hi.trans_eq hk.symm
    exact (hf ⟨i.val,HI⟩).trans (hv ⟨i.val,HI⟩)
  · rintro ⟨hz,hf⟩
    exact ⟨hz,fun i=>(hf ⟨i.val,i.isLt.trans_le d.length_le⟩ (i.isLt.trans_eq hk)).trans (hv i).symm⟩

private theorem frozen_point_transport {n m : ℕ} (Q : SpatialSource n) (R : SpatialSource m)
    (hd : n=m) (hs : HEq Q R) (p : Fin (n+1)→ℝ) (q : Fin (m+1)→ℝ) (hp : HEq p q)
    (k : ℕ) (levels : ℕ→ℝ) :
    ((FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i : Fin (n+1),i.val<k→p i=levels i.val) ↔
    ((FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) q=0 ∧
      ∀i : Fin (m+1),i.val<k→q i=levels i.val) := by
  cases hd
  cases eq_of_heq hs
  cases eq_of_heq hp
  rfl

private theorem parent_cast_heq {n m : ℕ} (h : n=m) (p : Fin m→ℝ) :
    HEq (fun i : Fin n=>p (Fin.cast h i)) p := by cases h;rfl

private theorem parent_cast_continuous {n m : ℕ} (h : n=m) :
    Continuous (fun (p : Fin m→ℝ) (i : Fin n)=>p (Fin.cast h i)) :=
  continuous_pi (fun _=>continuous_apply _)

private theorem parent_occurrence_transport {n m : ℕ} (Q : SpatialSource n) (R : SpatialSource m)
    (hd : n=m) (hs : HEq Q R) (p : Fin (n+1)→ℝ) (q : Fin (m+1)→ℝ) (hp : HEq p q)
    (k : ℕ) (levels : ℕ→ℝ) (ho : IntegralMixedAtomicOccurrence.Occurrence Q k levels p) :
    IntegralMixedAtomicOccurrence.Occurrence R k levels q := by
  cases hd
  cases eq_of_heq hs
  cases eq_of_heq hp
  exact ho

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
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.levels
  FormulaSignSlotRadialProviderAtomicGeometry.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot

theorem parent_dimension_provider (old : List Bool) :
    (P).ambient (preparedRoot old (E old))=num (provider old)+3 :=
  (FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old (E old)).trans
    ((FormulaSignSlotRadialProviderAtomic.native_dimension old).symm.trans
      (FormulaSignSlotRadialProviderAtomicGeometry.dimension_provider old))

theorem parent_point_dimension (old : List Bool) :
    (P).ambient (preparedRoot old (E old))+1=num (provider old)+4 := by
  have H := parent_dimension_provider old
  omega

noncomputable def parentPoint (old : List Bool) (p : Fin (num (provider old)+4)→ℝ) :
    Fin ((P).ambient (preparedRoot old (E old))+1)→ℝ := fun i=>
  p (Fin.cast (parent_point_dimension old) i)

theorem parentPoint_heq (old : List Bool) (p : Fin (num (provider old)+4)→ℝ) : HEq (parentPoint old p) p :=
  parent_cast_heq (parent_point_dimension old) p

theorem parent_source_provider (old : List Bool) (hv : A old) :
    HEq (Q (preparedRoot old (E old))) (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)) :=
  (FormulaSignSlotRadialProviderRetainedAppend.own_source_heq old hv).symm.trans
    ((FormulaSignSlotRadialProviderAtomic.source_provider old hv).trans
      (FormulaSignSlotRadialProviderAtomicGeometry.source_heq _).symm)

theorem parent_slice_iff (old : List Bool) (hv : A old) (hd : depth old<dim old)
    (p : Fin (num (provider old)+4)→ℝ) :
    parentPoint old p∈slice (Q (preparedRoot old (E old)))
      (parentDescriptor old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)).frame
      (parentValues old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)) ↔
      p∈frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv) := by
  have HD := descriptor_frozen_iff (Q (preparedRoot old (E old)))
    (parentDescriptor old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old))
    (parentValues old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old))
    (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv)
    (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old)
      (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old))
    (FormulaSignSlotRadialProviderRetainedAppend.parent_frozen_value old hv hd (E old)
      (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)) (parentPoint old p)
  have HT := frozen_point_transport _ _ (parent_dimension_provider old) (parent_source_provider old hv)
    (parentPoint old p) p (parentPoint_heq old p) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv)
  simpa only [frozenSlice,FormulaSignSlotRadialProviderAtomicGeometry.source,
    FormulaSignSlotRadialProviderMarkedGeometry.zeroSet,FormulaSignSlotRadialProviderMarkedGeometry.polynomial,
    Set.inter_def,Set.mem_ofPred_eq] using HD.trans HT

theorem parentPoint_continuous (old : List Bool) : Continuous (parentPoint old) :=
  parent_cast_continuous (parent_point_dimension old)

theorem parentPoint_occurrence (old : List Bool) (hv : A old)
    (p : Fin (num (provider old)+4)→ℝ) (k : ℕ) (levels : ℕ→ℝ)
    (ho : @IntegralMixedAtomicOccurrence.Occurrence (num (provider old)+3)
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)) k levels p) :
    @IntegralMixedAtomicOccurrence.Occurrence ((P).ambient (preparedRoot old (E old)))
      (Q (preparedRoot old (E old))) k levels (parentPoint old p) :=
  parent_occurrence_transport _ _ (parent_dimension_provider old).symm (parent_source_provider old hv).symm
    p (parentPoint old p) (parentPoint_heq old p).symm k levels ho

theorem parent_joinedIn (old : List Bool) (hv : A old) (hd : depth old<dim old)
    (p q : Fin (num (provider old)+4)→ℝ)
    (HP : JoinedIn (frozenSlice (provider old) (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv)) p q) :
    JoinedIn (slice (Q (preparedRoot old (E old)))
      (parentDescriptor old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)).frame
      (parentValues old hv hd (E old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)))
      (parentPoint old p) (parentPoint old q) := by
  apply (HP.map (parentPoint_continuous old).continuousOn).mono
  rintro _ ⟨p,hp,rfl⟩
  exact (parent_slice_iff old hv hd p).mpr hp

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
