/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicOccurrence
/-! # Actual atomic occurrences in the provider's common spatial coordinates -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAtomicGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank

private theorem transport_occurrence {n m : ℕ} (Q : SpatialSource n) (R : SpatialSource m)
    (hn : n=m) (hQ : HEq Q R) (k : ℕ) (levels : ℕ→ℝ) (p : Fin (n+1)→ℝ)
    (v : Fin (m+1)→ℝ) (he : HEq p v)
    (hp : IntegralMixedAtomicOccurrence.Occurrence Q k levels p) :
    IntegralMixedAtomicOccurrence.Occurrence R k levels v := by
  subst m
  cases eq_of_heq hQ
  cases eq_of_heq he
  exact hp

private theorem cast_point_heq {n m : ℕ} (h : n=m) (p : Fin (m+1)→ℝ) :
    HEq (fun i : Fin (n+1)=>p (Fin.cast (congrArg (·+1) h) i)) p := by cases h;rfl

theorem dimension_provider (q : List Bool) :
    (B).parameters.ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))=
      FormulaSignSlotRadialProviderMarkedGeometry.number (FormulaSignSlotRadialProviderAtomic.provider q)+3 :=
  (FormulaSignSlotRadialProviderAtomic.native_dimension q).trans
    (FormulaSignSlotRadialProviderAtomic.dimension_provider q)

attribute [local irreducible] FormulaSignSlotRadialExternalPrelude.spatial
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.source
  FormulaSignSlotRadialProviderAtomic.levels FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def source (c : List Bool) : SpatialSource (FormulaSignSlotRadialProviderMarkedGeometry.number c+3) :=
  FormulaSignSlotRadialProviderIntegerPlan.spatial c

theorem source_heq (c : List Bool) : HEq (source c) (FormulaSignSlotRadialProviderIntegerPlan.spatial c) := HEq.rfl

attribute [local irreducible] source

noncomputable def point (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    Fin (FormulaSignSlotRadialProviderMarkedGeometry.number (FormulaSignSlotRadialProviderAtomic.provider q)+4)→ℝ := fun i=>
  FormulaSignSlotRadialProviderAtomic.point q hv
    (Fin.cast (congrArg (·+1) (dimension_provider q).symm) i)

theorem point_heq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    HEq (FormulaSignSlotRadialProviderAtomic.point q hv) (point q hv) :=
  (cast_point_heq (dimension_provider q).symm _).symm

theorem occurrence (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    IntegralMixedAtomicOccurrence.Occurrence
      (source (FormulaSignSlotRadialProviderAtomic.provider q))
      (FormulaSignSlotRadialProviderAtomic.depth q) (FormulaSignSlotRadialProviderAtomic.levels q hv) (point q hv) :=
  transport_occurrence _ _ (dimension_provider q)
    ((FormulaSignSlotRadialProviderAtomic.source_provider q hv).trans
      (source_heq (FormulaSignSlotRadialProviderAtomic.provider q)).symm) _ _ _ _
    (point_heq q hv) (FormulaSignSlotRadialProviderAtomic.occurrence q hv)

theorem point_mem (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    point q hv∈FormulaSignSlotRadialProviderMarkedGeometry.zeroSet (FormulaSignSlotRadialProviderAtomic.provider q) := by
  simpa only [source,FormulaSignSlotRadialProviderMarkedGeometry.zeroSet,
    FormulaSignSlotRadialProviderMarkedGeometry.polynomial,Set.mem_ofPred_eq] using (occurrence q hv).zero

theorem point_heq_iff (a b : List Bool)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (hb : FormulaSignSlotRadialProviderAtomic.Valid b) :
    HEq (FormulaSignSlotRadialProviderAtomic.point a ha) (FormulaSignSlotRadialProviderAtomic.point b hb) ↔
      HEq (point a ha) (point b hb) :=
  ⟨fun h=>(point_heq a ha).symm.trans (h.trans (point_heq b hb)),
    fun h=>(point_heq a ha).trans (h.trans (point_heq b hb).symm)⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAtomicGeometry
