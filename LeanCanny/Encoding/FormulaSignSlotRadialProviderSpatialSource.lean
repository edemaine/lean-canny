/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
/-! # Provider spatial sources depend on the original and the actual radius

Metadata can change the integer root sources. A common spatial source needs
both the original term and the chosen radius to agree.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderSpatialSource
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceAt (n : ℕ) (term : List Bool) (r : ℕ) : SpatialSource (n+3) :=
  BoundedRegularLowModularTerm.source
    ({dim := fun _=>n,source := fun _=>term,radius := fun _=>r} : BoundedFullWriter.Readers) []

private theorem source_pointwise (P : BoundedFullWriter.Readers) (c : List Bool) :
    HEq (BoundedRegularLowModularTerm.source P c) (sourceAt (P.dim c) (P.source c) (P.radius c)) := HEq.rfl

private theorem sourceAt_congr (n m : ℕ) (s t : List Bool) (r v : ℕ)
    (hn : n=m) (hs : s=t) (hr : r=v) : HEq (sourceAt n s r) (sourceAt m t v) := by
  cases hn
  cases hs
  cases hr
  rfl

theorem spatial_heq (c d : List Bool)
    (ho : FormulaSignSlotRadialProviderIntegerPlan.original c=FormulaSignSlotRadialProviderIntegerPlan.original d)
    (hr : FormulaSignSlotRadialProviderIntegerPlan.radius c=FormulaSignSlotRadialProviderIntegerPlan.radius d) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial c) (FormulaSignSlotRadialProviderIntegerPlan.spatial d) := by
  have HE : HEq
      (sourceAt (FormulaSignSlotRadialProviderIntegerPlan.readers.dim c)
        (FormulaSignSlotRadialProviderIntegerPlan.readers.source c) (FormulaSignSlotRadialProviderIntegerPlan.readers.radius c))
      (sourceAt (FormulaSignSlotRadialProviderIntegerPlan.readers.dim d)
        (FormulaSignSlotRadialProviderIntegerPlan.readers.source d) (FormulaSignSlotRadialProviderIntegerPlan.readers.radius d)) := by
    apply sourceAt_congr
    · exact congrArg LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension ho
    · exact congrArg (fun u=>(LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation u).toData.toBits) ho
    · exact hr
  exact (source_pointwise FormulaSignSlotRadialProviderIntegerPlan.readers c).trans
    (HE.trans (source_pointwise FormulaSignSlotRadialProviderIntegerPlan.readers d).symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderSpatialSource
