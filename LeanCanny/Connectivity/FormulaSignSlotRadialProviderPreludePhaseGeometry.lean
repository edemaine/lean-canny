/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicReplayFields
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludeTargetGeometry
/-! # Same-provider marked preludes lie in the same actual component

Replay fixes their original projections. Auxiliary marked phases may differ.
No attachment of a word's current critical point is assumed or inferred.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludePhaseGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "field"=>FormulaSignSlotRadialProviderAtomic.field
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "Geo"=>FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "Eqn"=>FormulaSignSlotRadialProviderMarkedGeometry.equation
local notation "Allow"=>FormulaSignSlotRadialProviderMarkedGeometry.allowance
local notation "Radius"=>FormulaSignSlotRadialProviderMarkedGeometry.radius

noncomputable def markedAt (c q :List Bool) (hv:A q) (hc:provider q=c) :
    BoundedRegularSource.Marked (Eqn c) (Allow c) (Allow c) (Radius c):=
  hc ▸ FormulaSignSlotRadialProviderAtomic.MarkedPrelude.markedPoint q hv

theorem markedAt_values (c q :List Bool) (hv:A q) (hc:provider q=c) :
    (markedAt c q hv hc).val.val=preludeAt c q hv hc:=by
  subst c
  funext i
  exact FormulaSignSlotRadialProviderAtomic.MarkedPrelude.markedPoint_coordinate q hv i

theorem markedAt_projection (c q :List Bool) (hv:A q) (hc:provider q=c) (i:Fin (num c)) :
    (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c q hv hc)).val i=field q hv i.val:=by
  subst c
  exact FormulaSignSlotRadialProviderAtomic.MarkedPrelude.projection_coordinate q hv i

private theorem external_fields_at (c q :List Bool) (hv:A q) (hc:provider q=c)
    (he:FormulaSignSlotRadialExternalContext.external c) :
    ∃hp:FormulaSignSlotRadialExternalReplay.accepted c,∀i<num c,
      FormulaSignSlotRadialExternalCoordinates.point c
        (FormulaSignSlotRadialExternalReplay.accepted_valid c hp) i=field q hv i:=by
  subst c
  exact FormulaSignSlotRadialProviderAtomic.ReplayFields.external_fields q hv he

private theorem old_fields_at (c q :List Bool) (hv:A q) (hc:provider q=c)
    (he:¬FormulaSignSlotRadialExternalContext.external c) :
    ∃hp:IntegralMixedAuxiliaryCandidate.Valid CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope (pairFst c),
      ∀i:Fin (num c),IntegralMixedAuxiliaryCandidate.point
        CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
        CanonicalAuxiliaryCandidateCover.equation_scope (pairFst c) hp i=field q hv i.val:=by
  subst c
  exact FormulaSignSlotRadialProviderAtomic.ReplayFields.old_fields q hv he

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderAtomic.MarkedPrelude.markedPoint markedAt
  IntegralMixedAuxiliaryCandidate.Valid IntegralMixedAuxiliaryCandidate.point
  FormulaSignSlotRadialExternalCoordinates.point

theorem original_fields_eq (c a b :List Bool) (ha:A a) (hb:A b)
    (hca:provider a=c) (hcb:provider b=c) (i:Fin (num c)) :field a ha i.val=field b hb i.val:=by
  by_cases he:FormulaSignSlotRadialExternalContext.external c
  · obtain ⟨hpa,HPA⟩:=external_fields_at c a ha hca he
    obtain ⟨hpb,HPB⟩:=external_fields_at c b hb hcb he
    exact (HPA i.val i.isLt).symm.trans (HPB i.val i.isLt)
  · obtain ⟨hpa,HPA⟩:=old_fields_at c a ha hca he
    obtain ⟨hpb,HPB⟩:=old_fields_at c b hb hcb he
    exact (HPA i).symm.trans (HPB i)

theorem marked_projection_eq (c a b :List Bool) (ha:A a) (hb:A b)
    (hca:provider a=c) (hcb:provider b=c) :
    (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c a ha hca)).val=
      (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c b hb hcb)).val:=by
  funext i
  rw [markedAt_projection,markedAt_projection]
  exact original_fields_eq c a b ha hb hca hcb i

theorem prelude_joined_same_provider (c a b :List Bool) (ha:A a) (hb:A b)
    (hca:provider a=c) (hcb:provider b=c) :
    JoinedIn (Geo c) (preludeAt c a ha hca) (preludeAt c b hb hcb):=by
  have HP:=marked_projection_eq c a b ha hb hca hcb
  have HC:(BoundedRegularSource.markedProjection _ _ _ _ (markedAt c b hb hcb)).val∈
      connectedComponentIn (BoundedZeroSource.Bounded (Eqn c) (Radius c))
        (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c a ha hca)).val:=by
    rw [←HP]
    exact mem_connectedComponentIn (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c a ha hca)).property
  have HJ:=(FormulaSignSlotRadialProviderMarkedGeometry.marked_joined_iff c
    (markedAt c a ha hca) (markedAt c b hb hcb)).mpr HC
  simpa only [markedAt_values] using HJ

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludePhaseGeometry
