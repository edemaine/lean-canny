/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalPrelude
public import LeanCanny.Geometry.EffectivePolynomialBallConnections
/-! # The actual shared provider radius preserves original components

The spatial term, allowance and radius are the concrete provider readers.
Both endpoints are already in the bounded original zero set. The cutoff
and its original degree/mass charges are derived, rather than supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBallConnections
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Set
open scoped Classical
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
noncomputable abbrev equation (ctx : List Bool) :=
  AuxiliaryCandidateRegularLift.original n t (FormulaSignSlotRadialExternalPrelude.original ctx)
noncomputable abbrev radius := FormulaSignSlotRadialExternalPrelude.radius

theorem joined_iff (ctx : List Bool)
    (x y : BoundedZeroSource.Bounded (equation ctx) (radius ctx)) :
    JoinedIn (BoundedZeroSource.Original (equation ctx)) x.val y.val ↔
      JoinedIn (BoundedZeroSource.Bounded (equation ctx) (radius ctx)) x.val y.val :=
  EffectivePolynomialBallConnections.joined_iff_after_cutoff _ _ _ _
    (AuxiliaryCandidateRegularLift.original_degree n t _)
    (AuxiliaryCandidateRegularLift.original_mass n t _)
    (FormulaSignSlotRadialExternalPrelude.joiningExponent_le_radius ctx) _ _ x.property y.property

theorem component_iff (ctx : List Bool)
    (x y : BoundedZeroSource.Bounded (equation ctx) (radius ctx)) :
    y.val∈connectedComponentIn (BoundedZeroSource.Original (equation ctx)) x.val ↔
      y.val∈connectedComponentIn (BoundedZeroSource.Bounded (equation ctx) (radius ctx)) x.val :=
  EffectivePolynomialBallConnections.component_iff_after_cutoff _ _ _ _
    (AuxiliaryCandidateRegularLift.original_degree n t _)
    (AuxiliaryCandidateRegularLift.original_mass n t _)
    (FormulaSignSlotRadialExternalPrelude.joiningExponent_le_radius ctx) _ _ x.property y.property

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBallConnections
