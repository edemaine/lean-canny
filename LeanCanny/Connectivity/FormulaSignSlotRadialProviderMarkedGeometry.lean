/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBallConnections
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSampling
public import LeanCanny.Geometry.PolynomialComponentPaths
/-! # Actual provider marked lifts preserve original component membership -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Term.finitePolynomial CanonicalAuxiliaryCandidateCover.equation
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
abbrev original := FormulaSignSlotRadialExternalPrelude.original
noncomputable abbrev number := FormulaSignSlotRadialExternalPrelude.number
noncomputable abbrev radius := FormulaSignSlotRadialExternalPrelude.radius
noncomputable def equation (c : List Bool) := AuxiliaryCandidateRegularLift.original n t (original c)
noncomputable def allowance (c : List Bool) := AuxiliaryCandidateRegularLift.allowance t (original c)
noncomputable def polynomial (c : List Bool) : MvPolynomial (Fin (number c+4)) ℤ :=
  FermatCriticalHomogenization.polynomial (FormulaSignSlotRadialProviderIntegerPlan.spatial c).low
    (FormulaSignSlotRadialProviderIntegerPlan.spatial c).leading (FormulaSignSlotRadialProviderIntegerPlan.spatial c).degree
noncomputable def zeroSet (c : List Bool) := {x : Fin (number c+4)→ℝ | (polynomial c).eval₂ (Int.castRingHom ℝ) x=0}

theorem source_polynomial (c : List Bool) : polynomial c=
    BoundedRegularSource.polynomial (equation c) (allowance c) (allowance c) (radius c) := by
  simpa only [polynomial,FormulaSignSlotRadialProviderIntegerPlan.spatial,FormulaSignSlotRadialExternalPrelude.spatial,
    FormulaSignSlotRadialExternalPrelude.readers,equation,allowance,AuxiliaryCandidateRegularLift.original,
    AuxiliaryCandidateRegularLift.allowance,Function.comp_apply,number,original,radius,
    FormulaSignSlotRadialExternalPrelude.number,FormulaSignSlotRadialExternalContext.number,
    FormulaSignSlotRadialExternalPrelude.original,BoundedRegularLowCoefficient.readers] using
    BoundedRegularLowCoefficient.readers_source_polynomial number (t∘original) radius c

theorem zeroSet_eq (c : List Bool) : zeroSet c=
    BoundedRegularSource.Zeros (equation c) (allowance c) (allowance c) (radius c) := by
  unfold zeroSet
  rw [source_polynomial]
  rfl

theorem proper (c : List Bool) : IsProperMap (fun x : Fin (number c+4)→ℝ => (polynomial c).eval₂ (Int.castRingHom ℝ) x) :=
  IntegralMixedFrozenFrame.regular_source_proper FormulaSignSlotRadialProviderIntegerPlan.readers c

theorem marked_mem (c : List Bool)
    (z : BoundedRegularSource.Marked (equation c) (allowance c) (allowance c) (radius c)) : z.val.val∈zeroSet c := by
  rw [zeroSet_eq]
  exact z.val.property

theorem markedLift_mem (c : List Bool) (x : BoundedZeroSource.Bounded (equation c) (radius c)) :
    (BoundedRegularSource.markedLift (equation c) (allowance c) (allowance c) (radius c) x).val.val∈zeroSet c :=
  marked_mem c _

private theorem integer_component_joined {m : ℕ} (Q : MvPolynomial (Fin m) ℤ) (x y : Fin m→ℝ)
    (hx : x∈{v | Q.eval₂ (Int.castRingHom ℝ) v=0})
    (hy : y∈connectedComponentIn {v | Q.eval₂ (Int.castRingHom ℝ) v=0} x) :
    JoinedIn {v | Q.eval₂ (Int.castRingHom ℝ) v=0} x y := by
  simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using
    PolynomialComponentPaths.joinedIn_of_component (Q.map (Int.castRingHom ℝ)) x
      (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,Set.mem_ofPred_eq] using hx) y
      (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using hy)

private theorem marked_joined {m : ℕ} (Q : MvPolynomial (Fin m) ℤ) (D H R : ℕ)
    (hD : Q.totalDegree≤D) (hH : MvMass.mass Q≤2^H) (z v : BoundedRegularSource.Marked Q D H R) :
    JoinedIn (BoundedRegularSource.Zeros Q D H R) z.val.val v.val.val ↔
      (BoundedRegularSource.markedProjection Q D H R v).val∈
        connectedComponentIn (BoundedZeroSource.Bounded Q R) (BoundedRegularSource.markedProjection Q D H R z).val := by
  have HM := BoundedRegularSource.marked_component_iff Q D H R hD hH z v
  constructor
  · intro hj
    exact HM.mp (pathComponent_subset_component z.val ((joinedIn_iff_joined z.val.property v.val.property).mp hj))
  · intro hc
    have ha : v.val.val∈connectedComponentIn (BoundedRegularSource.Zeros Q D H R) z.val.val := by
      rw [connectedComponentIn_eq_image z.val.property]
      exact ⟨v.val,HM.mpr hc,rfl⟩
    exact integer_component_joined _ _ _ z.val.property ha

theorem marked_joined_iff (c : List Bool)
    (z v : BoundedRegularSource.Marked (equation c) (allowance c) (allowance c) (radius c)) :
    JoinedIn (zeroSet c) z.val.val v.val.val ↔
      (BoundedRegularSource.markedProjection _ _ _ _ v).val∈
        connectedComponentIn (BoundedZeroSource.Bounded (equation c) (radius c))
          (BoundedRegularSource.markedProjection _ _ _ _ z).val := by
  rw [zeroSet_eq]
  exact marked_joined _ _ _ _ (AuxiliaryCandidateRegularLift.original_degree n t (original c))
    (AuxiliaryCandidateRegularLift.original_mass n t (original c)) z v

theorem marked_original_component_iff (c : List Bool)
    (z v : BoundedRegularSource.Marked (equation c) (allowance c) (allowance c) (radius c)) :
    JoinedIn (zeroSet c) z.val.val v.val.val ↔
      (BoundedRegularSource.markedProjection _ _ _ _ v).val∈
        connectedComponentIn (BoundedZeroSource.Original (equation c))
          (BoundedRegularSource.markedProjection _ _ _ _ z).val :=
  (marked_joined_iff c z v).trans
    (FormulaSignSlotRadialProviderBallConnections.component_iff c
      (BoundedRegularSource.markedProjection _ _ _ _ z) (BoundedRegularSource.markedProjection _ _ _ _ v)).symm

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
