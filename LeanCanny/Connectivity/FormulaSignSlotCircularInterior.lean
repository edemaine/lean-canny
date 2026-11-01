/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotProjectedPieceAccess
public import LeanCanny.Connectivity.FormulaStrictWitnessCanonical
public import LeanCanny.Connectivity.ClopenPathCoverRetract
/-! # A closed algebraic circle source supplies the actual positive interior cover

Only one strict coordinate condition remains in the margin source. Its literal
circular witness equation is closed, has a continuous section and connected
fibers. Every clopen path cover of this closed source therefore transfers to
the original positive source with the same labels. The radial construction
then proves accessibility of every projected piece.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCircularInterior
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def negativeMargin (c : List Bool) : Term := .mul (.const (-1)) (.var (objectiveIndex c).val)
noncomputable def description (c : List Bool) : Description :=
  FormulaStrictWitness.lifted (N c) (.eqZero (p c)) (negativeMargin c)

theorem negativeMargin_scope (c : List Bool) : (negativeMargin c).arity≤N c := by
  have H : (objectiveIndex c).val < N c := (objectiveIndex c).isLt
  change max 0 ((objectiveIndex c).val+1)≤N c
  rw [max_eq_right (Nat.zero_le _)]
  exact Nat.succ_le_of_lt H

theorem wellFormed (c : List Bool) : (description c).WellFormed :=
  FormulaStrictWitness.lifted_wellFormed _ _ _ (scope c) (negativeMargin_scope c)

theorem closed (c : List Bool) : ClosedFormulaWitness.Closed (description c).formula :=
  .and (.eqZero _) (.eqZero _)

theorem function_eq (c : List Bool) :
    FormulaStrictWitness.function (N c) (.eqZero (p c)) (negativeMargin c)=value c := by
  funext x
  have HI : (objectiveIndex c).val < (FormulaStrictWitness.context (N c) (.eqZero (p c))).dimension :=
    (objectiveIndex c).isLt
  simp only [FormulaStrictWitness.function,negativeMargin,Term.eval,Formula.extend,
    dite_eq_left HI,Int.cast_neg,Int.cast_one,neg_mul,one_mul,neg_neg,value]
  rfl

noncomputable def equationRebase (c : List Bool) :
    StrictInequalityWitness.equation (value c) ≃ₜ
      StrictInequalityWitness.equation (FormulaStrictWitness.function (N c) (.eqZero (p c)) (negativeMargin c)) where
  toFun z := ⟨z.val,by rw [function_eq]; exact z.property⟩
  invFun z := ⟨z.val,by rw [← function_eq]; exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

noncomputable def equationHomeomorph (c : List Bool) :
    StrictInequalityWitness.equation (value c) ≃ₜ (description c).realization :=
  (equationRebase c).trans (FormulaStrictWitness.liftedHomeomorph (N c) (.eqZero (p c)) (negativeMargin c)
    (scope c) (negativeMargin_scope c))

noncomputable def circleHomeomorph (c : List Bool) :
    (description c).realization ≃ₜ CircularWitness.Space (StrictInequalityWitness.radius (value c)) :=
  (equationHomeomorph c).symm.trans (StrictInequalityWitness.homeomorph (value c))

noncomputable def projection (c : List Bool) : (description c).realization → Positive c :=
  CircularWitness.projection _ ∘ circleHomeomorph c
noncomputable def sectionPoint (c : List Bool) : Positive c → (description c).realization :=
  (circleHomeomorph c).symm ∘ CircularWitness.centerSection _ (StrictInequalityWitness.radius_nonneg (value c))

theorem projection_coordinate (c : List Bool) (y : (description c).realization) (i : Fin (N c)) :
    (projection c y).val.val i=y.val (Fin.castAdd 2 i) := by
  have H := FormulaStrictWitness.projection_val (N c) (.eqZero (p c)) (negativeMargin c)
    (scope c) (negativeMargin_scope c) y i
  convert H using 1
  rfl

theorem continuous_projection (c : List Bool) : Continuous (projection c) :=
  (CircularWitness.continuous_projection _).comp (circleHomeomorph c).continuous

theorem continuous_section (c : List Bool) : Continuous (sectionPoint c) :=
  (circleHomeomorph c).symm.continuous.comp (CircularWitness.continuous_section _
    (StrictInequalityWitness.radius_nonneg (value c)) (StrictInequalityWitness.continuous_radius _ (continuous_value c)))

theorem projection_section (c : List Bool) : Function.LeftInverse (projection c) (sectionPoint c) := by
  intro x
  simp only [projection,sectionPoint,Function.comp_apply,Homeomorph.apply_symm_apply]
  rfl

theorem fiber_joined (c : List Bool) (y : (description c).realization) :
    JoinedIn univ y (sectionPoint c (projection c y)) := by
  have H := (CircularWitness.fiber_joined _ (StrictInequalityWitness.radius_nonneg (value c)) (circleHomeomorph c y)).map
    (circleHomeomorph c).symm.continuous.continuousOn
  simpa only [sectionPoint,projection,Function.comp_apply,Homeomorph.symm_apply_apply,Set.image_univ_of_surjective (circleHomeomorph c).symm.surjective] using H

noncomputable def interiorCover (c : List Bool) {I : Type*} (C : ClopenPathCover (description c).realization I) :
    ClopenPathCover (Positive c) I :=
  C.retract (projection c) (sectionPoint c) (continuous_projection c) (continuous_section c) (projection_section c) (fiber_joined c)

theorem projected_accessible (c : List Bool) {I : Type*} (C : ClopenPathCover (description c).realization I) (i : I) :
    FrontierCover.Accessible (FormulaSignSlotRadialAccess.projectedPiece c ((interiorCover c C).piece i)) :=
  FormulaSignSlotProjectedPieceAccess.accessible c (interiorCover c C) i
end LeanCanny.Connectivity.FormulaSignSlotCircularInterior
