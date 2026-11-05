/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateRealization
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVectorPoint
public import LeanCanny.Geometry.AuxiliaryCandidateOuterRadius
/-! # A genuine old zero candidate realizes the source-aware marked prelude

The literal old source and label remain fixed. The shared provider radius is
at least the old candidate radius, and the two canonical slacks and every
power leaf belong to one prescribed n+8 root vector.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope

def context (u label aux : List Bool) := pair (pair u label) (pair [false] aux)
theorem old_context (u label aux : List Bool) :
    ¬FormulaSignSlotRadialExternalContext.external (context u label aux) := by
  simp [FormulaSignSlotRadialExternalContext.external,FormulaSignSlotRadialExternalContext.metadata,context]
theorem original_context (u label aux : List Bool) :
    FormulaSignSlotRadialExternalContext.original (context u label aux)=u := by
  simp only [FormulaSignSlotRadialExternalContext.original,context,pairFst_pair]
theorem number_context (u label aux : List Bool) :
    FormulaSignSlotRadialExternalContext.number (context u label aux)=n u := by
  rw [FormulaSignSlotRadialExternalContext.number,original_context]

theorem oldRadius_le (ctx : List Bool) :
    IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha
      (FormulaSignSlotRadialExternalContext.original ctx) ≤ FormulaSignSlotRadialExternalPrelude.radius ctx := by
  have H := le_max_left (FormulaSignSlotRadialExternalPrelude.oldRadius
    (FormulaSignSlotRadialExternalContext.original ctx))
    (FormulaSignSlotRadialExternalPrelude.jointRadius (FormulaSignSlotRadialExternalPrelude.jointHeader ctx))
  unfold FormulaSignSlotRadialExternalPrelude.radius
  dsimp only [FormulaSignSlotRadialExternalPrelude.oldRadius,FormulaSignSlotRadialExternalPrelude.original] at H ⊢
  omega

theorem radius_flag (u label aux : List Bool) (flag : Bool) :
    FormulaSignSlotRadialExternalPrelude.radius (pair (pair u label) (pair [flag] aux))=
      FormulaSignSlotRadialExternalPrelude.radius (context u label aux) := by
  simp only [FormulaSignSlotRadialExternalPrelude.radius,FormulaSignSlotRadialExternalPrelude.jointHeader,
    FormulaSignSlotRadialExternalPrelude.joiningCutoff,FormulaSignSlotRadialExternalContext.gridContext,
    FormulaSignSlotRadialExternalContext.metadata,FormulaSignSlotRadialExternalContext.original,
    FormulaSignSlotRadialExternalContext.number,context,pairFst_pair,pairSnd_pair]

theorem reindex_values {a b : ℕ} (h : a=b) (z : Fin a→ℝ) :
    Formula.extend z=Formula.extend (fun i : Fin b=>z (Fin.cast h.symm i)) ∧
      BoundedZeroSource.radial z=BoundedZeroSource.radial (fun i : Fin b=>z (Fin.cast h.symm i)) := by
  cases h
  exact ⟨rfl,rfl⟩

theorem point_values {nv : List Bool→ℕ} {tv : List Bool→Term}
    (hnv : UnaryFn nv) (htv : (fun q=>(tv q).toData.toBits)∈FP) (hav : ∀q,(tv q).arity≤nv q)
    (c d : List Bool) (hc : c=d) (hv : IntegralMixedAuxiliaryCandidate.Valid hnv htv hav c)
    (hw : IntegralMixedAuxiliaryCandidate.Valid hnv htv hav d) :
    Formula.extend (IntegralMixedAuxiliaryCandidate.point hnv htv hav c hv)=
      Formula.extend (IntegralMixedAuxiliaryCandidate.point hnv htv hav d hw) ∧
    BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.point hnv htv hav c hv)=
      BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.point hnv htv hav d hw) := by
  cases hc
  exact ⟨rfl,rfl⟩

theorem pointAt_values {nv : List Bool→ℕ} {tv : List Bool→Term}
    (hnv : UnaryFn nv) (htv : (fun q=>(tv q).toData.toBits)∈FP) (hav : ∀q,(tv q).arity≤nv q)
    (u label : List Bool) (hv : IntegralMixedAuxiliaryCandidate.Valid hnv htv hav (pair u label)) :
    Formula.extend (IntegralMixedAuxiliaryCandidate.point hnv htv hav (pair u label) hv)=
      Formula.extend (IntegralMixedAuxiliaryCandidate.pointAt hnv htv hav u label hv) ∧
    BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.point hnv htv hav (pair u label) hv)=
      BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.pointAt hnv htv hav u label hv) := by
  have H := reindex_values (congrArg nv (pairFst_pair u label))
    (IntegralMixedAuxiliaryCandidate.point hnv htv hav (pair u label) hv)
  unfold IntegralMixedAuxiliaryCandidate.pointAt
  exact H

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  AuxiliaryCandidateRegularLift.original IntegralMixedAuxiliaryCandidate.pointAt
  IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.source
  IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.input
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderIntegerPlan.parameters
  FormulaSignSlotRadialProviderIntegerPlan.plan

theorem valid (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) :
    IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (context u label aux)) := by
  simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,context,pairFst_pair] using hg.choose

noncomputable def boundedPoint (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) :
    BoundedZeroSource.Bounded
      (AuxiliaryCandidateRegularLift.original n t
        (IntegralMixedAuxiliaryMarkedIntegerSource.original (context u label aux)))
      (FormulaSignSlotRadialExternalPrelude.radius (context u label aux)) := by
  refine ⟨IntegralMixedAuxiliaryCandidate.point hn ht ha
    (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (context u label aux)) (valid u label aux hg),?_,?_⟩
  · unfold AuxiliaryCandidateRegularLift.original
    apply (Term.eval_finitePolynomial _ _ _).trans
    have HC : IntegralMixedAuxiliaryMarkedIntegerSource.candidate (context u label aux)=pair u label := by
      simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,context,pairFst_pair]
    have HE := (point_values hn ht ha _ _ HC (valid u label aux hg) hg.choose).1.trans
      (pointAt_values hn ht ha u label hg.choose).1
    rw [HE]
    simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,context,pairFst_pair] using hg.choose_spec
  · have H := IntegralMixedAuxiliaryCandidateRadius.point_radial_le hn ht ha u label hg.choose
    have HR := AuxiliaryCandidateOuterRadius.radiusSquared_mono (oldRadius_le (context u label aux))
    simp only [FormulaSignSlotRadialExternalContext.original,context,pairFst_pair] at HR
    have HC : IntegralMixedAuxiliaryMarkedIntegerSource.candidate (context u label aux)=pair u label := by
      simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,context,pairFst_pair]
    have HE := (point_values hn ht ha _ _ HC (valid u label aux hg) hg.choose).2.trans
      (pointAt_values hn ht ha u label hg.choose).2
    rw [HE]
    exact H.trans HR

theorem boundedPoint_coordinate (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (i : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (context u label aux))) :
    (boundedPoint u label aux hg).val i=IntegralMixedAuxiliaryCandidate.point hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate (context u label aux)) (valid u label aux hg) i := rfl

noncomputable def values (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) : ℕ→ℝ :=
  IntegralMixedAuxiliaryMarkedIntegerSource.values n t FormulaSignSlotRadialExternalPrelude.radius
    (context u label aux)
    (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha
      (context u label aux) (valid u label aux hg))
    (BoundedRegularSource.sphereSlack _ _ (boundedPoint u label aux hg))
    (BoundedRegularSource.regularSlack _ (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original (context u label aux)))
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original (context u label aux))) _ (boundedPoint u label aux hg)).re


theorem roots (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) (i : ℕ) :
    (FormulaSignSlotRadialProviderIntegerSource.source.polynomial
      (pair (context u label aux) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (values u label aux hg i)=0 := by
  rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_old _
    (by simpa only [pairFst_pair] using old_context u label aux)]
  have HS := IntegralMixedAuxiliaryMarkedSlackRoots.roots hn ht ha FormulaSignSlotRadialExternalPrelude.radius
    (context u label aux) (valid u label aux hg) _ (boundedPoint u label aux hg) (boundedPoint_coordinate u label aux hg)
  exact IntegralMixedAuxiliaryMarkedIntegerSource.roots hn ht ha FormulaSignSlotRadialExternalPrelude.radius
    (context u label aux) _ _ _
    (IntegralMixedAuxiliaryMarkedCandidateRealization.coordinate_root hn ht ha
      (context u label aux) (valid u label aux hg)) HS.1 HS.2 i

theorem marked_coordinates (u label aux : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) :
    (fun i : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (context u label aux)+4) => values u label aux hg i.val)=
      (BoundedRegularSource.markedLift _ (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original (context u label aux)))
        (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original (context u label aux))) _ (boundedPoint u label aux hg)).val.val := by
  exact IntegralMixedAuxiliaryMarkedIntegerSource.values_markedLift n t FormulaSignSlotRadialExternalPrelude.radius
    (context u label aux) _ _ _ (boundedPoint u label aux hg) _ (fun i hi => by
      rw [IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues,dite_eq_left hi]
      exact (boundedPoint_coordinate u label aux hg ⟨i,hi⟩).symm)

end LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
