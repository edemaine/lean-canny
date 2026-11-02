/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
public import LeanCanny.Geometry.IntegralMixedFramedSlackObservedRoots

/-! # The literal old candidate's canonical slacks satisfy the native replay sources -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedSlackRoots
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original oldKey tail)
open IntegralMixedAuxiliaryCandidateInterpretation (parameters)
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliaryParametricSlackSource (sphereSource regularSource regularizationAt penaltyAt)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular elementAt)
open IntegralMixedAuxiliaryMarkedOldInterpretation (count_at charge_at)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def savedSyntax {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :
    IntegralMixedFramedNativeBits.Syntax (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) :=
  IntegralMixedAuxiliarySlackSource.syntaxInput hn ht ha

theorem savedInputs {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :
    IntegralMixedFramedStepHeight.FamilyInputs (parameters n t) (planAt hn ht ha)
      (savedSyntax hn ht ha).nodes (savedSyntax hn ht ha).factor (savedSyntax hn ht ha).seed :=
  IntegralMixedAuxiliarySlackSource.inputs hn ht ha

theorem sphere_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :
    sphereSource hn ht ha R=IntegralMixedFramedSlackRootBits.sphereSource (parameters n t) (planAt hn ht ha)
      (dataAt hn ht ha) (savedSyntax hn ht ha) (savedInputs hn ht ha) (IntegralMixedAuxiliarySlackMatrix.count n) R := rfl

theorem regular_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :
    regularSource hn ht ha R=IntegralMixedFramedSlackRootBits.regularSource (parameters n t) (planAt hn ht ha)
      (dataAt hn ht ha) (savedSyntax hn ht ha) (savedInputs hn ht ha) (IntegralMixedAuxiliarySlackMatrix.count n)
      (IntegralMixedAuxiliarySlackMatrix.degree t) R (regularizationAt n t R) (penaltyAt n t R) := rfl

attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented planAt dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family oldKey candidate SquareSampleCompleteVertices.candidate

theorem roots {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx))
    (q : MvPolynomial (Fin (number n ctx)) ℤ) (a : BoundedZeroSource.Bounded q (R ctx))
    (hp : ∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hq i) :
    ((sphereSource hn ht ha (R∘tail)).polynomial (oldKey n t ctx)).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.sphereSlack q (R ctx) a)=0 ∧
      ((regularSource hn ht ha (R∘tail)).polynomial (oldKey n t ctx)).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.regularSlack q (AuxiliaryCandidateRegularLift.allowance t (original ctx))
          (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).re=0 := by
  have HR : (R∘tail) (oldKey n t ctx)=R ctx := congrArg R (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail n t ctx)
  have HD : IntegralMixedAuxiliarySlackMatrix.degree t (oldKey n t ctx)=
      BoundedZeroSource.powerDegree (AuxiliaryCandidateRegularLift.allowance t (original ctx)) :=
    congrArg BoundedZeroSource.powerDegree (charge_at n t ctx)
  have HL : regularizationAt n t (R∘tail) (oldKey n t ctx)=BoundedRegularSource.regularizationExponent
      (number n ctx) (AuxiliaryCandidateRegularLift.allowance t (original ctx))
      (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) := by
    simp only [regularizationAt,count_at,charge_at,HR]
  have HK : penaltyAt n t (R∘tail) (oldKey n t ctx)=BoundedZeroSource.penaltyExponent
      (number n ctx) (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) := by
    simp only [penaltyAt,count_at,charge_at,HR]
  rw [sphere_eq,regular_eq]
  exact IntegralMixedFramedSlackObservedRoots.roots (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (savedSyntax hn ht ha) (savedInputs hn ht ha)
    (oldKey n t ctx) (IntegralMixedAuxiliarySlackMatrix.count n) (R∘tail) (number n ctx) (R ctx)
    (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (AuxiliaryCandidateRegularLift.allowance t (original ctx))
    (IntegralMixedAuxiliarySlackMatrix.degree t) (regularizationAt n t (R∘tail)) (penaltyAt n t (R∘tail))
    (count_at n t ctx) HR HD HL HK q a (IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hq) hp
    (IntegralMixedAuxiliaryMarkedOldInterpretation.exists_interpretation (n:=n) (t:=t) hn ht ha ctx hq)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedSlackRoots
