/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedSlackRoots
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerRealization

/-! # The literal old candidate and canonical marked slacks have one native replay

The coordinate roots and both slack roots are derived from the old candidate.
The target bank realizes the entire correlated vector, including power leaves.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateRealization
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original values)
open IntegralMixedAuxiliaryMarkedIntegerPlan (parameters plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def oldValues {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (ctx : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx)) (i : ℕ) : ℝ :=
  if hi : i<number n ctx then IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hq ⟨i,hi⟩ else 0

attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family candidate SquareSampleCompleteVertices.candidate parameters plan

theorem coordinate_root {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (ctx : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx)) (i : ℕ) (hi : i<number n ctx) :
    ((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
      (pair (candidate ctx) (BinaryNatCode.encode (number n ctx-i)))).eval₂ (Int.castRingHom ℝ)
      (oldValues hn ht ha ctx hq i)=0 := by
  rw [oldValues,dite_eq_left hi]
  exact IntegralMixedAuxiliaryCandidateCoordinate.point_root hn ht ha (candidate ctx) hq ⟨i,hi⟩

theorem realizes {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx))
    (q : MvPolynomial (Fin (number n ctx)) ℤ) (a : BoundedZeroSource.Bounded q (R ctx))
    (hp : ∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hq i) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run
        (IntegralMixedFramedHistoryFamilyBits.initial (parameters hn ht ha) (plan hn ht ha R) ctx)
        ((plan hn ht ha R).rules ctx) (by have H:=(plan hn ht ha R).room ctx; omega))
      (fun j=>values n t R ctx (oldValues hn ht ha ctx hq)
        (BoundedRegularSource.sphereSlack q (R ctx) a)
        (BoundedRegularSource.regularSlack q (AuxiliaryCandidateRegularLift.allowance t (original ctx))
          (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).re (number n ctx+8-1-j)) := by
  have H:=IntegralMixedAuxiliaryMarkedSlackRoots.roots (n:=n) (t:=t) hn ht ha R ctx hq q a hp
  exact IntegralMixedAuxiliaryMarkedIntegerPlan.realizes_prescribed (n:=n) (t:=t) hn ht ha R ctx
    (oldValues hn ht ha ctx hq) (BoundedRegularSource.sphereSlack q (R ctx) a)
    (BoundedRegularSource.regularSlack q (AuxiliaryCandidateRegularLift.allowance t (original ctx))
      (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).re
    (coordinate_root hn ht ha ctx hq) H.1 H.2

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateRealization
