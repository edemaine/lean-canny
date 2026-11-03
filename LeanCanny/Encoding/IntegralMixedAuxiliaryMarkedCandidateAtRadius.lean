/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateRealization
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerRadius
public import LeanCanny.Geometry.AuxiliaryCandidateOuterRadius

/-! # Every filtered decoded candidate supplies its literal bounded replay point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateAtRadius
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (u label outer : List Bool) := pair (pair u label) outer
noncomputable def polynomial (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :=
  (t (original ctx)).finitePolynomial (number n ctx)

theorem valid {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) (hg : Good hn ht ha u label) :
    IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate (context u label outer)) := by
  simpa only [context,candidate,pairFst_pair] using Classical.choose hg

theorem point_word_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (q r : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q)
    (hr : IntegralMixedAuxiliaryCandidate.Valid hn ht ha r) (he : q=r) (i : ℕ)
    (hi : i<n (pairFst q)) (hj : i<n (pairFst r)) :
    IntegralMixedAuxiliaryCandidate.point hn ht ha q hq ⟨i,hi⟩=
      IntegralMixedAuxiliaryCandidate.point hn ht ha r hr ⟨i,hj⟩ := by
  cases he
  rfl

theorem bounded_transport {m k r : ℕ} (h : m=k) (p q : Term) (hp : p=q)
    (a : BoundedZeroSource.Bounded (q.finitePolynomial k) r) (x : Fin m→ℝ)
    (hx : ∀i,x i=a.val (Fin.cast h i)) :
    x∈BoundedZeroSource.Bounded (p.finitePolynomial m) r := by
  cases h
  cases hp
  have H : x=a.val := funext hx
  exact H.symm ▸ a.property

attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family SquareSampleCompleteVertices.candidate

noncomputable def boundedPoint {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    BoundedZeroSource.Bounded (polynomial n t (context u label outer)) (R (context u label outer)) := by
  refine ⟨IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate (context u label outer))
    (valid hn ht ha u label outer hg),?_⟩
  have HM : number n (context u label outer)=n u := by simp only [number,original,candidate,context,pairFst_pair]
  have HT : t (original (context u label outer))=t u := by simp only [original,candidate,context,pairFst_pair]
  have HQ : candidate (context u label outer)=pair u label := by simp only [candidate,context,pairFst_pair]
  let a:=AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u label hg (R (context u label outer)) hR
  have HP : ∀i : Fin (number n (context u label outer)),
      IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate (context u label outer))
        (valid hn ht ha u label outer hg) i=a.val (Fin.cast HM i) := by
    intro i
    have HI : i.val<n u := by rw [←HM]; exact i.isLt
    have H:=point_word_eq hn ht ha _ _ (valid hn ht ha u label outer hg) (Classical.choose hg) HQ i.val i.isLt
      (by simpa only [pairFst_pair] using HI)
    exact H.trans (AuxiliaryCandidateOuterRadius.coordinate hn ht ha u label hg (R (context u label outer)) hR (Fin.cast HM i)).symm
  have H:=bounded_transport HM _ _ HT a _ HP
  exact H

theorem coordinate {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer))
    (i : Fin (number n (context u label outer))) :
    (boundedPoint hn ht ha R u label outer hg hR).val i=
      IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate (context u label outer))
        (valid hn ht ha u label outer hg) i := rfl

theorem native_radius_le {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) :
    IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤
      IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha (context u label outer) := by
  have H:=IntegralMixedAuxiliaryMarkedIntegerPlan.candidate_radius_le hn ht ha (context u label outer)
  simpa only [original,candidate,context,pairFst_pair] using H

noncomputable def replayState {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) :=
  IntegralMixedFramedHistoryScript.run
    (IntegralMixedFramedHistoryFamilyBits.initial (IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha R) ctx)
    ((IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha R).rules ctx)
    (by have H:=(IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha R).room ctx; omega)

noncomputable def replayValues {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) : ℕ→ℝ :=
  let ctx:=context u label outer
  let q:=polynomial n t ctx
  let a:=boundedPoint hn ht ha R u label outer hg hR
  fun j=>IntegralMixedAuxiliaryMarkedIntegerSource.values n t R ctx
    (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha ctx (valid hn ht ha u label outer hg))
    (BoundedRegularSource.sphereSlack q (R ctx) a)
    (BoundedRegularSource.regularSlack q (AuxiliaryCandidateRegularLift.allowance t (original ctx))
      (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).re (number n ctx+8-1-j)

theorem realizes {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    IntegralMixedIntegerRealization.Realizes (replayState hn ht ha R (context u label outer))
      (replayValues hn ht ha R u label outer hg hR) :=
  IntegralMixedAuxiliaryMarkedCandidateRealization.realizes hn ht ha R (context u label outer)
    (valid hn ht ha u label outer hg) (polynomial n t (context u label outer))
    (boundedPoint hn ht ha R u label outer hg hR) (coordinate hn ht ha R u label outer hg hR)

theorem realizes_native {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) (hg : Good hn ht ha u label) :
    IntegralMixedIntegerRealization.Realizes
      (replayState hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) (context u label outer))
      (replayValues hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) u label outer hg
        (native_radius_le hn ht ha u label outer)) :=
  realizes hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) u label outer hg
    (native_radius_le hn ht ha u label outer)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateAtRadius
