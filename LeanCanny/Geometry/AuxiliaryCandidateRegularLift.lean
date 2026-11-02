/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateRadius
public import LeanCanny.Connectivity.AuxiliaryCandidateComponentCover
public import LeanCanny.Geometry.BoundedMarkedCoordinates
public import LeanCanny.ETR.PolynomialMass

/-! # Actual filtered candidate pairs attach to a fixed regular source

One original-only binary radius contains every decoded candidate. The literal
integer original equation supplies degree and mass allowances. Its marked
regular lift preserves the component relation INSIDE that bounded original
zero set, retains every original coordinate, and has a proper regular source.
No stabilization of all unbounded original connections is inferred.
-/
@[expose] public section
namespace LeanCanny.Geometry.AuxiliaryCandidateRegularLift
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR Set
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open IntegralMixedAuxiliaryCandidateRadius (radius)
open scoped Classical
attribute [local irreducible] IntegralMixedAuxiliaryCandidateRadius.radius IntegralMixedAuxiliaryCandidate.pointAt

noncomputable def original (n : List Bool→ℕ) (t : List Bool→Term) (u : List Bool) :=
  (t u).finitePolynomial (n u)

def allowance (t : List Bool→Term) (u : List Bool) : ℕ := (t u).toData.size

theorem allowance_unary {t : List Bool→Term} (ht : (fun q=>(t q).toData.toBits)∈FP) : UnaryFn (allowance t) :=
  UnaryFn.of_eq (UnaryFn.length ht) (fun q=>(t q).toData.length_toBits)

theorem original_degree (n : List Bool→ℕ) (t : List Bool→Term) (u : List Bool) :
    (original n t u).totalDegree≤allowance t u :=
  ((t u).totalDegree_finitePolynomial (n u)).trans (t u).degreeBound_le_dataSize

theorem original_mass (n : List Bool→ℕ) (t : List Bool→Term) (u : List Bool) :
    MvMass.mass (original n t u)≤2^allowance t u := (t u).finitePolynomial_mass (n u)

noncomputable def boundedPoint {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) :
    BoundedZeroSource.Bounded (original n t u) (radius hn ht ha u) :=
  ⟨IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg),
    (Term.eval_finitePolynomial _ _ _).trans (Classical.choose_spec hg),
    IntegralMixedAuxiliaryCandidateRadius.point_radial_le hn ht ha u label (Classical.choose hg)⟩

noncomputable def markedPoint {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) :
    BoundedRegularSource.Marked (original n t u) (allowance t u) (allowance t u) (radius hn ht ha u) :=
  BoundedRegularSource.markedLift _ _ _ _ (boundedPoint hn ht ha u label hg)

theorem marked_projection {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) :
    BoundedRegularSource.markedProjection _ _ _ _ (markedPoint hn ht ha u label hg)=boundedPoint hn ht ha u label hg :=
  BoundedRegularSource.markedProjection_lift _ _ _ _ _

theorem coordinate {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u label : List Bool) (hg : Good hn ht ha u label) (i : Fin (n u)) :
    (markedPoint hn ht ha u label hg).val.val (i.castAdd 4)=
      IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg) i := by
  have H:=congrArg (fun x : BoundedZeroSource.Bounded (original n t u) (radius hn ht ha u)=>x.val i)
    (marked_projection hn ht ha u label hg)
  rw [BoundedRegularSource.markedProjection_apply] at H
  exact H

theorem component_iff {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u a b : List Bool) (ha' : Good hn ht ha u a) (hb' : Good hn ht ha u b) :
    (boundedPoint hn ht ha u b hb').val∈
      connectedComponentIn (BoundedZeroSource.Bounded (original n t u) (radius hn ht ha u)) (boundedPoint hn ht ha u a ha').val ↔
      (markedPoint hn ht ha u b hb').val∈connectedComponent (markedPoint hn ht ha u a ha').val :=
  BoundedRegularSource.component_iff_lift (original n t u) (allowance t u) (allowance t u) (radius hn ht ha u)
    (original_degree n t u) (original_mass n t u) (boundedPoint hn ht ha u a ha') (boundedPoint hn ht ha u b hb')

theorem regular {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (u : List Bool) (x : Fin (n u+4)→ℝ)
    (hx : (BoundedRegularSource.polynomial (original n t u) (allowance t u) (allowance t u) (radius hn ht ha u)).eval₂ (Int.castRingHom ℝ) x=0) :
    ∃ j,(MvPolynomial.pderiv j (BoundedRegularSource.polynomial (original n t u) (allowance t u) (allowance t u)
      (radius hn ht ha u))).eval₂ (Int.castRingHom ℝ) x≠0 :=
  BoundedRegularSource.regular _ _ _ _ (original_degree n t u) (original_mass n t u) x hx

theorem proper {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (u : List Bool) :
    IsProperMap (fun x : Fin (n u+4)→ℝ=>
      (BoundedRegularSource.polynomial (original n t u) (allowance t u) (allowance t u) (radius hn ht ha u)).eval₂ (Int.castRingHom ℝ) x) :=
  BoundedRegularSource.proper _ _ _ _

end LeanCanny.Geometry.AuxiliaryCandidateRegularLift
