/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedThomCompleteness
public import LeanCanny.Algebra.IntegralMixedMarkedValuesCoordinates
public import LeanCanny.Encoding.IntegralMixedMarkedReplayValidity

/-! # Canonical chronological marked values satisfy every literal prelude leaf -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedCanonicalValues
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original values)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context valid polynomial boundedPoint coordinate replayValues)
open IntegralMixedAuxiliaryMarkedCandidateRealization (oldValues)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def chronological {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) : ℕ→ℝ :=
  let ctx:=context u label outer
  let q:=polynomial n t ctx
  let a:=boundedPoint hn ht ha R u label outer hg hR
  values n t R ctx (oldValues hn ht ha ctx (valid hn ht ha u label outer hg))
    (BoundedRegularSource.sphereSlack q (R ctx) a)
    (BoundedRegularSource.regularSlack q (AuxiliaryCandidateRegularLift.allowance t (original ctx))
      (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).re

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliaryMarkedIntegerPlan.parameters

theorem reverse_value {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer))
    (i : ℕ) (hi : i<number n (context u label outer)+8) :
    replayValues hn ht ha R u label outer hg hR (number n (context u label outer)+7-i)=
      chronological hn ht ha R u label outer hg hR i := by
  have H : number n (context u label outer)+8-1-(number n (context u label outer)+7-i)=i := by omega
  simp only [replayValues,chronological,H]

theorem roots {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) (i : ℕ) :
    ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair (context u label outer) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (chronological hn ht ha R u label outer hg hR i)=0 := by
  have H:=IntegralMixedAuxiliaryMarkedSlackRoots.roots (n:=n) (t:=t) hn ht ha R (context u label outer)
    (valid hn ht ha u label outer hg) (polynomial n t (context u label outer))
    (boundedPoint hn ht ha R u label outer hg hR) (coordinate hn ht ha R u label outer hg hR)
  exact IntegralMixedAuxiliaryMarkedIntegerSource.roots (n:=n) (t:=t) hn ht ha R (context u label outer)
    (oldValues hn ht ha (context u label outer) (valid hn ht ha u label outer hg)) _ _
    (IntegralMixedAuxiliaryMarkedCandidateRealization.coordinate_root hn ht ha _ _) H.1 H.2 i

theorem marked_coordinates {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    (fun i : Fin (number n (context u label outer)+4)=>chronological hn ht ha R u label outer hg hR i.val)=
      (BoundedRegularSource.markedLift (polynomial n t (context u label outer))
        (AuxiliaryCandidateRegularLift.allowance t (original (context u label outer)))
        (AuxiliaryCandidateRegularLift.allowance t (original (context u label outer))) (R (context u label outer))
        (boundedPoint hn ht ha R u label outer hg hR)).val.val := by
  let ctx:=context u label outer
  let a:=boundedPoint hn ht ha R u label outer hg hR
  have HX : (fun i : Fin (number n ctx)=>oldValues hn ht ha ctx (valid hn ht ha u label outer hg) i.val)=a.val := by
    funext i
    rw [oldValues,dite_eq_left i.isLt]
    exact (coordinate hn ht ha R u label outer hg hR i).symm
  change (fun i : Fin (number n ctx+4)=>chronological hn ht ha R u label outer hg hR i.val)=
    (BoundedRegularSource.lift (polynomial n t ctx) (AuxiliaryCandidateRegularLift.allowance t (original ctx))
      (AuxiliaryCandidateRegularLift.allowance t (original ctx)) (R ctx) a).val
  unfold chronological
  rw [IntegralMixedMarkedValuesCoordinates.first_coordinates,HX,BoundedRegularSource.lift_coordinates]

end LeanCanny.Encoding.IntegralMixedMarkedCanonicalValues
