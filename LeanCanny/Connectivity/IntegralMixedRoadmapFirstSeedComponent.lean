/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedGeometry
/-! # Keep the marked candidate's source component when choosing the first seed -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ}

noncomputable def firstZeroSet (u : List Bool) : Set (Fin (n u+3+1)→ℝ):={p |
  (FermatCriticalHomogenization.polynomial (source n t R0 u).low
    (source n t R0 u).leading (source n t R0 u).degree).eval₂ (Int.castRingHom ℝ) p=0}

noncomputable def firstMarkedPoint (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) : Fin (n u+3+1)→ℝ:=
  (BoundedRegularSource.markedLift (AuxiliaryCandidateRegularLift.original n t u)
    (AuxiliaryCandidateRegularLift.allowance t u) (AuxiliaryCandidateRegularLift.allowance t u) (R0 u)
    (AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u label hg (R0 u) hR)).val.val

theorem firstMarkedPoint_mem (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    firstMarkedPoint hn ht ha u label hg hR∈firstZeroSet (n:=n) (t:=t) (R0:=R0) u :=by
  let a:=AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u label hg (R0 u) hR
  let z:=BoundedRegularSource.markedLift (AuxiliaryCandidateRegularLift.original n t u)
    (AuxiliaryCandidateRegularLift.allowance t u) (AuxiliaryCandidateRegularLift.allowance t u) (R0 u) a
  change (FermatCriticalHomogenization.polynomial (source n t R0 u).low
    (source n t R0 u).leading (source n t R0 u).degree).eval₂ (Int.castRingHom ℝ) z.val.val=0
  rw [IntegralMixedOriginalRegularSource.source_polynomial]
  exact z.val.property

/-- Choose the critical point in the component of this candidate's canonical
marked lift. No accepted roadmap node or component-cover premise is used. -/
theorem exists_original_component_critical (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃p : Fin (n u+3+1)→ℝ,
      p∈connectedComponentIn (firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
        (firstMarkedPoint hn ht ha u label hg hR) ∧
      (FermatCriticalHomogenization.polynomial (source n t R0 u).low
        (source n t R0 u).leading (source n t R0 u).degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial (source n t R0 u).low
          (source n t R0 u).leading (source n t R0 u).degree)).eval₂ (Int.castRingHom ℝ) p=0 :=by
  let P:=source n t R0 u
  let F : IntegralMixedFrozenFrame.Frame (n u+3):=IntegralMixedFrozenFrame.originalFrame ∅ (fun _=>false)
    (fun _=>IntegralMixedCausalRowConstructor.Row.single (none : IntegralMixedCausalRowConstructor.Atom 0))
  let old : Fin 0→ℝ:=Fin.elim0
  have HE : IntegralMixedFrozenFrame.slice P F old=firstZeroSet (n:=n) (t:=t) (R0:=R0) u:=by
    ext p
    exact and_iff_left (by simp [F, IntegralMixedFrozenFrame.originalFrame])
  have HZ : firstMarkedPoint hn ht ha u label hg hR∈IntegralMixedFrozenFrame.slice P F old:=by
    rw [HE]
    exact firstMarkedPoint_mem hn ht ha u label hg hR
  obtain ⟨p,HP,HG⟩:=IntegralMixedFrozenFrame.exists_component_critical_of_proper P F old 0
    (Finset.notMem_empty _)
    (IntegralMixedFrozenFrame.regular_source_proper (BoundedRegularLowCoefficient.readers n t R0) u) _ HZ
  have HZero:= (connectedComponentIn_subset _ _ HP).1
  rw [HE] at HP
  refine ⟨p,HP,HZero,?_⟩
  intro i hi
  exact HG i (Finset.notMem_empty _) (fun h=>hi (congrArg Fin.val h))

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
