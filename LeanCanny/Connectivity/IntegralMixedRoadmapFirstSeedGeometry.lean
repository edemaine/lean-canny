/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
public import LeanCanny.Geometry.AuxiliaryCandidateOuterRadius
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedLayout
/-! # A first global critical point from original candidate data -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ}

/-- The native original candidate radius is enough to initialize the regular
source. No accepted roadmap node or sampled prelude is assumed. -/
theorem exists_original_critical (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃p : Fin (n u+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial (source n t R0 u).low
        (source n t R0 u).leading (source n t R0 u).degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial (source n t R0 u).low
          (source n t R0 u).leading (source n t R0 u).degree)).eval₂ (Int.castRingHom ℝ) p=0 :=by
  let a:=AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u label hg (R0 u) hR
  let z:=BoundedRegularSource.markedLift (AuxiliaryCandidateRegularLift.original n t u)
    (AuxiliaryCandidateRegularLift.allowance t u) (AuxiliaryCandidateRegularLift.allowance t u) (R0 u) a
  let P:=source n t R0 u
  have HZ : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂
      (Int.castRingHom ℝ) z.val.val=0:=by
    rw [IntegralMixedOriginalRegularSource.source_polynomial]
    exact z.val.property
  let F : IntegralMixedFrozenFrame.Frame (n u+3):=IntegralMixedFrozenFrame.originalFrame ∅ (fun _=>false)
    (fun _=>IntegralMixedCausalRowConstructor.Row.single (none : IntegralMixedCausalRowConstructor.Atom 0))
  let old : Fin 0→ℝ:=Fin.elim0
  have HS : z.val.val∈IntegralMixedFrozenFrame.slice P F old:=
    ⟨HZ,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  have HP : IsProperMap (fun p : Fin (n u+3+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p):=
    IntegralMixedFrozenFrame.regular_source_proper (BoundedRegularLowCoefficient.readers n t R0) u
  obtain ⟨p,hp,hgrad⟩:=IntegralMixedFrozenFrame.exists_component_critical_of_proper P F old 0
    (Finset.notMem_empty _) HP _ HS
  refine ⟨p,(connectedComponentIn_subset _ _ hp).1,?_⟩
  intro i hi
  apply hgrad i (Finset.notMem_empty _)
  intro he
  exact hi (congrArg Fin.val he)

private def FirstCritical {a : ℕ} (P : SpatialSource a) : Prop:=
  ∃p : Fin (a+1)→ℝ,
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0

private theorem first_critical_transport {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b)
    (hd : a=b) (he : HEq P Q) : FirstCritical P→FirstCritical Q:=by
  cases hd
  have h : P=Q:=eq_of_heq he
  cases h
  exact id

variable (hR0 : BinaryFn R0)
local notation "ROOT"=>IntegralMixedRoadmapFirstSeed.root hn ht ha hR0
local notation "Q"=>(fun u label : List Bool=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (ROOT u label))
attribute [local irreducible] IntegralMixedRoadmapFirstSeed.root IntegralMixedAuxiliaryMarkedIntegerPlan.spatial

theorem exists_first_critical (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃p : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (ROOT u label)+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial (Q u label).low (Q u label).leading (Q u label).degree).eval₂
        (Int.castRingHom ℝ) p=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial (Q u label).low (Q u label).leading (Q u label).degree)).eval₂
          (Int.castRingHom ℝ) p=0 :=by
  have HO : IntegralMixedAuxiliaryMarkedIntegerSource.original (ROOT u label)=u:=by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedRoadmapFirstSeed.candidate_root,pairFst_pair]
  have HD : n u+3=IntegralMixedAuxiliaryMarkedIntegerSource.number n (ROOT u label)+3:=by
    rw [IntegralMixedRoadmapFirstSeed.number_root]
  have HS : HEq (source n t R0 u) (Q u label):=by
    change HEq (source n t R0 u) (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (ROOT u label))
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO).symm
  exact first_critical_transport _ _ HD HS (exists_original_critical hn ht ha u label hg hR)

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
