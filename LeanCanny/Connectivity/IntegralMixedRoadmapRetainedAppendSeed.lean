/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendProgram
/-! # An accepted old vertex supplies a seed on the exact appended source -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def HasCritical {d :ℕ} (V :SpatialSource d):Prop:=
  ∃p :Fin (d+1)→ℝ,(FermatCriticalHomogenization.polynomial V.low V.leading V.degree).eval₂
    (Int.castRingHom ℝ) p=0 ∧ ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial V.low V.leading V.degree)).eval₂ (Int.castRingHom ℝ) p=0
private theorem critical_transport {a b :ℕ} (V :SpatialSource a) (W :SpatialSource b)
    (hd :a=b) (he :HEq V W):HasCritical V→HasCritical W:=by
  cases hd
  cases eq_of_heq he
  exact id

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] preparedRoot IntegralMixedRoadmapAtomic.dimension
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial

theorem exists_padding_critical (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (e :ℕ):
    ∃p :Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old e)+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).low
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).leading
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).degree).eval₂
          (Int.castRingHom ℝ) p=0 ∧ ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).low
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).leading
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)).degree)).eval₂
          (Int.castRingHom ℝ) p=0:=by
  have HO :IntegralMixedAuxiliaryMarkedIntegerSource.original (preparedRoot hn ht ha hR0 old e)=
      IntegralMixedRoadmapAtomic.original old:=by
    have HC :pairFst (preparedRoot hn ht ha hR0 old e)=IntegralMixedRoadmapAtomic.candidate old:=by
      simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
        pairFst_pair] using prepared_candidate hn ht ha hR0 old e
    exact congrArg pairFst HC
  have HD :n (pairFst (IntegralMixedRoadmapAtomic.candidate old))+3=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old e)+3:=by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,HO,IntegralMixedRoadmapAtomic.original]
  have HS :HEq (LeanCanny.Connectivity.IntegralMixedRoadmapGraph.originalSource
      (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old))
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (preparedRoot hn ht ha hR0 old e)):=by
    rw [spatial_source]
    exact (source_congr n t R0 _ _ HO).symm
  obtain ⟨p,hp,hg⟩:=LeanCanny.Connectivity.IntegralMixedRoadmapGraph.exists_global_seed hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  apply critical_transport _ _ HD HS
  exact ⟨p,hp,fun i hi=>hg i (fun h=>hi (congrArg Fin.val h))⟩

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
