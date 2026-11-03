/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphCoding
public import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentPaths
/-! # Actual graph vertices live in one original regular source

The candidate fixes one spatial domain. Accepted atomic words have literal
points in that domain, with source zero and the advertised critical rank.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.source IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension

noncomputable def originalSource (c : List Bool):=IntegralMixedOriginalRegularSource.source n t R0 (pairFst c)

theorem ambient_eq (c q : List Bool) (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    (B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))=n (pairFst c)+3 :=by
  rw [IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 q]
  exact congrArg (fun w : List Bool=>n (pairFst w)+3) hc

noncomputable def pointAt (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) : Fin (n (pairFst c)+3+1)→ℝ:=fun i=>
  IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 c q hc)).symm i)

private theorem cast_point_heq {a b : ℕ} (H : a=b) (p : Fin a→ℝ) :
    HEq p (fun i : Fin b=>p (Fin.cast H.symm i)) :=by cases H;rfl

private theorem occurrence_transport {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b)
    (H : a=b) (HP : HEq P Q) (p : Fin (a+1)→ℝ) (q : Fin (b+1)→ℝ) (Hp : HEq p q)
    (k : ℕ) (levels : ℕ→ℝ) (hz : IntegralMixedAtomicOccurrence.Occurrence P k levels p) :
    IntegralMixedAtomicOccurrence.Occurrence Q k levels q :=by
  cases H
  have HS : P=Q:=eq_of_heq HP
  have HX : p=q:=eq_of_heq Hp
  simpa only [HS,HX] using hz

theorem pointAt_occurrence (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    IntegralMixedAtomicOccurrence.Occurrence (originalSource (n:=n) (t:=t) (R0:=R0) c)
      (IntegralMixedRoadmapAtomic.depth q) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hv)
        (pointAt hn ht ha hR0 c q hv hc) :=by
  have HS:=IntegralMixedRoadmapAtomic.source_original hn ht ha hR0 q hv
  have HO : IntegralMixedRoadmapAtomic.original q=pairFst c:=congrArg pairFst hc
  rw [HO] at HS
  exact occurrence_transport (IntegralMixedRoadmapAtomic.source hn ht ha hR0 q) _
    (ambient_eq hn ht ha hR0 c q hc) HS (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) _
    (cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c q hc)) _) _ _
    (IntegralMixedRoadmapAtomic.occurrence hn ht ha hR0 q hv)

theorem pointAt_zero (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    (FermatCriticalHomogenization.polynomial (originalSource (n:=n) (t:=t) (R0:=R0) c).low
      (originalSource (n:=n) (t:=t) (R0:=R0) c).leading (originalSource (n:=n) (t:=t) (R0:=R0) c).degree).eval₂
        (Int.castRingHom ℝ) (pointAt hn ht ha hR0 c q hv hc)=0 :=
  (pointAt_occurrence hn ht ha hR0 c q hv hc).zero

theorem original_proper (c : List Bool) : IsProperMap (fun p : Fin (n (pairFst c)+3+1)→ℝ=>
    (FermatCriticalHomogenization.polynomial (originalSource (n:=n) (t:=t) (R0:=R0) c).low
      (originalSource (n:=n) (t:=t) (R0:=R0) c).leading (originalSource (n:=n) (t:=t) (R0:=R0) c).degree).eval₂
        (Int.castRingHom ℝ) p) :=
  IntegralMixedFrozenFrame.regular_source_proper (BoundedRegularLowCoefficient.readers n t R0) (pairFst c)

/-- A genuine global critical seed is constructed from any accepted vertex. -/
theorem exists_global_seed (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    ∃p : Fin (n (pairFst c)+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial (originalSource (n:=n) (t:=t) (R0:=R0) c).low
        (originalSource (n:=n) (t:=t) (R0:=R0) c).leading (originalSource (n:=n) (t:=t) (R0:=R0) c).degree).eval₂
          (Int.castRingHom ℝ) p=0 ∧ ∀i,i≠0→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (originalSource (n:=n) (t:=t) (R0:=R0) c).low
        (originalSource (n:=n) (t:=t) (R0:=R0) c).leading (originalSource (n:=n) (t:=t) (R0:=R0) c).degree)).eval₂
          (Int.castRingHom ℝ) p=0 :=by
  let P:=originalSource (n:=n) (t:=t) (R0:=R0) c
  let F : IntegralMixedFrozenFrame.Frame (n (pairFst c)+3):=IntegralMixedFrozenFrame.originalFrame ∅ (fun _=>false)
    (fun _=>IntegralMixedCausalRowConstructor.Row.single (none : IntegralMixedCausalRowConstructor.Atom 0))
  let old : Fin 0→ℝ:=Fin.elim0
  have HS : pointAt hn ht ha hR0 c q hv hc∈IntegralMixedFrozenFrame.slice P F old:=
    ⟨pointAt_zero hn ht ha hR0 c q hv hc,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  obtain ⟨p,HP,HG⟩:=IntegralMixedFrozenFrame.exists_component_critical_of_proper P F old 0
    (Finset.notMem_empty _) (original_proper (n:=n) (t:=t) (R0:=R0) c) _ HS
  exact ⟨p,(connectedComponentIn_subset _ _ HP).1,fun i hi=>HG i (Finset.notMem_empty _) hi⟩

theorem identity_pointAt_eq (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (hI : pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0) :
    pointAt hn ht ha hR0 c a hA hc=pointAt hn ht ha hR0 c b hB hd :=by
  have HI:=(IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 a b hA hB (hc.trans hd.symm)).mp hI
  have HAI : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 a hA)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 a hA):=
    cast_point_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 a)) _
  have HBI : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 b hB)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 b hB):=
    cast_point_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 b)) _
  have HA0 : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 a hA) (pointAt hn ht ha hR0 c a hA hc):=
    cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c a hc)) _
  have HB0 : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 b hB) (pointAt hn ht ha hR0 c b hB hd):=
    cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c b hd)) _
  exact eq_of_heq (HA0.symm.trans (HAI.trans (HI.trans (HBI.symm.trans HB0))))

noncomputable def zeroSet (c : List Bool) : Set (Fin (n (pairFst c)+3+1)→ℝ):={p |
  (FermatCriticalHomogenization.polynomial (originalSource (n:=n) (t:=t) (R0:=R0) c).low
    (originalSource (n:=n) (t:=t) (R0:=R0) c).leading (originalSource (n:=n) (t:=t) (R0:=R0) c).degree).eval₂
      (Int.castRingHom ℝ) p=0}

noncomputable def frozenSlice (c : List Bool) (k : ℕ) (levels : ℕ→ℝ) : Set (Fin (n (pairFst c)+3+1)→ℝ):=
  zeroSet (n:=n) (t:=t) (R0:=R0) c∩{p |∀i : Fin (n (pairFst c)+3+1),i.val<k→p i=levels i.val}

theorem pointAt_mem (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    pointAt hn ht ha hR0 c q hv hc∈frozenSlice (n:=n) (t:=t) (R0:=R0) c
      (IntegralMixedRoadmapAtomic.depth q) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hv) :=
  ⟨(pointAt_occurrence hn ht ha hR0 c q hv hc).zero,(pointAt_occurrence hn ht ha hR0 c q hv hc).frozen⟩

theorem identity_joined (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (hI : pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c) (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=by
  rw [←identity_pointAt_eq hn ht ha hR0 c a b hA hB hc hd hI]
  exact JoinedIn.refl (pointAt_zero hn ht ha hR0 c a hA hc)

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
