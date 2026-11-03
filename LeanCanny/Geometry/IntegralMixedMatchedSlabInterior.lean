/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealInterior
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
public import LeanCanny.Connectivity.ComponentSlabAnchorEndpoints
/-! # One matched physical family and its literal slab interior

The ordinal codes, closed branches and transported component pieces are
constructed together. No independently chosen branch families are identified.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

structure MatchedSlabInterior (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (h : Fin (n+1)) (hh : h∈F.frozen) (g : Fin (n+1)) (hg : g∉F.frozen)
    (values : Fin m→ℝ) (a b : ℝ) (t₀ : Ioo a b) where
  finite_index : Finite (IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t₀.val)
  curve : IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t₀.val→ℝ→Fin (n+1)→ℝ
  physical : ∀j t,t∈Icc a b→curve j t∈IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t
  anchor : ∀j,curve j t₀.val=j.val
  continuous : ∀j,ContinuousOn (curve j) (Icc a b)
  complete : ∀t : Ioo a b,∀y,y∈IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t.val↔∃!j,curve j t.val=y
  code : IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t₀.val→List Bool
  code_injective : Function.Injective code
  code_length : ∀j,(code j).length=(n+1)*B
  code_word : ∀j (t : Ioo a b),IntegralMixedFrozenFrameSectionCode.word
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t.val
    ⟨curve j t.val,physical j t.val (Ioo_subset_Icc_self t.property)⟩=code j
  near : ∀j endpoint,∀_he : endpoint∈Icc a b,∀y : Fin (n+1)→ℝ,
    ∀_hy : IntegralMixedSelectedCoordinateEndpoint.Frozen
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ endpoint y,
    (∀i : Free (sweep x F h hh g hg),IntegralMixedSelectedCoordinateEndpoint.Near
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ a b endpoint i
      (IntegralMixedSelectedCoordinateEndpoint.digit B (code j) i)
      (y (ClearedCoordinateCritical.freeIndex (sweep x F h hh g hg).critical.offset.val
        (fit (sweep x F h hh g hg)).le i)))↔curve j endpoint=y
  interior : ComponentSlabCover.InteriorData (coarseProjection P F values h) a b
    (IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val)
  clopen : ∀j,IsClopen (interior.piece j)
  readback : ∀j t,t∈Icc a b→(interior.arc j t).val=
    curve j t∘(FrozenCoordinateOrdering.permutation F.frozen).symm
  overlap : ∀i j,ClosedPathCover.Overlap interior.piece i j↔
    JoinedIn (shiftedSlice P F values h t₀.val)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (j.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)

theorem exists_matched_slab_interior (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (h : Fin (n+1)) (hh : h∈F.frozen) (g : Fin (n+1)) (hg : g∉F.frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ) (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ c)
    (hheight : ∀t∈Ioo a b,t∉realCriticalValues P F values h)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    Nonempty (MatchedSlabInterior x hm φ F h hh g hg values a b t₀) :=by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let x':=IntegralMixedCoordinateRename.state x e
  let r:=sweep x F h hh g hg
  have HI : Finite (IntegralMixedSelectedPhysicalFiber.physical x' hm r φ t₀.val):=
    (IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs x' hm r φ c a b t₀ havoid).1
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical x' hm r φ t₀.val):=HI
  obtain ⟨curve,HR,HA,HC,HE,code,Hinj,Hlen,Hword,Hnear⟩:=
    IntegralMixedSelectedCoordinateEndpoint.exists_matched_codes x' hm r φ c a b t₀ havoid
  have Hslice (j) (t) (ht : t∈Icc a b) : curve j t∘e.symm∈shiftedSlice P F values h t:=
    physical_mem_shiftedSlice x hm φ F h hh g hg values H t (curve j t) (HR j t ht)
  have Hcont (j) : ContinuousOn (fun t=>curve j t∘e.symm) (Icc a b):=
    (continuous_pi (fun i=>continuous_apply (e.symm i))).comp_continuousOn (HC j)
  have Hsample (t : Ioo a b) (y) (hy : y∈shiftedSlice P F values h t.val) :
      ∃j,JoinedIn (shiftedSlice P F values h t.val) y (curve j t.val∘e.symm):=by
    obtain ⟨z,hz,hphys⟩:=exists_path_sample_of_realCriticalValues x hm φ F h hh g hg values H
      t.val (hheight t.val t.property) y hy hp
    obtain ⟨j,Hj,_⟩:=(HE t (z∘e)).mp hphys
    refine ⟨j,?_⟩
    rw [Hj]
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using hz
  obtain ⟨arc,Hcontinuous,Hlevel,Hvalue,Hcover⟩:=
    exists_lift P F values h hh a b t₀ (fun j t=>curve j t∘e.symm) Hcont Hslice Hsample
  obtain ⟨D,Hcl,HD,Hoverlap⟩:=interior_of_sections_of_realCriticalValues x hm φ F h hh values H
    a b t₀ hheight hp arc Hcontinuous Hlevel Hcover
  have Hread (j) (t) (ht : t∈Icc a b) : (D.arc j t).val=curve j t∘e.symm:=by
    rw [HD]
    exact Hvalue j t ht
  refine ⟨{ finite_index := HI
            curve := curve
            physical := HR
            anchor := HA
            continuous := HC
            complete := HE
            code := code
            code_injective := Hinj
            code_length := Hlen
            code_word := Hword
            near := Hnear
            interior := D
            clopen := Hcl
            readback := Hread
            overlap := ?_ }⟩
  intro i j
  have HEQ:=Hoverlap i j
  rw [←HD i,←HD j,Hread i t₀.val (Ioo_subset_Icc_self t₀.property),
    Hread j t₀.val (Ioo_subset_Icc_self t₀.property),HA i,HA j] at HEQ
  exact HEQ

end LeanCanny.Geometry.IntegralMixedFrozenFrame
