/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSectionLift
public import LeanCanny.Connectivity.FiberSectionLimit
public import LeanCanny.Connectivity.ComponentSlabCover

/-! # Actual regular critical sections saturate the whole coarse slab -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def sectionMap {X J : Type} [TopologicalSpace X] (p : X→ℝ) (A B : ℝ)
    (arc : J→ℝ→X) (HA : ∀ j,ContinuousOn (arc j) (Icc A B))
    (HL : ∀ j t,t∈Icc A B→p (arc j t)=t) (j : J) : C(Ioo A B,p ⁻¹' Ioo A B) where
  toFun t:=⟨arc j t.val,by
    change p (arc j t.val)∈Ioo A B
    rw [HL j t.val (Ioo_subset_Icc_self t.property)]
    exact t.property⟩
  continuous_toFun:=by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp ((HA j).mono Ioo_subset_Icc_self)

theorem interior_of_sections {J : Type} [Finite J] (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (A B : ℝ) (t₀ : Ioo A B) (hheight : ∀ t∈Ioo A B,(heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (arc : J→ℝ→slice P (coarse F h) values) (HA : ∀ j,ContinuousOn (arc j) (Icc A B))
    (HL : ∀ j t,t∈Icc A B→coarseProjection P F values h (arc j t)=t)
    (HS : ∀ t : Ioo A B,∀ y : slice P (coarse F h) values,
      coarseProjection P F values h y=t.val→∃ j,
        JoinedIn ((coarseProjection P F values h) ⁻¹' {t.val}) y (arc j t.val)) :
    ∃ D : ComponentSlabCover.InteriorData (coarseProjection P F values h) A B J,
      (∀ j,IsClopen (D.piece j)) ∧ (∀ j t,D.arc j t=arc j t) ∧
      ∀ i j,ClosedPathCover.Overlap D.piece i j↔
        JoinedIn (shiftedSlice P F values h t₀.val) (arc i t₀.val).val (arc j t₀.val).val := by
  let O:=Ioo A B
  let p:=coarseProjection P F values h
  let : ContractibleSpace O:=(convex_Ioo A B).contractibleSpace ⟨t₀.val,t₀.property⟩
  let sections:=sectionMap p A B arc HA HL
  have Hproj (j : J) (t : O) : O.restrictPreimage p (sections j t)=t:=
    Subtype.ext (HL j t.val (Ioo_subset_Icc_self t.property))
  have Hcover (y : p ⁻¹' O) : ∃ j,JoinedIn ((O.restrictPreimage p) ⁻¹' {O.restrictPreimage p y}) y
      (sections j (O.restrictPreimage p y)) := by
    obtain ⟨j,HJ⟩:=HS (O.restrictPreimage p y) y.val rfl
    exact ⟨j,(RegularComponentTransport.joinedIn_restrictPreimage_iff p O (O.restrictPreimage p y)
      y (sections j (O.restrictPreimage p y)) rfl (Hproj _ _)).mpr HJ⟩
  have HP:=coarseProjection_proper P F values h hp
  have HAB:=t₀.property.1.trans t₀.property.2
  obtain ⟨C,HC,HF⟩:=exists_charts x hm φ F h hh values H A B hheight
  let piece:=FiberSectionCover.piece (O.restrictPreimage p) sections
  have Hcl (j : J) : IsClopen (piece j):=
    FiberSectionCover.isClopen_piece (O.restrictPreimage p) sections C HC HF (HP.restrictPreimage O) Hproj j
  let D : ComponentSlabCover.InteriorData p A B J:={
    piece:=piece
    closed j:=(Hcl j).isClosed
    cover:=FiberSectionCover.cover (O.restrictPreimage p) sections Hcover
    paths:=FiberSectionCover.paths (O.restrictPreimage p) sections C HC HF (HP.restrictPreimage O) Hproj
    arc:=arc
    continuous_arc:=HA
    arc_mem j t:=⟨sections j t,FiberSectionCover.section_mem_piece (O.restrictPreimage p) sections Hproj j t,rfl⟩
    level_left j:=HL j A ⟨le_rfl,HAB.le⟩
    level_right j:=HL j B ⟨HAB.le,le_rfl⟩
    limit_left j:=(FiberSectionCover.isConnected_ambient_endpoint p sections C HC HF HP Hproj HAB j).isPreconnected
    limit_right j:=(FiberSectionCover.isConnected_ambient_endpoint_right p sections C HC HF HP Hproj HAB j).isPreconnected }
  refine ⟨D,Hcl,fun _ _=>rfl,?_⟩
  intro i j
  have HE:=FiberSectionCover.overlap_iff_sample (O.restrictPreimage p) sections C HC HF (HP.restrictPreimage O) Hproj t₀ i j
  have HJ:=RegularComponentTransport.joinedIn_restrictPreimage_iff p O t₀ (sections i t₀) (sections j t₀) (Hproj _ _) (Hproj _ _)
  have HK:=joined_fiber_iff P F values h hh t₀.val (arc i t₀.val) (arc j t₀.val)
    (HL i t₀.val (Ioo_subset_Icc_self t₀.property)) (HL j t₀.val (Ioo_subset_Icc_self t₀.property))
  exact HE.trans (HJ.trans HK)

theorem exists_interior_data (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ)
    (A B : ℝ) (t₀ : Ioo A B)
    (havoid : ∀ t∈Ioo A B,t∉IntegralMixedSelectedCriticalCuts.bad
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ c)
    (hheight : ∀ t∈Ioo A B,(heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    let I:=IntegralMixedSelectedPhysicalFiber.physical (IntegralMixedCoordinateRename.state x e) hm (sweep x F h hh g hg) φ t₀.val
    Finite I ∧ ∃ D : ComponentSlabCover.InteriorData (coarseProjection P F values h) A B I,
      (∀ j,IsClopen (D.piece j)) ∧
      (∀ j,(D.arc j t₀.val).val=j.val ∘ e.symm) ∧
      ∀ i j,ClosedPathCover.Overlap D.piece i j↔
        JoinedIn (shiftedSlice P F values h t₀.val) (D.arc i t₀.val).val (D.arc j t₀.val).val := by
  obtain ⟨Hfin,curve,HA,HC,HR,HS⟩:=exists_sections x hm φ F h hh g hg values H c A B t₀ havoid hheight hp
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ t₀.val):=Hfin
  obtain ⟨arc,Hcont,Hlevel,Hvalue,Hsample⟩:=exists_lift P F values h hh A B t₀ curve HC HR HS
  obtain ⟨D,Hcl,HD,HE⟩:=interior_of_sections x hm φ F h hh values H A B t₀ hheight hp arc Hcont Hlevel Hsample
  refine ⟨Hfin,D,Hcl,?_,?_⟩
  · intro j
    calc
      _=(arc j t₀.val).val:=congrArg Subtype.val (HD j _)
      _=curve j t₀.val:=Hvalue j _ (Ioo_subset_Icc_self t₀.property)
      _=j.val ∘ (FrozenCoordinateOrdering.permutation F.frozen).symm:=HA j
  · intro i j
    simpa only [HD] using HE i j

end LeanCanny.Geometry.IntegralMixedFrozenFrame
