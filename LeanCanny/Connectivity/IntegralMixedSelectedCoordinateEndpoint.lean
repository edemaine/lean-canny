/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedRootCodes
/-! # Scalar-root ordinal limits of a validated physical branch

Only the midpoint tuple is used to anchor the physical branch. A scalar
root with its ordinal is unique throughout the retained slab, even when
other scalar roots never belong to physical critical points.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
open Set LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def Near (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint : ℝ) (i : Free r) (code : ℕ) (y : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε→∀ δ : ℝ,0<δ→∃ t : ℝ,t∈Ioo a b ∧ dist t endpoint<δ ∧
    ∃ z : ℝ,z∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ t i ∧
      IntegralMixedSelectedRootRank.rank x hm r φ t i z=code ∧ dist z y<ε

def Frozen (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (y : Fin (n+1)→ℝ) : Prop :=
  ∀ i,i.val<r.critical.offset.val→((data x hm r.critical).scales i : ℝ)*y i=heightValue x r φ t i

theorem near_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (i : Free r)
    (c : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : IntegralMixedCoordinateSquarefree.Valid x hm r i φ c) {a b : ℝ} (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,(IntegralMixedCoordinateSquarefree.exceptional x hm r i c).eval₂ φ.toRingHom t≠0)
    (f : ℝ→Fin (n+1)→ℝ) (HC : ContinuousOn f (Icc a b))
    (HR : ∀ t,t∈Icc a b→f t∈physical x hm r φ t)
    (endpoint : ℝ) (Hend : endpoint∈Icc a b) (y : ℝ) :
    Near x hm r φ a b endpoint i
      (IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i
        (f t₀.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i))) y↔
      f endpoint (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)=y := by
  let index:=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i
  let coord (t : ℝ):=f t index
  let g : C(Ioo a b,Free r→ℝ):=⟨fun t=>freeCoordinates r (f t.val),by
    have HG : Continuous (freeCoordinates r):=continuous_pi (fun _=>continuous_apply _)
    exact continuousOn_iff_continuous_domRestrict.mp ((HG.comp_continuousOn HC).mono Ioo_subset_Icc_self)⟩
  have HG (t : Ioo a b) : (selected x hm r i φ).eval₂ (Polynomial.evalRingHom t.val) (g t i)=0 :=
    (IntegralMixedSelectedRootRank.mem_roots x hm r φ t.val i _).mp
      (IntegralMixedFrozenFrameSectionCode.coordinate_mem x hm r φ t.val ⟨f t.val,HR t.val (Ioo_subset_Icc_self t.property)⟩ i)
  have HK (t : Ioo a b) : IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i (coord t₀.val)=
      IntegralMixedSelectedRootRank.rank x hm r φ t.val i (coord t.val) :=
    IntegralMixedSelectedRootRank.constant x hm r φ i c hc havoid g HG t₀ t
  have HU (t : Ioo a b) (z : ℝ) (hz : z∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ t.val i)
      (hk : IntegralMixedSelectedRootRank.rank x hm r φ t.val i z=
        IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i (coord t₀.val)) : z=coord t.val :=
    (IntegralMixedSelectedRootRank.rank_injective x hm r φ t.val i z (coord t.val) hz
      (IntegralMixedFrozenFrameSectionCode.coordinate_mem x hm r φ t.val ⟨f t.val,HR t.val (Ioo_subset_Icc_self t.property)⟩ i)).mp
      (hk.trans (HK t))
  have Hcoord : ContinuousOn coord (Icc a b):=(continuous_apply index).comp_continuousOn HC
  have Hcont:=Metric.continuousWithinAt_iff.mp (Hcoord endpoint Hend)
  have HAB : a<b:=t₀.property.1.trans t₀.property.2
  constructor
  · intro Hnear
    by_contra Hne
    have HD : 0<dist (coord endpoint) y:=dist_pos.mpr Hne
    obtain ⟨δ,Hδ,Hwithin⟩:=Hcont (dist (coord endpoint) y/3) (by positivity)
    obtain ⟨t,Ht,Hdist,z,Hroot,Hrank,Hzy⟩:=Hnear (dist (coord endpoint) y/3) (by positivity) δ Hδ
    have Hz:=HU ⟨t,Ht⟩ z Hroot Hrank
    have HCt:=Hwithin (Ioo_subset_Icc_self Ht) Hdist
    have Htri:=dist_triangle (coord endpoint) (coord t) y
    rw [Hz] at Hzy
    rw [dist_comm (coord endpoint) (coord t)] at Htri
    linarith
  · intro Hy
    subst y
    intro ε Hε δ Hδ
    obtain ⟨η,Hη,Hwithin⟩:=Hcont ε Hε
    have HEclosure : endpoint∈closure (Ioo a b) := by rw [closure_Ioo HAB.ne]; exact Hend
    obtain ⟨t,Ht,Hdist⟩:=Metric.mem_closure_iff.mp HEclosure (min δ η) (lt_min Hδ Hη)
    have Hdist' : dist t endpoint<min δ η:=by rwa [dist_comm]
    exact ⟨t,Ht,Hdist'.trans_le (min_le_left _ _),coord t,
      IntegralMixedFrozenFrameSectionCode.coordinate_mem x hm r φ t ⟨f t,HR t (Ioo_subset_Icc_self Ht)⟩ i,
      (HK ⟨t,Ht⟩).symm,Hwithin (Ioo_subset_Icc_self Ht) (Hdist'.trans_le (min_le_right _ _))⟩


theorem point_near_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    {a b : ℝ} (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c)
    (f : ℝ→Fin (n+1)→ℝ) (HC : ContinuousOn f (Icc a b))
    (HR : ∀ t,t∈Icc a b→f t∈physical x hm r φ t)
    (endpoint : ℝ) (Hend : endpoint∈Icc a b) (y : Fin (n+1)→ℝ) (hy : Frozen x hm r φ endpoint y) :
    (∀ i : Free r,Near x hm r φ a b endpoint i
      (IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i
        (f t₀.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)))
      (y (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)))↔f endpoint=y := by
  have HA (i : Free r) :=near_iff x hm r φ i (c.squarefreeIndex i) (c.squarefreeValid i) t₀
    (fun t ht HZ=>havoid t ht ⟨(1,i),HZ⟩) f HC HR endpoint Hend
    (y (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i))
  constructor
  · intro Hnear
    have Hfree : freeCoordinates r (f endpoint)=freeCoordinates r y :=funext (fun i=>(HA i).mp (Hnear i))
    calc
      _=IntegralMixedSweepRows.point x hm r φ endpoint (freeCoordinates r (f endpoint)):=
        (reconstruct x hm r φ endpoint (f endpoint) (HR endpoint Hend).1).symm
      _=IntegralMixedSweepRows.point x hm r φ endpoint (freeCoordinates r y):=
        congrArg (IntegralMixedSweepRows.point x hm r φ endpoint) Hfree
      _=y:=reconstruct x hm r φ endpoint y hy
  · intro HE i
    apply (HA i).mpr
    exact congrFun HE _

def digit {r : Rule n} (B : ℕ) (word : List Bool) (i : Free r) : ℕ :=
  Nat.fromBitsLE ((word.drop (i.val*B)).take B)

theorem exists_matched_codes (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c) :
    ∃ curve : physical x hm r φ t₀.val→ℝ→Fin (n+1)→ℝ,
    ∃ HR : ∀ j t,t∈Icc a b→curve j t∈physical x hm r φ t,
      (∀ j,curve j t₀.val=j.val) ∧ (∀ j,ContinuousOn (curve j) (Icc a b)) ∧
      (∀ t : Ioo a b,∀ y,y∈physical x hm r φ t.val↔∃! j,curve j t.val=y) ∧
      ∃ code : physical x hm r φ t₀.val→List Bool,
        Function.Injective code ∧ (∀ j,(code j).length=(n+1)*B) ∧
        (∀ j (t : Ioo a b),IntegralMixedFrozenFrameSectionCode.word x hm r φ t.val
          ⟨curve j t.val,HR j t.val (Ioo_subset_Icc_self t.property)⟩=code j) ∧
        ∀ j endpoint,∀ _Hend : endpoint∈Icc a b,∀ y : Fin (n+1)→ℝ,∀ _hy : Frozen x hm r φ endpoint y,
          (∀ i : Free r,Near x hm r φ a b endpoint i (digit B (code j) i)
            (y (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)))↔curve j endpoint=y := by
  obtain ⟨curve,HR,HA,HC,HE,code,HI,HL,HS⟩:=IntegralMixedSelectedRootCodes.exists_codes x hm r φ c a b t₀ havoid
  refine ⟨curve,HR,HA,HC,HE,code,HI,HL,HS,?_⟩
  intro j endpoint Hend y hy
  have Hanchor : (⟨curve j t₀.val,HR j t₀.val (Ioo_subset_Icc_self t₀.property)⟩ : physical x hm r φ t₀.val)=j :=
    Subtype.ext (HA j)
  have Hcode:=HS j t₀
  rw [Hanchor] at Hcode
  have HD (i : Free r) : digit B (code j) i=IntegralMixedSelectedRootRank.rank x hm r φ t₀.val i
      (curve j t₀.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)) := by
    rw [←Hcode]
    unfold digit
    rw [IntegralMixedFrozenFrameSectionCode.word_digit,IntegralMixedSelectedRootRank.ordinal_rank,HA j]
  apply Iff.trans ?_ (point_near_iff x hm r φ c t₀ havoid (curve j) (HC j) (HR j) endpoint Hend y hy)
  apply forall_congr'
  intro i
  rw [HD i]

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
