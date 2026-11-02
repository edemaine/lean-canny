/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedIntrinsicCode

/-! # A curve-free one-sided matching predicate for actual critical endpoints

An intrinsic word and an actual critical tuple near a cut determine the
endpoint of exactly one selected critical arc. The local predicate mentions
only current physical fibers, their finite-value words and metric tests.
Its native relative-parameter cost is not assumed or proved here.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedEndpointMatch
open Set LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def Near (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint : ℝ)
    (code : List Bool) (y : Fin (n+1)→ℝ) : Prop :=
  ∀ ε : ℝ,0<ε→∀ δ : ℝ,0<δ→∃ t : ℝ,t∈Ioo a b ∧ dist t endpoint<δ ∧
    ∃ v : physical x hm r φ t,IntegralMixedSelectedIntrinsicCode.word x hm r φ t v=code ∧ dist v.val y<ε

theorem near_word_length (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint : ℝ) (code : List Bool)
    (y : Fin (n+1)→ℝ) (H : Near x hm r φ a b endpoint code y) :
    code.length=IntegralMixedSelectedBranchCodes.width n B := by
  obtain ⟨t,_,_,v,HV,_⟩:=H 1 (by norm_num) 1 (by norm_num)
  rw [←HV]
  exact IntegralMixedSelectedIntrinsicCode.word_length x hm r φ t v

theorem near_nil_false (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint : ℝ) (y : Fin (n+1)→ℝ) :
    ¬Near x hm r φ a b endpoint [] y := by
  intro H
  have HL:=near_word_length x hm r φ a b endpoint [] y H
  have HP : 0<(n+1)*(B*(n+1)+1):=Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  change 0=(n+1)*(B*(n+1)+1) at HL
  omega

theorem exists_matched_codes (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c) :
    ∃ curve : physical x hm r φ t₀.val→ℝ→Fin (n+1)→ℝ,
    ∃ HR : ∀ j t,t∈Icc a b→curve j t∈physical x hm r φ t,
      (∀ j,curve j t₀.val=j.val) ∧
      (∀ j,ContinuousOn (curve j) (Icc a b)) ∧
      (∀ t : Ioo a b,∀ y,y∈physical x hm r φ t.val↔∃! j,curve j t.val=y) ∧
      ∃ code : physical x hm r φ t₀.val→List Bool,
        Function.Injective code ∧ (∀ j,(code j).length=IntegralMixedSelectedBranchCodes.width n B) ∧
        (∀ j (t : Ioo a b),IntegralMixedSelectedIntrinsicCode.word x hm r φ t.val
          ⟨curve j t.val,HR j t.val (Ioo_subset_Icc_self t.property)⟩=code j) ∧
        ∀ j endpoint,endpoint∈Icc a b→∀ y,Near x hm r φ a b endpoint (code j) y↔curve j endpoint=y := by
  obtain ⟨curve,HR,HA,HC,HE,code,HI,HL,HS⟩:=IntegralMixedSelectedIntrinsicCode.exists_codes x hm r φ c a b t₀ havoid
  have HU (j : physical x hm r φ t₀.val) (t : Ioo a b) (v : physical x hm r φ t.val)
      (HV : IntegralMixedSelectedIntrinsicCode.word x hm r φ t.val v=code j) : v.val=curve j t.val := by
    obtain ⟨k,Hk,_⟩:=(HE t v.val).mp v.property
    have HK : v=⟨curve k t.val,HR k t.val (Ioo_subset_Icc_self t.property)⟩:=Subtype.ext Hk.symm
    rw [HK,HS] at HV
    have Hkj:=HI HV
    subst k
    exact Hk.symm
  refine ⟨curve,HR,HA,HC,HE,code,HI,HL,HS,?_⟩
  intro j endpoint Hend y
  have Hcont:=Metric.continuousWithinAt_iff.mp (HC j endpoint Hend)
  have HAB : a<b:=t₀.property.1.trans t₀.property.2
  constructor
  · intro Hnear
    by_contra Hne
    have HD : 0<dist (curve j endpoint) y:=dist_pos.mpr Hne
    obtain ⟨δ,Hδ,Hwithin⟩:=Hcont (dist (curve j endpoint) y/3) (by positivity)
    obtain ⟨t,Ht,Hdist,v,Hword,Hvy⟩:=Hnear (dist (curve j endpoint) y/3) (by positivity) δ Hδ
    have Hvt:=HU j ⟨t,Ht⟩ v Hword
    have HCt:=Hwithin (Ioo_subset_Icc_self Ht) Hdist
    have Htri:=dist_triangle (curve j endpoint) (curve j t) y
    rw [Hvt] at Hvy
    rw [dist_comm (curve j endpoint) (curve j t)] at Htri
    linarith
  · intro Hy
    subst y
    intro ε Hε δ Hδ
    obtain ⟨η,Hη,Hwithin⟩:=Hcont ε Hε
    have HEclosure : endpoint∈closure (Ioo a b) := by rw [closure_Ioo HAB.ne]; exact Hend
    obtain ⟨t,Ht,Hdist⟩:=Metric.mem_closure_iff.mp HEclosure (min δ η) (lt_min Hδ Hη)
    have Hdist' : dist t endpoint<min δ η:=by rwa [dist_comm]
    exact ⟨t,Ht,Hdist'.trans_le (min_le_left _ _),
      ⟨curve j t,HR j t (Ioo_subset_Icc_self Ht)⟩,HS j ⟨t,Ht⟩,
      Hwithin (Ioo_subset_Icc_self Ht) (Hdist'.trans_le (min_le_right _ _))⟩

theorem near_fiber (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c)
    (endpoint : ℝ) (Hend : endpoint∈Icc a b) (raw : List Bool) :
    {y | Near x hm r φ a b endpoint raw y}.Subsingleton ∧
      {y | Near x hm r φ a b endpoint raw y}⊆physical x hm r φ endpoint := by
  obtain ⟨curve,HR,_,_,HE,code,HI,_,HS,HM⟩:=exists_matched_codes x hm r φ c a b t₀ havoid
  have Hindex (y : Fin (n+1)→ℝ) (Hy : Near x hm r φ a b endpoint raw y) :
      ∃ j,code j=raw ∧ curve j endpoint=y := by
    obtain ⟨t,Ht,_,v,HV,_⟩:=Hy 1 (by norm_num) 1 (by norm_num)
    obtain ⟨j,Hj,_⟩:=(HE ⟨t,Ht⟩ v.val).mp v.property
    have Hv : v=⟨curve j t,HR j t (Ioo_subset_Icc_self Ht)⟩:=Subtype.ext Hj.symm
    have HC : code j=raw:=(HS j ⟨t,Ht⟩).symm.trans
      ((congrArg (IntegralMixedSelectedIntrinsicCode.word x hm r φ t) Hv.symm).trans HV)
    refine ⟨j,HC,(HM j endpoint Hend y).mp ?_⟩
    rw [HC]
    exact Hy
  constructor
  · intro y Hy z Hz
    obtain ⟨j,Hj,HEj⟩:=Hindex y Hy
    obtain ⟨k,Hk,HEk⟩:=Hindex z Hz
    have Hjk:=HI (Hj.trans Hk.symm)
    subst k
    exact HEj.symm.trans HEk
  · intro y Hy
    obtain ⟨j,_,HEj⟩:=Hindex y Hy
    rw [←HEj]
    exact HR j endpoint Hend

end LeanCanny.Connectivity.IntegralMixedSelectedEndpointMatch
