/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedRootRank
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalArcs
/-! # Correlated physical branches have persistent scalar-root words

A physical midpoint tuple anchors the actual branch. Ghost coordinate roots
only create unused ordinals. The constructed code uses the complete selected
scalar root sets and retains the same old interpreting hom throughout.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedRootCodes
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_codes (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c) :
    ∃ curve : physical x hm r φ t₀.val→ℝ→Fin (n+1)→ℝ,
    ∃ HR : ∀ j t,t∈Icc a b→curve j t∈physical x hm r φ t,
      (∀ j,curve j t₀.val=j.val) ∧
      (∀ j,ContinuousOn (curve j) (Icc a b)) ∧
      (∀ t : Ioo a b,∀ y,y∈physical x hm r φ t.val↔∃! j,curve j t.val=y) ∧
      ∃ code : physical x hm r φ t₀.val→List Bool,
        Function.Injective code ∧ (∀ j,(code j).length=(n+1)*B) ∧
        ∀ j (t : Ioo a b),IntegralMixedFrozenFrameSectionCode.word x hm r φ t.val
          ⟨curve j t.val,HR j t.val (Ioo_subset_Icc_self t.property)⟩=code j := by
  obtain ⟨_,curve,HA,HC,HR,HE,_⟩:=IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs x hm r φ c a b t₀ havoid
  let code : physical x hm r φ t₀.val→List Bool:=IntegralMixedFrozenFrameSectionCode.word x hm r φ t₀.val
  refine ⟨curve,HR,HA,HC,HE,code,IntegralMixedFrozenFrameSectionCode.word_injective x hm r φ t₀.val,
    fun j=>IntegralMixedFrozenFrameSectionCode.word_length x hm r φ t₀.val j,?_⟩
  intro j t
  let f : C(Ioo a b,Fin (n+1)→ℝ):=⟨fun u=>curve j u.val,
    continuousOn_iff_continuous_domRestrict.mp ((HC j).mono Ioo_subset_Icc_self)⟩
  have HF (u : Ioo a b) : f u∈physical x hm r φ u.val:=HR j u.val (Ioo_subset_Icc_self u.property)
  have Hcut (u : ℝ) (hu : u∈Ioo a b) (i : Free r) :
      (IntegralMixedCoordinateSquarefree.exceptional x hm r i (c.squarefreeIndex i)).eval₂ φ.toRingHom u≠0 :=
    fun HZ=>havoid u hu ⟨(1,i),HZ⟩
  have HS:=IntegralMixedSelectedRootRank.word_constant x hm r φ c.squarefreeIndex c.squarefreeValid Hcut f HF t₀ t
  have HJ : (⟨f t₀,HF t₀⟩ : physical x hm r φ t₀.val)=j:=Subtype.ext (HA j)
  rw [HJ] at HS
  exact HS.symm

end LeanCanny.Connectivity.IntegralMixedSelectedRootCodes
