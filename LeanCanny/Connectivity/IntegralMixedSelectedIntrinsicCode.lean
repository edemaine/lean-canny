/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedBranchCodes

/-! # Intrinsic words count actual physical fiber values

The word of a physical critical tuple uses only its current actual fiber.
It does not refer to a chosen arc family or independently lifted roots.
A bijection of actual fibers transports the word to the persistent branch
rank word, because both count the same finite coordinate image.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedIntrinsicCode
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def values (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (i : Free r) : Finset ℝ := by
  letI:=IntegralMixedSelectedBranchCodes.labelFintype x hm r φ t
  exact Finset.univ.image (fun j : physical x hm r φ t=>freeCoordinates r j.val i)

noncomputable def rank (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (i : Free r) : ℕ :=
  ((values x hm r φ t i).filter (fun y=>y<freeCoordinates r a.val i)).card

noncomputable def word (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) : List Bool :=
  FixedWidthNatVector.encode (n+1) (B*(n+1)+1)
    (fun k=>if hk : k<n-r.critical.offset.val+1 then rank x hm r φ t a ⟨k,hk⟩ else 0)

theorem word_length (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) :
    (word x hm r φ t a).length=IntegralMixedSelectedBranchCodes.width n B :=
  FixedWidthNatVector.length_encode _ _ _

theorem image_transport (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (s t : ℝ)
    (f : physical x hm r φ s→physical x hm r φ t) (hf : Function.Surjective f) (i : Free r) :
    letI:=IntegralMixedSelectedBranchCodes.labelFintype x hm r φ s
    (Finset.univ.image (fun j=>freeCoordinates r (f j).val i))=values x hm r φ t i := by
  unfold values
  ext y
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨f j,rfl⟩
  · rintro ⟨j,Hj⟩
    obtain ⟨k,rfl⟩:=hf j
    exact ⟨k,Hj⟩

theorem rank_transport (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (s t : ℝ)
    (f : physical x hm r φ s→physical x hm r φ t) (hf : Function.Surjective f)
    (a : physical x hm r φ s) (i : Free r) :
    letI:=IntegralMixedSelectedBranchCodes.labelFintype x hm r φ s
    letI:=IntegralMixedSelectedBranchCodes.labelOrder x hm r φ s
    rank x hm r φ t (f a) i=IntegralMixedSelectedBranchRanks.rank (fun j=>freeCoordinates r (f j).val) a i := by
  let :=IntegralMixedSelectedBranchCodes.labelFintype x hm r φ s
  let :=IntegralMixedSelectedBranchCodes.labelOrder x hm r φ s
  rw [IntegralMixedSelectedBranchRanks.rank,FiniteImageRank.rank_eq,image_transport x hm r φ s t f hf]
  rfl

theorem word_transport (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (s t : ℝ)
    (f : physical x hm r φ s→physical x hm r φ t) (hf : Function.Surjective f)
    (a : physical x hm r φ s) :
    word x hm r φ t (f a)=IntegralMixedSelectedBranchCodes.word x hm r φ s (fun j=>freeCoordinates r (f j).val) a := by
  unfold word IntegralMixedSelectedBranchCodes.word IntegralMixedSelectedBranchRanks.word
  congr 1
  funext i
  split_ifs with hi
  · exact rank_transport x hm r φ s t f hf a ⟨i,hi⟩
  · rfl

theorem word_injective (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) : Function.Injective (word x hm r φ t) := by
  let :=IntegralMixedSelectedBranchCodes.labelFintype x hm r φ t
  let :=IntegralMixedSelectedBranchCodes.labelOrder x hm r φ t
  have Hfree : Function.Injective (fun j : physical x hm r φ t=>freeCoordinates r j.val) := by
    intro j k Hjk
    apply Subtype.ext
    calc
      _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r j.val):=(reconstruct x hm r φ t j.val j.property.1).symm
      _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r k.val):=congrArg (IntegralMixedSweepRows.point x hm r φ t) Hjk
      _=k.val:=reconstruct x hm r φ t k.val k.property.1
  have Hcard : Fintype.card (physical x hm r φ t)≤2^(B*(n+1)) := by
    simpa only [Nat.card_eq_fintype_card] using (IntegralMixedFrozenFrame.physical_finite_card x hm r φ t).2
  have Hfit (j : physical x hm r φ t) (i : Free r) :
      IntegralMixedSelectedBranchRanks.rank (fun k : physical x hm r φ t=>freeCoordinates r k.val) j i<2^(B*(n+1)+1) :=
    ((IntegralMixedSelectedBranchRanks.rank_le _ j i).trans Hcard).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  intro j k Hword
  apply IntegralMixedSelectedBranchRanks.word_injective r _ _ Hfree Hfit
  exact (word_transport x hm r φ t t id Function.surjective_id j).symm.trans
    (Hword.trans (word_transport x hm r φ t t id Function.surjective_id k))

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
        Function.Injective code ∧ (∀ j,(code j).length=IntegralMixedSelectedBranchCodes.width n B) ∧
        ∀ j (t : Ioo a b),word x hm r φ t.val ⟨curve j t.val,HR j t.val (Ioo_subset_Icc_self t.property)⟩=code j := by
  obtain ⟨curve,HA,HC,HR,HE,code,HI,HL,HS⟩:=IntegralMixedSelectedBranchCodes.exists_codes x hm r φ c a b t₀ havoid
  refine ⟨curve,HR,HA,HC,HE,code,HI,HL,?_⟩
  intro j t
  let f : physical x hm r φ t₀.val→physical x hm r φ t.val:=fun k=>⟨curve k t.val,HR k t.val (Ioo_subset_Icc_self t.property)⟩
  have Hsurj : Function.Surjective f := by
    intro y
    obtain ⟨k,Hk,_⟩:=(HE t y.val).mp y.property
    exact ⟨k,Subtype.ext Hk⟩
  exact (word_transport x hm r φ t₀.val t.val f Hsurj j).trans (HS j t).symm

end LeanCanny.Connectivity.IntegralMixedSelectedIntrinsicCode
