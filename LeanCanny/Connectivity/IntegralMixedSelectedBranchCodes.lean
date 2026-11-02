/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedBranchRanks
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalArcs

/-! # Constructed selected critical branches have persistent bounded words

Ranks count the distinct coordinate values of the actual physical critical
fiber, including shared coordinate values. The selected PSC cuts prove
persistence. The words are semantic branch labels; their native validation
and endpoint attachment remain separate cost obligations.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedBranchCodes
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

@[instance_reducible] noncomputable def labelFintype (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (anchor : ℝ) : Fintype (physical x hm r φ anchor) := by
  letI : Finite (physical x hm r φ anchor):=(IntegralMixedFrozenFrame.physical_finite_card x hm r φ anchor).1
  exact Fintype.ofFinite _

@[instance_reducible] noncomputable def labelOrder (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (anchor : ℝ) : LinearOrder (physical x hm r φ anchor) :=
  LinearOrder.lift' (IntegralMixedFrozenFrameSectionCode.word x hm r φ anchor)
    (IntegralMixedFrozenFrameSectionCode.word_injective x hm r φ anchor)

noncomputable def word (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (anchor : ℝ)
    (curve : physical x hm r φ anchor→Free r→ℝ) (j : physical x hm r φ anchor) : List Bool := by
  letI:=labelFintype x hm r φ anchor
  letI:=labelOrder x hm r φ anchor
  exact IntegralMixedSelectedBranchRanks.word r (B*(n+1)+1) curve j

def width (n B : ℕ) := (n+1)*(B*(n+1)+1)

theorem width_unary {n B : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) :
    UnaryFn (fun q=>width (n q) (B q)) :=
  (hn.add (UnaryFn.const 1)).mul ((hB.mul (hn.add (UnaryFn.const 1))).add (UnaryFn.const 1))

theorem exists_codes (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad x hm r φ c) :
    ∃ curve : physical x hm r φ t₀.val→ℝ→Fin (n+1)→ℝ,
      (∀ j,curve j t₀.val=j.val) ∧
      (∀ j,ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t,t∈Icc a b→curve j t∈physical x hm r φ t) ∧
      (∀ t : Ioo a b,∀ y,y∈physical x hm r φ t.val↔∃! j,curve j t.val=y) ∧
      ∃ code : physical x hm r φ t₀.val→List Bool,
        Function.Injective code ∧ (∀ j,(code j).length=width n B) ∧
        ∀ j (t : Ioo a b),code j=word x hm r φ t₀.val (fun k=>freeCoordinates r (curve k t.val)) j := by
  obtain ⟨_,curve,HA,HC,HR,HE,_⟩:=IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs x hm r φ c a b t₀ havoid
  let J:=physical x hm r φ t₀.val
  let :=labelFintype x hm r φ t₀.val
  let :=labelOrder x hm r φ t₀.val
  let f (j : J) : C(Ioo a b,Free r→ℝ):=⟨fun t=>freeCoordinates r (curve j t.val),by
    have HF : Continuous (freeCoordinates r):=continuous_pi (fun _=>continuous_apply _)
    exact continuousOn_iff_continuous_domRestrict.mp ((HF.comp_continuousOn (HC j)).mono Ioo_subset_Icc_self)⟩
  have HFroot (j : J) (t : Ioo a b) (i : Free r) :
      (selected x hm r i φ).eval₂ (Polynomial.evalRingHom t.val) (f j t i)=0 :=
    by
      change (selected x hm r i φ).eval₂ (Polynomial.evalRingHom t.val)
        (curve j t.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i))=0
      simpa only [Polynomial.eval_map] using
        IntegralMixedFrozenFrame.physical_coordinate_root x hm r φ t.val ⟨curve j t.val,HR j t.val (Ioo_subset_Icc_self t.property)⟩ i
  have Hcut (t : ℝ) (ht : t∈Ioo a b) (i : Free r) :
      (IntegralMixedCoordinateSquarefree.exceptional x hm r i (c.squarefreeIndex i)).eval₂ φ.toRingHom t≠0 :=
    fun HZ=>havoid t ht ⟨(1,i),HZ⟩
  have Hanchor : (fun j:J=>f j t₀)=(fun j:J=>freeCoordinates r j.val) := by
    funext j
    exact congrArg (freeCoordinates r) (HA j)
  have Hfree : Function.Injective (fun j:J=>freeCoordinates r j.val) := by
    intro j k Hjk
    apply Subtype.ext
    calc
      _=IntegralMixedSweepRows.point x hm r φ t₀.val (freeCoordinates r j.val):=(reconstruct x hm r φ t₀.val j.val j.property.1).symm
      _=IntegralMixedSweepRows.point x hm r φ t₀.val (freeCoordinates r k.val):=congrArg (IntegralMixedSweepRows.point x hm r φ t₀.val) Hjk
      _=k.val:=reconstruct x hm r φ t₀.val k.val k.property.1
  have Hcard : Fintype.card J≤2^(B*(n+1)) := by
    simpa only [Nat.card_eq_fintype_card] using (IntegralMixedFrozenFrame.physical_finite_card x hm r φ t₀.val).2
  have Hfit (v : J→Free r→ℝ) (j : J) (i : Free r) : IntegralMixedSelectedBranchRanks.rank v j i<2^(B*(n+1)+1) :=
    ((IntegralMixedSelectedBranchRanks.rank_le v j i).trans Hcard).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  let code : J→List Bool:=word x hm r φ t₀.val (fun j=>freeCoordinates r j.val)
  refine ⟨curve,HA,HC,HR,HE,code,?_,?_,?_⟩
  · exact IntegralMixedSelectedBranchRanks.word_injective r _ _ Hfree (Hfit _)
  · intro j
    exact IntegralMixedSelectedBranchRanks.word_length r _ _ j
  · intro j t
    change IntegralMixedSelectedBranchRanks.word r _ _ j=IntegralMixedSelectedBranchRanks.word r _ _ j
    rw [←Hanchor]
    exact IntegralMixedSelectedBranchRanks.word_eq x hm r φ c.squarefreeIndex c.squarefreeValid Hcut f HFroot _ j t₀ t

end LeanCanny.Connectivity.IntegralMixedSelectedBranchCodes
