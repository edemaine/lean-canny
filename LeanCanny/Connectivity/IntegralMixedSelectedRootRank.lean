/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedCoveringRootRank
public import LeanCanny.Algebra.ScaledSignQueries
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateOrder
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCode
/-! # Ranks among every real selected coordinate root persist

Ghost coordinate roots occupy unused ranks. Actual physical midpoint tuples
remain correlated through their actual physical branch; no arbitrary tuple
of coordinate roots is asserted physical.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedRootRank
open Set Polynomial LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def rank (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) (z : ℝ) : ℕ :=
  ((IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j).filter (fun u=>u<z)).card

theorem rank_signCount (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) (z : ℝ) :
    rank x hm r φ t j z=RootSignQueries.signCount
      (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j).roots.toFinset
      (fun _ : Fin 1=>Polynomial.X-Polynomial.C z) (fun _=>SignType.neg) := by
  have HS (u : ℝ) : SignType.sign (u-z)=SignType.neg↔u<z := by
    constructor
    · intro Hsign
      by_contra hu
      have HN : 0≤u-z:=sub_nonneg.mpr (le_of_not_gt hu)
      by_cases HZ : u-z=0
      · rw [HZ,sign_zero] at Hsign
        cases Hsign
      · have HP : 0<u-z:=lt_of_le_of_ne HN (Ne.symm HZ)
        rw [sign_pos HP] at Hsign
        cases Hsign
    · intro hu
      exact sign_neg (sub_neg.mpr hu)
  unfold rank RootSignQueries.signCount IntegralMixedFrozenFrameSectionCode.roots
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hmem,hu⟩
    refine ⟨hmem,?_⟩
    intro i
    simpa only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using (HS u).mpr hu
  · rintro ⟨hmem,hu⟩
    exact ⟨hmem,(HS u).mp (by simpa only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using hu 0)⟩

theorem mem_roots (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) (z : ℝ) :
    z∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j↔
      (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t) z=0 := by
  have HD:=specialized_degree x hm r j φ t
  have HP : IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j≠0 := by
    intro Hzero
    change (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j).natDegree=_ at HD
    rw [Hzero,Polynomial.natDegree_zero] at HD
    have Hpos : 0<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
      pow_pos (Nat.two_pow_pos _) _
    omega
  rw [IntegralMixedFrozenFrameSectionCode.roots,Multiset.mem_toFinset,Polynomial.mem_roots HP,
    IntegralMixedFrozenFrameSectionCode.polynomial]
  change (Polynomial.map (Polynomial.evalRingHom t) (selected x hm r j φ)).eval z=0↔_
  rw [Polynomial.eval_map]

theorem ordinal_rank (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (a : IntegralMixedSelectedPhysicalFiber.physical x hm r φ t) (j : Free r) :
    (IntegralMixedFrozenFrameSectionCode.ordinal x hm r φ t a j).val=
      rank x hm r φ t j (a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)) := by
  have H:=OrderedRealCells.root_rank (IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j)
    (IntegralMixedFrozenFrameSectionCode.ordinal x hm r φ t a j)
  rw [IntegralMixedFrozenFrameSectionCode.root_ordinal] at H
  exact H

theorem rank_injective (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) (u v : ℝ)
    (hu : u∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j)
    (hv : v∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j) :
    rank x hm r φ t j u=rank x hm r φ t j v↔u=v := by
  have H:=FiniteImageRank.rank_eq_iff (IntegralMixedFrozenFrameSectionCode.roots x hm r φ t j) id u v hu hv
  simpa only [rank,FiniteImageRank.rank_eq,Finset.image_id,id_eq] using H

theorem constant (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (j : Free r)
    (c : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : IntegralMixedCoordinateSquarefree.Valid x hm r j φ c) {a b : ℝ}
    (havoid : ∀ t∈Ioo a b,(IntegralMixedCoordinateSquarefree.exceptional x hm r j c).eval₂ φ.toRingHom t≠0)
    (f : C(Ioo a b,Free r→ℝ))
    (hf : ∀ t,(selected x hm r j φ).eval₂ (Polynomial.evalRingHom t.val) (f t j)=0)
    (s t : Ioo a b) : rank x hm r φ s.val j (f s j)=rank x hm r φ t.val j (f t j) := by
  let H:=IntegralMixedSelectedCoordinateOrder.scalar
    ((IntegralMixedCoordinateSquarefree.auxiliary x hm r j c).map (Polynomial.mapRingHom φ.toRingHom))
  have HC:=IntegralMixedSelectedCoordinateOrder.covering x hm r φ j c hc a b havoid
  have HE (u : Ioo a b) (v : Fin 1→ℝ) : H (u.val,v)=0↔
      v 0∈IntegralMixedFrozenFrameSectionCode.roots x hm r φ u.val j := by
    rw [IntegralMixedSelectedCoordinateOrder.scalar_zero_iff,Polynomial.eval₂_map]
    exact (IntegralMixedCoordinateSquarefree.roots_away x hm r j φ c hc u.val (v 0) (havoid _ u.property)).trans
      (mem_roots x hm r φ u.val j (v 0)).symm
  let fs : C(Ioo a b,Fin 1→ℝ):=⟨fun u _=>f u j,continuous_pi (fun _=>(continuous_apply j).comp f.continuous)⟩
  have HF (u : Ioo a b) : H (u.val,fs u)=0 := (HE u _).mpr ((mem_roots x hm r φ u.val j _).mpr (hf u))
  exact OrderedCoveringRootRank.constant H HC
    (fun u=>IntegralMixedFrozenFrameSectionCode.roots x hm r φ u.val j) HE fs HF s t


theorem word_constant (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (choice : Free r→Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ j,IntegralMixedCoordinateSquarefree.Valid x hm r j φ (choice j)) {a b : ℝ}
    (havoid : ∀ t∈Ioo a b,∀ j,(IntegralMixedCoordinateSquarefree.exceptional x hm r j (choice j)).eval₂ φ.toRingHom t≠0)
    (f : C(Ioo a b,Fin (n+1)→ℝ)) (hf : ∀ t,f t∈IntegralMixedSelectedPhysicalFiber.physical x hm r φ t.val)
    (s t : Ioo a b) :
    IntegralMixedFrozenFrameSectionCode.word x hm r φ s.val ⟨f s,hf s⟩=
      IntegralMixedFrozenFrameSectionCode.word x hm r φ t.val ⟨f t,hf t⟩ := by
  let g : C(Ioo a b,Free r→ℝ):=⟨fun u=>IntegralMixedSelectedPhysicalFiber.freeCoordinates r (f u),
    (continuous_pi (fun _=>continuous_apply _)).comp f.continuous⟩
  have HG (u : Ioo a b) (j : Free r) : (selected x hm r j φ).eval₂ (Polynomial.evalRingHom u.val) (g u j)=0 :=
    (mem_roots x hm r φ u.val j _).mp (IntegralMixedFrozenFrameSectionCode.coordinate_mem x hm r φ u.val ⟨f u,hf u⟩ j)
  unfold IntegralMixedFrozenFrameSectionCode.word
  congr 1
  funext i
  split_ifs with hi
  · rw [ordinal_rank,ordinal_rank]
    exact constant x hm r φ ⟨i,hi⟩ (choice ⟨i,hi⟩) (hc ⟨i,hi⟩) (fun u hu=>havoid u hu ⟨i,hi⟩)
      g (fun u=>HG u ⟨i,hi⟩) s t
  · rfl

end LeanCanny.Connectivity.IntegralMixedSelectedRootRank
