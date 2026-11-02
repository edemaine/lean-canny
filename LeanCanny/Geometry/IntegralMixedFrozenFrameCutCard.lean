/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSweepStep
public import Mathlib.Data.Set.Card

/-! # Actual selected sweep cuts have an original-width cardinal bound -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set Polynomial
open IntegralMixedSelectedGeometry
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem selected_polynomial_roots_ncard {A : Type} [CommRing A] (p : Polynomial A) (φ : A→+*ℝ)
    (hp : p.map φ≠0) : {a : ℝ | p.eval₂ φ a=0}.ncard≤p.natDegree := by
  let q:=p.map φ
  have HS : {a : ℝ | p.eval₂ φ a=0}⊆(q.roots.toFinset : Set ℝ) := by
    intro a ha
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change (p.map φ).eval a=0
    rw [Polynomial.eval_map]
    exact ha
  calc
    _≤(q.roots.toFinset : Set ℝ).ncard:=Set.ncard_le_ncard HS (Finset.finite_toSet _)
    _=q.roots.toFinset.card:=Set.ncard_coe_finset _
    _≤q.roots.card:=Multiset.toFinset_card_le _
    _≤q.natDegree:=Polynomial.card_roots' _
    _≤p.natDegree:=Polynomial.natDegree_map_le

theorem selected_bad_ncard (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (IntegralMixedSelectedCriticalCuts.bad x hm r φ c).ncard≤3*(n+1)*2^B := by
  let p (j : IntegralMixedSelectedCriticalCuts.Tag r):=
    (IntegralMixedSelectedCriticalCuts.cut x hm r φ c j).map φ.toRingHom
  let R (j : IntegralMixedSelectedCriticalCuts.Tag r):={a : ℝ //a∈(p j).roots.toFinset}
  have HP (j : IntegralMixedSelectedCriticalCuts.Tag r) : p j≠0 :=
    IntegralMixedRelativeCuts.selected_nonzero x hm r φ (IntegralMixedSelectedCriticalCuts.kind x hm r φ c j)
      (IntegralMixedSelectedCriticalCuts.kind_valid x hm r φ c j)
  let enc : IntegralMixedSelectedCriticalCuts.bad x hm r φ c→Σ j,R j:=fun a=>by
    let j:=Classical.choose a.property
    have hj:=Classical.choose_spec a.property
    refine ⟨j,a.val,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (HP j)).mpr ?_)⟩
    change ((IntegralMixedSelectedCriticalCuts.cut x hm r φ c j).map φ.toRingHom).eval a.val=0
    rw [Polynomial.eval_map]
    exact hj
  have HE : Function.Injective enc := by
    intro a b H
    apply Subtype.ext
    exact congrArg (fun z : Σ j,R j=>z.2.val) H
  have HR (j : IntegralMixedSelectedCriticalCuts.Tag r) : Nat.card (R j)≤2^B := by
    change Nat.card {a : ℝ //a∈(p j).roots.toFinset}≤_
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (Polynomial.natDegree_map_le.trans ((IntegralMixedSelectedCriticalCuts.cut_degree x hm r φ c j).trans hcap)))
  have HT : Fintype.card (IntegralMixedSelectedCriticalCuts.Tag r)≤3*(n+1) := by
    simp only [IntegralMixedSelectedCriticalCuts.Tag,Free,Fintype.card_prod,Fintype.card_fin]
    omega
  change Nat.card (IntegralMixedSelectedCriticalCuts.bad x hm r φ c)≤_
  calc
    _≤Nat.card (Σ j,R j):=Nat.card_le_card_of_injective enc HE
    _=∑ j,Nat.card (R j):=Nat.card_sigma
    _≤∑ _j : IntegralMixedSelectedCriticalCuts.Tag r,2^B:=Finset.sum_le_sum (fun j _=>HR j)
    _=Fintype.card (IntegralMixedSelectedCriticalCuts.Tag r)*2^B:=by simp
    _≤3*(n+1)*2^B:=Nat.mul_le_mul_right _ HT

theorem height_cut_roots_ncard (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) : {a : ℝ | (heightCut x hm F h).eval₂ φ.toRingHom a=0}.ncard≤2^B :=
  (selected_polynomial_roots_ncard _ φ.toRingHom (heightCut_nonzero x hm F h φ)).trans (heightCut_cap x hm F h)

theorem sweepBad_ncard (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (sweepBad x hm φ F h g hg c).ncard≤(3*(n+1)+1)*2^B := by
  apply (Set.ncard_union_le _ _).trans
  calc
    _≤3*(n+1)*2^B+2^B:=Nat.add_le_add
      (selected_bad_ncard (cutSource x F h) hm (cutRule x F h g hg) φ c hcap)
      (height_cut_roots_ncard x hm φ (line F h) h)
    _=(3*(n+1)+1)*2^B:=by ring

end LeanCanny.Geometry.IntegralMixedFrozenFrame
