/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameInternalSweep
/-! # Actual sweeps include every available retained endpoint

Old bank values may lie outside the bad/critical cut set. Adding this finite
range retains every old height as a cut and preserves avoidance on each
proper subslab. Every endpoint has a fresh origin or an existing producer.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem retained_sweep_cases (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice P F values).Nonempty) :
    (∃a,(a∈sweepBadReal x hm φ F h g hg values c ∨ ∃i,values i=a) ∧
      (∀i,values i=a) ∧ ∀y∈slice P F values,y h=a) ∨
    ∃N : ℕ,∃cut : Fin (N+2)→ℝ,StrictMono cut ∧
      (∀j,cut j∈sweepBadReal x hm φ F h g hg values c ∨ ∃i,values i=cut j) ∧
      (∀i,∃j,cut j=values i) ∧
      (∀y∈slice P F values,∃i : Fin (N+1),y h∈Icc (cut i.castSucc) (cut i.succ)) ∧
      ∀i : Fin (N+1),∀t∈Ioo (cut i.castSucc) (cut i.succ),
        t∉IntegralMixedSelectedCriticalCuts.bad (cutSource x F h) hm (cutRule x F h g hg) φ c ∧
        t∉realCriticalValues P (line F h) values h ∧ ∀j,t≠values j :=by
  let bad:=sweepBadReal x hm φ F h g hg values c
  let cuts:=bad∪Set.range values
  have HB : cuts.Finite:=(sweepBadReal_finite x hm φ F h g hg values H c).union (Set.finite_range values)
  obtain ⟨_,a,b,HA,HC,Hbound⟩:=finite_critical_range P F values h hh HF hp hne cuts HB
    (fun _ ht=>Or.inl (Or.inr ht))
  let s:=HB.toFinset
  have Hleast : IsLeast (s : Set ℝ) a:=by simpa only [s,Set.Finite.coe_toFinset] using HA
  have Hgreatest : IsGreatest (s : Set ℝ) b:=by simpa only [s,Set.Finite.coe_toFinset] using HC
  rcases FiniteCriticalSweepInternal.extrema_cases s a b Hleast Hgreatest with ⟨HE,_⟩|Hlt
  · left
    refine ⟨a,HA.1,fun i=>?_,fun y hy=>?_⟩
    · have HL:=HA.2 (Or.inr (Set.mem_range_self i))
      have HR:=HC.2 (Or.inr (Set.mem_range_self i))
      rw [←HE] at HR
      exact le_antisymm HR HL
    · have HH:=Hbound y hy
      rw [←HE] at HH
      exact le_antisymm HH.2 HH.1
  · right
    obtain ⟨N,cut,HM,_,_,Hmem,Hall,Havoid,Hcover⟩:=
      FiniteCriticalSweepInternal.exists_cuts s a b Hleast Hgreatest Hlt
    refine ⟨N,cut,HM,fun j=>HB.mem_toFinset.mp (Hmem j),?_,
      fun y hy=>Hcover (y h) (Hbound y hy),?_⟩
    · intro i
      exact Hall _ (HB.mem_toFinset.mpr (Or.inr (Set.mem_range_self i)))
    · intro i t ht
      have Hbad : t∉cuts:=fun hbad=>Havoid i t ht (HB.mem_toFinset.mpr hbad)
      refine ⟨fun Ht=>Hbad (Or.inl (Or.inl Ht)),fun Ht=>Hbad (Or.inl (Or.inr Ht)),?_⟩
      intro j hj
      exact Hbad (Or.inr ⟨j,hj.symm⟩)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
