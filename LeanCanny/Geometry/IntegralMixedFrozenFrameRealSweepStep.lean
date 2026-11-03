/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealSlabCover
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSweepStep
/-! # Sweep endpoint covers only need genuine real projection-critical heights

Relative exceptional factors retain all selected roots. The extra height cuts
are restricted to actual real critical values, whose fibers have physical
critical witnesses. Existing ghost-root sweeps are left unchanged.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def sweepBadReal (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ) : Set ℝ :=
  IntegralMixedSelectedCriticalCuts.bad (cutSource x F h) hm (cutRule x F h g hg) φ c ∪
    realCriticalValues P (line F h) values h

theorem sweepBadReal_finite (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ) :
    (sweepBadReal x hm φ F h g hg values c).Finite :=
  (IntegralMixedSelectedCriticalCuts.finite_bad _ _ _ _ _).union
    (realCriticalValues_finite x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) values H)

theorem sweep_from_real_root_covers (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (ends : ∀ a∈sweepBadReal x hm φ F h g hg values c,
      ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover ((coarseProjection P (line F h) values h) ⁻¹' {a}) I)) :
    ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (slice P F values) I) := by
  let p:=coarseProjection P (line F h) values h
  let : CompactSpace (slice P (coarse (line F h) h) values):=
    isCompact_iff_compactSpace.mp (coarse_compact P (line F h) values h hp)
  obtain ⟨N,cut,HM,_,HB,HA,HO⟩:=FiniteCriticalSweepOrigins.exists_cuts p
    (coarseProjection_continuous P (line F h) values h) _ (sweepBadReal_finite x hm φ F h g hg values H c)
  have Hends (j : Fin (N+2)) :
      ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (p ⁻¹' {cut j}) I) := by
    rcases HO j with Hbad | Hempty
    · exact ends _ Hbad
    · let : IsEmpty (p ⁻¹' {cut j}):=⟨fun y=>(Set.ext_iff.mp Hempty y.val).mp y.property⟩
      exact ⟨Unit,inferInstance,⟨emptyCover _⟩⟩
  choose E HE CE using Hends
  let : ∀ j,Finite (E j):=HE
  let EC (j : Fin (N+2)):= (CE j).some
  let seq : ℕ→ℝ:=fun j=>cut ⟨min j (N+1),by omega⟩
  have Hread (j : Fin (N+2)) : seq j.val=cut j := by
    apply congrArg cut
    apply Fin.ext
    have HJ:=j.isLt
    change min j.val (N+1)=j.val
    omega
  let mid (i : Fin (N+1)) : Ioo (seq i.val) (seq (i.val+1)):=
    ⟨(seq i.val+seq (i.val+1))/2,by
      have HL : seq i.val=cut i.castSucc:=Hread i.castSucc
      have HR : seq (i.val+1)=cut i.succ:=Hread i.succ
      have HS : seq i.val<seq (i.val+1):=by rw [HL,HR]; exact HM Fin.castSucc_lt_succ
      constructor <;> linarith⟩
  have Hslab (i : Fin (N+1)) :
      let I:=IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ (mid i).val
      Finite I ∧ Nonempty (ClopenPathCover (p ⁻¹' Icc (seq i.val) (seq (i.val+1)))
        (ComponentSlabCover.SelectedIndex I (E i.castSucc) (E i.succ))) := by
    have HL : seq i.val=cut i.castSucc:=Hread i.castSucc
    have HR : seq (i.val+1)=cut i.succ:=Hread i.succ
    have Havoid : ∀ a∈Ioo (seq i.val) (seq (i.val+1)),a∉sweepBadReal x hm φ F h g hg values c := by
      rw [HL,HR]
      exact HA i
    have Hleft : ClopenPathCover (p ⁻¹' {seq i.val}) (E i.castSucc):=by rw [HL]; exact EC i.castSucc
    have Hright : ClopenPathCover (p ⁻¹' {seq (i.val+1)}) (E i.succ):=by rw [HR]; exact EC i.succ
    exact exists_slab_cover_of_realCriticalValues x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values H c
      (seq i.val) (seq (i.val+1)) (mid i)
      (fun a ha Hbad=>Havoid a ha (Or.inl Hbad))
      (fun a ha Hzero=>Havoid a ha (Or.inr Hzero)) hp Hleft Hright
  let J (i : Fin (N+1)):=ComponentSlabCover.SelectedIndex
    (IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ (mid i).val)
    (E i.castSucc) (E i.succ)
  let : ∀ i : Fin (N+1),Finite (IntegralMixedSelectedPhysicalFiber.physical
      (cutSource x F h) hm (cutRule x F h g hg) φ (mid i).val):=fun i=>(Hslab i).1
  let : ∀ i,Finite (J i):=fun _=>inferInstance
  let D (i : Fin (N+1)):= (Hslab i).2.some
  have Hbound : ∀ y,p y∈Icc (seq 0) (seq (N+1)) := by
    intro y
    have H0 : seq 0=cut 0:=Hread 0
    have HN : seq (N+1)=cut (Fin.last (N+1)):=Hread (Fin.last (N+1))
    rw [H0,HN]
    exact HB y
  let cover:=FiniteSlabCover.componentCover p seq D
    (coarseProjection_continuous P (line F h) values h) Hbound
  exact ⟨Σ i,J i,inferInstance,⟨cover.comap (coarseLineHomeomorph P F values h hh)⟩⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
