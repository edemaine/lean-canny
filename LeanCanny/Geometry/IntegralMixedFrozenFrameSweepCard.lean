/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameEndpointFiber
public import LeanCanny.Connectivity.FiniteCriticalSweepCount
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCard
public import LeanCanny.Connectivity.FiniteSlabCover

/-! # Count the actual root-origin and physical-section labels of a sweep -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem sweep_from_root_covers_card (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Ecap : ℕ) (HEcap : 1≤Ecap)
    (ends : ∀ a∈sweepBad x hm φ F h g hg c,
      ∃ I : Type,Finite I ∧ Nat.card I≤Ecap ∧ Nonempty (ClopenPathCover ((coarseProjection P (line F h) values h) ⁻¹' {a}) I)) :
    ∃ I : Type,Finite I ∧ Nat.card I≤((3*(n+1)+1)*2^B+1)*(2^(B*(n+1))+2*Ecap) ∧
      Nonempty (ClopenPathCover (slice P F values) I) := by
  let p:=coarseProjection P (line F h) values h
  let : CompactSpace (slice P (coarse (line F h) h) values):=
    isCompact_iff_compactSpace.mp (coarse_compact P (line F h) values h hp)
  obtain ⟨N,HN,cut,HM,_,HB,HA,HO⟩:=FiniteCriticalSweepCount.exists_cuts_bound p
    (coarseProjection_continuous P (line F h) values h) _ (sweepBad_finite x hm φ F h g hg c)
  have Hends (j : Fin (N+2)) :
      ∃ I : Type,Finite I ∧ Nat.card I≤Ecap ∧ Nonempty (ClopenPathCover (p ⁻¹' {cut j}) I) := by
    rcases HO j with Hbad | Hempty
    · exact ends _ Hbad
    · let : IsEmpty (p ⁻¹' {cut j}):=⟨fun y=>(Set.ext_iff.mp Hempty y.val).mp y.property⟩
      exact ⟨Unit,inferInstance,by simpa only [Nat.card_unique] using HEcap,⟨emptyCover _⟩⟩
  choose E HE HC CE using Hends
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
    have Havoid : ∀ a∈Ioo (seq i.val) (seq (i.val+1)),a∉sweepBad x hm φ F h g hg c := by
      rw [HL,HR]
      exact HA i
    have Hleft : ClopenPathCover (p ⁻¹' {seq i.val}) (E i.castSucc):=by rw [HL]; exact EC i.castSucc
    have Hright : ClopenPathCover (p ⁻¹' {seq (i.val+1)}) (E i.succ):=by rw [HR]; exact EC i.succ
    exact exists_slab_cover x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values H c
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
  refine ⟨Σ i,J i,inferInstance,?_,⟨cover.comap (coarseLineHomeomorph P F values h hh)⟩⟩
  have HNc : N+1≤(3*(n+1)+1)*2^B+1:=Nat.add_le_add_right (HN.trans (sweepBad_ncard x hm φ F h g hg c hcap)) 1
  have HJ (i : Fin (N+1)) : Nat.card (J i)≤2^(B*(n+1))+2*Ecap := by
    change Nat.card (_ ⊕ (_ ⊕ _))≤_
    rw [Nat.card_sum,Nat.card_sum]
    have Hphysical:=(physical_finite_card (cutSource x F h) hm (cutRule x F h g hg) φ (mid i).val).2
    have HL:=HC i.castSucc
    have HR:=HC i.succ
    omega
  calc
    Nat.card (Σ i,J i)=∑ i,Nat.card (J i):=Nat.card_sigma
    _≤∑ _i : Fin (N+1),(2^(B*(n+1))+2*Ecap):=Finset.sum_le_sum (fun i _=>HJ i)
    _=(N+1)*(2^(B*(n+1))+2*Ecap):=by simp
    _≤_:=Nat.mul_le_mul_right _ HNc

end LeanCanny.Geometry.IntegralMixedFrozenFrame
