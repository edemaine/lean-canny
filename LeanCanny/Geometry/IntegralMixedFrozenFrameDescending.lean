/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSweepStep
public import LeanCanny.Geometry.IntegralMixedFrozenFrameTerminalInterval

/-! # Actual descending frame covers consume one retained birth per level

Endpoint covers are constructed by smaller-free-rank recursion after actual
correlated scalar births. No recursive cover is a premise. The immutable
spatial source and its original cap are fixed throughout this construction.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open UniformIntegralPowerSchedule
open scoped Classical
variable {n : ℕ}

private def CoverAt (P : SpatialSource n) (S B k : ℕ) : Prop :=
  ∀ (m : ℕ) (ι : Type) [Fintype ι] (x : State P S B m ι) (F : Frame n),
    n+1-F.frozen.card=k→m+k≤S+1→FreeNormal F→
    ∀ (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ),
      (∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)→
      (∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)→
      ∀ values : Fin m→ℝ,(∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)→
        ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (slice P F values) I)

private theorem covers_at (P : SpatialSource n) (S B : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∀ k,CoverAt P S B k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k IH =>
    intro m ι _ x F Hk Hbudget HF φ z hz hφ values H
    have HC : (F.frozenᶜ).card=k := by
      rw [Finset.card_compl,Fintype.card_fin]
      exact Hk
    by_cases HK0 : k=0
    · have HE : F.frozenᶜ=∅:=Finset.card_eq_zero.mp (HC.trans HK0)
      have Hall (i : Fin (n+1)) : i∈F.frozen := by
        by_contra Hnot
        have Hmem : i∈F.frozenᶜ:=Finset.mem_compl.mpr Hnot
        rw [HE] at Hmem
        exact Finset.notMem_empty i Hmem
      exact ⟨Unit,inferInstance,⟨fully_frozen_cover P F values Hall⟩⟩
    have hm : m≤S:=by omega
    by_cases HK1 : k=1
    · obtain ⟨h,Hsingle⟩:=Finset.card_eq_one.mp (HC.trans HK1)
      have hh : h∉F.frozen:=Finset.mem_compl.mp (by rw [Hsingle]; exact Finset.mem_singleton_self h)
      have Hall (i : Fin (n+1)) (hi : i≠h) : i∈F.frozen := by
        by_contra Hnot
        have Hmem : i∈F.frozenᶜ:=Finset.mem_compl.mpr Hnot
        rw [Hsingle] at Hmem
        exact hi (Finset.mem_singleton.mp Hmem)
      exact ⟨slice P F values,(last_free_finite_card x hm φ F h hh Hall values H).1,
        ⟨last_free_cover x hm φ F h hh Hall values H⟩⟩
    have HK2 : 1<k:=by omega
    obtain ⟨h,Hh⟩:=Finset.card_pos.mp (show 0<(F.frozenᶜ).card by omega)
    have hh : h∉F.frozen:=Finset.mem_compl.mp Hh
    obtain ⟨g,Hg,Hgh⟩:=Finset.exists_mem_ne (show 1<(F.frozenᶜ).card by omega) h
    have hg : g∉(line F h).frozen := by
      intro Hmem
      rcases Finset.mem_insert.mp Hmem with Hgh' | Hgf
      · exact Hgh Hgh'
      · exact (Finset.mem_compl.mp Hg) Hgf
    obtain ⟨c⟩:=IntegralMixedRelativeCuts.exists_choices (cutSource x F h) hm (cutRule x F h g hg) φ
    apply sweep_from_root_covers x hm φ F h hh g hg values H c hp
    intro a ha
    have Hnext (born : State P S B (m+1) (ι⊕Unit))
        (ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : (ι⊕Unit)→ℝ)
        (hw : ∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) w=0)
        (hψ : ∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=w (born.sampler.scalar i)^weights S (2^B) (m+1) i)
        (Hnew : ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i) :
        ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover ((coarseProjection P (line F h) values h) ⁻¹' {a}) I) := by
      have Hfree : n+1-(advance F h).frozen.card=k-1 := by
        have HE:=advance_rank F h hh
        omega
      have Hroom : (m+1)+(k-1)≤S+1:=by omega
      obtain ⟨I,Hfin,⟨C⟩⟩:=IH (k-1) (by omega) (m+1) (ι⊕Unit) born (advance F h)
        Hfree Hroom (HF.advance h) ψ w hw hψ (Fin.cons a values) Hnew
      exact ⟨I,Hfin,⟨C.comap (endpointHomeomorph P F values h hh HF a)⟩⟩
    rcases ha with Hbad | Hheight
    · obtain ⟨j,Hj⟩:=Hbad
      let kind:=IntegralMixedSelectedCriticalCuts.kind (cutSource x F h) hm (cutRule x F h g hg) φ c j
      have Hkind:=IntegralMixedSelectedCriticalCuts.kind_valid (cutSource x F h) hm (cutRule x F h g hg) φ c j
      obtain ⟨d,_,w,ψ,hw,_,_,hψ,Hnew,_,_⟩:=continue_sweep_cut x hm φ F h hh HF g hg kind Hkind
        hcap z hz hφ values H a Hj
      exact Hnext (cutState x hm F h g hg kind d) ψ w hw hψ Hnew
    · have HR : (linePolynomial x hm F h hh).eval₂ φ.toRingHom a=0:=
        (normal_cut_root_iff x hm φ F h hh HF a).mp Hheight
      obtain ⟨w,ψ,hw,_,_,hψ,Hnew,_,_⟩:=continue_line x hm F h hh φ z hz hφ values H a HR
      exact Hnext (lineState x hm F h hh) ψ w hw hψ Hnew

theorem exists_recursive_cover {S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (F : Frame n) (Hbudget : m+(n+1-F.frozen.card)≤S+1) (HF : FreeNormal F)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ)
    (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (slice P F values) I) :=
  covers_at P S B hcap hp (n+1-F.frozen.card) m ι x F rfl Hbudget HF φ z hz hφ values H

end LeanCanny.Geometry.IntegralMixedFrozenFrame
