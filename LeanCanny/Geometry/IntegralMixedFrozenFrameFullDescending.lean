/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealSweepStep
public import LeanCanny.Geometry.IntegralMixedPrefixCriticalRealization
public import LeanCanny.Geometry.IntegralMixedFrozenFrameTerminalInterval

/-! # Real-critical endpoint recursion with full physical witnesses

The deterministic first-free coordinate preserves prefix ordering and atomic
reference heights. Exceptional-factor endpoints use actual scalar cut births.
Every additional height endpoint is an actual real critical value and uses a
full correlated physical birth, rather than an annihilator-only shadow.
The spatial source remains the literal original source at every recursion.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private def FullCoverAt (P : SpatialSource n) (S B k : ℕ) : Prop :=
  ∀ (m : ℕ) (ι : Type) [Fintype ι] (x : State P S B m ι) (F : Frame n),
    n+1-F.frozen.card=k→m+k≤S+1→FreeNormal F→AtomicRows F m→PrefixFrozen F→
    ∀ (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ),
      (∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)→
      (∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)→
      ∀ values : Fin m→ℝ,(∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)→
        ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (slice P F values) I)

private theorem full_covers_at (P : SpatialSource n) (S B : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∀ k,FullCoverAt P S B k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k IH =>
    intro m ι _ x F Hk Hbudget HF HA HP φ z hz hφ values H
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
    obtain ⟨h,g,_,_,hh,hg,HPadvance,_⟩:=HP.exists_step (by omega)
    obtain ⟨c⟩:=IntegralMixedRelativeCuts.exists_choices (cutSource x F h) hm (cutRule x F h g hg) φ
    apply sweep_from_real_root_covers x hm φ F h hh g hg values H c hp
    intro a ha
    have Hnext {κ : Type} [Fintype κ] (born : State P S B (m+1) κ)
        (ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : κ→ℝ)
        (hw : ∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) w=0)
        (hψ : ∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=w (born.sampler.scalar i)^weights S (2^B) (m+1) i)
        (Hnew : ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i) :
        ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover ((coarseProjection P (line F h) values h) ⁻¹' {a}) I) := by
      have Hfree : n+1-(advance F h).frozen.card=k-1 := by
        have HE:=advance_rank F h hh
        omega
      have Hroom : (m+1)+(k-1)≤S+1:=by omega
      obtain ⟨I,Hfin,⟨C⟩⟩:=IH (k-1) (by omega) (m+1) κ born (advance F h)
        Hfree Hroom (HF.advance h) (HA.advance h) HPadvance ψ w hw hψ (Fin.cons a values) Hnew
      exact ⟨I,Hfin,⟨C.comap (endpointHomeomorph P F values h hh HF a)⟩⟩
    rcases ha with Hbad | Hheight
    · obtain ⟨j,Hj⟩:=Hbad
      let kind:=IntegralMixedSelectedCriticalCuts.kind (cutSource x F h) hm (cutRule x F h g hg) φ c j
      have Hkind:=IntegralMixedSelectedCriticalCuts.kind_valid (cutSource x F h) hm (cutRule x F h g hg) φ c j
      obtain ⟨d,_,w,ψ,hw,_,_,hψ,Hnew,_,_⟩:=continue_sweep_cut x hm φ F h hh HF g hg kind Hkind
        hcap z hz hφ values H a Hj
      exact Hnext (cutState x hm F h g hg kind d) ψ w hw hψ Hnew
    · obtain ⟨point,hpoint,hcoordinate,hgradient⟩:=
        (line_realCriticalValues_iff P F values h hh HF a).mp Hheight
      let d:=HA.pointData h h hh hh
      let born:=criticalStep x hm d.rule
      obtain ⟨_,_,w,ψ,hw,_,_,_,hψ,Hnew⟩:=HP.real_extend_point x hm hn charge hdegree hcap
        F HA h h hh hh z hz φ hφ values H point hpoint hgradient
      have Hvalues : ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
          (Fin.cons a values : Fin (m+1)→ℝ) i := by
        intro i
        simpa only [born,d,IntegralMixedFullHistoryScript.step,hcoordinate] using Hnew i
      exact Hnext born ψ w hw hψ Hvalues

theorem exists_full_recursive_cover {S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (F : Frame n) (Hbudget : m+(n+1-F.frozen.card)≤S+1) (HF : FreeNormal F)
    (HA : AtomicRows F m) (HP : PrefixFrozen F) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ)
    (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover (slice P F values) I) :=
  full_covers_at P S B hcap hn charge hdegree hp (n+1-F.frozen.card) m ι x F rfl Hbudget HF HA HP φ z hz hφ values H

end LeanCanny.Geometry.IntegralMixedFrozenFrame
