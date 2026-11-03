/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCriticalExtrema
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealSweepStep

/-! # Actual finite critical cuts enclose the entire compact slice

No artificial outer endpoints are inserted. The least and greatest cuts can
be ghost exceptional roots; actual attained critical extrema still ensure
that their closed interval contains every source coordinate value.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n k S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem finite_critical_range (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice P F values).Nonempty) (cuts : Set ℝ) (hcuts : cuts.Finite)
    (hcritical : realCriticalValues P (line F h) values h⊆cuts) :
    cuts.Nonempty ∧ ∃ a b : ℝ,IsLeast cuts a ∧ IsGreatest cuts b ∧
      ∀ y∈slice P F values,y h∈Icc a b := by
  obtain ⟨lo,hi,Hlo,_,Hcl,Hch,Henclose⟩:=exists_critical_extrema P F values h hh HF hp hne
  have Hne : cuts.Nonempty:=⟨lo h,hcritical Hcl⟩
  obtain ⟨a,Ha⟩:=hcuts.isCompact.exists_isLeast Hne
  obtain ⟨b,Hb⟩:=hcuts.isCompact.exists_isGreatest Hne
  refine ⟨Hne,a,b,Ha,Hb,fun y hy=>?_⟩
  exact ⟨(Ha.2 (hcritical Hcl)).trans (Henclose y hy).1,
    (Henclose y hy).2.trans (Hb.2 (hcritical Hch))⟩

/-- All finite ordinary exceptional cuts together with genuine critical heights
suffice; no signed power cutoff or additional initial bank is required. -/
theorem sweepBadReal_range (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice P F values).Nonempty) :
    (sweepBadReal x hm φ F h g hg values c).Nonempty ∧
      ∃ a b : ℝ,IsLeast (sweepBadReal x hm φ F h g hg values c) a ∧
        IsGreatest (sweepBadReal x hm φ F h g hg values c) b ∧
        ∀ y∈slice P F values,y h∈Icc a b :=
  finite_critical_range P F values h hh HF hp hne _
    (sweepBadReal_finite x hm φ F h g hg values H c) (fun _ ht=>Or.inr ht)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
