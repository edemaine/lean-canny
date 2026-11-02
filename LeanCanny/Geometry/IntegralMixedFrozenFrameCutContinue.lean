/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameLineContinue
public import LeanCanny.Algebra.IntegralMixedNormalizedScalarCorrelated

/-! # Selected sweep-cut roots retain exact free-coordinate endpoints

The native cut source is frozen-first. Reframing preserves the literal
scalar prefix, bank and old tuple; no critical physical lift occurs.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem line_slice {k : ℕ} (P : SpatialSource n) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (HF : FreeNormal F) (values : Fin k→ℝ) (a : ℝ) :
    shiftedSlice P (line F h) values h a=slice P F values∩{y | y h=a} := by
  rw [shiftedSlice_fiber P (line F h) values h (Finset.mem_insert_self h F.frozen) a,coarse_line F h hh]
  ext y
  simp only [mem_inter_iff,mem_ofPred_eq,line_projection F h (HF h hh) values y]

noncomputable def cutSource (x : State P S B m ι) (F : Frame n) (h : Fin (n+1)) :=
  IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation (line F h).frozen)
noncomputable def cutRule (x : State P S B m ι) (F : Frame n) (h : Fin (n+1))
    (g : Fin (n+1)) (hg : g∉(line F h).frozen) :=
  sweep x (line F h) h (Finset.mem_insert_self h F.frozen) g hg

noncomputable def cutState [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Kind
      (IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) (cutRule x F h g hg)) (d : ℕ) :
    State P S B (m+1) (ι⊕Unit) :=
  reframe (IntegralMixedRelativeCuts.step (cutSource x F h) hm (cutRule x F h g hg) c d) P x.critical_cap

theorem cutState_native_prefix [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Kind
      (IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) (cutRule x F h g hg))
    (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) (hcap : d≤2^B) :
    (cutState x hm F h g hg c d).sampler.scalarPrefix=
      (IntegralMixedFullHistoryScript.step (cutSource x F h) hm (.cut (cutRule x F h g hg) c d hd hcap)).sampler.scalarPrefix := rfl

theorem cutState_native_bank [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Kind
      (IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) (cutRule x F h g hg))
    (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) (hcap : d≤2^B) :
    (cutState x hm F h g hg c d).bank=
      (IntegralMixedFullHistoryScript.step (cutSource x F h) hm (.cut (cutRule x F h g hg) c d hd hcap)).bank := rfl

theorem continue_sweep_cut [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (c : IntegralMixedRelativeCuts.Kind
      (IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation (line F h).frozen)) (cutRule x F h g hg))
    (hc : IntegralMixedRelativeCuts.Valid (cutSource x F h) hm (cutRule x F h g hg) φ c)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (IntegralMixedRelativeCuts.factor (cutSource x F h) hm (cutRule x F h g hg) c).eval₂ φ.toRingHom a=0) :
    ∃ d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree,
      let born:=cutState x hm F h g hg c d
      ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
        (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i) ∧
        actualSlice born ψ (advance F h)=shiftedSlice P (line F h) values h a ∧
        actualSlice born ψ (coarse (advance F h) h)=actualSlice x φ F := by
  let p:=IntegralMixedRelativeCuts.factor (cutSource x F h) hm (cutRule x F h g hg) c
  have HD : p.natDegree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree:=
    IntegralMixedRelativeCuts.factor_degree (cutSource x F h) hm (cutRule x F h g hg) c
  obtain ⟨d,hd,y,ψ,hy,hold,HR,hψ,Hnew⟩:=selected_scalar_real_extend_correlated x hm p (HD.trans hcap)
    φ (IntegralMixedRelativeCuts.selected_nonzero (cutSource x F h) hm (cutRule x F h g hg) φ c hc) z hz hφ values H a ha
  refine ⟨d,hd.trans HD,y,ψ,hy,hold,HR,hψ,Hnew,?_,?_⟩
  · rw [actualSlice_eq (cutState x hm F h g hg c d) ψ _ (Fin.cons a values) Hnew,
      slice_advance P F h hh values a,line_slice P F h hh HF values a]
  · rw [actualSlice_eq (cutState x hm F h g hg c d) ψ _ (Fin.cons a values) Hnew,actualSlice_eq x φ F values H]
    exact slice_coarse_advance P F h hh values a

end LeanCanny.Geometry.IntegralMixedFrozenFrame
