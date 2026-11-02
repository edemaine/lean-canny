/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameOrder
public import LeanCanny.Algebra.IntegralMixedRelativeCutCorrelated

/-! # Actual selected cut births realize the next coarse/fiber frame

The tagged interpreter constructs the new hom and literal old tuple. With
one new scalar reference, the next full slice is the selected affine-level
fiber; coarsening it recovers the exact old slice. No independent root lift,
new spatial polynomial, endpoint cover or adjacency evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem continue_cut (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : IntegralMixedRelativeCuts.Kind P r)
    (hc : IntegralMixedRelativeCuts.Valid x hm r φ c)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (IntegralMixedRelativeCuts.factor x hm r c).eval₂ φ.toRingHom a=0)
    (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen) :
    ∃ d : ℕ,∃ hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree,
      let command : IntegralMixedFullHistoryScript.Command P B:=.cut r c d hd (hd.trans hcap)
      let born:=IntegralMixedFullHistoryScript.step x hm command
      ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
        (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i) ∧
        actualSlice born ψ (level F j)=actualSlice x φ F∩{u | projection F values j u=a} ∧
        actualSlice born ψ (coarse (level F j) j)=actualSlice x φ F := by
  obtain ⟨d,hd,y,ψ,hy,hold,hrestrict,hψ,Hnew⟩:=IntegralMixedRelativeCuts.real_extend_correlated
    x hm r φ c hc hcap z hz hφ values H a ha
  refine ⟨d,hd,y,ψ,hy,hold,hrestrict,hψ,Hnew,?_,?_⟩
  · rw [actualSlice_eq _ ψ _ (Fin.cons a values) Hnew,actualSlice_eq x φ F values H]
    exact slice_level P F j hj values a
  · rw [actualSlice_eq _ ψ _ (Fin.cons a values) Hnew,actualSlice_eq x φ F values H]
    exact slice_coarse_level P F j hj values a

end LeanCanny.Geometry.IntegralMixedFrozenFrame
