/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameHeightCut
public import LeanCanny.Algebra.IntegralMixedNormalizedScalarCorrelated

/-! # Selected height-cut roots retain the exact endpoint frame

This is an actual scalar-only normalized birth. It requires no lift of an
eliminant root to a real critical physical point. Serializing this new
height-polynomial birth in the native tagged language is a separate task.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem continue_height (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t=0) :
    ∃ d≤heightDegree x hm F h,
      let born:=normalizedScalarStep x hm (IntegralRelativeTruncation.truncate (heightCut x hm F h) d) d
      ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
        (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons t values : Fin (m+1)→ℝ) i) ∧
        actualSlice born ψ (level (coarse F h) h)=shiftedSlice P F values h t ∧
        actualSlice born ψ (coarse (level (coarse F h) h) h)=actualSlice x φ (coarse F h) := by
  obtain ⟨d,hd,y,ψ,hy,hold,HR,hψ,Hnew⟩:=selected_scalar_real_extend_correlated x hm (heightCut x hm F h)
    (heightCut_cap x hm F h) φ (heightCut_nonzero x hm F h φ) z hz hφ values H t ht
  refine ⟨d,hd.trans (heightCut_degree x hm F h),y,ψ,hy,hold,HR,hψ,Hnew,?_,?_⟩
  · rw [actualSlice_eq _ ψ _ (Fin.cons t values) Hnew,
      slice_level P (coarse F h) h (Finset.notMem_erase h F.frozen) values t,
      shiftedSlice_fiber P F values h hh t]
    rfl
  · rw [actualSlice_eq _ ψ _ (Fin.cons t values) Hnew,
      actualSlice_eq x φ (coarse F h) values H]
    exact slice_coarse_level P (coarse F h) h (Finset.notMem_erase h F.frozen) values t

end LeanCanny.Geometry.IntegralMixedFrozenFrame
