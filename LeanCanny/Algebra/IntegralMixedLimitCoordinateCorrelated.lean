/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRealization
public import LeanCanny.Algebra.IntegralMixedSourceReframe
/-! # A retained original limit coordinate with the same correlated old sample

After selecting a relative limit factor, the actual normalized scalar birth
retains its chosen root and every original quotient value simultaneously. The
old physical tuple remains literal. No arbitrary absolute norm root is lifted.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralHistorySampler
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem real_extend_correlated (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : ((factor x hm r j c).map φ.toRingHom).eval a=0) :
    ∃ d : ℕ, d ≤ degree P r ∧
      ∃ y : (ι ⊕ Unit) → ℝ,
      ∃ ψ : (step x hm r j c d).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ((step x hm r j c d).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i, y (Sum.inl i)=z i) ∧
        (ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ) ∧
        (∀ i, ψ ((step x hm r j c d).sampler.scalarPrefix.basis.generator i)=
          y ((step x hm r j c d).sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        ∀ i, ψ ((step x hm r j c d).bank.numerator i)/
          ((step x hm r j c d).bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1) → ℝ) i := by
  have ha' : (factor x hm r j c).eval₂ φ.toRingHom a=0 := by
    simpa only [Polynomial.eval_map] using ha
  obtain ⟨d,hd,y,hy,htail,hhead⟩ := real_extend x hm r j φ c hc z hz hφ a ha'
  obtain ⟨ψ,hψ⟩ := (step x hm r j c d).sampler.interpret ℝ y hy
  have hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI := hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,htail] at HI
    exact HI.trans (hφ i).symm
  refine ⟨d,hd,y,ψ,hy,htail,hrestrict,hψ,fun i => Fin.cases (hhead ψ hψ) (fun j => ?_) i⟩
  change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=values j
  have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j))=φ (x.bank.numerator j) :=
    congrArg (fun χ => χ (x.bank.numerator j)) hrestrict
  rw [HE]
  exact H j

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
