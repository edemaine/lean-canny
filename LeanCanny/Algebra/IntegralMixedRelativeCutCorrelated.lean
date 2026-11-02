/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCuts
public import LeanCanny.Algebra.IntegralMixedFullHistoryScript
public import LeanCanny.Algebra.IntegralMixedSourceReframe

/-! # Every selected relative cut retains the same old interpreting hom

The actual tagged scalar cut uses its selected specialized degree, extends
the old physical tuple, and retains its root and all old bank quotients.
The source and original scalar degree cap remain fixed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralHistorySampler
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem real_extend_correlated (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (hc : Valid x hm r φ c)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (factor x hm r c).eval₂ φ.toRingHom a=0) :
    ∃ d : ℕ,∃ hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree,
      let command : IntegralMixedFullHistoryScript.Command P B:=.cut r c d hd (hd.trans hcap)
      let born:=IntegralMixedFullHistoryScript.step x hm command
      ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
        (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i := by
  obtain ⟨d,hd,y,hy,htail,hhead⟩:=real_extend x hm r φ c hc hcap z hz hφ a ha
  obtain ⟨ψ,hψ⟩:=(step x hm r c d).sampler.interpret ℝ y hy
  have Hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI:=hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,htail] at HI
    exact HI.trans (hφ i).symm
  refine ⟨d,hd,y,ψ,hy,htail,Hrestrict,hψ,fun i=>Fin.cases (hhead ψ hψ) (fun j=>?_) i⟩
  change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=values j
  have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j))=φ (x.bank.numerator j) :=
    congrArg (fun χ=>χ (x.bank.numerator j)) Hrestrict
  rw [HE]
  exact H j

end LeanCanny.Algebra.IntegralMixedRelativeCuts
