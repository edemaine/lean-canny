/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalCutDegree
/-! # A chosen selected cut is the literal decoded next scalar command

For an existing causal frame record, a selected factor root supplies the
correct stored degree. Executing that rewritten record has one full real
extension, retaining the same old tuple, interpreting hom and bank values.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordDegree
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRecordBits IntegralMixedCriticalSweep IntegralHistorySampler
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem real_extend_record (x : State P S B m ι) (hm : m≤S) (hn : 0<n) (code : List Bool)
    (hcut : IntegralMixedUnitRecordCode.critical code=false)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hc : IntegralMixedRelativeCuts.Valid x hm
      ((IntegralMixedCausalUnitRecordBits.cut P hn m code hcap).rule (commonDenominator x) (commonDenominator_ne_zero x)) φ
      ((IntegralMixedCausalUnitRecordBits.cut P hn m code hcap).kind (commonDenominator x) (commonDenominator_ne_zero x)))
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (IntegralMixedRelativeCuts.factor x hm
      ((IntegralMixedCausalUnitRecordBits.cut P hn m code hcap).rule (commonDenominator x) (commonDenominator_ne_zero x))
      ((IntegralMixedCausalUnitRecordBits.cut P hn m code hcap).kind (commonDenominator x) (commonDenominator_ne_zero x))).eval₂ φ.toRingHom a=0) :
    let old:=IntegralMixedCausalUnitRecordBits.cut P hn m code hcap
    let q:=commonDenominator x
    let hq:=commonDenominator_ne_zero x
    let d:=IntegralMixedRelativeCuts.selectedDegree x hm (old.rule q hq) φ (old.kind q hq)
    let hd:=IntegralMixedRelativeCuts.selectedDegree_bound x hm (old.rule q hq) φ (old.kind q hq)
    let c : IntegralMixedFullHistoryScript.Command P B:=.cut (old.rule q hq) (old.kind q hq) d hd (hd.trans hcap)
    let born:=IntegralMixedFullHistoryScript.step x hm c
    (IntegralMixedCausalUnitRecordBits.record P hn m (withDegree code d) hcap).template.command q hq=c ∧
    ∃y : (ι⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i :=by
  dsimp only
  refine ⟨command P hn m code hcut _ (IntegralMixedRelativeCuts.selectedDegree_bound _ _ _ _ _) hcap _ _,?_⟩
  exact IntegralMixedRelativeCuts.real_extend_selectedDegree x hm _ φ _ hc hcap z hz hφ values H a ha

end LeanCanny.Encoding.IntegralMixedCausalRecordDegree
