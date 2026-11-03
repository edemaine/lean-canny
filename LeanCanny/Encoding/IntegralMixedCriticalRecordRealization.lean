/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
public import LeanCanny.Algebra.IntegralMixedCriticalRealExtension
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
/-! # One full correlated extension for the exact original critical record

Frozen equations, the original source equation and all nonobjective free
gradients are honest geometric inputs. The source's original even degree
supplies the odd derivative exponent required for real physical roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical

theorem odd_degree_sub_one {n : ℕ} (P : SpatialSource n) (heven : Even P.degree) : Odd (P.degree-1):=by
  obtain ⟨k,hk⟩:=heven
  refine ⟨k-1,?_⟩
  have H:=P.degree_two
  omega

theorem marked_degree_odd (n : List Bool→ℕ) (t : List Bool→LeanCanny.ETR.Term) (R : List Bool→ℕ)
    (root : List Bool) : Odd ((IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root).degree-1):=by
  apply odd_degree_sub_one
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
  exact LeanCanny.Geometry.BoundedZeroSource.powerDegree_even _

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem real_extend_record (x : State P S B m ι) (hm : m≤S) (hn : 0<n) (d : Data n m)
    (charge : ℕ) (hdegree : P.degree=LeanCanny.Geometry.BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ)
    (hfrozen : ∀i,i.val<d.rule.offset.val→((data x hm d.rule).scales i:ℝ)*a i=φ (expression x (d.rule.heights i)))
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0)
    (hg : ∀i : Fin (n+1),d.rule.offset.val≤ i.val→i≠(data x hm d.rule).free→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0) :
    let t:=a (ClearedCoordinateCritical.freeIndex d.rule.offset.val ((family x hm d.rule).fit []).le
      ((family x hm d.rule).coordinate []))
    let c : IntegralMixedFullHistoryScript.Command P B:=.critical d.rule
    let born:=IntegralMixedFullHistoryScript.step x hm c
    (IntegralMixedCausalUnitRecordBits.record P hn m d.code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=c ∧
    ∃y : ((ι⊕Variables (n+1))⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (ambient i))^physical S (2^B) m=a i) ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons t values : Fin (m+1)→ℝ) i:=by
  refine ⟨command_decode P hn d hcap _ _,?_⟩
  apply criticalStep_real_extend_correlated x hm d.rule _ z hz φ hφ values H a hfrozen hp hg
  apply odd_degree_sub_one
  rw [hdegree]
  exact LeanCanny.Geometry.BoundedZeroSource.powerDegree_even charge

end LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
