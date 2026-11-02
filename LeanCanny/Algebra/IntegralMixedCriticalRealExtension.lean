/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryCriticalRealExtension
public import LeanCanny.Algebra.IntegralMixedRelativeScalar

/-! # Correlated real realization of an actual mixed critical birth

A point satisfying the literal frozen equations of a physical command extends
the complete old sample. Both the critical block and its actual scalar companion
are constructed. No interpreting-hom extension or root regularity is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem criticalStep_real_extend_correlated (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (hd : Odd (P.degree-1)) (z : ι → ℝ)
    (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m → ℝ) (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1) → ℝ)
    (hfrozen : ∀ i, i.val<r.offset.val → ((data x hm r).scales i:ℝ)*a i=φ (expression x (r.heights i)))
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0)
    (hg : ∀ i : Fin (n+1), r.offset.val ≤ i.val → i≠(data x hm r).free →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0) :
    let t := a (ClearedCoordinateCritical.freeIndex r.offset.val ((family x hm r).fit []).le
      ((family x hm r).coordinate []))
    ∃ y : ((ι ⊕ Variables (n+1)) ⊕ Unit) → ℝ,
    ∃ ψ : (criticalStep x hm r).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ i, ((criticalStep x hm r).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i, y (Sum.inl (Sum.inl i))=z i) ∧
      (∀ i, y (Sum.inl (ambient i))^physical S (2^B) m=a i) ∧
      (ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ) ∧
      (∀ i, ψ ((criticalStep x hm r).sampler.scalarPrefix.basis.generator i)=
        y ((criticalStep x hm r).sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀ i, ψ ((criticalStep x hm r).bank.numerator i)/((criticalStep x hm r).bank.denominator i:ℝ)=
        (Fin.cons t values : Fin (m+1) → ℝ) i := by
  dsimp only
  have Hf : ∀ i, i ∈ (data x hm r).frozen ↔ i.val<r.offset.val := by
    intro i
    simp only [data,Finset.mem_filter,Finset.mem_univ,true_and]
  obtain ⟨mu,hmu,hunused⟩ := coordinate_multipliers x.sampler (data x hm r) a (by
    intro i hi hfree
    apply hg i _ hfree
    have HH := mt (Hf i).mpr hi
    omega)
  obtain ⟨w,hw,hwold,hwa,_⟩ := IntegralHistorySampler.criticalStep_real_extend
    x.sampler (data x hm r) hd z hz φ hφ a mu hp (fun i hi => hfrozen i ((Hf i).mp hi)) hmu hunused
  obtain ⟨χ,hχ,_,hroot⟩ := criticalCandidate_root x.sampler (data x hm r) r.offset.val
    ((family x hm r).fit []) Hf ((family x hm r).objective []) ((family x hm r).coordinate []) rfl w hw
  have Hχ : χ=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    exact (hχ i).trans ((congrArg (fun t : ℝ => t^weights S (2^B) m i) (hwold (x.sampler.scalar i))).trans (hφ i).symm)
  have HP : criticalPolynomial x hm r=criticalCandidate x.sampler (data x hm r) r.offset.val
      ((family x hm r).fit []) ((family x hm r).objective []) ((family x hm r).coordinate []) :=
    IntegralHistoryCriticalBits.annihilator_eq (family x hm r) []
  rw [Hχ,← HP,hwa] at hroot
  let t := a (ClearedCoordinateCritical.freeIndex r.offset.val ((family x hm r).fit []).le
    ((family x hm r).coordinate []))
  obtain ⟨y,hy,hyold,hyhead⟩ := scalarStep_real_extend_recover_root_integer
    (IntegralHistorySampler.criticalStep x.sampler (data x hm r)) hm (Nat.two_pow_pos B)
    (criticalPolynomial x hm r) (criticalDegree x hm r) (criticalDegree_cap x hm r)
    (criticalLeading x hm r) (criticalLeading_ne_zero x hm r) (criticalLeading_coefficient x hm r)
    w hw φ (fun i => (congrArg (fun t : ℝ => t^weights S (2^B) m i) (hwold (x.sampler.scalar i))).trans (hφ i).symm |>.symm)
    t (criticalPolynomial_specialized_degree x hm r φ)
    (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1≤2))) hroot
  obtain ⟨ψ,hψ⟩ := (criticalStep x hm r).sampler.interpret ℝ y hy
  have hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI := hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (Sum.inl (x.sampler.scalar i)))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,hyold,hwold] at HI
    exact HI.trans (hφ i).symm
  refine ⟨y,ψ,hy,fun i => (hyold _).trans (hwold i),fun i => ?_,hrestrict,hψ,fun i => ?_⟩
  · rw [hyold]
    exact hwa i
  · refine Fin.cases (hyhead ψ hψ) (fun j => ?_) i
    change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=values j
    have HE := congrArg (fun χ => χ (x.bank.numerator j)) hrestrict
    exact (congrArg (fun t : ℝ => t/(x.bank.denominator j:ℝ)) HE).trans (H j)

end LeanCanny.Algebra.IntegralMixedHistory
