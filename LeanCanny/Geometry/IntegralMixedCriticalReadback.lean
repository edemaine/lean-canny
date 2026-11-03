/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCriticalRealExtension
/-! # Reading a geometric critical point from the actual powered block

The raw new ambient coordinates are raised to their creating physical
power. The old tuple supplies the interpreting hom. The new scalar's
annihilator root is not used to infer physical criticality.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCriticalReadback
open LeanCanny.Algebra IntegralMixedHistory IntegralHistorySampler
open FlatAffineCriticalStage UniformIntegralPowerSchedule MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def point (z : ((ι⊕Variables (n+1))⊕Unit)→ℝ) (i : Fin (n+1)) : ℝ :=
  z (Sum.inl (ambient i))^physical S (2^B) m

noncomputable def CriticalPoint (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a : Fin (n+1)→ℝ) : Prop :=
  (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0 ∧
  (∀i,i.val<r.offset.val→((data x hm r).scales i:ℝ)*a i=φ (expression x (r.heights i))) ∧
  ∀i : Fin (n+1),r.offset.val ≤ i.val → i≠(data x hm r).free→
    (pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) a=0

theorem roots_interpret (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (z : ((ι⊕Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((IntegralMixedHistory.criticalStep x hm r).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) (fun j=>z (Sum.inl (Sum.inl j)))=0) ∧
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        z (Sum.inl (Sum.inl (x.sampler.scalar i)))^weights S (2^B) m i) ∧
      CriticalPoint x hm r φ (point (S:=S) (B:=B) (m:=m) z) :=by
  have HR:=scalarStep_old_roots (IntegralHistorySampler.criticalStep x.sampler (data x hm r)) hm
    (Nat.two_pow_pos B) (criticalPolynomial x hm r) (criticalDegree x hm r) z hz
  obtain ⟨φ,hold,hφ,hp,hh,hg,hi⟩:=criticalStep_roots_interpret x.sampler (data x hm r) (z∘Sum.inl) HR
  refine ⟨φ,hold,hφ,hp,?_,?_⟩
  · intro i hif
    have HI : i∈(data x hm r).frozen:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hif⟩
    have HN:=PhysicalPowerCriticalRows.normal_height_sum (Int.castRingHom ℝ) (data x hm r).objective
      (data x hm r).scales (data x hm r).free i (point (S:=S) (B:=B) (m:=m) z) 1
    simp only [pow_one] at HN
    exact HN.symm.trans (hh i HI)
  · intro i hif hfree
    apply CoordinateFrozenCriticalElimination.free_gradient_zero (Int.castRingHom ℝ) _
      (data x hm r).objective (data x hm r).scales (data x hm r).frozen (data x hm r).free
      _ _ hg hi i _ hfree
    intro HI
    have HH : i.val<r.offset.val:=(Finset.mem_filter.mp HI).2
    omega

theorem roots_for_interpretation (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (z : ((ι⊕Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((IntegralMixedHistory.criticalStep x hm r).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z (Sum.inl (Sum.inl (x.sampler.scalar i)))^weights S (2^B) m i) :
    CriticalPoint x hm r φ (point (S:=S) (B:=B) (m:=m) z) :=by
  obtain ⟨ψ,_,hψ,Hψ⟩:=roots_interpret x hm r z hz
  have HE : ψ=φ:=x.sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (hφ i).symm)
  exact HE ▸ Hψ

end LeanCanny.Geometry.IntegralMixedCriticalReadback
