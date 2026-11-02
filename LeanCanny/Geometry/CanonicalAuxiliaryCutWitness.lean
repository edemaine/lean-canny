/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleFrame

/-! # Constructed one-step witnesses with exact old-hom restriction

Every witness is a literal tagged limit-coordinate birth, followed by the
bank-only next-source reframe. Its data come from the proved component sampling
theorem, including validity of the selected relative factor. No next-bank bound
is supplied to the witness; the child frame derives that bound separately.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCanonicalDilation IntegralMixedDilationAdvance UniformIntegralPowerSchedule
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame
open scoped Classical
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

structure CutWitness (F : SampleFrame n S B D t ht) (hk : F.frozen<n)
    (b : slice (polynomial n t) F.frozen F.parameters) where
  choice : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source F.frozen D t ht F.birth B F.height) (criticalRule F))
  valid : IntegralMixedLimitCoordinate.Valid F.state (birth_le F) (criticalRule F) (coordinate F) F.hom choice
  degree : ℕ
  degree_le : degree≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) (criticalRule F)
  root : F.carrier ⊕ Unit → ℝ
  hom : (cutState F choice degree degree_le).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ
  roots : ∀ i, ((cutState F choice degree degree_le).sampler.rows i).eval₂ (Int.castRingHom ℝ) root=0
  keeps : ∀ i, root (Sum.inl i)=F.root i
  restricts : hom.comp (AdjoinRoot.ofAlgHom ℤ _)=F.hom
  interprets : ∀ i, hom ((cutState F choice degree degree_le).sampler.scalarPrefix.basis.generator i)=
    root ((cutState F choice degree degree_le).sampler.scalar i)^weights S (2^B) (F.birth+1) i
  recovers : ∀ i, hom ((cutState F choice degree degree_le).bank.numerator i)/
    ((cutState F choice degree degree_le).bank.denominator i:ℝ)=
      (Fin.cons (b.val ⟨F.frozen,hk⟩) F.values : Fin (F.birth+1) → ℝ) i

namespace CutWitness
variable {F : SampleFrame n S B D t ht} {hk : F.frozen<n}
    {b : slice (polynomial n t) F.frozen F.parameters}

noncomputable def frame (W : CutWitness F hk b)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B) :
    SampleFrame n S B D t ht :=
  child F hk hcap b W.choice W.degree W.degree_le W.root W.hom W.roots W.interprets W.recovers

end CutWitness

theorem degree_pos (n D : ℕ) (t : Term) (ht : (term n t).degreeBound≤D) : 0<D := by
  have H := AuxiliaryTiltedTerm.degreeBound n t
  have HT := ht
  omega

theorem exists_cut (F : SampleFrame n S B D t ht) (hk : F.frozen<n) (ha : t.arity≤n)
    (C : Set (slice (polynomial n t) F.frozen F.parameters)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) F.frozen F.parameters) (hx0 : x0∈C) :
    ∃ b : slice (polynomial n t) F.frozen F.parameters, b∈C ∧ Nonempty (CutWitness F hk b) := by
  let _ := F.finite
  have HM : F.birth+1≤S := by have H := F.room; omega
  obtain ⟨b,hb,c,hc,d,hd,y,ψ,hy,hold,hrestrict,hψ,Hnew,_⟩ := continue_component
    F.state (birth_le F) HM F.bank_bound F.hom F.root F.root_eq F.interprets F.values F.recovers
    ha hk (degree_pos n D t ht) F.selector F.parameters F.correlated C hC x0 hx0
    (IntegralMixedCausalLevelCapacity.coefficient (n+1) D (FixedWidthPolynomial.count (F.birth+1) B)
      (nextHeight n S B D F.height))
  exact ⟨b,hb,⟨c,hc,d,hd,y,ψ,hy,hold,hrestrict,hψ,Hnew⟩⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
