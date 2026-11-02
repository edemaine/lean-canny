/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryStepHeight
public import LeanCanny.Geometry.CanonicalAuxiliaryTerminal

/-! # Actual real frames for bounded recursive original-coordinate sampling

Each frame packages one actual changing-source state, complete physical root,
interpreting hom and recovered bank. Its budget is the derived bank height;
the other height premise concerns only the fixed original integer syntax.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCanonicalDilation IntegralMixedDilationAdvance UniformIntegralPowerSchedule
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling
open scoped Classical
attribute [local irreducible] source

structure SampleFrame (n S B D : ℕ) (t : Term) (ht : (term n t).degreeBound≤D) where
  frozen : ℕ
  frozen_le : frozen≤n
  birth : ℕ
  height : ℕ
  carrier : Type
  finite : Fintype carrier
  state : State (source frozen D t ht birth B height) S B birth carrier
  root : carrier → ℝ
  root_eq : ∀ i, (state.sampler.rows i).eval₂ (Int.castRingHom ℝ) root=0
  hom : state.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ
  interprets : ∀ i, hom (state.sampler.scalarPrefix.basis.generator i)=root (state.sampler.scalar i)^weights S (2^B) birth i
  values : Fin birth → ℝ
  recovers : ∀ i, hom (state.bank.numerator i)/(state.bank.denominator i:ℝ)=values i
  parameters : Fin n → ℝ
  selector : Fin frozen → Fin birth
  correlated : ∀ i : Fin n, ∀ hi : i.val<frozen, parameters i=values (selector ⟨i.val,hi⟩)
  bank_bound : state.bank.Bounds height
  height_pos : 1≤height
  word_bound : wordBudget n D t≤height
  room : birth+(n-frozen)≤S

namespace SampleFrame
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

def criticalRule (F : SampleFrame n S B D t ht) : Rule (n+2) :=
  rule (F.frozen_le.trans (Nat.le_succ n)) F.selector

def coordinate (F : SampleFrame n S B D t ht) : Fin (n+2-(criticalRule F).critical.offset.val+1) :=
  coordinateIndex (F.frozen_le.trans (Nat.le_succ n)) F.selector
    (⟨F.frozen,Nat.lt_succ_of_le F.frozen_le⟩:Fin (n+1)) (Nat.le_refl F.frozen)

theorem birth_le (F : SampleFrame n S B D t ht) : F.birth≤S := by
  have H := F.room
  omega

noncomputable def cutState (F : SampleFrame n S B D t ht)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source F.frozen D t ht F.birth B F.height) (criticalRule F)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) (criticalRule F)) :
    State (source (F.frozen+1) D t ht (F.birth+1) B (nextHeight n S B D F.height)) S B (F.birth+1) (F.carrier ⊕ Unit) := by
  letI := F.finite
  exact nextState F.state (birth_le F) _ F.selector (coordinate F) c d hd

noncomputable def child (F : SampleFrame n S B D t ht) (hk : F.frozen<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (b : slice (polynomial n t) F.frozen F.parameters)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source F.frozen D t ht F.birth B F.height) (criticalRule F)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) (criticalRule F))
    (y : F.carrier ⊕ Unit → ℝ) (ψ : (cutState F c d hd).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hy : ∀ i, ((cutState F c d hd).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0)
    (hψ : ∀ i, ψ ((cutState F c d hd).sampler.scalarPrefix.basis.generator i)=
      y ((cutState F c d hd).sampler.scalar i)^weights S (2^B) (F.birth+1) i)
    (Hnew : ∀ i, ψ ((cutState F c d hd).bank.numerator i)/((cutState F c d hd).bank.denominator i:ℝ)=
      (Fin.cons (b.val ⟨F.frozen,hk⟩) F.values : Fin (F.birth+1) → ℝ) i) : SampleFrame n S B D t ht where
  frozen := F.frozen+1
  frozen_le := by omega
  birth := F.birth+1
  height := nextHeight n S B D F.height
  carrier := F.carrier ⊕ Unit
  finite := by letI := F.finite; infer_instance
  state := cutState F c d hd
  root := y
  root_eq := hy
  hom := ψ
  interprets := hψ
  values := Fin.cons (b.val ⟨F.frozen,hk⟩) F.values
  recovers := Hnew
  parameters := b.val
  selector := nextSelector F.selector
  correlated := by
    have HOld : ∀ i : Fin n, ∀ hi : i.val<F.frozen, b.val i=F.values (F.selector ⟨i.val,hi⟩) :=
      fun i hi => (b.property.2 i hi).trans (F.correlated i hi)
    exact next_parameters hk F.selector F.values (b.val ⟨F.frozen,hk⟩) b.val HOld rfl
  bank_bound := by
    let _ := F.finite
    exact nextState_bank_bounds F.state (birth_le F) F.bank_bound F.height_pos
      ((word_le_budget n F.frozen D t F.frozen_le).trans F.word_bound) hcap _ F.selector (coordinate F) c d hd
  height_pos := nextHeight_pos n S B D F.height F.height_pos
  word_bound := F.word_bound.trans (le_nextHeight n S B D F.height)
  room := by have H := F.room; omega

end SampleFrame
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
