/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryInitialFrame

/-! # An actual empty-bank frame at an original chosen height seed

The level source uses exactly the supplied G. This permits the native seed
wordBudget+1 without identifying it with max 1 wordBudget. Empty-bank bounds,
roots and interpreting hom are constructed, not supplied as premises.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralHistorySampler
open AuxiliaryTiltedTerm UniformIntegralPowerSchedule
open scoped Classical

noncomputable def seededInitialState {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G : ℕ) : State (source 0 D t ht 0 B G) S B 0 (Fin 0) := by
  apply IntegralMixedHistory.base _ (IntegralHistorySampler.base S (2^B))
  have HC : PurePowerReductionBounds.dimension (n+3) (FixedLeadingTiltedSource.degree D)≤
      IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
    unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
    omega
  have HE : (source 0 D t ht 0 B G).degree=FixedLeadingTiltedSource.degree D := rfl
  rw [HE]
  exact HC.trans hcap

attribute [local irreducible] source

noncomputable def seededInitialFrame {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G : ℕ) (hG : 1≤G) (hword : wordBudget n D t≤G) : SampleFrame n S B D t ht where
  frozen := 0
  frozen_le := Nat.zero_le _
  birth := 0
  height := G
  carrier := Fin 0
  finite := inferInstance
  state := seededInitialState t ht hcap G
  root := Fin.elim0
  root_eq := by intro i; exact Fin.elim0 i
  hom := Algebra.ofId ℤ ℝ
  interprets := by intro i; exact Fin.elim0 i
  values := Fin.elim0
  recovers := by intro i; exact Fin.elim0 i
  parameters := 0
  selector := Fin.elim0
  correlated := by intro i hi; omega
  bank_bound := by constructor <;> intro i <;> exact Fin.elim0 i
  height_pos := hG
  word_bound := hword
  room := by simpa only [Nat.zero_add,Nat.sub_zero] using hn

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
