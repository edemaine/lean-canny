/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleFrame

/-! # An actual empty-bank initial frame from original syntax only

No current matrix bound, sampler, interpreting-hom reader or initial real
parameter is supplied. The empty sampler and integer base algebra provide
those data. The single initial spatial cap covers every future cut degree.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralHistorySampler
open AuxiliaryTiltedTerm UniformIntegralPowerSchedule
open scoped Classical

 def initialHeight (n D : ℕ) (t : Term) : ℕ := max 1 (wordBudget n D t)

noncomputable def initialState {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B) :
    State (source 0 D t ht 0 B (initialHeight n D t)) S B 0 (Fin 0) := by
  apply IntegralMixedHistory.base _ (IntegralHistorySampler.base S (2^B))
  have HC : PurePowerReductionBounds.dimension (n+3) (FixedLeadingTiltedSource.degree D)≤
      IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
    unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
    omega
  have HE : (source 0 D t ht 0 B (initialHeight n D t)).degree=FixedLeadingTiltedSource.degree D := rfl
  rw [HE]
  exact HC.trans hcap

noncomputable def initialFrame {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B) :
    SampleFrame n S B D t ht where
  frozen := 0
  frozen_le := Nat.zero_le _
  birth := 0
  height := initialHeight n D t
  carrier := Fin 0
  finite := inferInstance
  state := initialState t ht hcap
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
  height_pos := Nat.le_max_left _ _
  word_bound := Nat.le_max_right _ _
  room := by simpa only [Nat.zero_add,Nat.sub_zero] using hn

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
