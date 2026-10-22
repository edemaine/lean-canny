/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskSpace

/-! # Decreasing internal task priorities

The concrete request writers enforce determinant → factor → moment → source,
with diagonal shortcuts and zero requests. This statement concerns actual task
words, including malformed external inputs, and uses no answer certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation

def priority (q : List Bool) : ℕ :=
  if isZero q then 0 else if isDeterminant q then 4 else if isFactor q then 3 else if isMoment q then 2 else 1

theorem priority_zero : priority [] = 0 := rfl
theorem priority_determinant (p : List Bool) : priority (determinantTask p) = 4 := rfl
theorem priority_factor (p : List Bool) : priority (factorTask p) = 3 := rfl
theorem priority_moment (p : List Bool) : priority (momentTask p) = 2 := rfl
theorem priority_source (p : List Bool) : priority (sourceTask p) = 1 := rfl

/-- Original matrix context, independent of the internal stage and indices. -/
def origin (q : List Bool) : List Bool :=
  if isZero q then [] else if isDeterminant q then payload q
  else if isFactor q then pairFst (pairFst (payload q))
  else if isMoment q then pairFst (pairFst (payload q)) else pairFst (payload q)

theorem origin_zero : origin [] = [] := rfl
theorem origin_determinant (p : List Bool) : origin (determinantTask p) = p := rfl
theorem origin_factor (p : List Bool) : origin (factorTask p) = pairFst (pairFst p) := rfl
theorem origin_moment (p : List Bool) : origin (momentTask p) = pairFst (pairFst p) := rfl
theorem origin_source (p : List Bool) : origin (sourceTask p) = pairFst p := rfl

theorem origin_length_le (q : List Bool) : (origin q).length ≤ q.length := by
  have hp : (payload q).length ≤ q.length := by simp only [payload, List.length_drop]; omega
  have h1 := (pairFst_length_le (payload q)).trans hp
  have h2 := (pairFst_length_le (pairFst (payload q))).trans h1
  unfold origin
  split_ifs <;> first | exact Nat.zero_le _ | exact hp | exact h2 | exact h1

theorem priority_le (q : List Bool) : priority q ≤ 4 := by unfold priority; split_ifs <;> decide

theorem priority_pos (q : List Bool) (hq : isZero q = false) : 0 < priority q := by
  simp only [priority, hq, Bool.false_eq_true, ite_false]
  split_ifs <;> decide

attribute [local irreducible] isZero isDeterminant isFactor isMoment payload
  PolynomialPower.Access.lower PolynomialPower.Access.coefficientInput
  MatrixMoment.EntryBits.rowIndex MatrixMoment.EntryBits.colIndex MatrixMoment.EntryBits.sinkIndex
  MatrixPower.Controller.entryInput MatrixPower.Controller.halted MatrixPower.Controller.needsEntry
  MatrixPower.Controller.initialPacket ModularAccess.mode
  BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul BinaryNat.add BinaryNat.sub BinaryNat.succ

private theorem lifted_range {G : PolynomialPower.ModularFamily} (b : PolynomialPower.ModularAccess G)
    (task : List Bool → List Bool) (zero : List Bool) (P : List Bool → Prop)
    (hz : P zero) (ht : ∀ p, P (task p)) (p : List Bool) :
    P (PolynomialPower.RecursiveStage.liftedTask b task zero p) := by
  unfold PolynomialPower.RecursiveStage.liftedTask
  split_ifs
  · exact ht _
  · exact hz

private theorem augmented_range (b : MatrixMoment.EntryBits.Access)
    (r c m : List Bool → List Bool) (zero : List Bool) (P : List Bool → Prop)
    (hz : P zero) (hr : ∀ p, P (r p)) (hc : ∀ p, P (c p)) (hm : ∀ p, P (m p)) (p : List Bool) :
    P (MatrixMoment.EntryBits.task b r c m zero p) := by
  unfold MatrixMoment.EntryBits.task
  split_ifs <;> first | exact hz | exact hr _ | exact hc _ | exact hm _

variable {F : ModularFamily} (a : ModularAccess F)

theorem determinant_query_shape (s : List Bool) :
    (DeterminantStage.controller a factorTask []).query s = [] ∨
      ∃ p, (DeterminantStage.controller a factorTask []).query s = factorTask p := by
  change (fun q => q = [] ∨ ∃ p, q = factorTask p)
    (PolynomialPower.RecursiveStage.liftedTask a.powerAccess (factorTask ∘ ModularAccess.splitDegree) []
      (MatrixPower.Controller.entryInput s))
  exact lifted_range a.powerAccess (factorTask ∘ ModularAccess.splitDegree) []
    (fun q => q = [] ∨ ∃ p, q = factorTask p) (Or.inl rfl)
    (fun p => Or.inr ⟨ModularAccess.splitDegree p, rfl⟩) _

theorem factor_query_shape (s : SingleCall.State) : ∃ p,
    (FactorStage.program a sourceTask momentTask).controller.query s = sourceTask p ∨
    (FactorStage.program a sourceTask momentTask).controller.query s = momentTask p := by
  dsimp only [SingleCall.Program.controller, FactorStage.program]
  split_ifs
  · exact ⟨_, Or.inl rfl⟩
  · exact ⟨_, Or.inr rfl⟩

theorem moment_query_shape (s : List Bool) :
    (MomentStage.controller a sourceTask []).query s = [] ∨
      ∃ p, (MomentStage.controller a sourceTask []).query s = sourceTask p := by
  let P := fun q : List Bool => q = [] ∨ ∃ p, q = sourceTask p
  have haug (p : List Bool) : P (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess
      (MomentStage.rowTask a sourceTask) (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) [] p) := by
    exact augmented_range a.momentAccess.scalarBits
      (MomentStage.rowTask a sourceTask ∘ PolynomialMoment.vectorInput)
      (MomentStage.columnTask a sourceTask ∘ PolynomialMoment.vectorInput)
      (MomentStage.matrixTask a sourceTask ∘ PolynomialMoment.matrixInput) [] P (Or.inl rfl)
      (fun q => Or.inr ⟨rowInput a.dimension (PolynomialMoment.vectorInput q), rfl⟩)
      (fun q => Or.inr ⟨columnInput a.dimension (PolynomialMoment.vectorInput q), rfl⟩)
      (fun q => Or.inr ⟨matrixInput a.dimension (PolynomialMoment.matrixInput q), rfl⟩)
      (PolynomialMoment.augmentedInput p)
  change P (PolynomialPower.RecursiveStage.liftedTask a.momentAccess.power
    (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess (MomentStage.rowTask a sourceTask)
      (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) []
    (MatrixPower.Controller.entryInput s))
  exact lifted_range a.momentAccess.power
    (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess (MomentStage.rowTask a sourceTask)
      (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) [] P (Or.inl rfl) haug _

theorem determinant_query_origin (s : List Bool) :
    (DeterminantStage.controller a factorTask []).query s = [] ∨
      origin ((DeterminantStage.controller a factorTask []).query s) = pairFst s := by
  change (fun q => q = [] ∨ origin q = pairFst s)
    (PolynomialPower.RecursiveStage.liftedTask a.powerAccess (factorTask ∘ ModularAccess.splitDegree) []
      (MatrixPower.Controller.entryInput s))
  unfold PolynomialPower.RecursiveStage.liftedTask
  split_ifs
  · right
    simp only [Function.comp_apply, origin_factor, ModularAccess.splitDegree,
      PolynomialPower.Access.coefficientInput, MatrixPower.Controller.entryInput, pairFst_pair]
  · exact Or.inl rfl

theorem factor_query_origin (s : SingleCall.State) :
    origin ((FactorStage.program a sourceTask momentTask).controller.query s) = pairFst (pairFst s.1) := by
  dsimp only [SingleCall.Program.controller, FactorStage.program]
  split_ifs
  · simp only [origin_source, ModularAccess.diagonalInput, attachDegree,
      Berkowitz.EntryAccess.diagonalInput, pairFst_pair]
  · exact origin_moment _

theorem moment_query_origin (s : List Bool) :
    (MomentStage.controller a sourceTask []).query s = [] ∨
      origin ((MomentStage.controller a sourceTask []).query s) = pairFst (pairFst (pairFst s)) := by
  have haug (p : List Bool) :
      PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess
        (MomentStage.rowTask a sourceTask) (MomentStage.columnTask a sourceTask)
        (MomentStage.matrixTask a sourceTask) [] p = [] ∨
      origin (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess
        (MomentStage.rowTask a sourceTask) (MomentStage.columnTask a sourceTask)
        (MomentStage.matrixTask a sourceTask) [] p) = pairFst (pairFst (pairFst p)) := by
    unfold PolynomialMoment.RecursiveStage.augmentedTask MatrixMoment.EntryBits.task
    dsimp only [Function.comp_apply]
    split_ifs <;> first
    | exact Or.inl rfl
    | right
      simp only [Function.comp_apply, MomentStage.rowTask, MomentStage.columnTask, MomentStage.matrixTask,
        origin_source, rowInput, columnInput, matrixInput, attachDegree, vectorBase, matrixBase,
        Berkowitz.EntryAccess.rowInput, Berkowitz.EntryAccess.columnInput, Berkowitz.EntryAccess.matrixInput,
        PolynomialMoment.vectorInput, PolynomialMoment.matrixInput, MatrixMoment.EntryBits.rowInput,
        MatrixMoment.EntryBits.columnInput, MatrixMoment.EntryBits.matrixInput, PolynomialMoment.augmentedInput,
        pairFst_pair]
  change (fun q => q = [] ∨ origin q = pairFst (pairFst (pairFst s)))
    (PolynomialPower.RecursiveStage.liftedTask a.momentAccess.power
      (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess (MomentStage.rowTask a sourceTask)
        (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) []
      (MatrixPower.Controller.entryInput s))
  unfold PolynomialPower.RecursiveStage.liftedTask
  split_ifs
  · simpa only [PolynomialPower.Access.coefficientInput, MatrixPower.Controller.entryInput, pairFst_pair]
      using haug (PolynomialPower.Access.coefficientInput a.momentAccess.power.bits
        (MatrixPower.Controller.entryInput s))
  · exact Or.inl rfl

variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)

theorem requested_nonzero (g : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hn : (controller a source).needs (((controller a source).reference g)^[t] ((controller a source).initial q)) = true) :
    isZero q = false := by
  apply Bool.eq_false_iff.mpr
  intro hz
  rw [needs_iterate] at hn
  simp only [hz, ite_true, zeroProgram, SingleCall.Program.controller, Bool.false_eq_true] at hn

theorem internal_query_origin (g : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hn : (controller a source).needs (((controller a source).reference g)^[t] ((controller a source).initial q)) = true)
    (hs : ¬SelectedSource q) :
    (controller a source).query (((controller a source).reference g)^[t] ((controller a source).initial q)) = [] ∨
    origin ((controller a source).query
      (((controller a source).reference g)^[t] ((controller a source).initial q))) = origin q := by
  have hz := requested_nonzero a source g q t hn
  rw [query_iterate]
  by_cases hd : isDeterminant q = true
  · simp only [hz, hd, Bool.false_eq_true, ite_false, ite_true]
    have hc : pairFst (((DeterminantStage.controller a factorTask []).reference g)^[t]
        (DeterminantStage.initial a (payload q))) = payload q :=
      PolynomialPower.RecursiveStage.context_iterate a.powerAccess (DeterminantStage.entryTask a factorTask []) g (payload q) t
    simpa only [hc, origin, hz, hd, Bool.false_eq_true, ite_false, ite_true] using
      determinant_query_origin a (((DeterminantStage.controller a factorTask []).reference g)^[t]
        (DeterminantStage.initial a (payload q)))
  · have hd' := Bool.eq_false_iff.mpr hd
    by_cases hf : isFactor q = true
    · simp only [hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
      right
      rw [factor_query_origin, SingleCall.Program.context_iterate]
      simp only [origin, hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
    · have hf' := Bool.eq_false_iff.mpr hf
      by_cases hm : isMoment q = true
      · simp only [hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true]
        have hc : pairFst (((MomentStage.controller a sourceTask []).reference g)^[t]
            (MomentStage.initial a (payload q))) = payload q :=
          PolynomialPower.RecursiveStage.context_iterate a.momentAccess.power
            (PolynomialMoment.RecursiveStage.entryTask a.momentAccess (MomentStage.rowTask a sourceTask)
              (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) g (payload q) t
        simpa only [hc, origin, hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true] using
          moment_query_origin a (((MomentStage.controller a sourceTask []).reference g)^[t]
            (MomentStage.initial a (payload q)))
      · exact False.elim (hs ⟨hz, hd', hf', Bool.eq_false_iff.mpr hm⟩)

theorem internal_query_priority (g : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hn : (controller a source).needs (((controller a source).reference g)^[t] ((controller a source).initial q)) = true)
    (hs : ¬SelectedSource q) :
    priority ((controller a source).query
      (((controller a source).reference g)^[t] ((controller a source).initial q))) < priority q := by
  have hz := requested_nonzero a source g q t hn
  rw [query_iterate]
  by_cases hd : isDeterminant q = true
  · have hp : priority q = 4 := by simp only [priority, hz, hd, Bool.false_eq_true, ite_false, ite_true]
    rw [hp]
    simp only [hz, hd, Bool.false_eq_true, ite_false, ite_true]
    rcases determinant_query_shape a _ with he | ⟨p, he⟩
    · rw [he, priority_zero]; decide
    · rw [he, priority_factor]; decide
  · have hd' : isDeterminant q = false := Bool.eq_false_iff.mpr hd
    by_cases hf : isFactor q = true
    · have hp : priority q = 3 := by simp only [priority, hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
      rw [hp]
      simp only [hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
      obtain ⟨p, he | he⟩ := factor_query_shape a _
      · rw [he, priority_source]; decide
      · rw [he, priority_moment]; decide
    · have hf' : isFactor q = false := Bool.eq_false_iff.mpr hf
      by_cases hm : isMoment q = true
      · have hp : priority q = 2 := by simp only [priority, hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true]
        rw [hp]
        simp only [hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true]
        rcases moment_query_shape a _ with he | ⟨p, he⟩
        · rw [he, priority_zero]; decide
        · rw [he, priority_source]; decide
      · exact False.elim (hs ⟨hz, hd', hf', Bool.eq_false_iff.mpr hm⟩)

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
