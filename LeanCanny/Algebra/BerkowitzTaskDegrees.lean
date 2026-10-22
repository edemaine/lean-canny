/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskRouting

/-! # Internal requests never increase the selected polynomial degree

Flattened coefficient indices are reduced modulo the truncation width before
subtraction. This bounds the requested degree on arbitrary controller states,
without requiring a matrix-index invariant or a certificate for child answers.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open Berkowitz

def selectedDegree (F : ModularFamily) (q : List Bool) : ℕ :=
  if isZero q then 0 else if isDeterminant q then F.degree (payload q)
  else if isFactor q then Nat.fromBitsLE (pairSnd (payload q))
  else if isMoment q then Nat.fromBitsLE (pairSnd (payload q))
  else Nat.fromBitsLE (pairSnd (pairSnd (pairSnd (payload q))))

theorem selectedDegree_zero (F : ModularFamily) : selectedDegree F [] = 0 := rfl
theorem selectedDegree_factor (F : ModularFamily) (p : List Bool) :
    selectedDegree F (factorTask p) = Nat.fromBitsLE (pairSnd p) := rfl
theorem selectedDegree_moment (F : ModularFamily) (p : List Bool) :
    selectedDegree F (momentTask p) = Nat.fromBitsLE (pairSnd p) := rfl
theorem selectedDegree_source (F : ModularFamily) (p : List Bool) :
    selectedDegree F (sourceTask p) = Nat.fromBitsLE (pairSnd (pairSnd (pairSnd p))) := rfl

attribute [local irreducible] BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul
  BinaryNat.add BinaryNat.sub BinaryNat.succ
  PolynomialPower.Access.lower PolynomialPower.Access.coefficientInput
  MatrixMoment.EntryBits.rowIndex MatrixMoment.EntryBits.colIndex MatrixMoment.EntryBits.sinkIndex
  BinaryNat.pred selectedDegree

private theorem coefficientInput_degree_le (a : PolynomialPower.Access) (p : List Bool) :
    Nat.fromBitsLE (pairSnd (pairSnd (pairSnd (a.coefficientInput p)))) ≤ Nat.fromBitsLE (a.degree (pairFst p)) := by
  simp only [PolynomialPower.Access.coefficientInput, pairSnd_pair, BinaryNat.sub_pair,
    QueryBits.sourceDegree_eq_code, QueryBits.targetDegree_eq_code, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, QueryBits.inputDimension]
  have h : Nat.fromBitsLE (QueryBits.rowIndex p) % (Nat.fromBitsLE (a.degree (pairFst p)) + 1) <
      Nat.fromBitsLE (a.degree (pairFst p)) + 1 := Nat.mod_lt _ (by omega)
  omega

variable {F : ModularFamily} (a : ModularAccess F)

theorem determinant_query_degree_le (s : List Bool) :
    selectedDegree F ((DeterminantStage.controller a factorTask []).query s) ≤ F.degree (pairFst s) := by
  change selectedDegree F (PolynomialPower.RecursiveStage.liftedTask a.powerAccess
    (factorTask ∘ ModularAccess.splitDegree) [] (MatrixPower.Controller.entryInput s)) ≤ _
  unfold PolynomialPower.RecursiveStage.liftedTask
  split_ifs
  · simp only [Function.comp_apply, selectedDegree_factor, ModularAccess.splitDegree, pairSnd_pair]
    have h := coefficientInput_degree_le a.powerAccess.bits (MatrixPower.Controller.entryInput s)
    simpa only [ModularAccess.powerAccess, MatrixPower.Controller.entryInput, pairFst_pair,
      a.degree_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h
  · rw [selectedDegree_zero]
    exact Nat.zero_le _

theorem factor_query_degree_le (s : SingleCall.State) :
    selectedDegree F ((FactorStage.program a sourceTask momentTask).controller.query s) ≤ Nat.fromBitsLE (pairSnd s.1) := by
  dsimp only [SingleCall.Program.controller, FactorStage.program]
  split_ifs
  · simp only [selectedDegree_source, ModularAccess.diagonalInput, attachDegree, pairSnd_pair]
    exact le_refl _
  · rw [selectedDegree_moment]

theorem moment_query_degree_le (s : List Bool) :
    selectedDegree F ((MomentStage.controller a sourceTask []).query s) ≤ Nat.fromBitsLE (pairSnd (pairFst s)) := by
  have haug (p : List Bool) : selectedDegree F (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess
      (MomentStage.rowTask a sourceTask) (MomentStage.columnTask a sourceTask)
      (MomentStage.matrixTask a sourceTask) [] p) ≤ Nat.fromBitsLE (pairSnd (pairSnd (pairSnd p))) := by
    unfold PolynomialMoment.RecursiveStage.augmentedTask MatrixMoment.EntryBits.task
    dsimp only [Function.comp_apply]
    split_ifs <;> first
    | rw [selectedDegree_zero]; exact Nat.zero_le _
    | simp only [Function.comp_apply, MomentStage.rowTask, MomentStage.columnTask, MomentStage.matrixTask,
        selectedDegree_source, rowInput, columnInput, matrixInput, attachDegree,
        PolynomialMoment.vectorInput, PolynomialMoment.matrixInput, MatrixMoment.EntryBits.rowInput,
        MatrixMoment.EntryBits.columnInput, MatrixMoment.EntryBits.matrixInput, PolynomialMoment.augmentedInput,
        pairFst_pair, pairSnd_pair]
      exact le_refl _
  change selectedDegree F (PolynomialPower.RecursiveStage.liftedTask a.momentAccess.power
    (PolynomialMoment.RecursiveStage.augmentedTask a.momentAccess (MomentStage.rowTask a sourceTask)
      (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) []
      (MatrixPower.Controller.entryInput s)) ≤ _
  unfold PolynomialPower.RecursiveStage.liftedTask
  split_ifs
  · have h := (haug _).trans (coefficientInput_degree_le a.momentAccess.power.bits (MatrixPower.Controller.entryInput s))
    simpa only [PolynomialMoment.ModularAccess.power, ModularAccess.momentAccess,
      MatrixPower.Controller.entryInput, pairFst_pair, Function.comp_apply, BinaryNat.normalize_eq_bits,
      Nat.fromBitsLE_bits] using h
  · rw [selectedDegree_zero]
    exact Nat.zero_le _

variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)

theorem internal_query_degree_le (g : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hn : (controller a source).needs (((controller a source).reference g)^[t] ((controller a source).initial q)) = true)
    (hs : ¬SelectedSource q) :
    selectedDegree F ((controller a source).query
      (((controller a source).reference g)^[t] ((controller a source).initial q))) ≤ selectedDegree F q := by
  have hz := requested_nonzero a source g q t hn
  rw [query_iterate]
  by_cases hd : isDeterminant q = true
  · simp only [hz, hd, Bool.false_eq_true, ite_false, ite_true]
    have hc : pairFst (((DeterminantStage.controller a factorTask []).reference g)^[t]
        (DeterminantStage.initial a (payload q))) = payload q :=
      PolynomialPower.RecursiveStage.context_iterate a.powerAccess (DeterminantStage.entryTask a factorTask []) g (payload q) t
    conv_rhs => simp only [selectedDegree, hz, hd, Bool.false_eq_true, ite_false, ite_true]
    simpa only [hc] using
      determinant_query_degree_le a (((DeterminantStage.controller a factorTask []).reference g)^[t]
        (DeterminantStage.initial a (payload q)))
  · have hd' := Bool.eq_false_iff.mpr hd
    by_cases hf : isFactor q = true
    · simp only [hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
      have h := factor_query_degree_le a ((((FactorStage.program a sourceTask momentTask).controller).reference g)^[t]
        (SingleCall.Program.initial (payload q)))
      rw [SingleCall.Program.context_iterate] at h
      conv_rhs => simp only [selectedDegree, hz, hd', hf, Bool.false_eq_true, ite_false, ite_true]
      exact h
    · have hf' := Bool.eq_false_iff.mpr hf
      by_cases hm : isMoment q = true
      · simp only [hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true]
        have hc : pairFst (((MomentStage.controller a sourceTask []).reference g)^[t]
            (MomentStage.initial a (payload q))) = payload q :=
          PolynomialPower.RecursiveStage.context_iterate a.momentAccess.power
            (PolynomialMoment.RecursiveStage.entryTask a.momentAccess (MomentStage.rowTask a sourceTask)
              (MomentStage.columnTask a sourceTask) (MomentStage.matrixTask a sourceTask) []) g (payload q) t
        conv_rhs => simp only [selectedDegree, hz, hd', hf', hm, Bool.false_eq_true, ite_false, ite_true]
        simpa only [hc] using
          moment_query_degree_le a (((MomentStage.controller a sourceTask []).reference g)^[t]
            (MomentStage.initial a (payload q)))
      · exact False.elim (hs ⟨hz, hd', hf', Bool.eq_false_iff.mpr hm⟩)

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
