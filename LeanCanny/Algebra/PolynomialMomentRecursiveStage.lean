/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialMomentSpace
public import LeanCanny.Algebra.PolynomialPowerRecursiveStage
public import LeanCanny.Algebra.MatrixMomentTaskRouting

/-! # Resumable coefficients of polynomial scalar moments

Source/sink and degree guards route each scalar entry to a row, column,
matrix coefficient, or zero task. No source-answer certificate is assumed.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialMoment.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open ModularAccess MatrixPower
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
attribute [local irreducible] MatrixMoment.EntryBits.entry PolynomialPower.Access.lower
  PolynomialPower.Access.coefficientInput MatrixPower.Controller.halted MatrixPower.Controller.needsEntry

def augmentedTask (rowTask columnTask matrixTask : List Bool → List Bool) (zeroTask : List Bool) :
    List Bool → List Bool :=
  MatrixMoment.EntryBits.task a.scalarBits (rowTask ∘ vectorInput) (columnTask ∘ vectorInput)
    (matrixTask ∘ matrixInput) zeroTask ∘ augmentedInput

theorem augmentedTask_FP (ha : a.ControlsPolyTime) (rowTask columnTask matrixTask : List Bool → List Bool)
    (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) (zeroTask : List Bool) :
    augmentedTask a rowTask columnTask matrixTask zeroTask ∈ FP := by
  have hd := mem_FP_comp pairFst_mem_FP ha.dimension
  have hR := mem_FP_comp vectorInput_mem_FP hr
  have hC := mem_FP_comp vectorInput_mem_FP hc
  have hM := mem_FP_comp matrixInput_mem_FP hm
  have h := MatrixMoment.EntryBits.task_FP a.scalarBits hd (rowTask ∘ vectorInput) (columnTask ∘ vectorInput)
    (matrixTask ∘ matrixInput) hR hC hM zeroTask
  exact mem_FP_comp augmentedInput_mem_FP h

theorem augmentedTask_eq (rowTask columnTask matrixTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hr : ∀ p, answer (rowTask p) = a.bits.row p) (hc : ∀ p, answer (columnTask p) = a.bits.column p)
    (hm : ∀ p, answer (matrixTask p) = a.bits.entry p) (hz : answer zeroTask = []) (p : List Bool) :
    answer (augmentedTask a rowTask columnTask matrixTask zeroTask p) = a.augmentedCoefficient p :=
  MatrixMoment.EntryBits.task_eq a.scalarBits (rowTask ∘ vectorInput) (columnTask ∘ vectorInput)
    (matrixTask ∘ matrixInput) answer zeroTask
    (fun q => hr (vectorInput q)) (fun q => hc (vectorInput q)) (fun q => hm (matrixInput q)) hz (augmentedInput p)

noncomputable def entryTask (rowTask columnTask matrixTask : List Bool → List Bool) (zeroTask : List Bool) :
    List Bool → List Bool :=
  PolynomialPower.RecursiveStage.liftedTask a.power (augmentedTask a rowTask columnTask matrixTask zeroTask) zeroTask

noncomputable def initial : List Bool → List Bool := PolynomialPower.RecursiveStage.initial a.power

noncomputable def controller (rowTask columnTask matrixTask : List Bool → List Bool) (zeroTask : List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) :=
  PolynomialPower.RecursiveStage.controller a.power (entryTask a rowTask columnTask matrixTask zeroTask)

theorem entryTask_FP (ha : a.ControlsPolyTime) (rowTask columnTask matrixTask : List Bool → List Bool)
    (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) (zeroTask : List Bool) :
    entryTask a rowTask columnTask matrixTask zeroTask ∈ FP :=
  PolynomialPower.RecursiveStage.liftedTask_FP a.power (power_controls a ha)
    (augmentedTask a rowTask columnTask matrixTask zeroTask)
    (augmentedTask_FP a ha rowTask columnTask matrixTask hr hc hm zeroTask) zeroTask

theorem entryTask_eq (rowTask columnTask matrixTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hr : ∀ p, answer (rowTask p) = a.bits.row p) (hc : ∀ p, answer (columnTask p) = a.bits.column p)
    (hm : ∀ p, answer (matrixTask p) = a.bits.entry p) (hz : answer zeroTask = []) (p : List Bool) :
    answer (entryTask a rowTask columnTask matrixTask zeroTask p) = a.power.power.entry p :=
  PolynomialPower.RecursiveStage.liftedTask_eq a.power (augmentedTask a rowTask columnTask matrixTask zeroTask)
    answer zeroTask (augmentedTask_eq a rowTask columnTask matrixTask answer zeroTask hr hc hm hz) hz p

theorem certificates (ha : a.ControlsPolyTime) (rowTask columnTask matrixTask : List Bool → List Bool)
    (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) (zeroTask : List Bool) :
    (controller a rowTask columnTask matrixTask zeroTask).Certificates (encQ := encBits) (encS := encBits) :=
  PolynomialPower.RecursiveStage.certificates a.power (power_controls a ha)
    (entryTask a rowTask columnTask matrixTask zeroTask) (entryTask_FP a ha rowTask columnTask matrixTask hr hc hm zeroTask)

theorem halted_after (rowTask columnTask matrixTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hr : ∀ p, answer (rowTask p) = a.bits.row p) (hc : ∀ p, answer (columnTask p) = a.bits.column p)
    (hm : ∀ p, answer (matrixTask p) = a.bits.entry p) (hz : answer zeroTask = []) (c : List Bool) :
    (controller a rowTask columnTask matrixTask zeroTask).halted
      (((controller a rowTask columnTask matrixTask zeroTask).reference answer)^[work
        ((F.dimension c + 2) * (F.degree c + 1)) (F.exponent c + 2).size (F.exponent c + 2) + 1] (initial a c)) = true :=
  PolynomialPower.RecursiveStage.halted_after a.power (entryTask a rowTask columnTask matrixTask zeroTask) answer
    (entryTask_eq a rowTask columnTask matrixTask answer zeroTask hr hc hm hz) c

theorem output_when_halted (rowTask columnTask matrixTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hr : ∀ p, answer (rowTask p) = a.bits.row p) (hc : ∀ p, answer (columnTask p) = a.bits.column p)
    (hm : ∀ p, answer (matrixTask p) = a.bits.entry p) (hz : answer zeroTask = []) (c : List Bool) (t : ℕ)
    (hh : (controller a rowTask columnTask matrixTask zeroTask).halted
      (((controller a rowTask columnTask matrixTask zeroTask).reference answer)^[t] (initial a c)) = true) :
    (controller a rowTask columnTask matrixTask zeroTask).output
      (((controller a rowTask columnTask matrixTask zeroTask).reference answer)^[t] (initial a c)) = F.value c := by
  have h := PolynomialPower.RecursiveStage.output_when_halted a.power (entryTask a rowTask columnTask matrixTask zeroTask)
    answer (entryTask_eq a rowTask columnTask matrixTask answer zeroTask hr hc hm hz) c t hh
  refine h.trans ?_
  change residueBits (((MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c) ^ (F.exponent c + 2))
    0 (Fin.last (F.dimension c + 1))).coeff (F.degree c)) = _
  rw [MatrixMoment.matrixFin_pow_moment]
  rfl

theorem state_length (rowTask columnTask matrixTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hr : ∀ p, answer (rowTask p) = a.bits.row p) (hc : ∀ p, answer (columnTask p) = a.bits.column p)
    (hm : ∀ p, answer (matrixTask p) = a.bits.entry p) (hz : answer zeroTask = []) (c : List Bool) (t : ℕ) :
    (((controller a rowTask columnTask matrixTask zeroTask).reference answer)^[t] (initial a c)).length ≤
      2 * c.length + 2 + 64 * (((F.dimension c + 2) * (F.degree c + 1)).size +
        (F.exponent c + 2).size + (F.modulus c).size + 1) ^ 2 :=
  PolynomialPower.RecursiveStage.state_length a.power (entryTask a rowTask columnTask matrixTask zeroTask) answer
    (entryTask_eq a rowTask columnTask matrixTask answer zeroTask hr hc hm hz) c t

end LeanCanny.Algebra.PolynomialMoment.RecursiveStage
