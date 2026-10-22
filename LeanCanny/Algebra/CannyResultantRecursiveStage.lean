/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoefficientSpace
public import LeanCanny.Algebra.ShiftCoefficientRecursiveStage
public import LeanCanny.Algebra.SylvesterPolynomialTaskRouting

/-! # A resumable original-entry source for Canny's resultant

Sylvester band guards and the constant-right coefficient guard return zero
immediately. Every other entry makes one original-polynomial coefficient
request. The shifted-left branch computes its binomial factor locally in
native polynomial space. No child-answer computation certificate is assumed.
Supplied Sylvester orders need not equal source polynomial degrees; the
default orders recover the usual Canny resultant source.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.Computation
open Turing.MultiTapeTM

variable {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder)

noncomputable def selectRight : List Bool → Bool :=
  SylvesterPolynomialBits.RecursiveStage.selectRight a.modular.bits

noncomputable def active : List Bool → Bool :=
  SylvesterPolynomialBits.RecursiveStage.active a.modular.bits

noncomputable def leftInput : List Bool → List Bool :=
  SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits

def rightInput : List Bool → List Bool := SylvesterPolynomialBits.RecursiveStage.rightInput

def constantRight (p : List Bool) : Bool :=
  decide (BinaryNat.normalize (ShiftCoefficientBits.rightIndex (rightInput p)) = [])

noncomputable def request (p : List Bool) : Bool :=
  if active a p then if selectRight a p then constantRight p else true else false

noncomputable def leftQuery : List Bool → List Bool := ShiftCoefficientBits.coefficientInput ∘ leftInput a
def rightQuery : List Bool → List Bool := Access.constantInput ∘ rightInput

noncomputable def finish (p : List Bool) : List Bool :=
  if selectRight a (pairFst p) then pairSnd p
  else ShiftCoefficientBits.RecursiveStage.finish a.shiftAccess (pair (leftInput a (pairFst p)) (pairSnd p))

noncomputable def program (leftTask rightTask : List Bool → List Bool) : SingleCall.Program where
  request := request a
  query := fun p => if selectRight a p then rightTask (rightQuery p) else leftTask (leftQuery a p)
  immediate := fun _ => []
  finish := finish a

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul BinaryNat.mulMod
  BinaryNat.powMod BinomialResidue.value SylvesterPolynomialBits.RecursiveStage.selectRight
  SylvesterPolynomialBits.RecursiveStage.active SylvesterPolynomialBits.RecursiveStage.leftInput
  SylvesterPolynomialBits.RecursiveStage.rightInput ShiftCoefficientBits.coefficientInput
  ShiftCoefficientBits.RecursiveStage.finish

theorem selectRight_FP (ha : a.ControlsPolyTime) : (fun p => [selectRight a p]) ∈ FP :=
  SylvesterPolynomialBits.RecursiveStage.selectRight_FP a.modular.bits (a.modular_controlsWithCoefficients ha)

theorem active_FP (ha : a.ControlsPolyTime) : (fun p => [active a p]) ∈ FP :=
  SylvesterPolynomialBits.RecursiveStage.active_FP a.modular.bits (a.modular_controlsWithCoefficients ha)

theorem leftInput_FP (ha : a.ControlsPolyTime) : leftInput a ∈ FP :=
  SylvesterPolynomialBits.RecursiveStage.leftInput_FP a.modular.bits (a.modular_controlsWithCoefficients ha)

theorem rightInput_FP : rightInput ∈ FP := SylvesterPolynomialBits.RecursiveStage.rightInput_FP

theorem constantRight_FP : (fun p => [constantRight p]) ∈ FP :=
  (stringEq_fppred (mem_FP_comp (mem_FP_comp rightInput_FP ShiftCoefficientBits.rightIndex_mem_FP)
    BinaryNat.normalize_mem_FP) (constFn_mem_FP [])).flag_mem_FP

theorem request_FP (ha : a.ControlsPolyTime) : (fun p => [request a p]) ∈ FP := by
  have hr := (flag_computable (selectRight_FP a ha)).ite' constantRight_FP (constFn_mem_FP [true])
  have h := (flag_computable (active_FP a ha)).ite' hr (constFn_mem_FP [false])
  refine mem_FP_of_eq h ?_
  intro p
  unfold request
  split_ifs <;> rfl

theorem leftQuery_FP (ha : a.ControlsPolyTime) : leftQuery a ∈ FP :=
  mem_FP_comp (leftInput_FP a ha) ShiftCoefficientBits.coefficientInput_mem_FP

theorem rightQuery_FP : rightQuery ∈ FP := mem_FP_comp rightInput_FP Access.constantInput_mem_FP

theorem finish_space (ha : a.ControlsPolyTime) : SpaceFunction (finish a) := by
  have hp := mem_FP_comp pairFst_mem_FP (selectRight_FP a ha)
  have hq := mem_FP_pair (mem_FP_comp pairFst_mem_FP (leftInput_FP a ha)) pairSnd_mem_FP
  have hl := (ShiftCoefficientBits.RecursiveStage.finish_space a.shiftAccess ha.direction).precompose
    (fun p => pair (leftInput a (pairFst p)) (pairSnd p)) hq
  have E := SpaceFunction.branch (fun p => selectRight a (pairFst p)) hp
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP) hl
  exact E.congr (funext fun _ => by simp only [Function.comp_apply, finish])

theorem certificates (ha : a.ControlsPolyTime) (leftTask rightTask : List Bool → List Bool)
    (hl : leftTask ∈ FP) (hr : rightTask ∈ FP) :
    (program a leftTask rightTask).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) := by
  have hq := (flag_computable (selectRight_FP a ha)).ite'
    (mem_FP_comp rightQuery_FP hr) (mem_FP_comp (leftQuery_FP a ha) hl)
  exact (program a leftTask rightTask).certificates_of_space (request_FP a ha) hq
    (.of_polyTime (FP.computable (constFn_mem_FP []))) (finish_space a ha).computable

theorem value_eq (leftTask rightTask answer : List Bool → List Bool)
    (hl : ∀ p, answer (leftTask p) = a.leftCoefficient p)
    (hr : ∀ p, answer (rightTask p) = a.rightCoefficient p) (p : List Bool) :
    (program a leftTask rightTask).value answer p = a.modular.determinant.entry p := by
  have hs (u : List Bool) : ShiftCoefficientBits.computed a.shiftAccess u = F.shiftSource.value u :=
    ShiftCoefficientBits.computed_correct a.shiftAccess u (F.shiftSource.polynomial (ShiftCoefficientBits.original u))
      (F.shiftSource.direction (ShiftCoefficientBits.original u)) (a.shift_represents.direction _)
      (fun k => a.shift_represents.coefficient (pairFst u) k)
  change (program a leftTask rightTask).value answer p = a.modular.bits.entry p
  rw [SylvesterPolynomialBits.RecursiveStage.entry_eq]
  change (program a leftTask rightTask).value answer p =
    if active a p then if selectRight a p then a.constantCoefficient (rightInput p)
      else F.shiftSource.value (leftInput a p) else []
  by_cases hb : active a p = true
  · by_cases hr' : selectRight a p = true
    · by_cases hc : BinaryNat.normalize (ShiftCoefficientBits.rightIndex (rightInput p)) = []
      <;> simp only [SingleCall.Program.value, program, request, finish, hb, hr', constantRight, hc,
        decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false, pairFst_pair, pairSnd_pair,
        hr, rightQuery, Function.comp_apply, Access.constantCoefficient, Access.constantInput]
    · have hr'' := Bool.eq_false_iff.mpr hr'
      simp only [SingleCall.Program.value, program, request, finish, hb, hr'', ite_true,
        Bool.false_eq_true, ite_false, pairFst_pair, pairSnd_pair, leftQuery, Function.comp_apply, hl]
      exact (ShiftCoefficientBits.RecursiveStage.finish_correct a.shiftAccess (leftInput a p)).trans (hs _)
  · have hb' := Bool.eq_false_iff.mpr hb
    simp only [SingleCall.Program.value, program, request, hb', Bool.false_eq_true, ite_false]

theorem halted_after (leftTask rightTask answer : List Bool → List Bool) (p : List Bool) :
    (program a leftTask rightTask).controller.halted
      (((program a leftTask rightTask).controller.reference answer)^[1] (SingleCall.Program.initial p)) = true :=
  (program a leftTask rightTask).halted_after answer p

theorem query_iterate (leftTask rightTask answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (program a leftTask rightTask).controller.query
      (((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) =
      if selectRight a p then rightTask (rightQuery p) else leftTask (leftQuery a p) := by
  change (program a leftTask rightTask).query
    ((((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)).1) = _
  rw [SingleCall.Program.context_iterate]
  rfl

theorem needs_iterate (leftTask rightTask answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (program a leftTask rightTask).controller.needs
      (((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = request a p := by
  change (program a leftTask rightTask).request
    ((((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)).1) = _
  rw [SingleCall.Program.context_iterate]
  rfl

theorem leftQuery_context (p : List Bool) : pairFst (leftQuery a p) = pairFst p := by
  simp only [leftQuery, Function.comp_apply, ShiftCoefficientBits.coefficientInput, pairFst_pair, leftInput,
    SylvesterPolynomialBits.RecursiveStage.leftInput_context]

theorem rightQuery_context (p : List Bool) : pairFst (rightQuery p) = pairFst p := by
  simp only [rightQuery, Function.comp_apply, Access.constantInput, pairFst_pair, rightInput,
    SylvesterPolynomialBits.RecursiveStage.rightInput_context]

theorem output_when_halted (leftTask rightTask answer : List Bool → List Bool)
    (hl : ∀ p, answer (leftTask p) = a.leftCoefficient p)
    (hr : ∀ p, answer (rightTask p) = a.rightCoefficient p) (p : List Bool) (t : ℕ)
    (hh : (program a leftTask rightTask).controller.halted
      (((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = true) :
    (program a leftTask rightTask).controller.output
      (((program a leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = a.modular.determinant.entry p :=
  ((program a leftTask rightTask).output_when_halted answer p t hh).trans (value_eq a leftTask rightTask answer hl hr p)

end LeanCanny.Algebra.CannyResultantBits.RecursiveStage
