/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzDeterminantRecursiveStage
public import LeanCanny.Algebra.BerkowitzFactorRecursiveStage
public import LeanCanny.Algebra.BerkowitzMomentRecursiveStage
public import LeanCanny.Computation.ControllerDispatch

/-! # One task interface for determinant, factor, moment, and source stages

Two-bit tags identify stages; the empty word is the zero task. A supplied
source controller shares this task type and may itself request other stages.
Only its local native certificates are needed, not a certificate for the
original coefficient answer function.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open RecursiveController.Controller
open Turing.MultiTapeTM

def tag (b c : Bool) (p : List Bool) : List Bool := b :: c :: p
def determinantTask : List Bool → List Bool := tag false false
def factorTask : List Bool → List Bool := tag false true
def momentTask : List Bool → List Bool := tag true false
def sourceTask : List Bool → List Bool := tag true true
def payload (p : List Bool) : List Bool := p.drop 2
def isZero (p : List Bool) : Bool := p.isEmpty
def isDeterminant (p : List Bool) : Bool := !p[0]?.getD false && !p[1]?.getD false
def isFactor (p : List Bool) : Bool := !p[0]?.getD false
def isMoment (p : List Bool) : Bool := !p[1]?.getD false

theorem tag_FP (b c : Bool) : tag b c ∈ FP := mem_FP_comp (cons_mem_FP c) (cons_mem_FP b)
theorem payload_FP : payload ∈ FP := drop_mem_FP id_mem_FP (UnaryFn.const 2)
theorem isZero_computable : ComputableTidilyInPolyTime isZero encBits encBool := ComputableTidilyInPolyTime.bitsIsEmpty

private theorem first_not_computable : ComputableTidilyInPolyTime isFactor encBits encBool :=
  ComputableTidilyInPolyTime.bool_not.comp (flag_computable (getBit_mem_FP id_mem_FP (UnaryFn.const 0)))

theorem isMoment_computable : ComputableTidilyInPolyTime isMoment encBits encBool :=
  ComputableTidilyInPolyTime.bool_not.comp (flag_computable (getBit_mem_FP id_mem_FP (UnaryFn.const 1)))

theorem isDeterminant_computable : ComputableTidilyInPolyTime isDeterminant encBits encBool :=
  ComputableTidilyInPolyTime.bool_and' first_not_computable isMoment_computable

def zeroProgram : SingleCall.Program where
  request := fun _ => false
  query := id
  immediate := fun _ => []
  finish := pairSnd

theorem zero_controls : zeroProgram.Controls :=
  ⟨constFn_mem_FP [false], id_mem_FP, constFn_mem_FP [], pairSnd_mem_FP⟩

variable {F : ModularFamily} (a : ModularAccess F)
attribute [local irreducible] ModularAccess.factorValue PolynomialPower.Access.lower
  PolynomialPower.Access.coefficientInput MatrixMoment.EntryBits.entry
  MatrixPower.Controller.halted MatrixPower.Controller.needsEntry
  ModularFamily.value PolynomialMoment.ModularFamily.value

noncomputable def answer (q : List Bool) : List Bool :=
  if isZero q then []
  else if isDeterminant q then F.value (payload q)
  else if isFactor q then ModularAccess.factorValue a (payload q)
  else if isMoment q then (momentFamily F).value (payload q)
  else a.entry (payload q)

theorem answer_eq (q : List Bool) : answer a q =
    if isZero q then [] else if isDeterminant q then F.value (payload q)
    else if isFactor q then ModularAccess.factorValue a (payload q)
    else if isMoment q then (momentFamily F).value (payload q)
    else a.entry (payload q) := rfl

theorem answer_zero : answer a [] = [] := rfl

theorem answer_determinant (p : List Bool) : answer a (determinantTask p) = F.value p := rfl
theorem answer_factor (p : List Bool) : answer a (factorTask p) = ModularAccess.factorValue a p := rfl
theorem answer_moment (p : List Bool) : answer a (momentTask p) = (momentFamily F).value p := rfl
theorem answer_source (p : List Bool) : answer a (sourceTask p) = a.entry p := rfl

-- Dispatch proofs compare stage interfaces, not executions of their binary
-- metadata writers or parsers.
attribute [local irreducible] isZero isDeterminant isFactor isMoment payload
  MatrixPower.Controller.initialPacket BinaryNat.div BinaryNat.mod BinaryNat.normalize
  BinaryNat.succ BinaryNat.mul BinaryNat.add BinaryNat.sub FactorStage.program

abbrev RemainderState (S : Type) := ChoiceState (List Bool) S
abbrev FactorState (S : Type) := ChoiceState SingleCall.State (RemainderState S)
abbrev PowerState (S : Type) := ChoiceState (List Bool) (FactorState S)
abbrev State (S : Type) := ChoiceState SingleCall.State (PowerState S)

abbrev encState {S : Type} (encS : S ↪ List Bool) : State S ↪ List Bool :=
  encChoice SingleCall.encState (encChoice encBits (encChoice SingleCall.encState (encChoice encBits encS)))

noncomputable def controller {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S) :
    RecursiveController.Controller (List Bool) (State S) :=
  choose isZero zeroProgram.controller
    (choose isDeterminant (prepare (DeterminantStage.controller a factorTask []) payload)
      (choose isFactor (prepare (FactorStage.program a sourceTask momentTask).controller payload)
        (choose isMoment (prepare (MomentStage.controller a sourceTask []) payload) (prepare source payload))))

theorem certificates {S : Type} [Inhabited S] {encS : S ↪ List Bool}
    (ha : a.ControlsPolyTime) (source : RecursiveController.Controller (List Bool) S)
    (hs : source.Certificates (encQ := encBits) (encS := encS)) :
    (controller a source).Certificates (encQ := encBits) (encS := encState encS) := by
  have hp := FP.computable payload_FP
  have hd := prepare_certificates (DeterminantStage.controller a factorTask []) payload
    (DeterminantStage.certificates a ha factorTask (tag_FP false true) []) hp
  have hf := prepare_certificates (FactorStage.program a sourceTask momentTask).controller payload
    (FactorStage.certificates a ha sourceTask momentTask (tag_FP true true) (tag_FP true false)) hp
  have hm := prepare_certificates (MomentStage.controller a sourceTask []) payload
    (MomentStage.certificates a ha sourceTask (tag_FP true true) []) hp
  have hsource := prepare_certificates source payload hs hp
  have hms := choose_certificates isMoment (prepare (MomentStage.controller a sourceTask []) payload)
    (prepare source payload) isMoment_computable hm hsource
  have hfs := choose_certificates isFactor (prepare (FactorStage.program a sourceTask momentTask).controller payload)
    _ first_not_computable hf hms
  have hds := choose_certificates isDeterminant (prepare (DeterminantStage.controller a factorTask []) payload)
    _ isDeterminant_computable hd hfs
  exact choose_certificates isZero zeroProgram.controller _ isZero_computable (zeroProgram.certificates zero_controls) hds

theorem halted_iterate {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (controller a source).halted (((controller a source).reference g)^[t] ((controller a source).initial q)) =
      if isZero q then zeroProgram.controller.halted ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))
      else if isDeterminant q then (DeterminantStage.controller a factorTask []).halted
        (((DeterminantStage.controller a factorTask []).reference g)^[t] (DeterminantStage.initial a (payload q)))
      else if isFactor q then (FactorStage.program a sourceTask momentTask).controller.halted
        ((((FactorStage.program a sourceTask momentTask).controller).reference g)^[t] (SingleCall.Program.initial (payload q)))
      else if isMoment q then (MomentStage.controller a sourceTask []).halted
        (((MomentStage.controller a sourceTask []).reference g)^[t] (MomentStage.initial a (payload q)))
      else source.halted ((source.reference g)^[t] (source.initial (payload q))) := by
  simp only [controller, choose_halted_iterate, prepare_halted_iterate]
  rfl

theorem output_iterate {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (controller a source).output (((controller a source).reference g)^[t] ((controller a source).initial q)) =
      if isZero q then zeroProgram.controller.output ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))
      else if isDeterminant q then (DeterminantStage.controller a factorTask []).output
        (((DeterminantStage.controller a factorTask []).reference g)^[t] (DeterminantStage.initial a (payload q)))
      else if isFactor q then (FactorStage.program a sourceTask momentTask).controller.output
        ((((FactorStage.program a sourceTask momentTask).controller).reference g)^[t] (SingleCall.Program.initial (payload q)))
      else if isMoment q then (MomentStage.controller a sourceTask []).output
        (((MomentStage.controller a sourceTask []).reference g)^[t] (MomentStage.initial a (payload q)))
      else source.output ((source.reference g)^[t] (source.initial (payload q))) := by
  simp only [controller, choose_output_iterate, prepare_output_iterate]
  rfl

theorem needs_iterate {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (controller a source).needs (((controller a source).reference g)^[t] ((controller a source).initial q)) =
      if isZero q then zeroProgram.controller.needs ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))
      else if isDeterminant q then (DeterminantStage.controller a factorTask []).needs
        (((DeterminantStage.controller a factorTask []).reference g)^[t] (DeterminantStage.initial a (payload q)))
      else if isFactor q then (FactorStage.program a sourceTask momentTask).controller.needs
        ((((FactorStage.program a sourceTask momentTask).controller).reference g)^[t] (SingleCall.Program.initial (payload q)))
      else if isMoment q then (MomentStage.controller a sourceTask []).needs
        (((MomentStage.controller a sourceTask []).reference g)^[t] (MomentStage.initial a (payload q)))
      else source.needs ((source.reference g)^[t] (source.initial (payload q))) := by
  simp only [controller, choose_needs_iterate, prepare_needs_iterate]
  rfl

theorem query_iterate {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (controller a source).query (((controller a source).reference g)^[t] ((controller a source).initial q)) =
      if isZero q then zeroProgram.controller.query ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))
      else if isDeterminant q then (DeterminantStage.controller a factorTask []).query
        (((DeterminantStage.controller a factorTask []).reference g)^[t] (DeterminantStage.initial a (payload q)))
      else if isFactor q then (FactorStage.program a sourceTask momentTask).controller.query
        ((((FactorStage.program a sourceTask momentTask).controller).reference g)^[t] (SingleCall.Program.initial (payload q)))
      else if isMoment q then (MomentStage.controller a sourceTask []).query
        (((MomentStage.controller a sourceTask []).reference g)^[t] (MomentStage.initial a (payload q)))
      else source.query ((source.reference g)^[t] (source.initial (payload q))) := by
  simp only [controller, choose_query_iterate, prepare_query_iterate]
  rfl

def determinantBudget (c : List Bool) : ℕ := MatrixPower.work
  ((F.dimension c + 1) * (F.dimension c + 1) * (F.degree c + 1)) (F.dimension c).size (F.dimension c) + 1

def momentBudget (p : List Bool) : ℕ := MatrixPower.work
  ((trailingDimension F (pairFst p) + 2) * (Nat.fromBitsLE (pairSnd p) + 1))
  (momentExponent F (pairFst p) + 2).size (momentExponent F (pairFst p) + 2) + 1

def budget (sourceBudget : List Bool → ℕ) (q : List Bool) : ℕ :=
  if isZero q then 0 else if isDeterminant q then determinantBudget (F := F) (payload q)
  else if isFactor q then 1 else if isMoment q then momentBudget (F := F) (payload q) else sourceBudget (payload q)

theorem halted_after {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (sourceBudget : List Bool → ℕ)
    (hs : ∀ p, source.halted ((source.reference (answer a))^[sourceBudget p] (source.initial p)) = true)
    (q : List Bool) :
    (controller a source).halted (((controller a source).reference (answer a))^[budget (F := F) sourceBudget q]
      ((controller a source).initial q)) = true := by
  rw [halted_iterate]
  unfold budget
  split_ifs
  · rfl
  · exact DeterminantStage.halted_after a factorTask (answer a) [] (answer_factor a) (answer_zero a) (payload q)
  · exact FactorStage.halted_after a sourceTask momentTask (answer a) (payload q)
  · exact MomentStage.halted_after a sourceTask (answer a) [] (answer_source a) (answer_zero a) (payload q)
  · exact hs (payload q)

theorem output_correct {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
    (hs : ∀ p t, source.halted ((source.reference (answer a))^[t] (source.initial p)) = true →
      source.output ((source.reference (answer a))^[t] (source.initial p)) = a.entry p)
    (q : List Bool) (t : ℕ)
    (hh : (controller a source).halted (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = true) :
    (controller a source).output (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = answer a q := by
  rw [halted_iterate] at hh
  rw [output_iterate]
  rw [answer_eq a q]
  split_ifs at hh ⊢
  · exact (zeroProgram.output_when_halted (answer a) q t hh).trans rfl
  · exact DeterminantStage.output_when_halted a factorTask (answer a) [] (answer_factor a) (answer_zero a) (payload q) t hh
  · exact FactorStage.output_when_halted a sourceTask momentTask (answer a) (answer_source a) (answer_moment a) (payload q) t hh
  · exact MomentStage.output_when_halted a sourceTask (answer a) [] (answer_source a) (answer_zero a) (payload q) t hh
  · exact hs (payload q) t hh

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
