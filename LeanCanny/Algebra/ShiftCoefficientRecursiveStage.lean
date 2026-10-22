/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ShiftCoefficientSpace
public import LeanCanny.Computation.SingleCallController

/-! # A shifted coefficient with one resumable source request

The original coefficient is the sole recursive request. Native polynomial-space
postprocessing computes the binomial factor and modular arithmetic, so the
binomial computation needs no suspended controller or execution clock.
-/

@[expose] public section

namespace LeanCanny.Algebra.ShiftCoefficientBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM MatrixPower

attribute [local irreducible] BinaryNat.mulMod BinaryNat.powMod ArithmeticBits.negate
  BinomialResidue.value binomialInput coefficientInput computed finishFactor finishProduct

def finish (a : Access) (z : List Bool) : List Bool :=
  finishProduct (pair (pairFst z)
    (pair (BinomialResidue.value (binomialInput (pairFst z))) (finishFactor a z)))

theorem finish_space (a : Access) (hd : a.direction ∈ FP) : SpaceFunction (finish a) := by
  have B := BinomialResidue.evaluator.precompose (binomialInput ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP binomialInput_mem_FP)
  have C := SpaceFunction.ofFP (finishFactor a) (finishFactor_mem_FP a hd)
  have E := ((SpaceFunction.ofFP pairFst pairFst_mem_FP).pairOutputs (B.pairOutputs C)).postcompose
    finishProduct finishProduct_mem_FP
  exact E.congr (funext fun _ => by simp only [Function.comp_apply, finish])

theorem finish_correct (a : Access) (p : List Bool) :
    finish a (pair p (a.coefficient (coefficientInput p))) = computed a p := by
  simp only [finish, finishProduct, finishFactor, computed, ShiftCoefficientBits.finish, factor,
    pairFst_pair, pairSnd_pair]

def program (a : Access) (sourceTask : List Bool → List Bool) : SingleCall.Program where
  request := fun _ => true
  query := sourceTask ∘ coefficientInput
  immediate := fun _ => []
  finish := finish a

theorem certificates (a : Access) (hd : a.direction ∈ FP) (sourceTask : List Bool → List Bool)
    (hs : sourceTask ∈ FP) : (program a sourceTask).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) := by
  have hq := mem_FP_comp coefficientInput_mem_FP hs
  exact (program a sourceTask).certificates_of_space (constFn_mem_FP [true]) hq
    (.of_polyTime (FP.computable (constFn_mem_FP []))) (finish_space a hd).computable

theorem value_eq (a : Access) (sourceTask answer : List Bool → List Bool)
    (hs : ∀ p, answer (sourceTask p) = a.coefficient p) (p : List Bool) :
    (program a sourceTask).value answer p = computed a p := by
  simp only [SingleCall.Program.value, program, ite_true, Function.comp_apply, hs, finish_correct]

theorem output_when_halted (a : Access) (sourceTask answer : List Bool → List Bool)
    (hs : ∀ p, answer (sourceTask p) = a.coefficient p) (F : Family) (h : Represents a F)
    (p : List Bool) (t : ℕ)
    (hh : (program a sourceTask).controller.halted
      (((program a sourceTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = true) :
    (program a sourceTask).controller.output
      (((program a sourceTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = F.value p := by
  rw [(program a sourceTask).output_when_halted answer p t hh, value_eq a sourceTask answer hs p]
  exact computed_correct a p (F.polynomial (original p)) (F.direction (original p)) (h.direction _)
    (fun k => h.coefficient (pairFst p) k)

end LeanCanny.Algebra.ShiftCoefficientBits.RecursiveStage
