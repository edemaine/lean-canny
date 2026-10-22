/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialMoment
public import LeanCanny.Algebra.PolynomialMomentRecursiveStage

/-! # Berkowitz moments requesting only original matrix coefficients -/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.MomentStage
open LeanCanny.Encoding LeanCanny.Computation
open ModularAccess MatrixPower
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
attribute [local irreducible] PolynomialPower.Access.lower PolynomialPower.Access.coefficientInput
  MatrixMoment.EntryBits.entry MatrixPower.Controller.halted MatrixPower.Controller.needsEntry

def rowTask (sourceTask : List Bool → List Bool) : List Bool → List Bool := sourceTask ∘ rowInput a.dimension
def columnTask (sourceTask : List Bool → List Bool) : List Bool → List Bool := sourceTask ∘ columnInput a.dimension
def matrixTask (sourceTask : List Bool → List Bool) : List Bool → List Bool := sourceTask ∘ matrixInput a.dimension

noncomputable def initial : List Bool → List Bool := PolynomialMoment.RecursiveStage.initial a.momentAccess

noncomputable def controller (sourceTask : List Bool → List Bool) (zeroTask : List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) :=
  PolynomialMoment.RecursiveStage.controller a.momentAccess (rowTask a sourceTask)
    (columnTask a sourceTask) (matrixTask a sourceTask) zeroTask

theorem certificates (ha : a.ControlsPolyTime) (sourceTask : List Bool → List Bool)
    (hs : sourceTask ∈ FP) (zeroTask : List Bool) :
    (controller a sourceTask zeroTask).Certificates (encQ := encBits) (encS := encBits) := by
  have hr := mem_FP_comp (rowInput_mem_FP ha.dimension) hs
  have hc := mem_FP_comp (columnInput_mem_FP ha.dimension) hs
  have hm := mem_FP_comp (matrixInput_mem_FP ha.dimension) hs
  exact PolynomialMoment.RecursiveStage.certificates a.momentAccess (moment_controls a ha)
    (rowTask a sourceTask) (columnTask a sourceTask) (matrixTask a sourceTask) hr hc hm zeroTask

theorem halted_after (sourceTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hs : ∀ p, answer (sourceTask p) = a.entry p) (hz : answer zeroTask = []) (p : List Bool) :
    (controller a sourceTask zeroTask).halted
      (((controller a sourceTask zeroTask).reference answer)^[work
        ((trailingDimension F (pairFst p) + 2) * (Nat.fromBitsLE (pairSnd p) + 1))
        (momentExponent F (pairFst p) + 2).size (momentExponent F (pairFst p) + 2) + 1] (initial a p)) = true :=
  PolynomialMoment.RecursiveStage.halted_after a.momentAccess (rowTask a sourceTask) (columnTask a sourceTask)
    (matrixTask a sourceTask) answer zeroTask (fun q => hs (rowInput a.dimension q))
    (fun q => hs (columnInput a.dimension q)) (fun q => hs (matrixInput a.dimension q)) hz p

theorem output_when_halted (sourceTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hs : ∀ p, answer (sourceTask p) = a.entry p) (hz : answer zeroTask = []) (p : List Bool) (t : ℕ)
    (hh : (controller a sourceTask zeroTask).halted
      (((controller a sourceTask zeroTask).reference answer)^[t] (initial a p)) = true) :
    (controller a sourceTask zeroTask).output
      (((controller a sourceTask zeroTask).reference answer)^[t] (initial a p)) = (momentFamily F).value p :=
  PolynomialMoment.RecursiveStage.output_when_halted a.momentAccess (rowTask a sourceTask) (columnTask a sourceTask)
    (matrixTask a sourceTask) answer zeroTask (fun q => hs (rowInput a.dimension q))
    (fun q => hs (columnInput a.dimension q)) (fun q => hs (matrixInput a.dimension q)) hz p t hh

theorem state_length (sourceTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hs : ∀ p, answer (sourceTask p) = a.entry p) (hz : answer zeroTask = []) (p : List Bool) (t : ℕ) :
    (((controller a sourceTask zeroTask).reference answer)^[t] (initial a p)).length ≤
      2 * p.length + 2 + 64 *
        (((trailingDimension F (pairFst p) + 2) * (Nat.fromBitsLE (pairSnd p) + 1)).size +
          (momentExponent F (pairFst p) + 2).size + (F.modulus (pairFst (pairFst p))).size + 1) ^ 2 :=
  PolynomialMoment.RecursiveStage.state_length a.momentAccess (rowTask a sourceTask) (columnTask a sourceTask)
    (matrixTask a sourceTask) answer zeroTask (fun q => hs (rowInput a.dimension q))
    (fun q => hs (columnInput a.dimension q)) (fun q => hs (matrixInput a.dimension q)) hz p t

end LeanCanny.Algebra.BerkowitzPolynomial.MomentStage
