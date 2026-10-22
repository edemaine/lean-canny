/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialSpace
public import LeanCanny.Algebra.PolynomialPowerRecursiveStage

/-! # A resumable polynomial determinant coefficient stage

The outer power delegates factor coefficients to tasks, including the lower
triangular guard of the coefficient matrix. The final FP parity correction
returns the actual determinant coefficient. Factor answer computability is
not assumed by the controller certificate or its correctness proofs.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.DeterminantStage
open LeanCanny.Encoding LeanCanny.Computation
open ModularAccess MatrixPower Polynomial
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
attribute [local irreducible] PolynomialPower.Access.lower PolynomialPower.Access.coefficientInput
  MatrixPower.Controller.halted MatrixPower.Controller.needsEntry factorValue finish

noncomputable def entryTask (factorTask : List Bool → List Bool) (zeroTask : List Bool) : List Bool → List Bool :=
  PolynomialPower.RecursiveStage.liftedTask a.powerAccess (factorTask ∘ splitDegree) zeroTask

noncomputable def initial : List Bool → List Bool := PolynomialPower.RecursiveStage.initial a.powerAccess

def output (s : List Bool) : List Bool :=
  finish a (pair (pairFst s) (MatrixPower.ModularAccess.valueBits s))

noncomputable def controller (factorTask : List Bool → List Bool) (zeroTask : List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) :=
  { PolynomialPower.RecursiveStage.controller a.powerAccess (entryTask a factorTask zeroTask) with output := output a }

theorem entryTask_FP (ha : a.ControlsPolyTime) (factorTask : List Bool → List Bool)
    (hf : factorTask ∈ FP) (zeroTask : List Bool) : entryTask a factorTask zeroTask ∈ FP :=
  PolynomialPower.RecursiveStage.liftedTask_FP a.powerAccess (power_controls a ha) (factorTask ∘ splitDegree)
    (mem_FP_comp splitDegree_mem_FP hf) zeroTask

theorem entryTask_eq (factorTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hf : ∀ p, answer (factorTask p) = factorValue a p) (hz : answer zeroTask = []) (p : List Bool) :
    answer (entryTask a factorTask zeroTask p) = a.powerAccess.power.entry p := by
  exact PolynomialPower.RecursiveStage.liftedTask_eq a.powerAccess (factorTask ∘ splitDegree) answer zeroTask
    (fun q => hf (splitDegree q)) hz p

theorem output_FP (ha : a.ControlsPolyTime) : output a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair pairFst_mem_FP MatrixPower.ModularAccess.valueBits_mem_FP) (finish_mem_FP a ha)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem certificates (ha : a.ControlsPolyTime) (factorTask : List Bool → List Bool)
    (hf : factorTask ∈ FP) (zeroTask : List Bool) :
    (controller a factorTask zeroTask).Certificates (encQ := encBits) (encS := encBits) := by
  have h := PolynomialPower.RecursiveStage.certificates a.powerAccess (power_controls a ha)
    (entryTask a factorTask zeroTask) (entryTask_FP a ha factorTask hf zeroTask)
  exact ⟨h.initial, h.halted, .of_polyTime (FP.computable (output_FP a ha)), h.needs, h.query, h.advance, h.resume⟩

theorem reference_eq (factorTask answer : List Bool → List Bool) (zeroTask : List Bool) :
    (controller a factorTask zeroTask).reference answer =
      (PolynomialPower.RecursiveStage.controller a.powerAccess (entryTask a factorTask zeroTask)).reference answer := rfl

theorem halted_after (factorTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hf : ∀ p, answer (factorTask p) = factorValue a p) (hz : answer zeroTask = []) (c : List Bool) :
    (controller a factorTask zeroTask).halted
      (((controller a factorTask zeroTask).reference answer)^[MatrixPower.work
        ((F.dimension c + 1) * (F.dimension c + 1) * (F.degree c + 1)) (F.dimension c).size (F.dimension c) + 1]
        (initial a c)) = true :=
  PolynomialPower.RecursiveStage.halted_after a.powerAccess (entryTask a factorTask zeroTask) answer
    (entryTask_eq a factorTask answer zeroTask hf hz) c

theorem output_when_halted (factorTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hf : ∀ p, answer (factorTask p) = factorValue a p) (hz : answer zeroTask = []) (c : List Bool) (t : ℕ)
    (hh : (controller a factorTask zeroTask).halted
      (((controller a factorTask zeroTask).reference answer)^[t] (initial a c)) = true) :
    (controller a factorTask zeroTask).output
      (((controller a factorTask zeroTask).reference answer)^[t] (initial a c)) = F.value c := by
  have hentry := entryTask_eq a factorTask answer zeroTask hf hz
  have hv := PolynomialPower.RecursiveStage.output_when_halted a.powerAccess (entryTask a factorTask zeroTask) answer hentry c t hh
  have hc := PolynomialPower.RecursiveStage.context_iterate a.powerAccess (entryTask a factorTask zeroTask) answer c t
  change finish a (pair
    (pairFst (((PolynomialPower.RecursiveStage.controller a.powerAccess (entryTask a factorTask zeroTask)).reference answer)^[t]
      (PolynomialPower.RecursiveStage.initial a.powerAccess c)))
    ((PolynomialPower.RecursiveStage.controller a.powerAccess (entryTask a factorTask zeroTask)).output
      (((PolynomialPower.RecursiveStage.controller a.powerAccess (entryTask a factorTask zeroTask)).reference answer)^[t]
        (PolynomialPower.RecursiveStage.initial a.powerAccess c)))) = _
  rw [hc, hv]
  change finish a (pair c (residueBits
    (((Berkowitz.powerMatrix (F.matrix c) ^ F.dimension c) (Berkowitz.powerQuery (F.dimension c) 0).row
      (Berkowitz.powerQuery (F.dimension c) 0).col).coeff (F.degree c)))) = _
  rw [finish_pair]
  have hdet := Berkowitz.det_eq_powerMatrix (F.matrix c)
  have hs : (-1 : (ZMod (F.modulus c))[X]) ^ F.dimension c = C ((-1 : ZMod (F.modulus c)) ^ F.dimension c) := by simp
  simp only [ModularFamily.value, hdet, hs, Polynomial.coeff_C_mul]

theorem state_length (factorTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (hf : ∀ p, answer (factorTask p) = factorValue a p) (hz : answer zeroTask = []) (c : List Bool) (t : ℕ) :
    (((controller a factorTask zeroTask).reference answer)^[t] (initial a c)).length ≤
      2 * c.length + 2 + 64 *
        (((F.dimension c + 1) * (F.dimension c + 1) * (F.degree c + 1)).size +
          (F.dimension c).size + (F.modulus c).size + 1) ^ 2 :=
  PolynomialPower.RecursiveStage.state_length a.powerAccess (entryTask a factorTask zeroTask) answer
    (entryTask_eq a factorTask answer zeroTask hf hz) c t

end LeanCanny.Algebra.BerkowitzPolynomial.DeterminantStage
