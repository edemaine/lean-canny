/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
/-! # Total actual critical coefficients request one relative coefficient

The valid-birth guard returns zero outside the original script. One
uniform source, rather than a family chosen separately at each valid
word, supplies the native relative characteristic and common scalar.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScaledCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem finishAt_value (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (c : List Bool) :
    finishAt S scalar exponent c (S.value c) = value S scalar exponent c := by
  unfold finishAt
  rw [powerPost_packet, IntegralBerkowitzBlockBits.Source.value, multiplyPost_packet]
  exact (value_eq S scalar exponent c).symm
end LeanCanny.Algebra.IntegralScaledCharacteristicBits

namespace LeanCanny.Algebra.IntegralCriticalFlatActualCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] relative relativeAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.source IntegralScaledCharacteristicBits.value
  IntegralBerkowitzBlockBits.Source.value IntegralClearedCriticalBits.Source.value

private theorem scalar_FP_modulus_eq (a : List Bool → ℤ) (m n : List Bool → ℕ)
    (hm : ∀ c, m c = n c) (H : (fun c => residueBits (a c : ZMod (m c))) ∈ FP) :
    (fun c => residueBits (a c : ZMod (n c))) ∈ FP :=
  mem_FP_of_eq H (fun c => congrArg (fun modulus : ℕ => residueBits (a c : ZMod modulus)) (hm c))

noncomputable def program (F : Scripts) : SingleCall.Program where
  request c := decide (IntegralCriticalTotalCompanionBits.valid F c)
  query := IntegralCriticalFlatEulerBits.next F.toParameters .relativePower
  immediate _ := []
  finish := IntegralScaledCharacteristicBits.finish (characteristic F) (relative F).leading
    (fun c => (relative F).layout.bound c + 1)

theorem controls (F : Scripts) (h : Controls F) : (program F).Controls where
  request := (IntegralCriticalTotalCompanionBits.valid_FP F h.task).flag_mem_FP
  query := IntegralCriticalFlatEulerBits.next_FP F.toParameters h.task.toAccess .relativePower
  immediate := constFn_mem_FP []
  finish := IntegralScaledCharacteristicBits.finish_FP (characteristic F) (characteristicAccess F h)
    (relative F).leading (fun c => (relative F).layout.bound c + 1)
    ((relativeAccess F h).bound.add (BinaryFn.const 1))
    (scalar_FP_modulus_eq (relative F).leading (IntegralCriticalHistoryTask.modulus F.toParameters)
      (characteristic F).modulus (fun c => (characteristic_modulus F c).symm) (scalar_FP F h))

theorem value (F : Scripts) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralCriticalTotalCompanionBits.valid F c →
      answer (IntegralCriticalFlatEulerBits.next F.toParameters .relativePower c) = (characteristic F).value c) :
    (program F).value answer c = IntegralCriticalTotalCreatingBits.coefficientValue F c := by
  by_cases hv : IntegralCriticalTotalCompanionBits.valid F c
  · simp only [SingleCall.Program.value, program, hv, decide_true, ite_true,
      IntegralScaledCharacteristicBits.finish, pairFst_pair, pairSnd_pair,
      IntegralCriticalTotalCreatingBits.coefficientValue]
    rw [he hv, IntegralScaledCharacteristicBits.finishAt_value]
    exact congrFun (polynomial_value F) c
  · simp only [SingleCall.Program.value, program, hv, decide_false, Bool.false_eq_true, ite_false,
      IntegralCriticalTotalCreatingBits.coefficientValue]

theorem actual_value (F : Scripts) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralCriticalTotalCompanionBits.valid F c →
      answer (IntegralCriticalFlatEulerBits.next F.toParameters .relativePower c) = (characteristic F).value c) :
    (program F).value answer c = IntegralCriticalTotalCompanionBits.coefficientValue F c :=
  (value F answer c he).trans (IntegralCriticalTotalCreatingBits.coefficientValue_eq F c)

theorem requests_iff (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (program F).controller.Requests answer budget c child ↔ IntegralCriticalTotalCompanionBits.valid F c ∧
      child = IntegralCriticalFlatEulerBits.next F.toParameters .relativePower c := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_rank (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : isPhase .criticalCoefficient c) (hc : (program F).controller.Requests answer budget c child) :
    rank F.toParameters child < rank F.toParameters c := by
  obtain ⟨_, rfl⟩ := (requests_iff F answer budget c child).mp hc
  apply IntegralCriticalFlatEulerBits.next_lower_rank
  change phase c = 25 at hp
  change 24 < phase c
  omega

theorem requests_tasks (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (r c child : List Bool)
    (ht : Tasks F.toParameters r c) (hc : (program F).controller.Requests answer budget c child) : Tasks F.toParameters r child := by
  obtain ⟨_, rfl⟩ := (requests_iff F answer budget c child).mp hc
  exact IntegralCriticalFlatEulerBits.next_tasks F.toParameters .relativePower r c ht

end LeanCanny.Algebra.IntegralCriticalFlatActualCoefficientBits
