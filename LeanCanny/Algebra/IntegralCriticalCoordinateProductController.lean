/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalCoordinateProductSpace
public import LeanCanny.Computation.ControllerRequests

/-! # Recursive coordinate-times-gradient coefficients

A zero selected spatial exponent returns zero locally. Otherwise the
selected exponent is decremented at the same width and one gradient
coefficient is requested. The original source and derivative rank survive.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCoordinateMulBits
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

variable (A W selected : List Bool → ℕ) (target task : List Bool → List Bool)

noncomputable def program : SingleCall.Program where
  request c := decide (positive A W selected target c)
  query c := task (query A W selected target c)
  immediate _ := []
  finish := pairSnd

theorem program_controls (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected)
    (ht : target ∈ FP) (hq : task ∈ FP) : (program A W selected target task).Controls :=
  ⟨(positive_fppred A W selected target hA hW hs ht).flag_mem_FP,
    mem_FP_comp (f := query A W selected target) (g := task) (query_FP A W selected target hA hW hs ht) hq,
    constFn_mem_FP [], pairSnd_mem_FP⟩

theorem program_value (coefficient answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = coefficient q) (c : List Bool) :
    (program A W selected target task).value answer c = value A W selected target coefficient c := by
  by_cases h : positive A W selected target c <;>
    simp only [SingleCall.Program.value, program, h, decide_true, decide_false, Bool.false_eq_true,
      ite_true, ite_false, pairSnd_pair, value, he]

theorem program_requests_iff (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (program A W selected target task).controller.Requests answer budget c child ↔
      positive A W selected target c ∧ child = task (query A W selected target c) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.FixedWidthCoordinateMulBits

namespace LeanCanny.Algebra.IntegralCriticalCoordinateProductBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalGradientBits
set_option backward.isDefEq.respectTransparency false

noncomputable def program (S : Source) (task : List Bool → List Bool) : SingleCall.Program :=
  FixedWidthCoordinateMulBits.program (arity S) (width S) selected targetWord (task ∘ gradientQuery)

theorem program_controls (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S task).Controls :=
  FixedWidthCoordinateMulBits.program_controls _ _ _ _ _ (a.free.comp pairFst_mem_FP)
    (a.targetWidth.comp pairFst_mem_FP) (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (mem_FP_comp gradientQuery_FP ht)

attribute [local irreducible] value IntegralClearedCoefficientBits.Source.value

theorem program_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = (family S).value q) (c : List Bool) :
    (program S task).value answer c = value S c := by
  unfold value
  exact FixedWidthCoordinateMulBits.program_value (arity S) (width S) selected targetWord (task ∘ gradientQuery)
    ((family S).value ∘ gradientQuery) answer (fun q => he (gradientQuery q)) c

end LeanCanny.Algebra.IntegralCriticalCoordinateProductBits
