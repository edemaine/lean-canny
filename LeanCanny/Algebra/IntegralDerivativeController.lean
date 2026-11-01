/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDerivativeCorrect
public import LeanCanny.Computation.ControllerRequests

/-! # Recursive derivative coefficients with binary degree bounds

The spatial target is bumped at the original width, one original
coefficient is requested, and its reply is multiplied by the native
exponent factor. Out-of-bound spatial targets return zero locally.
The parameter-algebra adapter preserves the saved source and basis ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A W V D selected : List Bool → ℕ) (target modulus task : List Bool → List Bool)

noncomputable def program : SingleCall.Program where
  request c := decide (FixedWidthQuery.Bounded A V target (fun c => D c - 1) c)
  query c := task (query A W V selected target c)
  immediate _ := []
  finish := finish A V selected target modulus

theorem program_controls (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : BinaryFn D)
    (hs : UnaryFn selected) (ht : target ∈ FP) (hm : modulus ∈ FP) (hq : task ∈ FP) :
    (program A W V D selected target modulus task).Controls :=
  ⟨(FixedWidthQuery.bounded_binary_fppred hA hV (hD.sub (BinaryFn.const 1)) ht).flag_mem_FP,
    mem_FP_comp (f := query A W V selected target) (g := task) (query_mem_FP A W V selected target hA hW hV hs ht) hq,
    constFn_mem_FP [], finish_mem_FP A V selected target modulus hA hV hs ht hm⟩

theorem program_value (coefficient answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = coefficient q) (c : List Bool) :
    (program A W V D selected target modulus task).value answer c = value A W V D selected target modulus coefficient c := by
  simp only [SingleCall.Program.value, program, decide_eq_true_eq, he, value]

theorem program_requests_iff (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (program A W V D selected target modulus task).controller.Requests answer budget c child ↔
      FixedWidthQuery.Bounded A V target (fun c => D c - 1) c ∧ child = task (query A W V selected target c) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.FixedWidthDerivativeBits

namespace LeanCanny.Algebra.IntegralDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

noncomputable def program (S : Source) (task : List Bool → List Bool) : SingleCall.Program :=
  FixedWidthDerivativeBits.program (arity S) (width S) (width S) (degree S) (selected S) pairSnd (modulus S)
    (task ∘ coefficientQuery)

theorem program_controls (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S task).Controls := by
  have HM : BinaryFn (fun z => S.modulus (original z)) := a.modulus.comp original_FP
  exact FixedWidthDerivativeBits.program_controls _ _ _ _ _ _ _ _ (a.arity.comp original_FP)
    (a.sourceWidth.comp original_FP) (a.sourceWidth.comp original_FP) (a.degree.comp original_FP)
    (a.selected.comp original_FP) pairSnd_mem_FP HM.bits_mem_FP
    (mem_FP_comp coefficientQuery_FP ht)

theorem program_value (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = a.coefficient q) (c : List Bool) :
    (program S task).value answer c = value S a c := by
  unfold value
  exact FixedWidthDerivativeBits.program_value _ _ _ _ _ _ _ _
    (a.coefficient ∘ coefficientQuery) answer (fun q => he (coefficientQuery q)) c

theorem program_packet (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = a.coefficient q) (c : List Bool) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (program S task).value answer (pair (IntegralClearedCoefficientBits.context c r.val t.val) (BinaryNatCode.encode k)) =
      MatrixPower.residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((MvPolynomial.pderiv (S.selected c) (S.polynomial c)).coeff
          (RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) k)))
        r t : ℤ) : ZMod (S.modulus c)) :=
  (program_value S a task answer he _).trans (packet S a c k r t)

end LeanCanny.Algebra.IntegralDerivativeBits
