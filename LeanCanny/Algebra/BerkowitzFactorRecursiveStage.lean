/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialFactorSpace
public import LeanCanny.Computation.SingleCallController

/-! # Resumable polynomial Berkowitz factor coefficients

Constants return immediately. Diagonal and moment requests suspend once, then
apply modular negation. No computation certificate for either answer is used.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.FactorStage
open LeanCanny.Encoding LeanCanny.Computation
open ModularAccess
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
-- Compare named FP operations when composing certificates, without evaluating
-- the selector's binary division while checking function types.
attribute [local irreducible] mode diagonalInput oneCoefficient negative

def program (diagonalTask momentTask : List Bool → List Bool) : SingleCall.Program where
  request := fun p => mode a [false, true] p || mode a [true, true] p
  query := fun p => if mode a [false, true] p then diagonalTask (diagonalInput a p) else momentTask p
  immediate := fun p => if mode a [true] p then oneCoefficient a p else []
  finish := negative a

theorem controls (ha : a.ControlsPolyTime) (diagonalTask momentTask : List Bool → List Bool)
    (hd : diagonalTask ∈ FP) (hm : momentTask ∈ FP) : (program a diagonalTask momentTask).Controls := by
  have hdiag := flag_computable (mode_mem_FP a ha [false, true])
  have hmom := flag_computable (mode_mem_FP a ha [true, true])
  have hor : ComputableTidilyInPolyTime (fun b : Bool × Bool => b.1 || b.2)
      (encPair encBool encBool) encBool := ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 || b.2)
  have hreq := hor.comp (hdiag.prod hmom)
  have hdiagQuery := mem_FP_comp (diagonalInput_mem_FP a ha) hd
  have hq := hdiag.ite' hdiagQuery hm
  have hone := oneCoefficient_mem_FP a ha
  have hi := (flag_computable (mode_mem_FP a ha [true])).ite' hone (constFn_mem_FP [])
  have hflag : (fun p => [mode a [false, true] p || mode a [true, true] p]) ∈ FP := hreq.encoded
  exact ⟨hflag, hq, hi, negative_mem_FP a ha⟩

theorem value_eq (diagonalTask momentTask answer : List Bool → List Bool)
    (hd : ∀ p, answer (diagonalTask p) = a.entry p)
    (hm : ∀ p, answer (momentTask p) = (momentFamily F).value p) (p : List Bool) :
    (program a diagonalTask momentTask).value answer p = factorValue a p := by
  by_cases h2 : Berkowitz.QueryBits.selector a.dimension (pairFst p) = [false, true]
  · simp [SingleCall.Program.value, program, factorValue, mode, h2, hd]
  · by_cases h3 : Berkowitz.QueryBits.selector a.dimension (pairFst p) = [true, true]
    · simp [SingleCall.Program.value, program, factorValue, mode, h3, hm]
    · simp [SingleCall.Program.value, program, factorValue, mode, h2, h3]

theorem certificates (ha : a.ControlsPolyTime) (diagonalTask momentTask : List Bool → List Bool)
    (hd : diagonalTask ∈ FP) (hm : momentTask ∈ FP) :
    (program a diagonalTask momentTask).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) :=
  (program a diagonalTask momentTask).certificates (controls a ha diagonalTask momentTask hd hm)

theorem halted_after (diagonalTask momentTask answer : List Bool → List Bool) (p : List Bool) :
    (program a diagonalTask momentTask).controller.halted
      (((program a diagonalTask momentTask).controller.reference answer)^[1] (SingleCall.Program.initial p)) = true :=
  (program a diagonalTask momentTask).halted_after answer p

theorem output_when_halted (diagonalTask momentTask answer : List Bool → List Bool)
    (hd : ∀ p, answer (diagonalTask p) = a.entry p)
    (hm : ∀ p, answer (momentTask p) = (momentFamily F).value p) (p : List Bool) (t : ℕ)
    (hh : (program a diagonalTask momentTask).controller.halted
      (((program a diagonalTask momentTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = true) :
    (program a diagonalTask momentTask).controller.output
      (((program a diagonalTask momentTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) =
        factorValue a p :=
  ((program a diagonalTask momentTask).output_when_halted answer p t hh).trans
    (value_eq a diagonalTask momentTask answer hd hm p)

theorem state_length (diagonalTask momentTask answer : List Bool → List Bool) (p : List Bool) (t B : ℕ)
    (hd : mode a [false, true] p = true → (answer (diagonalTask (diagonalInput a p))).length ≤ B)
    (hm : mode a [true, true] p = true → (answer (momentTask p)).length ≤ B) :
    (SingleCall.encState (((program a diagonalTask momentTask).controller.reference answer)^[t]
      (SingleCall.Program.initial p))).length ≤ 2 * p.length + 4 + B := by
  apply (program a diagonalTask momentTask).state_length_of_bound answer p t B
  intro hr
  cases hdiag : mode a [false, true] p with
  | true =>
    simpa only [program, hdiag, ite_true] using hd hdiag
  | false =>
    have hmom : mode a [true, true] p = true := by
      simpa only [program, hdiag, Bool.false_or] using hr
    simpa only [program, hdiag, Bool.false_eq_true, ite_false] using hm hmom

end LeanCanny.Algebra.BerkowitzPolynomial.FactorStage
