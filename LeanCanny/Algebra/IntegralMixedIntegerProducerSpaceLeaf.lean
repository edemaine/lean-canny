/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSpace
/-! # Native integer leaves retain charged local-space certificates -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical

noncomputable def leaf (P : Parameters) (a : Access P) (p : Phase)
    (f : List Bool → List Bool) (E : SpaceFunction f) : Machine :=
  ofSingleCall (IntegralMixedIntegerProducerBits.leafProgram f)
    ((IntegralMixedIntegerProducerBits.leafProgram f).certificates_of_space (constFn_mem_FP [false]) id_mem_FP
      E.computable (SpaceFunction.ofFP _ id_mem_FP).computable)
    (IntegralMixedIntegerProducerBits.selected P p) (IntegralMixedIntegerProducerBits.selected_FP P a p)
    f (fun _ => 0) (UnaryFn.const 0)

theorem leaf_correct (P : Parameters) (a : Access P) (p : Phase)
    (f : List Bool → List Bool) (E : SpaceFunction f) (answer : List Bool → List Bool) :
    Correct (leaf P a p f E) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _
    rfl
  · intro q _ hr
    cases hr
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((IntegralMixedIntegerProducerBits.leafProgram f).requests_iff answer budget q c).mp hc
    cases hr

end LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits
