/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.SpaceFunctionWordExistence
public import LeanCanny.Computation.SpaceDeciderOutput
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Polynomially balanced images of PSPACE languages

A bounded search for an original word transfers a space bound without requiring
a polynomial-time inverse. Candidates use the library's framed-word decoder;
padding after the first frame lets one fixed width represent every shorter word.
-/
@[expose] public section
namespace LeanCanny.Computation
open Turing.MultiTapeTM Encoding.Brackets

theorem bounded_image_mem_PSPACE {L : Language} {f : List Bool → List Bool}
    (hL : L ∈ PSPACE) (hf : f ∈ FP) {bound : List Bool → ℕ}
    (hb : UnaryFn bound) (hbalance : ∀ w ∈ L, w.length ≤ bound (f w)) :
    f '' L ∈ PSPACE := by
  classical
  let candidate := fun p : List Bool => unframe (pairSnd p)
  have hc : candidate ∈ FP := ComputableTidilyInPolyTime.unframe.comp pairSnd_mem_FP
  have htest := ((SpaceDecider.ofPSPACE hL).indicator.precompose candidate hc).andFlags
    (SpaceFunction.ofFP _ (stringEq_fppred (mem_FP_comp hc hf) pairFst_mem_FP).flag_mem_FP)
  have hw := ((UnaryFn.const 2).mul hb).add (UnaryFn.const 1)
  have he := htest.exists_words hw
  have HD := he.decider (fun w => decide (w = [true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
    (L := f '' L) (fun x => by
      simp only [List.cons.injEq, and_true, decide_eq_true_eq, Set.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hl := hbalance w hw
        let padding := List.replicate (2 * bound (f w) - 2 * w.length) false
        refine ⟨frame w ++ padding, ?_, ?_⟩
        · simp only [List.length_append, length_frame, padding, List.length_replicate]
          omega
        · simp [candidate, unframe_frame_append, hw]
      · rintro ⟨w, _, h⟩
        simp only [Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq,
          candidate, pairFst_pair, pairSnd_pair] at h
        exact ⟨unframe w, h.1, h.2⟩)
  exact HD.mem_PSPACE

end LeanCanny.Computation
