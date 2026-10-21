/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationList
public import LeanCanny.ETR.SingleEquationComplexity

/-!
# A polynomial-time reduction from equation systems to one equation

The reduction validates the encoded term list and then writes its sum of squares.
Malformed inputs map to `1 = 0`. This certifies the final normalization stage;
the earlier compilation of arbitrary Boolean formulas to systems remains separate.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationList


def language : Language := {bits | ∃ ts : List Term,
  bits = SumSquares.listBits ts ∧ ∃ env : ℕ → ℝ, ∀ t ∈ ts, t.eval env = 0}

def toSingleEquation (bits : List Bool) : List Bool :=
  if recognize bits = true then Codec.taggedOne 1 (SumSquares.collapse bits)
  else (Formula.eqZero (.const 1)).encode

theorem toSingleEquation_mem_FP : toSingleEquation ∈ FP :=
  (FPPred.of_flag recognize_mem_FP).ite_mem_FP
    (Codec.taggedOne_mem_FP 1 SumSquares.collapse_mem_FP)
    (constFn_mem_FP (Formula.eqZero (.const 1)).encode)

theorem toSingleEquation_listBits (ts : List Term) :
    toSingleEquation (SumSquares.listBits ts) =
      (Formula.eqZero (SumSquares.accumulate ts (.const 0))).encode := by
  rw [toSingleEquation, ite_eq_left ((recognize_true_iff _).mpr ⟨ts, rfl⟩),
    SumSquares.collapse_listBits, ← Formula.eqZero_encode]

/-- Correct on every binary string; the source uses one shared existential assignment. -/
theorem toSingleEquation_correct (bits : List Bool) :
    bits ∈ language ↔ toSingleEquation bits ∈ SingleEquation.language := by
  constructor
  · rintro ⟨ts, rfl, env, hterms⟩
    rw [toSingleEquation_listBits, SingleEquation.encode_mem_language]
    exact ⟨env, (SumSquares.accumulate_zero_iff ts env).mpr hterms⟩
  · intro h
    by_cases hr : recognize bits = true
    · obtain ⟨ts, rfl⟩ := (recognize_true_iff bits).mp hr
      rw [toSingleEquation_listBits, SingleEquation.encode_mem_language] at h
      obtain ⟨env, heq⟩ := h
      exact ⟨ts, rfl, env, (SumSquares.accumulate_zero_iff ts env).mp heq⟩
    · rw [toSingleEquation, ite_eq_right hr, SingleEquation.encode_mem_language] at h
      exact False.elim (Formula.not_satisfiable_eqZero_one h)

theorem reduces_to_singleEquation : PolyTimeReduces language SingleEquation.language :=
  ⟨toSingleEquation, FP.computable toSingleEquation_mem_FP, toSingleEquation_correct⟩

theorem reduces_to_etr : PolyTimeReduces language ETR.language :=
  reduces_to_singleEquation.trans SingleEquation.reduces_to_etr

theorem mem_existsReal : language ∈ LeanCanny.ExistsReal := reduces_to_etr

end LeanCanny.ETR.EquationList
