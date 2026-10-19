/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NNFFP

/-!
# ETR in negation normal form is ∃ℝ-complete

The total normalizer fixes exactly the canonical NNF encodings. Comparing its
output with its input therefore gives a polynomial-time syntax predicate. A
guarded identity reduces the NNF satisfiability language back to ETR.
-/

@[expose] public section

namespace LeanCanny.ETR.NNF
open Complexity
open LeanCanny.Encoding.Brackets

theorem normalize_shape (bits : List Bool) :
    ∃ p : Formula, normalize bits = p.encode ∧ p.IsNNF = true := by
  by_cases hr : Grammar.recognizeFormula bits = true
  · obtain ⟨p, rfl⟩ := (Grammar.recognizeFormula_true_iff bits).mp hr
    exact ⟨p.nnf true, normalize_encode p, p.nnf_isNNF true⟩
  · exact ⟨.falsum, by rw [normalize, ite_eq_right hr]; rfl, rfl⟩

theorem normalize_eq_self_iff (bits : List Bool) :
    normalize bits = bits ↔ ∃ p : Formula, bits = p.encode ∧ p.IsNNF = true := by
  constructor
  · intro h
    obtain ⟨p, hp, hn⟩ := normalize_shape bits
    exact ⟨p, h.symm.trans hp, hn⟩
  · rintro ⟨p, rfl, hp⟩
    rw [normalize_encode, p.nnf_eq_self_of_isNNF hp]

theorem normalize_idempotent (bits : List Bool) : normalize (normalize bits) = normalize bits := by
  obtain ⟨p, hp, hn⟩ := normalize_shape bits
  rw [hp, normalize_encode, p.nnf_eq_self_of_isNNF hn]

def IsNNFEncoding (bits : List Bool) : Prop := normalize bits = bits

instance (bits : List Bool) : Decidable (IsNNFEncoding bits) := by
  unfold IsNNFEncoding
  infer_instance

theorem isNNFEncoding_fppred : FPPred IsNNFEncoding :=
  stringEq_fppred normalize_mem_FP id_mem_FP

theorem isNNFEncoding_encode_iff (p : Formula) : IsNNFEncoding p.encode ↔ p.IsNNF = true := by
  simp [IsNNFEncoding, normalize_eq_self_iff, Formula.encode_injective.eq_iff]

/-- Retain exactly NNF inputs and reject all other strings with falsum. -/
def toETR (bits : List Bool) : List Bool :=
  if IsNNFEncoding bits then bits else Formula.falsum.encode

theorem toETR_mem_FP : toETR ∈ FP :=
  isNNFEncoding_fppred.ite_mem_FP id_mem_FP (constFn_mem_FP Formula.falsum.encode)

theorem toETR_correct (bits : List Bool) : bits ∈ language ↔ toETR bits ∈ ETR.language := by
  by_cases hn : IsNNFEncoding bits
  · obtain ⟨p, rfl, hp⟩ := (normalize_eq_self_iff bits).mp hn
    rw [toETR, ite_eq_left hn, encode_mem_language, ETR.encode_mem_language]
    simp only [hp, true_and]
  · have hnot : bits ∉ language := by
      rintro ⟨p, rfl, hp, _⟩
      exact hn ((isNNFEncoding_encode_iff p).mpr hp)
    simp [toETR, hn, hnot]

theorem reduces_to_etr : language ≤ₚ ETR.language :=
  ⟨toETR, toETR_mem_FP, toETR_correct⟩

theorem mem_existsReal : language ∈ LeanCanny.ExistsReal := reduces_to_etr

theorem existsRealComplete : LeanCanny.ExistsRealComplete language :=
  ⟨mem_existsReal, (LeanCanny.existsRealHard_iff language).mpr etr_reduces_to_nnf⟩

end LeanCanny.ETR.NNF
