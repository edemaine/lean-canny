/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Tactic.PolyTime

public import LeanCanny.ETR.Complexity
public import LeanCanny.ETR.EncodingFP
public import LeanCanny.ETR.SingleEquation

/-!
# The single-equation language belongs to ∃ℝ

The reduction checks the outer constructor tag and forwards equation inputs to
ETR, replacing other inputs with a fixed no-instance. Its machine-level time
certificate uses the verified bracket splitter. It does not assume a polynomial-
time implementation of the general normalizer.
-/

@[expose] public section

namespace LeanCanny.ETR.SingleEquation

open LeanCanny.Encoding.Brackets

def HasEquationTag (bits : List Bool) : Prop := firstChild bits = (Codec.unary 1).toBits

instance hasEquationTagDecidable (bits : List Bool) : Decidable (HasEquationTag bits) := by
  unfold HasEquationTag
  infer_instance

theorem hasEquationTag_fppred : FPPred HasEquationTag :=
  stringEq_fppred firstChild_mem_FP (constFn_mem_FP (Codec.unary 1).toBits)

theorem hasEquationTag_encode_iff (p : Formula) :
    HasEquationTag p.encode ↔ ∃ t : Term, p = .eqZero t := by
  rw [HasEquationTag, p.firstChild_encode, Codec.unary_toBits_injective.eq_iff]
  exact p.constructorTag_eq_one_iff

/-- Forward equation-tagged strings and replace every other input with falsum. -/
def toETR (bits : List Bool) : List Bool :=
  if HasEquationTag bits then bits else Formula.falsum.encode

theorem toETR_mem_FP : toETR ∈ FP :=
  hasEquationTag_fppred.ite_mem_FP id_mem_FP (constFn_mem_FP Formula.falsum.encode)

/-- Correct on all binary strings, including malformed equation-tagged inputs. -/
theorem toETR_mem_language_iff (bits : List Bool) :
    toETR bits ∈ ETR.language ↔ bits ∈ language := by
  by_cases ht : HasEquationTag bits
  · rw [toETR, ite_eq_left ht]
    constructor
    · intro h
      obtain ⟨p, hp, hs⟩ := (ETR.mem_language_iff bits).mp h
      subst bits
      obtain ⟨t, rfl⟩ := (hasEquationTag_encode_iff p).mp ht
      exact ⟨t, rfl, hs⟩
    · exact fun h => language_subset_etr h
  · rw [toETR, ite_eq_right ht]
    have hn : bits ∉ language := by
      rintro ⟨t, rfl, _⟩
      exact ht ((hasEquationTag_encode_iff _).mpr ⟨t, rfl⟩)
    simp [hn]

theorem reduces_to_etr : PolyTimeReduces language ETR.language :=
  ⟨toETR, FP.computable toETR_mem_FP, fun bits => (toETR_mem_language_iff bits).symm⟩

theorem mem_existsReal : language ∈ LeanCanny.ExistsReal := reduces_to_etr

end LeanCanny.ETR.SingleEquation
