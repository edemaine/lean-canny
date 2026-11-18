/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.DerivedSyntax
public import LeanCanny.CountingHierarchy.FlatSentenceEncoding

/-! # Counting bounds for library-derived syntax encodings

Strict image recognition and a uniform polynomial-time compiler preserve the
existing counting levels, including rejection of malformed inputs.
-/

@[expose] public section
namespace LeanCanny.CountingHierarchy.DerivedSentenceEncoding
open Turing.MultiTapeTM Encoding Encoding.DerivedSyntax ETR
open Cslib.Complexity

abbrev code := formulaEncoding

def compile (w : List Bool) : List Bool :=
  if valid formulaDecoder w then FlatSentenceEncoding.compile (toFlat w) else Formula.falsum.encode

theorem compile_FP : compile ∈ FP :=
  (FPPred.of_flag (valid_polyTime formulaDecoder).tidy.encoded).ite_mem_FP
    (mem_FP_comp toFlat_FP FlatSentenceEncoding.compile_FP) (constFn_mem_FP _)

@[simp] theorem compile_code (p : Formula) : compile (code p) = p.encode := by
  have hv := (valid_iff formulaDecoder _).mpr ⟨p, rfl⟩
  simp only [compile, hv, ↓reduceIte, toFlat_encoded]
  exact FlatSentenceEncoding.compile_code p

theorem compile_correct (T : Formula → Prop) (hf : ¬T .falsum) (w : List Bool) :
    (∃ p, w = code p ∧ T p) ↔ ∃ p, compile w = p.encode ∧ T p := by
  constructor
  · rintro ⟨p, rfl, hp⟩
    exact ⟨p, compile_code p, hp⟩
  · rintro ⟨p, hp, ht⟩
    by_cases hv : valid formulaDecoder w = true
    · obtain ⟨q, rfl⟩ := (valid_iff formulaDecoder w).mp hv
      rw [compile_code] at hp
      have hqp := Formula.encode_injective hp
      exact ⟨q, rfl, hqp.symm ▸ ht⟩
    · simp only [compile, hv, Bool.false_eq_true, ↓reduceIte] at hp
      have he := Formula.encode_injective hp
      exact False.elim (hf (he.symm ▸ ht))

def etrLanguage : Set (List Bool) := {w | ∃ p, w = code p ∧ p.Satisfiable}

theorem etr_mem : etrLanguage ∈ CountingLevel 26 encBits := by
  have hred : PolyTimeReduces etrLanguage ETR.language := by
    refine ⟨compile, compile_FP.computableInPolyTime, ?_⟩
    intro w
    rw [ETR.mem_language_iff]
    exact compile_correct Formula.Satisfiable Formula.not_satisfiable_falsum w
  exact hred.mem_CountingLevel etr_mem_CountingLevel

def twoBlockLanguage : Set (List Bool) :=
  {w | ∃ r : ℕ, ∃ p : Formula, w = ExistsForall.encSentence (r, code p) ∧
    ExistsForall.SentenceHolds r p}

noncomputable def compileSentence (w : List Bool) : List Bool :=
  if valid spaceDecoder w then
    ExistsForall.encSentence (ExistsForall.parameterCount w, compile (ExistsForall.matrixBits w))
  else ExistsForall.encSentence (0, Formula.falsum.encode)

theorem compileSentence_FP : compileSentence ∈ FP := by
  have hbody := mem_FP_comp ExistsForall.matrixBits_mem_FP compile_FP
  have hp := (ExistsForall.parameterCount_unary.prod hbody).encoded
  exact (FPPred.of_flag (valid_polyTime spaceDecoder).tidy.encoded).ite_mem_FP hp (constFn_mem_FP _)

@[simp] theorem compileSentence_code (r : ℕ) (p : Formula) :
    compileSentence (ExistsForall.encSentence (r, code p)) =
      ExistsForall.encSentence (r, p.encode) := by
  have hv : valid spaceDecoder (ExistsForall.encSentence (r, code p)) = true :=
    (valid_iff spaceDecoder _).mpr ⟨(r, p), rfl⟩
  simp only [compileSentence, hv, ↓reduceIte, ExistsForall.parameterCount_encoded,
    ExistsForall.matrixBits_encoded, compile_code]

theorem compileSentence_correct (w : List Bool) :
    w ∈ twoBlockLanguage ↔ compileSentence w ∈ ExistsForall.language := by
  constructor
  · rintro ⟨r, p, rfl, hp⟩
    rwa [compileSentence_code, ExistsForall.encode_mem_language]
  · intro hw
    by_cases hv : valid spaceDecoder w = true
    · obtain ⟨⟨r, p⟩, he⟩ := (valid_iff spaceDecoder w).mp hv
      have he' : ExistsForall.encSentence (r, code p) = w := he
      rw [← he', compileSentence_code, ExistsForall.encode_mem_language] at hw
      exact ⟨r, p, he'.symm, hw⟩
    · simp only [compileSentence, hv, Bool.false_eq_true, ↓reduceIte,
        ExistsForall.encode_mem_language] at hw
      exact False.elim (ExistsForall.not_sentence_falsum 0 hw)

theorem twoBlock_mem : twoBlockLanguage ∈ CountingLevel 60 encBits :=
  (show PolyTimeReduces twoBlockLanguage ExistsForall.language from
    ⟨compileSentence, compileSentence_FP.computableInPolyTime, compileSentence_correct⟩).mem_CountingLevel
      ExistsForall.mem_CountingLevel

end LeanCanny.CountingHierarchy.DerivedSentenceEncoding
