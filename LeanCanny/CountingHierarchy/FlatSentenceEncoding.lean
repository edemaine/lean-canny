/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatSyntaxInverse
public import LeanCanny.CountingHierarchy.ExistentialUpperBound
public import LeanCanny.CountingHierarchy.ExistsForallUpperBound

/-! # Counting bounds under the shared abstract's flat input convention -/

@[expose] public section
namespace LeanCanny.CountingHierarchy.FlatSentenceEncoding

open Turing.MultiTapeTM LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.ETR
open Cslib.Complexity

abbrev code (p : Formula) := FlatSyntax.encoding (FlatSyntax.formulaTokens p)

def roundTrip (w : List Bool) : Prop := FlatSyntax.translate (FlatSyntaxInverse.parse w) = w

instance (w : List Bool) : Decidable (roundTrip w) := inferInstanceAs (Decidable (_ = _))

def compile (w : List Bool) : List Bool :=
  if roundTrip w then FlatSyntaxInverse.parse w else Formula.falsum.encode

theorem roundTrip_FP : FPPred roundTrip :=
  stringEq_fppred (mem_FP_comp (f := FlatSyntaxInverse.parse) (g := FlatSyntax.translate) FlatSyntaxInverse.parse_FP FlatSyntax.translate_FP) id_mem_FP

theorem compile_FP : compile ∈ FP :=
  roundTrip_FP.ite_mem_FP FlatSyntaxInverse.parse_FP (constFn_mem_FP _)

theorem compile_code (p : Formula) : compile (code p) = p.encode := by
  have hp : roundTrip (code p) := by
    rw [roundTrip, FlatSyntaxInverse.parse_formula, FlatSyntax.translate_formula]
  rw [compile, ite_eq_left hp, FlatSyntaxInverse.parse_formula]

/-- The compiler preserves any semantic property that rejects falsum. -/
theorem compile_correct (T : Formula → Prop) (hf : ¬T .falsum) (w : List Bool) :
    (∃ p, w = code p ∧ T p) ↔ ∃ p, compile w = p.encode ∧ T p := by
  constructor
  · rintro ⟨p, rfl, hp⟩
    exact ⟨p, compile_code p, hp⟩
  · rintro ⟨p, hp, ht⟩
    by_cases hr : roundTrip w
    · rw [compile, ite_eq_left hr] at hp
      refine ⟨p, ?_, ht⟩
      rw [roundTrip, hp, FlatSyntax.translate_formula] at hr
      exact hr.symm
    · rw [compile, ite_eq_right hr] at hp
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
  {w | ∃ r : ℕ, ∃ p : Formula, w = ExistsForall.encSentence (r, code p) ∧ ExistsForall.SentenceHolds r p}

noncomputable def compileSentence (w : List Bool) : List Bool :=
  if ExistsForall.frameFlag w then
    ExistsForall.encSentence (ExistsForall.parameterCount w, compile (ExistsForall.matrixBits w))
  else ExistsForall.encSentence (0, Formula.falsum.encode)

theorem compileSentence_FP : compileSentence ∈ FP := by
  have hbody := mem_FP_comp ExistsForall.matrixBits_mem_FP compile_FP
  have hp := (ExistsForall.parameterCount_unary.prod hbody).encoded
  exact (FPPred.of_flag ExistsForall.frameFlag_polyTime.tidy.encoded).ite_mem_FP hp (constFn_mem_FP _)

theorem twoBlock_normalized (w : List Bool) : w ∈ twoBlockLanguage ↔
    ExistsForall.FrameCanonical w ∧ ∃ p, ExistsForall.matrixBits w = code p ∧
      ExistsForall.SentenceHolds (ExistsForall.parameterCount w) p := by
  constructor
  · rintro ⟨r, p, rfl, hp⟩
    refine ⟨?_, p, ?_, ?_⟩
    · rw [ExistsForall.FrameCanonical, ExistsForall.reencode, Decoder.decode_enc]
    · exact ExistsForall.matrixBits_encoded r (code p)
    · rwa [ExistsForall.parameterCount_encoded]
  · rintro ⟨hw, p, hp, hs⟩
    refine ⟨ExistsForall.parameterCount w, p, ?_, hs⟩
    change ExistsForall.encSentence (ExistsForall.parameterCount w, ExistsForall.matrixBits w) = w at hw
    exact hw.symm.trans (congrArg (fun bits => ExistsForall.encSentence (ExistsForall.parameterCount w, bits)) hp)

theorem compileSentence_correct (w : List Bool) :
    w ∈ twoBlockLanguage ↔ compileSentence w ∈ ExistsForall.language := by
  rw [twoBlock_normalized, ExistsForall.frameFlag_iff]
  cases hb : ExistsForall.frameFlag w
  · simp only [Bool.false_eq_true, false_and, compileSentence, hb, ↓reduceIte,
      ExistsForall.encode_mem_language]
    exact iff_of_false (by trivial) (ExistsForall.not_sentence_falsum 0)
  · simp only [compileSentence, hb, ↓reduceIte, true_and]
    rw [compile_correct (ExistsForall.SentenceHolds (ExistsForall.parameterCount w))
      (ExistsForall.not_sentence_falsum _)]
    constructor
    · rintro ⟨p, hp, hs⟩
      rw [hp, ExistsForall.encode_mem_language]
      exact hs
    · rintro ⟨r, p, hp, hs⟩
      have he := ExistsForall.encSentence.injective hp
      have hr : ExistsForall.parameterCount w = r := congrArg Prod.fst he
      refine ⟨p, congrArg Prod.snd he, ?_⟩
      rwa [hr]

theorem twoBlock_mem : twoBlockLanguage ∈ CountingLevel 60 encBits :=
  (show PolyTimeReduces twoBlockLanguage ExistsForall.language from
    ⟨compileSentence, compileSentence_FP.computableInPolyTime, compileSentence_correct⟩).mem_CountingLevel
      ExistsForall.mem_CountingLevel

end LeanCanny.CountingHierarchy.FlatSentenceEncoding
