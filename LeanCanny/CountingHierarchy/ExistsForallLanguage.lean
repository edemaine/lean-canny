/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ExistsForallSource

/-! # The encoded language ∃∀ℝ -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.ExistsForall

open LeanCanny LeanCanny.ETR Cslib Cslib.Complexity Turing.MultiTapeTM

/-- Variables below `r` are existential parameters; all remaining variables
are universally quantified. Terms use integer constants and polynomial operations. -/
def SentenceHolds (r : ℕ) (p : Formula) : Prop :=
  ∃ x : Fin r → ℝ, ∀ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) → p.Holds env

def language : Set (List Bool) :=
  {w | ∃ r : ℕ, ∃ p : Formula, w = encSentence (r, p.encode) ∧ SentenceHolds r p}

theorem sentence_nnf (r : ℕ) (p : Formula) : SentenceHolds r (p.nnf true) ↔ SentenceHolds r p := by
  simp only [SentenceHolds, Formula.holds_nnf, ite_true]

theorem not_sentence_falsum (r : ℕ) : ¬SentenceHolds r Formula.falsum := by
  rintro ⟨x, hx⟩
  exact hx (fun j => if h : j < r then x ⟨j, h⟩ else 0) (fun i => by rw [dite_eq_left i.isLt])

theorem parameterCount_encoded (r : ℕ) (bits : List Bool) : parameterCount (encSentence (r, bits)) = r := by
  rw [parameterCount, Decoder.decode_enc]

theorem matrixBits_encoded (r : ℕ) (bits : List Bool) : matrixBits (encSentence (r, bits)) = bits := by
  rw [matrixBits, Decoder.decode_enc]

theorem matrix_encoded (r : ℕ) (p : Formula) : matrix (encSentence (r, p.encode)) = p.nnf true := by
  apply Formula.encode_injective
  rw [← matrix_encode, matrixBits_encoded, NNF.normalize_encode]

theorem encode_mem_language (r : ℕ) (p : Formula) : encSentence (r, p.encode) ∈ language ↔ SentenceHolds r p := by
  constructor
  · rintro ⟨s, q, heq, hq⟩
    have hp := encSentence.injective heq
    have hs : r = s := congrArg Prod.fst hp
    have hformula : p = q := Formula.encode_injective (congrArg Prod.snd hp)
    exact hs.symm ▸ hformula.symm ▸ hq
  · intro h
    exact ⟨r, p, rfl, h⟩

def reencode (w : List Bool) : List Bool := encSentence (decoder.decode w)

def FrameCanonical (w : List Bool) : Prop := reencode w = w

theorem reencode_mem_FP : reencode ∈ FP := by
  change ComputableTidilyInPolyTime (fun w => encSentence (decoder.decode w)) encBits encBits
  exact decoder.computableInPolyTime.tidy.encoded

theorem frameCanonical_fppred : FPPred FrameCanonical :=
  LeanCanny.Encoding.Brackets.stringEq_fppred reencode_mem_FP id_mem_FP

noncomputable def frameFlag : List Bool → Bool := Classical.choose frameCanonical_fppred

theorem frameFlag_polyTime : ComputableInPolyTime frameFlag encBits encBool :=
  (flag_computable (Classical.choose_spec frameCanonical_fppred).1).computableInPolyTime

theorem frameFlag_iff (w : List Bool) : FrameCanonical w ↔ frameFlag w = true :=
  (Classical.choose_spec frameCanonical_fppred).2 w

theorem matrix_malformed (w : List Bool) (h : Grammar.recognizeFormula (matrixBits w) ≠ true) :
    matrix w = Formula.falsum := by
  apply Formula.encode_injective
  rw [← matrix_encode, NNF.normalize, ite_eq_right h]
  rfl

theorem language_iff_normalized (w : List Bool) :
    w ∈ language ↔ FrameCanonical w ∧ SentenceHolds (parameterCount w) (matrix w) := by
  constructor
  · rintro ⟨r, p, rfl, hp⟩
    refine ⟨?_, ?_⟩
    · rw [FrameCanonical, reencode, Decoder.decode_enc]
    · rw [parameterCount_encoded, matrix_encoded, sentence_nnf]
      exact hp
  · rintro ⟨hf, hs⟩
    by_cases hg : Grammar.recognizeFormula (matrixBits w) = true
    · obtain ⟨p, hp⟩ := (Grammar.recognizeFormula_true_iff (matrixBits w)).mp hg
      have hw : w = encSentence (parameterCount w, p.encode) := by
        change encSentence (parameterCount w, matrixBits w) = w at hf
        rw [hp] at hf
        exact hf.symm
      rw [hw, encode_mem_language]
      have hm : matrix w = p.nnf true := by
        apply Formula.encode_injective
        rw [← matrix_encode, hp, NNF.normalize_encode]
      exact (sentence_nnf (parameterCount w) p).mp (hm ▸ hs)
    · rw [matrix_malformed w hg] at hs
      exact False.elim (not_sentence_falsum _ hs)

end LeanCanny.CountingHierarchy.ExistsForall
