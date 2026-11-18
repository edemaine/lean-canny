/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.List.FinRange
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Policy.BinaryIntUnaryFin
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import LeanCanny.Encoding.FlatSyntaxInverse

/-! # Uniform conversion from library-derived arithmetic encodings

The implementation syntax uses natural variable indices, so its codecs and
translators are independent of a fixed dimension. The abstract's bounded syntax
is related to these words by structural induction in the bridge.
-/

@[expose] public section
namespace LeanCanny.Encoding.DerivedSyntax
open Turing.MultiTapeTM LeanCanny.ETR Brackets
open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

attribute [local encoding_rule] encUnary

/-- The policy's finite enumeration uses the numeric variable index in every dimension. -/
theorem finite_variable_encoding (n : ℕ) (i : Fin n) :
    EncodingPolicy.BinaryIntUnaryFin.fin n i = encUnary i.val := by
  change encUnary (FinEnum.equiv i).val = encUnary i.val
  congr 1
  change (List.finRange n).dedup.idxOf i = i.val
  rw [List.dedup_eq_self.mpr (List.nodup_finRange n)]
  exact List.idxOf_finRange i

derive_encoding termEncoding : Term
derive_encoding formulaEncoding : Formula

def termDecoder : PartialDecoder termEncoding :=
  termEncoding_decoder (.ofDecoder Decoder.intBin) (.ofDecoder Decoder.unary)

def formulaDecoder : PartialDecoder formulaEncoding :=
  formulaEncoding_decoder termDecoder termDecoder

/-- Apply a bitstring transformation separately to each framed word and concatenate. -/
def mapFrames (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  (frames w).flatMap f

theorem mapFrames_FP {f : List Bool → List Bool} (hf : f ∈ FP) : mapFrames f ∈ FP := by
  obtain ⟨a, d, ha⟩ := hf.polyBounded_length.exists_le
  have hl := computableInDegree_frames.computableInPolyTime.tidy
  have hs : ComputableTidilyInPolyTime (fun q : List Bool × List Bool => q.1 ++ f q.2)
      (encPair encBits encBits) encBits :=
    (ComputableTidilyInPolyTime.fst encBits encBits).append
      (hf.comp (ComputableTidilyInPolyTime.snd encBits encBits)) (fun _ => rfl)
  have h := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (step := fun (_ : Bool) state token => state ++ f token)
    (ComputableTidilyInPolyTime.const false) hl
    (ComputableTidilyInPolyTime.const ([] : List Bool))
    (hs.comp (((ComputableTidilyInPolyTime.fst (encPair encBool encBits) encBits).snd').prod
      (ComputableTidilyInPolyTime.snd (encPair encBool encBits) encBits)))
    (growth := fun w => a * ((encList encBits (frames w)).length + 1) ^ d)
    (by exact (PolyBounded.const a).mul ((hl.polyBounded_length.add (.const 1)).pow d))
    (by
      intro w state token ht
      have htlen : token.length ≤ (encList encBits (frames w)).length := by
        have hm : token.length ≤ ((frames w).map List.length).sum :=
          List.single_le_sum (fun v _ => Nat.zero_le v) token.length (List.mem_map_of_mem ht)
        exact hm.trans (sum_length_le_length_encList encBits (frames w))
      have hh := (ha token).trans (Nat.mul_le_mul_left a
        (Nat.pow_le_pow_left (Nat.add_le_add_right htlen 1) d))
      simpa only [encBits_apply, List.length_append] using Nat.add_le_add_left hh state.length)
  have hfold : ∀ (xs : List (List Bool)) (state : List Bool), xs.foldl (fun state token => state ++ f token) state =
      state ++ xs.flatMap f := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => intro state; simp [List.foldl_cons, ih, List.append_assoc]
  exact mem_FP_of_eq h (fun w => by simp [mapFrames, hfold])

/-- Translate one derived term token to the original flat alphabet. -/
def termToken (w : List Bool) : List Bool :=
  if w.take 1 = [false] then frame w
  else if w.take 2 = [true, false] then
    frame (true :: encUnary ((w.drop 2).length + 8))
  else if w.take 3 = [true, true, false] then FlatSyntax.operatorBits 0
  else FlatSyntax.operatorBits 1

def termToFlat := mapFrames termToken

/-- A comparison contains a complete term stream as its scalar payload. -/
def formulaToken (w : List Bool) : List Bool :=
  if w.take 1 = [false] then FlatSyntax.operatorBits 2
  else if w.take 2 = [true, false] then FlatSyntax.operatorBits 3 ++ termToFlat (w.drop 2)
  else if w.take 3 = [true, true, false] then FlatSyntax.operatorBits 4 ++ termToFlat (w.drop 3)
  else if w.take 4 = [true, true, true, false] then FlatSyntax.operatorBits 5
  else if w.take 5 = [true, true, true, true, false] then FlatSyntax.operatorBits 6
  else FlatSyntax.operatorBits 7

def toFlat := mapFrames formulaToken

theorem termToken_FP : termToken ∈ FP := by
  have hvar := mem_FP_comp
    (((UnaryFn.length (drop_mem_FP id_mem_FP (UnaryFn.const 2))).add (UnaryFn.const 8)).encoded)
    (cons_mem_FP true)
  exact (stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 1)) (constFn_mem_FP [false])).ite_mem_FP
    FlatSyntax.frame_FP
    ((stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 2)) (constFn_mem_FP [true, false])).ite_mem_FP
      (mem_FP_comp (f := fun w => true :: encUnary ((w.drop 2).length + 8))
        (g := frame) hvar FlatSyntax.frame_FP)
      ((stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 3))
        (constFn_mem_FP [true, true, false])).ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _)))

theorem termToFlat_FP : termToFlat ∈ FP := mapFrames_FP termToken_FP

theorem formulaToken_FP : formulaToken ∈ FP := by
  have test (bs : List Bool) := stringEq_fppred
    (take_mem_FP id_mem_FP (UnaryFn.const bs.length)) (constFn_mem_FP bs)
  have body (k : ℕ) (tag : ℕ) := appendFn_mem_FP
    (constFn_mem_FP (FlatSyntax.operatorBits tag))
    (mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const k)) termToFlat_FP)
  exact (test [false]).ite_mem_FP (constFn_mem_FP _)
    ((test [true, false]).ite_mem_FP (body 2 3)
      ((test [true, true, false]).ite_mem_FP (body 3 4)
        ((test [true, true, true, false]).ite_mem_FP (constFn_mem_FP _)
          ((test [true, true, true, true, false]).ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _)))))

theorem toFlat_FP : toFlat ∈ FP := mapFrames_FP formulaToken_FP

private theorem mapFrames_encoding {α : Type} (f : List Bool → List Bool)
    (enc : α ↪ List Bool) (xs : List α) :
    mapFrames f (encList enc xs) = xs.flatMap (fun x => f (enc x)) := by
  simp only [mapFrames, frames_encList, List.flatMap_map]

theorem termToFlat_encoded (t : Term) :
    termToFlat (termEncoding t) = FlatSyntax.encoding (FlatSyntax.termTokens t) := by
  induction t <;>
    simp only [termToFlat, termEncoding_apply, mapFrames_encoding] at *
  all_goals simp_all [termEncoding_tokens, termEncodingTokenEncoding, termToken,
    FlatSyntax.termTokens, FlatSyntax.tokenEncoding]
  all_goals rfl

theorem toFlat_encoded (p : Formula) :
    toFlat (formulaEncoding p) = FlatSyntax.encoding (FlatSyntax.formulaTokens p) := by
  induction p <;>
    simp only [toFlat, formulaEncoding_apply, mapFrames_encoding] at *
  all_goals simp_all [formulaEncoding_tokens, formulaEncodingTokenEncoding, formulaToken,
    FlatSyntax.formulaTokens, termToFlat_encoded]

/-- Native recognition of precisely the selected codec's image. -/
def valid {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) (w : List Bool) : Bool :=
  (D.decode w).isSome

theorem valid_polyTime {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) :
    ComputableInPolyTime (valid D) encBits encBool := by
  have h : ComputableInPolyTime (@Option.isSome α) (encOption enc) encBool := by fun_prop
  exact h.comp D.computable

theorem valid_iff {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) (w : List Bool) :
    valid D w = true ↔ ∃ a, enc a = w := by
  simp only [valid, Option.isSome_iff_exists, D.decode_eq_some_iff]

def spaceEncoding := encPair encUnary formulaEncoding
def pointEncoding := encPair encUnary (encList formulaEncoding)
def spaceDecoder : PartialDecoder spaceEncoding := (PartialDecoder.ofDecoder Decoder.unary).pair formulaDecoder
def pointDecoder : PartialDecoder pointEncoding :=
  (PartialDecoder.ofDecoder Decoder.unary).pair formulaDecoder.list

def spaceToFlat (w : List Bool) : List Bool := frame (unframe w) ++ toFlat (dropFrame w)
def pointToFlat (w : List Bool) : List Bool :=
  frame (unframe w) ++ mapFrames (fun token => frame (toFlat token)) (dropFrame w)

theorem spaceToFlat_FP : spaceToFlat ∈ FP :=
  appendFn_mem_FP (mem_FP_comp ComputableTidilyInPolyTime.unframe FlatSyntax.frame_FP)
    (mem_FP_comp ComputableTidilyInPolyTime.dropFrame toFlat_FP)

theorem pointToFlat_FP : pointToFlat ∈ FP :=
  appendFn_mem_FP (mem_FP_comp ComputableTidilyInPolyTime.unframe FlatSyntax.frame_FP)
    (mem_FP_comp ComputableTidilyInPolyTime.dropFrame
      (mapFrames_FP (mem_FP_comp toFlat_FP FlatSyntax.frame_FP)))

@[simp] theorem spaceToFlat_encoded (n : ℕ) (p : Formula) :
    spaceToFlat (spaceEncoding (n, p)) =
      encPair encUnary FlatSyntax.encoding (n, FlatSyntax.formulaTokens p) := by
  simp [spaceToFlat, spaceEncoding, toFlat_encoded]

@[simp] theorem pointToFlat_encoded (n : ℕ) (p a b : Formula) :
    pointToFlat (pointEncoding (n, [p, a, b])) =
      encPair encUnary (encList FlatSyntax.encoding)
        (n, [FlatSyntax.formulaTokens p, FlatSyntax.formulaTokens a, FlatSyntax.formulaTokens b]) := by
  change frame (unframe (frame (encUnary n) ++ encList formulaEncoding [p, a, b])) ++
      mapFrames (fun token => frame (toFlat token))
        (dropFrame (frame (encUnary n) ++ encList formulaEncoding [p, a, b])) =
    frame (encUnary n) ++ encList FlatSyntax.encoding
      [FlatSyntax.formulaTokens p, FlatSyntax.formulaTokens a, FlatSyntax.formulaTokens b]
  rw [unframe_frame_append, dropFrame_frame_append, mapFrames_encoding]
  simp only [List.flatMap_cons, List.flatMap_nil, toFlat_encoded]
  rfl

end LeanCanny.Encoding.DerivedSyntax
