/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
/-! # Native total fallback headers for any original saved-record writer -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask

noncomputable def fallbackOfWords (P : Parameters) (words : List Bool → List Bool) (root : List Bool) :=
  WordList.encode ((List.range (5*(P.cap root+2))).map fun i => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCanonicalUnitHeaderBits.selection (P.ambient root) (P.degree root) (words (fallbackKey root i))))

noncomputable def fallbackWordEntry (P : Parameters) (words : List Bool → List Bool) (z : List Bool) :=
  pair (IntegralMixedCommandHeaderBits.encode (IntegralMixedCanonicalUnitHeaderBits.selection
    (P.ambient (pairFst z)) (P.degree (pairFst z)) (words (fallbackPacket z)))) []

theorem fallbackOfWords_FP (P : Parameters) (a : Access P) (words : List Bool → List Bool) (hw : words∈FP) :
    fallbackOfWords P words ∈ FP := by
  have HW := mem_FP_comp fallbackPacket_FP hw
  have HE : fallbackWordEntry P words ∈ FP := mem_FP_pair (IntegralMixedCanonicalUnitHeaderBits.selection_FP
    (a.ambient.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP) _ HW) (constFn_mem_FP [])
  have HN := ((UnaryFn.const 5).mul (a.cap.add (UnaryFn.const 2))).replicate_mem_FP true
  apply mem_FP_of_eq (flatMap_range_mem_FP HE HN)
  intro root
  simp only [fallbackOfWords,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    fallbackWordEntry,fallbackPacket,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem fallbackOfWords_get (P : Parameters) (words : List Bool → List Bool) (root : List Bool) (i : ℕ)
    (hi : i<5*(P.cap root+2)) : WordList.get (fallbackOfWords P words root) i =
    IntegralMixedCommandHeaderBits.encode (IntegralMixedCanonicalUnitHeaderBits.selection
      (P.ambient root) (P.degree root) (words (fallbackKey root i))) := by
  rw [fallbackOfWords,WordList.get_encode]
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
