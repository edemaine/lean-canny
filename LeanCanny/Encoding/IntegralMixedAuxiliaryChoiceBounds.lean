/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryChoicePrepare
/-! # One original polynomial bounds every prepared bounded recipe descriptor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def inputLength (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :=
  2*q.length+2+2*n q*scalarWidth n t q

theorem inputLength_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : UnaryFn (inputLength n t) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add
    (((UnaryFn.const 2).mul hn).mul (scalarWidth_unary hn ht))

theorem encoded_input_length (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ) :
    (pair original (encode (scalarWidth n t original) labels)).length=inputLength n t original := by
  rw [pair_length,encode_length]
  rfl

theorem advice_length_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    ∃ p : Polynomial ℕ, ∀ original (labels : Fin (n original) → ℕ × ℕ),
      (encode (scalarWidth n t original) labels).length≤p.eval original.length := by
  obtain ⟨p,hp⟩ := output_length_poly_of_mem_FP
    ((((UnaryFn.const 2).mul hn).mul (scalarWidth_unary hn ht)).mem_FP)
  refine ⟨p,fun original labels => ?_⟩
  simpa only [encode_length,List.length_replicate] using hp original

theorem root_length_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    ∃ p : Polynomial ℕ, ∀ original (labels : Fin (n original) → ℕ × ℕ),
      (∀ i,(labels i).1≤scalarCeiling n t original) →
      (∀ i,(labels i).2≤scalarCeiling n t original) →
      (IntegralMixedAuxiliaryRecipeRoot.root original labels (encode (scalarWidth n t original) labels)).length≤
        p.eval original.length := by
  obtain ⟨r,hr⟩ := output_length_poly_of_mem_FP (inputLength_unary hn ht).mem_FP
  obtain ⟨p,hp⟩ := prepare_length_polynomial hn ht
  refine ⟨p.comp r,fun original labels hc hd => ?_⟩
  have Hinput : (pair original (encode (scalarWidth n t original) labels)).length≤r.eval original.length := by
    rw [encoded_input_length]
    simpa only [List.length_replicate] using hr original
  have H := hp (pair original (encode (scalarWidth n t original) labels))
  rw [prepare_encode n t original labels hc hd] at H
  simpa only [Polynomial.eval_comp] using H.trans (p.eval_mono Hinput)
end LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
