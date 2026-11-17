/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledNormNegative
public import LeanCanny.CountingHierarchy.RootLabelWitnessEncoding

/-! # A polynomial-width Boolean witness for real feasibility -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

@[expose] noncomputable def normWitnessTest (C : Controlled P enc a) (d : α → ℕ)
    (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1) (q : α × List Bool) : Bool :=
  decide (codedFiniteCriticalDeterminant (d q.1) (C.massExponent q.1) (P q.1) (hdeg q.1)
    (rootLabelWordWitness q.2).1 (rootLabelWordWitness q.2).2 < 0)

@[expose] def feasibilityWitnessWidth (_C : Controlled P enc a) (d : α → ℕ) (w : α) : ℕ :=
  rootLabelWitnessWidth ((d w + 1) ^ n w) (criticalRootLabelLength (n w) (d w))

theorem feasibilityWitnessWidth_polyTime (C : Controlled P enc a) {d : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (C.feasibilityWitnessWidth d) enc encUnary :=
  rootLabelWitnessWidth_polyTime
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) C.arity_computable)
    (criticalRootLabelLength_polyTime C.arity_computable hd)

/-- The verifier uses the constructed sign algorithm for the final norm,
with polynomial-time decoding and source-family reindexing. -/
theorem normWitnessTest_mem (C : Controlled P enc a) (E : Decoder enc) {d : α → ℕ}
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    (hd : ComputableInPolyTime d enc encNat) :
    C.normWitnessTest d hdeg ∈ CountingFunction (a + 24) (encPair enc encBits) encBool := by
  have hf := ComputableInPolyTime.fst enc encBits
  let C' := C.preprocess Prod.fst hf
  have hdecode := rootLabelWordWitness_polyTime.comp (ComputableInPolyTime.snd enc encBits)
  have hdata := (ComputableInPolyTime.fst encRootLabelCode encNat).comp hdecode
  have he := (ComputableInPolyTime.snd encRootLabelCode encNat).comp hdecode
  have hneg := C'.normNegative_mem (Decoder.pair E Decoder.bits)
    (fun q => hdpos q.1) (fun q => hdeg q.1) (hd.comp hf) hdata he
  change (fun q => C.normWitnessTest d hdeg q) ∈ _
  simpa only [normWitnessTest, normInteger, C', preprocess, Function.comp_apply] using hneg

/-- The word width is computed from the primary instance alone. Soundness
also covers every malformed witness, through the total bounded decoder. -/
theorem feasibility_iff_word_witness (C : Controlled P enc a) (d : α → ℕ)
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    (heven : ∀ w, Even (d w + 2))
    (hFn : ∀ w, ∀ x : Fin (n w) → ℝ, 0 ≤ eval x ((P w).map (Int.castRingHom ℝ))) (w : α) :
    (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0) ↔
      ∃ word : List Bool, word.length = C.feasibilityWitnessWidth d w ∧
        C.normWitnessTest d hdeg (w, word) = true := by
  constructor
  · intro hzero
    obtain ⟨data, hdata, e, he, hneg⟩ :=
      (real_zero_iff_negative_codedCriticalDeterminant (d w) (hdpos w) (heven w)
        (C.massExponent w) (P w) (hdeg w) (C.mass_le w) (hFn w)).mp hzero
    obtain ⟨word, hlen, hdecode⟩ := exists_rootLabelWordWitness hdata he
    refine ⟨word, hlen, ?_⟩
    simp only [normWitnessTest, hdecode]
    exact decide_eq_true hneg
  · rintro ⟨word, _hlen, htest⟩
    have hneg := of_decide_eq_true htest
    exact real_zero_of_negative_codedCriticalDeterminant (d w) (hdpos w) (heven w)
      (C.massExponent w) (P w) (hdeg w) (C.mass_le w) (hFn w)
      (rootLabelWordWitness word).1 (rootLabelWordWitness word).2 hneg

end LeanCanny.CountingHierarchy.Controlled
