/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeWordCriterion
public import LeanCanny.CountingHierarchy.ControlledWordDegreePiece
public import LeanCanny.CountingHierarchy.SelectionCounterexampleCorrectness
public import LeanCanny.CountingHierarchy.CounterexampleVariableOrder
public import LeanCanny.CountingHierarchy.BoundedTwoTestDecision

/-! # A fixed counting-level decision for controlled existential-universal zero avoidance

The counting-hierarchy result follows OpenAI,
*Existential–universal real sentences in the counting hierarchy* (October 4, 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf
The historical `LeanCanny` namespace records the host project, not authorship.
-/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] finiteRelativeSection finiteRelativeCharacteristic
  LeanCanny.CountingHierarchy.relativeCharacteristic relativeBivariate specializedRelativeSection
  firstVariableCoefficient degreePiecePolynomial candidateCoordinate parametricCoordinatePolynomial
  indexedEquationPositivityPolynomial selectionEquation selectionInequality selectionExtraEquation
  selectionExtraInequality candidateSelection

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

theorem nonnegative_twoBlock_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hFn : ∀ w (x : Fin (m w) → ℝ) (z : Fin (n w) → ℝ),
      0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w)) :
    {w | ∃ x : Fin (m w) → ℝ, ∀ z : Fin (n w) → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w) ≠ 0} ∈
        CountingLevel (a + 60) enc := by
  let d : α → ℕ := fun w => 2 * (C.degreeBound w + 1)
  have hd (w : α) : 1 ≤ d w := by dsimp only [d]; omega
  have he (w : α) : Even (d w + 2) := by
    refine ⟨C.degreeBound w + 2, ?_⟩
    dsimp only [d]
    omega
  have hP (w : α) : (P w).totalDegree ≤ d w + 1 := (C.degree_le w).trans (by dsimp only [d]; omega)
  let CE : Controlled (fun w => finiteRelativeSection (d w) (P w) (hP w)) enc (a + 10) :=
    C.relativeSection E hn hm
  let N := CE.degreeBound
  let b := CE.massExponent
  let W := fun q : α × List Bool => degreePiecePolynomial
    (finiteRelativeSection (d q.1) (P q.1) (hP q.1)) (N q.1) (choiceDegree (N q.1) q.2).val
  let CW₀ := CE.wordDegreePiece E hm
  let CW : Controlled W (encPair enc encBits) (a + 12) := CW₀.mono (by omega : a + 10 + 2 ≤ a + 12)
  have hCWdegree (q : α × List Bool) : CW.degreeBound q = 2 * (N q.1 + 1) := rfl
  have hCWmass (q : α × List Bool) : CW.massExponent q = degreePieceMassExponent (N q.1) (b q.1) := rfl
  have hw := ComputableInPolyTime.fst enc encBits
  have hword := ComputableInPolyTime.snd enc encBits
  let EW := Decoder.pair E Decoder.bits
  have hpos (q : α × List Bool) : 0 < m q.1 + 1 := Nat.zero_lt_succ _
  let CR₀ := (C.counterexampleOrder hn hm).preprocess (fun q : α × List Bool => q.1) hw
  let CR := CR₀.mono (by omega : a ≤ a + 12 + 20)
  let CP₀ := CW.selectionSystem EW hpos (fun q => q.2) hword
  let CQ₀ := CW.selectedCounterexampleSystem CR (hn.comp hw) EW hpos (fun q => q.2) hword
  let CP := CP₀.mono (by omega : a + 12 + 21 ≤ a + 33)
  let CQ := CQ₀.mono (by omega : a + 12 + 21 ≤ a + 33)
  let width : α → ℕ := fun w => choiceTupleWidth (N w)
    (candidateIndexBound (m w + 1) (2 * (N w + 1)))
    (candidateDegree (m w + 1) (2 * (N w + 1))) (m w + 1)
  have hm₁ := ComputableInPolyTime.unary_add' hm (ComputableInPolyTime.const 1)
  have hD := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.binary_add' CE.degree_computable (.const 1))
  have hwidth : ComputableInPolyTime width enc encUnary := choiceTupleWidth_polyTime CE.degree_computable
    (candidateIndexBound_polyTime hm₁ hD) (candidateDegree_polyTime hm₁ hD) hm₁
  have hNative := bounded_two_test_decision_mem CP CQ E width hwidth
  have hNative' : {w | ∃ word : List Bool, word.length = width w ∧
      (∃ x, MvPolynomial.eval₂ (Int.castRingHom ℝ) x
        (indexedEquationPositivityPolynomial
          (selectionEquation (W (w, word)) (CW.degreeBound (w, word)) (CW.degree_le (w, word)) (hpos (w, word)) word)
          (selectionInequality (W (w, word)) (CW.degreeBound (w, word)) (CW.massExponent (w, word))
            (CW.degree_le (w, word)) (hpos (w, word)) word) (m w + 1 + 1) (m w + 1)) = 0) ∧
      ¬∃ y, MvPolynomial.eval₂ (Int.castRingHom ℝ) y
        (indexedEquationPositivityPolynomial
          (selectionExtraEquation (W (w, word)) (counterexamplePolynomial (P w))
            (CW.degreeBound (w, word)) (CW.degree_le (w, word)) (hpos (w, word)) word)
          (selectionExtraInequality (u := n w) (W (w, word)) (CW.degreeBound (w, word)) (CW.massExponent (w, word))
            (CW.degree_le (w, word)) (hpos (w, word)) word) (m w + 1 + 2) (m w + 1)) = 0} ∈
        CountingLevel (a + 60) enc := by
    simpa only [Nat.add_assoc] using hNative
  convert hNative' using 1
  ext w
  simp only [Set.mem_ofPred_eq]
  have hmat := relative_good_iff_word_two_tests (d w) (hd w) (he w) (P w) (hP w) (hFn w)
    (N w) (b w) (CE.degree_le w) (CE.mass_le w)
  dsimp only at hmat
  rw [hmat]
  apply exists_congr
  intro word
  apply and_congr_right
  intro _
  rw [exists_selectionSystem_zero_iff, exists_selectionCounterexampleSystem_zero_iff]
  simp only [eval_counterexamplePolynomial, hCWdegree, hCWmass, W]

/-- Squaring supplies nonnegativity without changing the source's function
level or any quantified zero set. Both real blocks may have size zero. -/
theorem twoBlock_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    {w | ∃ x : Fin (m w) → ℝ, ∀ z : Fin (n w) → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w) ≠ 0} ∈
        CountingLevel (a + 60) enc := by
  have h := (C.pow (fun _ => 2) (ComputableInPolyTime.const 2)).nonnegative_twoBlock_mem E hn hm
    (fun w x z => by
      rw [MvPolynomial.eval₂_pow]
      exact sq_nonneg _)
  simpa only [MvPolynomial.eval₂_pow, pow_ne_zero_iff (by decide : 2 ≠ 0)] using h

end LeanCanny.CountingHierarchy.Controlled
