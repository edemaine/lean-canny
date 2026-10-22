/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveInfinitesimalFamily
public import LeanCanny.ETR.CoerciveSymbolicReference

/-! # Four exact eventual sign patterns characterize encoded ETR -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveInfinitesimalFamily
open LeanCanny.Algebra LeanCanny.Encoding
open CoerciveSourceSampling CoercivePreparationControls CoerciveSymbolicSampling
open Polynomial SymbolicScaledSquarefree
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
attribute [local irreducible] CoercivePreparationControls.referenceExponent CoerciveSymbolicBounds.queryDegree

noncomputable def wantedQuery (left right : Bool) (bits : List Bool) : Query bits → SignType
  | .inl _ => 0
  | .inr false => wanted left
  | .inr true => wanted right

theorem accepts_iff_patterns (bits : List Bool) (f : Query bits → SignType) :
    accepts bits f ↔ ∃ left right : Bool, ∀ j, f j = wantedQuery left right bits j := by
  constructor
  · rintro ⟨hzero, hleft, hright⟩
    have pick {s : SignType} (hs : s ≤ 0) : ∃ b : Bool, s = wanted b := by
      rcases SignType.nonpos_iff.mp hs with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    obtain ⟨left, hl⟩ := pick hleft
    obtain ⟨right, hr⟩ := pick hright
    refine ⟨left, right, ?_⟩
    rintro (i | b)
    · exact hzero i
    · cases b
      · exact hl
      · exact hr
  · rintro ⟨left, right, h⟩
    refine ⟨fun i => h (.inl i), ?_, ?_⟩
    · rw [h (.inr false)]
      change wanted left ≤ 0
      cases left <;> decide
    · rw [h (.inr true)]
      change wanted right ≤ 0
      cases right <;> decide

noncomputable def indexOf (bits : List Bool) : Query bits → Fin (dimension bits + 2)
  | .inl i => ⟨i.val, by omega⟩
  | .inr false => ⟨dimension bits, by omega⟩
  | .inr true => ⟨dimension bits + 1, by omega⟩

theorem queryIndex_indexOf (bits : List Bool) (j : Query bits) : queryIndex bits (indexOf bits j).val = j := by
  rcases j with i | b
  · change (if hi : i.val < dimension bits then Sum.inl ⟨i.val, hi⟩ else
      Sum.inr (decide (i.val ≠ dimension bits))) = Sum.inl i
    rw [dite_eq_left i.isLt]
  · cases b <;> simp [indexOf, queryIndex]

theorem pattern_queryIndex (left right : Bool) (bits : List Bool) (i : ℕ) :
    pattern left right bits i = wantedQuery left right bits (queryIndex bits i) := by
  unfold pattern queryIndex
  split_ifs with hlt heq
  · rfl
  · subst i
    simp only [ne_eq, not_true_eq_false, decide_false, wantedQuery]
  · simp only [decide_eq_true heq, wantedQuery]

theorem indexed_patterns_iff (left right : Bool) (bits : List Bool) (f : Query bits → SignType) :
    (∀ i : Fin (dimension bits + 2), f (queryIndex bits i.val) = pattern left right bits i.val) ↔
      ∀ j, f j = wantedQuery left right bits j := by
  constructor
  · intro h j
    have hj := h (indexOf bits j)
    rwa [pattern_queryIndex, queryIndex_indexOf] at hj
  · intro h i
    rw [pattern_queryIndex]
    exact h _

def Exact (left right : Bool) (bits : List Bool) (s : ℝ) : Prop :=
  ∃ theta : ℝ, (family bits).parameter.eval₂ (scalarEvaluation s) theta = 0 ∧
    ∀ j, SignType.sign ((clearedQuery bits j).eval₂ (scalarEvaluation s) theta) = wantedQuery left right bits j

theorem exact_iff_native (left right : Bool) (bits : List Bool) (s : ℝ) :
    Exact left right bits s ↔ InfinitesimalRootBits.Realizes (signFamily left right) bits s := by
  simp only [InfinitesimalRootBits.Realizes, InfinitesimalRootBits.queries, InfinitesimalRootBits.pattern,
    signFamily, rootFamily, BinaryNatCode.encode, Polynomial.eval_map]
  change (∃ theta : ℝ, (family bits).parameter.eval₂ (scalarEvaluation s) theta = 0 ∧
    ∀ j, SignType.sign ((clearedQuery bits j).eval₂ (scalarEvaluation s) theta) = wantedQuery left right bits j) ↔ _
  apply exists_congr
  intro theta
  apply and_congr_right
  intro _
  rw [Nat.fromBitsLE_bits]
  simpa only [scalarEvaluation, ParameterTarski.evalHom] using
    (indexed_patterns_iff left right bits
      (fun j => SignType.sign ((clearedQuery bits j).eval₂ (scalarEvaluation s) theta))).symm

theorem realizes_iff_exact (bits : List Bool) (s : ℝ) :
    Realizes bits s ↔ ∃ left right : Bool, Exact left right bits s := by
  constructor
  · rintro ⟨theta, ht, hs⟩
    obtain ⟨left, right, hp⟩ := (accepts_iff_patterns bits _).mp hs
    exact ⟨left, right, theta, ht, hp⟩
  · rintro ⟨left, right, theta, ht, hs⟩
    exact ⟨theta, ht, (accepts_iff_patterns bits _).mpr ⟨left, right, hs⟩⟩

/-- Each inequality contributes its negative and zero cases; eventual stability
allows one fixed pair of these cases throughout a common positive interval. -/
theorem correct_patterns (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ left right : Bool, bits ∈ InfinitesimalRootBits.eventualRealizableLanguage (signFamily left right) := by
  constructor
  · intro h
    have hr := (CoerciveSymbolicReference.correct bits).mp h
    obtain ⟨left, right, theta, ht, hsign⟩ := (realizes_iff_exact bits _).mp hr
    refine ⟨left, right, CoerciveSymbolicReference.reference bits, InfinitesimalSign.dyadic_pos _, ?_⟩
    intro s hs hsmall
    apply (exact_iff_native left right bits s).mp
    have h := (ParameterTarski.realizable_stable (family bits).parameter (parameter_ne_zero bits)
      (clearedQuery bits) (wantedQuery left right bits) s (CoerciveSymbolicReference.reference bits)
      hs (InfinitesimalSign.dyadic_pos _) hsmall.le le_rfl).mpr ?_
    · simpa only [Exact, Polynomial.eval_map, scalarEvaluation, ParameterTarski.evalHom] using h
    · refine ⟨theta, ?_, ?_⟩
      · simpa only [Polynomial.eval_map, scalarEvaluation, ParameterTarski.evalHom] using ht
      · simpa only [Polynomial.eval_map, scalarEvaluation, ParameterTarski.evalHom] using hsign
  · rintro ⟨left, right, delta, hd, h⟩
    apply (CoerciveSymbolicSampling.correct bits).mpr
    refine ⟨delta, hd, fun s hs hsmall => ?_⟩
    exact (realizes_iff_exact bits s).mpr ⟨left, right, (exact_iff_native left right bits s).mpr (h s hs hsmall)⟩

end LeanCanny.ETR.CoerciveInfinitesimalFamily
