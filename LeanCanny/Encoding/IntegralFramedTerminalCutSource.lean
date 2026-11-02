/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
public import LeanCanny.Encoding.IntegralFramedCutCoefficientTest
/-! # Actual full cut coefficients on an arbitrary complete terminal prefix

The same parent task selects all four untruncated factor kinds and every
lower choice. Only its indexed coefficient/choice fields change. If the
old arity exceeds the terminal dimension the polynomial is zero; otherwise
its variables occupy the literal terminal suffix.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.query

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))

noncomputable def oldArity (c d : List Bool) :=
  (IntegralMixedFramedChoiceProbeSourceBits.source P D H).arity (IntegralFramedCutCoefficientTest.query P (pair c d))
noncomputable def count (c : List Bool) := (family P D H).birth (key c)
noncomputable def arity (c d : List Bool) := min (oldArity P D H c d) (count P D H key c)
noncomputable def polynomial (c d : List Bool) : MvPolynomial (Fin (arity P D H key c d)) ℤ :=
  if hfit : oldArity P D H c d≤count P D H key c then
    MvPolynomial.rename (Fin.cast (Nat.min_eq_left hfit).symm)
      (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (IntegralFramedCutCoefficientTest.query P (pair c d)))
  else 0

noncomputable def source (hF : ∀ root,1≤F root)
    (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q) :
    SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) where
  arity:=arity P D H key
  newer c d:=count P D H key c-arity P D H key c d
  polynomial:=polynomial P D H key
  degree c d:=IntegralMixedFramedChoiceProbeSourceBits.degree P D H (IntegralFramedCutCoefficientTest.query P (pair c d))+1
  mass c d:=IntegralMixedFramedChoiceProbeSourceBits.massBound P D H L F C (IntegralFramedCutCoefficientTest.query P (pair c d))+1
  dimension c d := by
    change count P D H key c-arity P D H key c d+arity P D H key c d=count P D H key c
    exact Nat.sub_add_cancel (Nat.min_le_right _ _)
  polynomial_degree c d := by
    unfold polynomial
    split_ifs
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans
        ((IntegralMixedFramedChoiceProbeSourceBits.polynomial_degree P D H _).trans (Nat.le_succ _))
    · rw [MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  polynomial_mass c d := by
    unfold polynomial
    split_ifs
    · exact (MvMass.rename_le _ _).trans
        ((IntegralMixedFramedChoiceProbeSourceBits.polynomial_mass P D H L F C hs hF hf _).trans
          (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    · rw [MvMass.zero]
      exact Nat.zero_le _

theorem oldArity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (fun z=>oldArity P D H (pairFst z) (pairSnd z)) :=
  (IntegralMixedFramedChoiceProbeSourceBits.arity_unary P a D H).comp
    (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) (IntegralFramedCutCoefficientTest.query_FP P a))

theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (count P D H key) :=
  ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk).of_eq
    (fun _=>(IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm)

end LeanCanny.Encoding.IntegralFramedTerminalCutTest
