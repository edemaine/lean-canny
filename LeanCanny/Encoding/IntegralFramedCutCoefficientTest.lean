/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutSuccessorInput
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
/-! # Full relative coefficients tested on the same successor joint tail

The sampler and vertex label are fixed by the parent task. Extra test words
select coefficient and finite choice only. The head variable is unused, so
the polynomial evaluates on the literal old tail even for an empty parent.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutCoefficientTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

def query (P : Parameters) (z : List Bool) := IntegralMixedCutCoefficientQueryBits.query P (pair (pairFst z) (pairSnd z))
theorem query_FP (P : Parameters) (a : Access P) : query P∈FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) (IntegralMixedCutCoefficientQueryBits.query_FP P a)
theorem query_normalize (P : Parameters) (z : List Bool) : query P (pair (pairFst z) (pairSnd z))=query P z := by
  simp only [query,pairFst_pair,pairSnd_pair]

theorem dimension (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (z : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (pairFst z)) :
    (IntegralMixedFramedChoiceProbeSourceBits.source P D H).arity (query P z)+1=
      (IntegralFramedCutSuccessor.input P D H L F C hs).count (pairFst z) := by
  simpa only [query,pairFst_pair] using IntegralFramedCutSuccessor.probe_arity P D H L F C hs
    (pair (pairFst z) (pairSnd z)) (by simpa only [pairFst_pair] using ha)

theorem dimension_pair (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (c d : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    (IntegralMixedFramedChoiceProbeSourceBits.source P D H).arity (query P (pair c d))+1=
      (IntegralFramedCutSuccessor.input P D H L F C hs).count c := by
  simpa only [pairFst_pair] using dimension P D H L F C hs (pair c d) (by simpa only [pairFst_pair] using ha)

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (c d : List Bool) :
    MvPolynomial (Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)) ℤ :=
  if ha : IntegralMixedFramedFullCutProbeBits.Active P c then
    MvPolynomial.rename (Fin.cast (dimension_pair P D H L F C hs c d ha))
      (MvPolynomial.rename Fin.succ (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (query P (pair c d))))
  else 0

noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  IntegralMixedFramedChoiceProbeSourceBits.degree P D H (query P z)+1
noncomputable def mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (z : List Bool) :=
  IntegralMixedFramedChoiceProbeSourceBits.massBound P D H L F C (query P z)+1

theorem degree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (degree P D H) := by
  have HD : BinaryFn (fun z=>IntegralMixedFramedChoiceProbeSourceBits.degree P D H (query P z)) :=
    (IntegralMixedFramedChoiceProbeSourceBits.degree_binary P a D H).comp (query_FP P a)
  exact HD.add (BinaryFn.const 1)
theorem mass_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (mass P D H L F C) := by
  have HM : BinaryFn (fun z=>IntegralMixedFramedChoiceProbeSourceBits.massBound P D H L F C (query P z)) :=
    (IntegralMixedFramedChoiceProbeSourceBits.massBound_binary P a D H L F C hL hF hC).comp (query_FP P a)
  exact HM.add (BinaryFn.const 1)

noncomputable def test (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hF : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key) :
    SquareSampleCompleteIndexedPolynomialTest.Test (IntegralFramedCutSuccessor.input P D H L F C hs) where
  polynomial := polynomial P D H L F C hs
  degree := degree P D H
  mass := mass P D H L F C
  polynomial_degree z := by
    unfold polynomial
    split_ifs
    · apply (MvPolynomial.totalDegree_rename_le _ _).trans
      apply (MvPolynomial.totalDegree_rename_le _ _).trans
      have HD:=IntegralMixedFramedChoiceProbeSourceBits.polynomial_degree P D H (query P (pair (pairFst z) (pairSnd z)))
      rw [query_normalize] at HD ⊢
      exact HD.trans (Nat.le_succ _)
    · rw [MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  polynomial_mass z := by
    unfold polynomial
    split_ifs
    · apply (MvMass.rename_le _ _).trans
      apply (MvMass.rename_le _ _).trans
      have HM:=IntegralMixedFramedChoiceProbeSourceBits.polynomial_mass P D H L F C hs hF hf
        (query P (pair (pairFst z) (pairSnd z)))
      rw [query_normalize] at HM ⊢
      exact HM.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    · rw [MvMass.zero]
      exact Nat.zero_le _

end LeanCanny.Encoding.IntegralFramedCutCoefficientTest
