/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TarskiQuerySpace

/-! # PSPACE decision consequences of the original-source Tarski evaluator -/

@[expose] public section

namespace LeanCanny.Algebra.TarskiQueryBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open IntegerTarskiSeedBits

def zeroLanguage (F : Family) : Language := {c | value F c = 0}
def positiveLanguage (F : Family) : Language := {c | 0 < value F c}
def negativeLanguage (F : Family) : Language := {c | value F c < 0}

theorem integerCode_fst_zero_iff (z : ℤ) :
    pairFst (SignStatisticBits.integerCode z) = [] ↔ z ≤ 0 := by
  simp only [SignStatisticBits.integerCode, pairFst_pair, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega

theorem integerCode_snd_zero_iff (z : ℤ) :
    pairSnd (SignStatisticBits.integerCode z) = [] ↔ 0 ≤ z := by
  simp only [SignStatisticBits.integerCode, pairSnd_pair, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega

noncomputable def zeroDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceDecider (zeroLanguage F) := by
  have hflag := ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))).flag_mem_FP
  apply (evaluator a hF P Q).decider (fun v => decide (pairFst v = [] ∧ pairSnd v = [])) hflag
  intro c
  simp only [zeroLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, integerCode_fst_zero_iff, integerCode_snd_zero_iff]
  omega

noncomputable def positiveDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceDecider (positiveLanguage F) := by
  have hflag := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (evaluator a hF P Q).decider (fun v => decide (pairFst v ≠ [])) hflag
  intro c
  simp only [positiveLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, integerCode_fst_zero_iff]
  omega

noncomputable def negativeDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceDecider (negativeLanguage F) := by
  have hflag := (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (evaluator a hF P Q).decider (fun v => decide (pairSnd v ≠ [])) hflag
  intro c
  simp only [negativeLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, integerCode_snd_zero_iff]
  omega

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    zeroLanguage F ∈ PSPACE := (zeroDecider a hF P Q).mem_PSPACE

theorem positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    positiveLanguage F ∈ PSPACE := (positiveDecider a hF P Q).mem_PSPACE

theorem negativeLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    negativeLanguage F ∈ PSPACE := (negativeDecider a hF P Q).mem_PSPACE

end LeanCanny.Algebra.TarskiQueryBits
