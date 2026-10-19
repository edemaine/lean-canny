/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternEnumeration
public import LeanCanny.Algebra.SignPatternWeights

/-! # Polynomial-space scaled sign-pattern counts

For a polynomially bounded number of indexed polynomials, enumerate all ternary
queries, compute their signed weights and Tarski values, and sum them with full
workspace/clock accounting. Original coefficient readers may use polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignPatternBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def termOutput (z : List Bool) : List Bool :=
  IntegerSumBits.multiply (pair (pairSnd (pairFst z)) (pairSnd z))

theorem termOutput_mem_FP : termOutput ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
    IntegerSumBits.multiply_mem_FP
  refine mem_FP_of_eq (g := termOutput) h ?_
  intro z
  simp only [termOutput, Function.comp_apply]

noncomputable def summandEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (summand F q)) := by
  let W := (weightEvaluator a hF hs).withInput
  let Q := ((queryEvaluator a hF H P).precompose pairFst pairFst_mem_FP).withInput
  let E := (W.chain Q).postcompose termOutput termOutput_mem_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, termOutput, pairFst_pair, pairSnd_pair, IntegerSumBits.multiply_codes, summand]

noncomputable def evaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (scaledCount F c)) := by
  let E := IntegerSumBits.evaluator (summandEvaluator a hF hs H P)
    (fun c => Ternary.count (F.count c)) (Ternary.count_mem_FP hF.count hF.countUnary)
    (fun c j => summand F (pair c (BinaryNatCode.encode j))) (fun _ _ => rfl)
  refine E.congr (funext fun c => ?_)
  simp only [Ternary.count_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact congrArg SignStatisticBits.integerCode (by
    simpa only [BinaryNatCode.encode] using sum_eq_scaledCount F c)

def positiveLanguage (F : Family) : Language := {c | 0 < scaledCount F c}

def realizableLanguage (F : Family) : Language := {c | ∃ x : ℝ,
  ((F.root c).map (algebraMap ℤ ℝ)).eval x = 0 ∧
    ∀ i : Fin (Nat.fromBitsLE (F.count c)),
      SignType.sign (((F.polynomial c i.val).map (algebraMap ℤ ℝ)).eval x) = F.pattern c i.val}

def guardedRealizableLanguage (F : Family) : Language := {c | F.root c ≠ 0 ∧ c ∈ realizableLanguage F}

theorem positive_iff_realizable (F : Family) (c : List Bool) (hp : F.root c ≠ 0) :
    c ∈ positiveLanguage F ↔ c ∈ realizableLanguage F := by
  have hi : Function.Injective (algebraMap ℤ ℝ) := by
    intro x y h
    exact Int.cast_injective h
  have hr : (F.root c).map (algebraMap ℤ ℝ) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hp
  simpa only [positiveLanguage, realizableLanguage, Set.mem_ofPred_eq, scaledCount] using
    RootSignQueries.scaledRootCount_pos_iff ((F.root c).map (algebraMap ℤ ℝ)) hr
      (fun i : Fin (Nat.fromBitsLE (F.count c)) => (F.polynomial c i.val).map (algebraMap ℤ ℝ))
      (fun i => F.pattern c i.val)

theorem positiveLanguage_eq_guarded (F : Family) : positiveLanguage F = guardedRealizableLanguage F := by
  ext c
  by_cases hp : F.root c = 0
  · simp only [positiveLanguage, guardedRealizableLanguage, Set.mem_ofPred_eq, scaledCount, hp,
      Polynomial.map_zero, RootSignQueries.scaledRootCount_zero_left, lt_self_iff_false, ne_eq,
      not_true_eq_false, false_and]
  · simp only [guardedRealizableLanguage, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨hp, (positive_iff_realizable F c hp).mp h⟩
    · intro h
      exact (positive_iff_realizable F c hp).mpr h.2

noncomputable def positiveDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceDecider (positiveLanguage F) := by
  have hflag := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (evaluator a hF hs H P).decider (fun v => decide (pairFst v ≠ [])) hflag
  intro c
  simp only [positiveLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, TarskiQueryBits.integerCode_fst_zero_iff]
  omega

theorem positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    positiveLanguage F ∈ PSPACE := (positiveDecider a hF hs H P).mem_PSPACE

theorem guardedRealizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    guardedRealizableLanguage F ∈ PSPACE := by
  rw [← positiveLanguage_eq_guarded]
  exact positiveLanguage_mem_PSPACE a hF hs H P

theorem realizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient)
    (hp : ∀ c, F.root c ≠ 0) : realizableLanguage F ∈ PSPACE := by
  have h : positiveLanguage F = realizableLanguage F := by
    ext c
    exact positive_iff_realizable F c (hp c)
  rw [← h]
  exact positiveLanguage_mem_PSPACE a hF hs H P

end LeanCanny.Algebra.SignPatternBits
