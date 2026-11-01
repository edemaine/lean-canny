/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalCompanionFields
public import LeanCanny.Algebra.IntegralCriticalCoefficientValue

/-! # A total carrier-free scalar companion family

Only valid chronological births select an actual polynomial. Missing
births have zero coefficient data and zero leading scalar. The top
coefficient is represented by its proved integer scalar matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem creating_birth (F : Scripts) (q : List Bool) (h : valid F q) :
    (creatingFamily F q h).birth [] = IntegralCriticalHistoryTask.birth F.toParameters q :=
  creating_older_length F q h

theorem commandAt_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    IntegralCriticalScriptFP.commandAt (IntegralCriticalFlatClearedHeightBits.metadata F) q
      (IntegralCriticalHistoryTask.birth F.toParameters q) = some (chosen (F.rules (root q)) (creatingIndex F q h)) := by
  let G := generatorQueries F (fun _ => q) (fun _ => h)
  have H := IntegralCriticalScriptSelectedFP.commandAt_creating G q
  change (F.rules (root q)).reverse[(older (F.rules (root q)) (creatingIndex F q h)).length]? = _ at H
  rw [creating_older_length] at H
  exact H

theorem commandDegree_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    commandDegree F q = (chosen (F.rules (root q)) (creatingIndex F q h)).degree := by
  unfold commandDegree IntegralCriticalScriptFP.degree
  rw [commandAt_creating F q h]
  rfl

theorem commandOffset_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    commandOffset F q = (chosen (F.rules (root q)) (creatingIndex F q h)).offset.val := by
  unfold commandOffset IntegralCriticalScriptFP.offset
  rw [commandAt_creating F q h]
  rfl

theorem selectedDegree_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    selectedDegree F q = IntegralScalarRootHistoryBounds.degree (creatingFamily F q h) [] := by
  rw [selectedDegree, ite_eq_left h, commandDegree_creating F q h, commandOffset_creating F q h]
  rfl

noncomputable def leadingInteger (F : Scripts) (q : List Bool) : ℤ :=
  if h : valid F q then IntegralHistoryCriticalBits.leadingInteger (creatingFamily F q h) else 0

noncomputable def leading (F : Scripts) (q : List Bool) : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q) :=
  (leadingInteger F q : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))

noncomputable def coefficient (F : Scripts) (q : List Bool) (k : ℕ) :
    Matrix (Fin (oldRank F q)) (Fin (oldRank F q)) (ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) :=
  if k = selectedDegree F q then leading F q • 1 else
    if h : valid F q then fun r t => IntegralHistoryCriticalBits.coefficientEntry (creatingFamily F q h)
      k r.val t.val (IntegralCriticalHistoryTask.modulus F.toParameters q) else 0

noncomputable def family (F : Scripts) : IntegralScalarGeneratorBits.Family where
  width := oldRank F
  scalarDegree := scalarDegree F
  selectedDegree := selectedDegree F
  modulus := IntegralCriticalHistoryTask.modulus F.toParameters
  modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters
  oldRow := oldRow F
  oldCol := oldCol F
  row := scalarRow F
  col := scalarCol F
  coefficient := coefficient F
  leading := leading F
  leading_eq q := by
    change (if selectedDegree F q = selectedDegree F q then _ else _) = _
    exact ite_eq_left rfl

attribute [local irreducible] IntegralHistoryCriticalBits.coefficientEntry IntegralHistoryCriticalBits.leadingInteger
  coefficient leadingInteger leading family

theorem coefficient_creating (F : Scripts) (q : List Bool) (h : valid F q) (k : ℕ) (r t : Fin (oldRank F q)) :
    coefficient F q k r t = IntegralHistoryCriticalBits.coefficientEntry (creatingFamily F q h)
      k r.val t.val (IntegralCriticalHistoryTask.modulus F.toParameters q) := by
  by_cases hk : k = selectedDegree F q
  · subst k
    unfold coefficient leading leadingInteger
    rw [ite_eq_left rfl, dite_eq_left h, selectedDegree_creating F q h,
      IntegralHistoryCriticalBits.coefficientEntry_leading]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have HR : r.val < (IntegralHistoryCriticalBits.source (creatingFamily F q h)).rank [] := by
      change r.val < count ((creatingFamily F q h).birth []) ((creatingFamily F q h).width [])
      rw [creating_birth]
      exact r.isLt
    have HT : t.val < (IntegralHistoryCriticalBits.source (creatingFamily F q h)).rank [] := by
      change t.val < count ((creatingFamily F q h).birth []) ((creatingFamily F q h).width [])
      rw [creating_birth]
      exact t.isLt
    rw [Nat.mod_eq_of_lt HR, Nat.mod_eq_of_lt HT]
    simp only [Fin.ext_iff]
    split_ifs <;> simp only [mul_one, mul_zero]
  · unfold coefficient
    rw [ite_eq_right hk, dite_eq_left h]

attribute [local irreducible] IntegralClearedCriticalLeadingBits.integer IntegralHistoryCriticalBits.source

theorem leading_FP (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) :
    (fun q => residueBits (leading F q)) ∈ FP := by
  have HN : BinaryFn (fun q => (F.rules (root q)).length) := BinaryFn.ofUnary (a.count.comp RankedHistoryTask.root_FP)
  have HI := (HN.sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary (birth_unary F a))
  have HR := bank_denominator_reader_FP
    (fun q => F.cap (root q)) (fun q => F.width (root q)) (fun q => F.ambient (root q))
    (fun q => F.sourceWidth (root q)) (fun q => F.degree (root q)) (fun q => F.height (root q))
    (fun q => F.rules (root q)) (fun q => F.length_le (root q)) (fun q => F.scalar_bound (root q))
    (IntegralCriticalHistoryTask.modulus F.toParameters) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters)
    (IntegralCriticalScriptFP.access (IntegralCriticalFlatClearedHeightBits.metadata F) n)
    (fun q => (F.rules (root q)).length - 1 - IntegralCriticalHistoryTask.birth F.toParameters q) HI
  have HP := (valid_FP F a).ite_mem_FP HR (constFn_mem_FP [])
  refine mem_FP_of_eq HP (fun q => ?_)
  unfold leading
  by_cases h : valid F q
  · simp only [ite_eq_left h]
    let i := creatingIndex F q h
    have HG : (((List.ofFn (run (F.rules (root q)) (F.length_le (root q))
        (F.scalar_bound (root q))).bank.denominator)[i.val]?).getD 0) =
        (run (F.rules (root q)) (F.length_le (root q)) (F.scalar_bound (root q))).bank.denominator i := by
      rw [List.getElem?_ofFn, dite_eq_left i.isLt]
      rfl
    have HE := (origin (F.rules (root q)) (F.scalar_bound (root q)) (F.length_le (root q)) i).denominator_eq
    have HM : (run (F.rules (root q)) (F.length_le (root q)) (F.scalar_bound (root q))).bank.denominator i = leadingInteger F q := by
      unfold leadingInteger
      rw [dite_eq_left h]
      unfold IntegralHistoryCriticalBits.leadingInteger
      exact HE
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) (HG.trans HM)
  · simp only [ite_eq_right h]
    unfold leadingInteger
    rw [dite_eq_right h, Int.cast_zero]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
