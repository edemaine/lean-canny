/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationModularTop
public import LeanCanny.Algebra.IntegralMixedNormalizationTopPowerSnapshot
public import LeanCanny.Computation.NativeTwoCallBranch
/-! # A normalization inverse term multiplies two charged recursive replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.mulMod

def termLeft (P : Parameters) := IntegralCriticalFlatEulerBits.next P .frozenPowerTerm

def termRight (P : Parameters) (z : List Bool) := IntegralCriticalFlatEulerBits.next P .derivativeCoefficient (pairFst z)

def multiplyPost (P : Parameters) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))

theorem multiplyPost_FP (P : Parameters) (a : Access P) : multiplyPost P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact mem_FP_comp (f := fun z => pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))
    (g := BinaryNat.mulMod) (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

noncomputable def inverseTermValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff
    (get P .target q) : ℤ) : ZMod (modulus P q)) *
      ((modularTop P F q ^ get P .target q) (topRow P F q) (topCol P F q)))

theorem inverseTerm_result (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (hi : answer (termLeft P q) = inverseValue P F q)
    (hp : answer (termRight P (pair q (answer (termLeft P q)))) = topPowerValue P F q) :
    DependentTwoCall.result (termLeft P) (termRight P) (multiplyPost P) answer q = inverseTermValue P F q := by
  unfold DependentTwoCall.result
  rw [hp, hi]
  simp only [multiplyPost, pairFst_pair, pairSnd_pair]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact ArithmeticBits.mulMod_residueBits _ _ _

abbrev InverseMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .frozenPowerTerm q → get P .target q ≤ matrixDimension P F q → answer q = inverseValue P F q

abbrev TopPowerMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .derivativeCoefficient q → answer q = topPowerValue P F q

noncomputable def selected10 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .frozenPowerSum q && decide (get P .target q ≤ matrixDimension P F q)

theorem selected10_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected10 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .frozenPowerSum)).and
    ((get_binary P a .target).le (matrixDimension_binary P a F h))).flag_mem_FP
    (fun q => by cases hb : selected P .frozenPowerSum q <;>
      by_cases hk : get P .target q ≤ matrixDimension P F q <;> simp [selected10, hb, hk])

theorem selected10_iff (P : Parameters) (F : Family) (q : List Bool) : selected10 P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .frozenPowerSum q) ∧
      get P .target q ≤ matrixDimension P F q := by
  simp only [selected10, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

noncomputable def stage10 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofTwoCalls (termLeft P) (termRight P) (multiplyPost P)
    (IntegralCriticalFlatEulerBits.next_FP P a .frozenPowerTerm)
    (mem_FP_comp pairFst_mem_FP (IntegralCriticalFlatEulerBits.next_FP P a .derivativeCoefficient)) (multiplyPost_FP P a)
    (selected10 P F) (selected10_FP P a F h) (inverseTermValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct10 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (x : (q : List Bool) → ZMod (modulus P q))
    (hi : InverseMatches P F (fun q => residueBits (x q)))
    (hp : TopPowerMatches P F (fun q => residueBits (x q))) :
    Correct (stage10 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · intro q hq
    have H := (selected10_iff P F q).mp hq
    apply inverseTerm_result
    · have HD : matrixDimension P F (termLeft P q) = matrixDimension P F q :=
        congrArg (dimension F) (saved_next P .frozenPowerTerm q)
      have HK : get P .target (termLeft P q) ≤ matrixDimension P F (termLeft P q) := by
        rw [HD, show get P .target (termLeft P q) = get P .target q from IntegralCriticalFlatEulerBits.next_get P .frozenPowerTerm q .target]
        exact H.2
      exact (hi _ (next_valid P .frozenPowerTerm q H.1.1) ((next_routine P .frozenPowerTerm q).trans H.1.2.1)
        (IntegralCriticalFlatEulerBits.next_phase P .frozenPowerTerm q) HK).trans (inverseValue_next P F .frozenPowerTerm q)
    · change residueBits (x (IntegralCriticalFlatEulerBits.next P .derivativeCoefficient (pairFst (pair q _)))) = _
      rw [pairFst_pair]
      exact (hp _ (next_valid P .derivativeCoefficient q H.1.1) ((next_routine P .derivativeCoefficient q).trans H.1.2.1)
        (IntegralCriticalFlatEulerBits.next_phase P .derivativeCoefficient q)).trans (topPower_next P F .derivativeCoefficient q)
  · intro q _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (termLeft P q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (IntegralCriticalFlatEulerBits.next_root P .frozenPowerTerm q))
  · intro q _
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q c budget hq hc
    have H := (selected10_iff P F q).mp hq
    have HP := H.1.2.2
    change phase q = 10 at HP
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hc with hl | hr
    · rw [hl]
      exact next_frame P .frozenPowerTerm q (by change 9 < phase q; omega)
    · rw [hr]
      unfold termRight
      rw [pairFst_pair]
      exact next_frame P .derivativeCoefficient q (by change 1 < phase q; omega)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
