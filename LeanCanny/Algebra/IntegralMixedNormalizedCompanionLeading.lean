/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoefficientQuery
public import LeanCanny.Algebra.IntegralMixedNormalizationReplies
/-! # Normalized producer leading values are charged diagonal coefficient requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leadingPacket (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  pair q (pair (BinaryNatCode.encode (F.degree (IntegralMixedVirtualTaskBits.saved P q))) (pair [] []))

def leadingTask (P : Parameters) (F : Family) : List Bool → List Bool :=
  IntegralMixedCoefficientQueryBits.writer P .normalization .eulerSum ∘ leadingPacket P F

theorem leadingTask_FP (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : leadingTask P F ∈ FP :=
  by
    have HD : BinaryFn (fun q => F.degree (IntegralMixedVirtualTaskBits.saved P q)) :=
      hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
    exact mem_FP_comp (mem_FP_pair id_mem_FP
      (mem_FP_pair HD.bits_mem_FP (constFn_mem_FP (pair [] []))))
      (IntegralMixedCoefficientQueryBits.writer_FP P a .normalization .eulerSum)

theorem leadingTask_fields (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    get P .row (leadingTask P F q) = 0 ∧ get P .col (leadingTask P F q) = 0 ∧
      get P .coefficient (leadingTask P F q) = F.degree (IntegralMixedVirtualTaskBits.saved P q) := by
  have HG (f : Field) := IntegralMixedCoefficientQueryBits.writer_get P .normalization .eulerSum (leadingPacket P F q) f
  have HZ : Nat.fromBitsLE ([] : List Bool) = 0 := rfl
  simp only [leadingPacket, IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord,
    IntegralPowerProductBits.factorWord, pairFst_pair, pairSnd_pair, HZ, BinaryNatCode.encode, Nat.fromBitsLE_bits] at HG
  have HR := HG .row
  have HC := HG .col
  have HK := HG .coefficient
  norm_num only [reduceCtorEq, ite_true, ite_false, Nat.zero_min] at HR HC HK
  exact ⟨HR, HC, HK.trans (min_eq_left (cut_degree_cap P F g q))⟩

theorem leadingTask_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (leadingTask P F q) = IntegralMixedVirtualTaskBits.saved P q := by
  unfold leadingTask
  rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_saved]
  rw [leadingPacket, pairFst_pair]

theorem leadingTask_modulus (P : Parameters) (F : Family) (q : List Bool) :
    modulus P (leadingTask P F q) = modulus P q := by
  unfold leadingTask
  rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_modulus]
  rw [leadingPacket, pairFst_pair]

theorem leadingTask_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    normalizedValue P F (leadingTask P F q) = IntegralMixedNormalizationTopBits.leadingValue P F q := by
  have HF := leadingTask_fields P F g q
  have HA : matrixAxes P F (leadingTask P F q) := by
    unfold matrixAxes
    rw [HF.1, HF.2.1]
    exact ⟨pow_pos (Nat.two_pow_pos _) _, pow_pos (Nat.two_pow_pos _) _⟩
  have HK : get P .coefficient (leadingTask P F q) = F.degree (IntegralMixedVirtualTaskBits.saved P (leadingTask P F q)) := by
    rw [HF.2.2, leadingTask_saved]
  rw [normalizedValue_top P F _ HA HK, HF.1, HF.2.1, ite_eq_left rfl]
  unfold IntegralMixedNormalizationTopBits.leadingValue
  rw [leadingTask_saved, leadingTask_modulus]

abbrev NormalizationMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .eulerSum q → answer q = normalizedValue P F q

theorem normalization_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool)
    (hm : IntegralMixedNormalizationDispatcherBits.Matches P a F h hd height hb answer) : NormalizationMatches P F answer := by
  intro q hv hr hp
  exact (hm q hv hr).trans (IntegralMixedNormalizationDispatcherBits.model_phase14 P a F h hd height hb q hv hr hp)

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧ isPhase p q ∧
    2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 6)).and
      ((isPhase_FP p).and (((BinaryFn.const 2).le (get_binary P a .slot15)).and
        ((get_binary P a .slot15).le (BinaryFn.const 4)))))).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧ isPhase p q ∧
      2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by simp only [selected, decide_eq_true_eq]

def leadingProgram (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := true
  query := leadingTask P F
  immediate _ := []
  finish := pairSnd

theorem leading_controls (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : (leadingProgram P F).Controls :=
  ⟨constFn_mem_FP [true], leadingTask_FP P a F hd, constFn_mem_FP [], pairSnd_mem_FP⟩

noncomputable def leadingStage (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : Machine :=
  ofSingleCall (leadingProgram P F) ((leadingProgram P F).certificates (leading_controls P a F hd))
    (selected P .originalCoefficient) (selected_FP P a .originalCoefficient) (IntegralMixedNormalizationTopBits.leadingValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
