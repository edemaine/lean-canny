/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseController
/-! # A native adaptive stage computes the actual inverse coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def selected9 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .frozenPowerTerm q && decide (get P .target q ≤ matrixDimension P F q)

theorem selected9_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected9 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .frozenPowerTerm)).and
    ((get_binary P a .target).le (matrixDimension_binary P a F h))).flag_mem_FP
    (fun q => by cases hb : selected P .frozenPowerTerm q <;>
      by_cases hk : get P .target q ≤ matrixDimension P F q <;> simp [selected9, hb, hk])

theorem selected9_iff (P : Parameters) (F : Family) (q : List Bool) : selected9 P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .frozenPowerTerm q) ∧
      get P .target q ≤ matrixDimension P F q := by
  simp only [selected9, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

def inverseStateBound (P : Parameters) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat 2).length + IntegralCriticalHistoryEvaluator.residueWidth P q + 2

theorem inverseStateBound_unary (P : Parameters) (a : Access P) : UnaryFn (inverseStateBound P) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const (2 * (encNat 2).length))).add
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a) |>.add (UnaryFn.const 2)

noncomputable def stage9 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := DependentTwoCall.controller (indexTask P F) (inverseTask P) (inversePost P)
  certificates := DependentTwoCall.certificates _ _ _ (indexTask_FP P a F h) (inverseTask_FP P a) (inversePost_FP P a)
  selected := selected9 P F
  selected_FP := selected9_FP P a F h
  model := inverseValue P F
  clock _ := 2
  clock_binary := BinaryFn.const 2
  stateBound := inverseStateBound P
  stateBound_unary := inverseStateBound_unary P a

theorem inverseValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = inverseValue P F q := ⟨_, rfl⟩

theorem correct9 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hi : IndexMatches P F (fun q => residueBits (x q)))
    (hc : CharacteristicMatches P F (fun q => residueBits (x q))) :
    Correct (stage9 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact DependentTwoCall.halted_after _ _ _ _ q
  · intro q t hq hh
    have H := (selected9_iff P F q).mp hq
    exact (DependentTwoCall.output_when_halted _ _ _ _ q t hh).trans
      (inverse_result P F g _ hi hc q H.1.1 H.1.2.1 H.2)
  · intro q t hq
    have H := (selected9_iff P F q).mp hq
    have HS := DependentTwoCall.state_length (indexTask P F) (inverseTask P) (inversePost P)
      (fun q => residueBits (x q)) q t
    rw [inverse_result P F g _ hi hc q H.1.1 H.1.2.1 H.2] at HS
    have HL := IntegralCriticalHistoryEvaluator.answer_length P x (indexTask P F q)
    have HR : RankedHistoryTask.root (indexTask P F q) = RankedHistoryTask.root q :=
      IntegralMixedNormalizationFieldBits.query_root P id .clearedGridSum _ _ q
    have HL' : (residueBits (x (indexTask P F q))).length ≤ IntegralCriticalHistoryEvaluator.residueWidth P q :=
      HL.trans_eq (congrArg (fun r => (numericCap P r).size) HR)
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    have HV : (inverseValue P F q).length ≤ IntegralCriticalHistoryEvaluator.residueWidth P q := by
      exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
    change _ ≤ inverseStateBound P q
    unfold inverseStateBound
    exact HS.trans (by omega)
  · intro q c budget hq hreq
    have H := (selected9_iff P F q).mp hq
    have HP := H.1.2.2
    change phase q = 9 at HP
    rcases DependentTwoCall.requests_cases (indexTask P F) (inverseTask P) (inversePost P)
      (fun q => residueBits (x q)) budget q c hreq with hl | hr
    · rw [hl]
      unfold indexTask
      exact IntegralMixedNormalizationFieldBits.query_frame P id .clearedGridSum _ _ q
        (by simp only [id_eq]; change 8 < phase q; omega)
    · rw [hr]
      unfold inverseTask
      have HF := IntegralMixedNormalizationFieldBits.query_frame P pairFst .productPower
        (fun z => modulus P (pairFst z)) (inverseIndex P)
        (pair q (residueBits (x (indexTask P F q))))
        (by simp only [pairFst_pair]; change 6 < phase q; omega)
      simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
