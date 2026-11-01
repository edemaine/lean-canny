/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationIndexQueries
/-! # Native trailing indices remain canonical arithmetic answers

Index tasks carry a modulus greater than the matrix dimension. Their
natural trailing index then fits that modulus without losing information.
All coefficient-zero children explicitly use modulus two.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected8 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧
    isPhase .clearedGridSum q ∧ matrixDimension P F q < modulus P q)

theorem selected8_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (fun q => [selected8 P F q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 5)).and
      ((isPhase_FP .clearedGridSum).and ((matrixDimension_binary P a F h).lt (modulus_binary P a))))).flag_mem_FP

theorem selected8_iff (P : Parameters) (F : Family) (q : List Bool) : selected8 P F q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .clearedGridSum q ∧ matrixDimension P F q < modulus P q := by
  simp only [selected8, decide_eq_true_eq]

noncomputable def indexValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if matrixDimension P F q < modulus P q then
    BinaryNatCode.encode (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree
  else []

theorem indexValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = indexValue P F q := by
  unfold indexValue
  split_ifs with hm
  · let k := (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree
    have HK : k < modulus P q := by
      have HD := (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree_le_natDegree
      rw [characteristic_natDegree] at HD
      exact HD.trans_lt hm
    refine ⟨(k : ZMod (modulus P q)), ?_⟩
    unfold residueBits
    rw [ZMod.val_natCast_of_lt HK]
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

noncomputable def stage8 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := LowestCoefficientBits.RecursiveStage.controller (matrixDimension P F) (zeroTask P)
  certificates := LowestCoefficientBits.RecursiveStage.certificates _ (matrixDimension_binary P a F h) _ (zeroTask_FP P a)
  selected := selected8 P F
  selected_FP := selected8_FP P a F h
  model := indexValue P F
  clock q := matrixDimension P F q + 1
  clock_binary := (matrixDimension_binary P a F h).add (BinaryFn.const 1)
  stateBound := LowestCoefficientBits.RecursiveStage.stateBound (matrixDimension P F)
  stateBound_unary := LowestCoefficientBits.RecursiveStage.stateBound_unary _ (matrixDimension_binary P a F h)

theorem correct8 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : ZeroMatches P F answer) :
    Correct (stage8 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact LowestCoefficientBits.RecursiveStage.halted_after _ _ answer q
  · intro q t hq hhhalt
    have H := (selected8_iff P F q).mp hq
    have HE := LowestCoefficientBits.RecursiveStage.output_when_halted_flags (matrixDimension P F) (zeroTask P) answer q
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly (by rw [characteristic_natDegree])
      (zeroTask_truth P F g answer hx q H.1 H.2.1) t hhhalt
    change _ = indexValue P F q
    exact HE.trans (by unfold indexValue; rw [ite_eq_left H.2.2.2])
  · intro q t _
    exact LowestCoefficientBits.RecursiveStage.state_length_any _ _ answer q t
  · intro q c budget hq hreq
    have H := (selected8_iff P F q).mp hq
    obtain ⟨i, _, rfl⟩ := LowestCoefficientBits.RecursiveStage.requests_cases (matrixDimension P F) (zeroTask P) answer budget q c hreq
    have HP := H.2.2.1
    change phase q = 8 at HP
    have HF := IntegralMixedNormalizationFieldBits.query_frame P pairFst .originalGridTerm (fun _ => 2)
      (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode i))
      (by simp only [pairFst_pair]; change 7 < phase q; omega)
    unfold zeroTask
    simpa only [pairFst_pair] using HF

theorem indexTask_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) : indexValue P F (indexTask P F q) =
      BinaryNatCode.encode (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree := by
  have HS : IntegralMixedVirtualTaskBits.saved P (indexTask P F q) = IntegralMixedVirtualTaskBits.saved P q :=
    IntegralMixedNormalizationFieldBits.query_saved P id .clearedGridSum _ _ q
  have HD : matrixDimension P F (indexTask P F q) = matrixDimension P F q := congrArg (dimension F) HS
  unfold indexValue
  rw [indexTask_modulus P F g q hv, HD, ite_eq_left (Nat.lt_succ_self _), HS]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
