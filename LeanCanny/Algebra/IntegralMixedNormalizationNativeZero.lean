/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationZeroQueries
public import LeanCanny.Computation.ControllerPostprocess
/-! # Native normalization coefficient-zero flags with canonical residue codes

Flag tasks use modulus two. Zero coefficients return one; nonzero
coefficients return canonical zero. Other caller moduli are outside this
branch, keeping the global arithmetic answer type unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected7 (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧
    isPhase .originalGridTerm q ∧ modulus P q = 2)

theorem selected7_FP (P : Parameters) (a : Access P) : (fun q => [selected7 P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 5)).and
      ((isPhase_FP .originalGridTerm).and ((modulus_binary P a).eq (BinaryFn.const 2))))).flag_mem_FP

theorem selected7_iff (P : Parameters) (q : List Bool) : selected7 P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .originalGridTerm q ∧ modulus P q = 2 := by
  simp only [selected7, decide_eq_true_eq]

noncomputable def zeroValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if modulus P q = 2 then
    if (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff (get P .coefficient q) = 0 then [true] else []
  else []

theorem zeroValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = zeroValue P F q := by
  unfold zeroValue
  split_ifs with hm hz
  · rw [hm]
    exact ⟨1, by decide⟩
  all_goals exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem normalized_zero_flag (z : ℤ) :
    BinaryNat.normalize [decide (z = 0)] = if z = 0 then [true] else [] := by
  by_cases hz : z = 0
  · simp only [hz, decide_true, ite_true]
    decide
  · simp only [hz, decide_false, ite_false]
    decide

noncomputable def stage7 (P : Parameters) (a : Access P) (F : Family) (height : List Bool → ℕ) (hh : BinaryFn height) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (zeroProgram P height).controller.postprocess BinaryNat.normalize
  certificates := RecursiveController.Controller.postprocess_certificates _
    (IntegerZeroBits.RecursiveStage.certificates _ (rootBudget_binary P a height hh) _ (smallTask_FP P a))
    _ BinaryNat.normalize_mem_FP
  selected := selected7 P
  selected_FP := selected7_FP P a
  model := zeroValue P F
  clock := (zeroProgram P height).count
  clock_binary := ((BinaryFn.const 2).mul (rootBudget_binary P a height hh)).add (BinaryFn.const 4)
  stateBound := IntegerZeroBits.RecursiveStage.stateBound (rootBudget P height)
  stateBound_unary := IntegerZeroBits.RecursiveStage.stateBound_unary _ (rootBudget_binary P a height hh)

theorem correct7 (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (height : List Bool → ℕ) (hb : BinaryFn height)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (answer : List Bool → List Bool) (hx : CharacteristicMatches P F answer) :
    Correct (stage7 P a F height hb) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (zeroProgram P height).halted_after answer q
  · intro q t hq hhhalt
    have H := (selected7_iff P q).mp hq
    change (zeroProgram P height).controller.halted
      (((zeroProgram P height).controller.reference answer)^[t] ((zeroProgram P height).initial q)) = true at hhhalt
    change BinaryNat.normalize ((zeroProgram P height).controller.output
      (((zeroProgram P height).controller.reference answer)^[t] ((zeroProgram P height).initial q))) = _
    rw [(zeroProgram P height).output_when_halted answer q t hhhalt,
      zeroProgram_value P F g height hh hc answer hx q H.1 H.2.1, normalized_zero_flag]
    change _ = zeroValue P F q
    unfold zeroValue
    rw [ite_eq_left H.2.2.2]
  · intro q t _
    exact IntegerZeroBits.RecursiveStage.state_length _ _ answer q t
  · intro q c budget hq hreq
    have H := (selected7_iff P q).mp hq
    change (zeroProgram P height).controller.Requests answer budget q c at hreq
    obtain ⟨i, _, rfl⟩ := IntegerZeroBits.RecursiveStage.requests_cases (rootBudget P height) (smallTask P) answer budget q c hreq
    have HP := H.2.2.1
    change phase q = 7 at HP
    have HF := IntegralMixedNormalizationFieldBits.query_frame P pairFst .productPower
      (fun z => Nat.fromBitsLE (pairSnd z) + 1) (fun z => get P .coefficient (pairFst z))
      (pair q (BinaryNatCode.encode i)) (by simp only [pairFst_pair]; change 6 < phase q; omega)
    unfold smallTask
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
