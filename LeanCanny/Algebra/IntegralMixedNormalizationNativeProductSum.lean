/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationProductSumQueries
/-! # Native finite matrix products for actual normalized coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

def productSumProgram (P : Parameters) (F : Family) :=
  ModularFold.RecursiveStage.sumProgram (matrixDimension P F) (inverseSumModulus P) (productLoopTask P)

theorem productSum_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ProductTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (ha : matrixAxes P F q) :
    (productSumProgram P F).value answer q = productValue P F q := by
  have HE := ModularFold.RecursiveStage.sum_partialValueWithModulus (matrixDimension P F) (inverseSumModulus P)
    (productLoopTask P) answer (modulus P) (inverseSum_modulus P) q (productSummand P F q)
    (Nat.pos_of_ne_zero (modulus_ne_zero P q)) (productLoop_reply P F g answer hx q hv ha)
    (matrixDimension P F q) le_rfl
  exact HE.trans (productValue_sum P F q ha).symm

def productSumStateBound (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat (matrixDimension P F q)).length + IntegralCriticalHistoryEvaluator.residueWidth P q + 2

theorem productSumStateBound_unary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : UnaryFn (productSumStateBound P F) := by
  have HL : UnaryFn (fun q => (encNat (matrixDimension P F q)).length) :=
    (UnaryFn.length (matrixDimension_binary P a F h).bits_mem_FP).of_eq (fun q => by
      simp only [length_encNat_eq_size, Nat.size_eq_bits_len, BinaryNatCode.encode])
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HL)).add
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)).add (UnaryFn.const 2)

theorem productSum_state (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ProductTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (ha : matrixAxes P F q) (t : ℕ) :
    (RecursiveFold.encState ((((productSumProgram P F).controller.reference answer)^[t])
      ((productSumProgram P F).initial q))).length ≤ productSumStateBound P F q := by
  apply (productSumProgram P F).orbit_length answer q t (IntegralCriticalHistoryEvaluator.residueWidth P q)
  intro k hk
  unfold productSumProgram
  rw [ModularFold.RecursiveStage.sum_partialValueWithModulus (matrixDimension P F) (inverseSumModulus P)
    (productLoopTask P) answer (modulus P) (inverseSum_modulus P) q (productSummand P F q)
    (Nat.pos_of_ne_zero (modulus_ne_zero P q)) (productLoop_reply P F g answer hx q hv ha) k hk]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))

noncomputable def selected13 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .coordinateGradientProduct q && decide (matrixAxes P F q)

theorem selected13_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected13 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .coordinateGradientProduct)).and
    (((get_binary P a .row).lt (matrixDimension_binary P a F h)).and
      ((get_binary P a .col).lt (matrixDimension_binary P a F h)))).flag_mem_FP
    (fun q => by cases hb : selected P .coordinateGradientProduct q <;> simp [selected13, matrixAxes, hb])

theorem selected13_iff (P : Parameters) (F : Family) (q : List Bool) : selected13 P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .coordinateGradientProduct q) ∧ matrixAxes P F q := by
  simp only [selected13, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

noncomputable def stage13 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (productSumProgram P F).controller
  certificates := ModularFold.RecursiveStage.sum_certificates _ _ _ (matrixDimension_binary P a F h)
    (modulus_binary P a).bits_mem_FP (productLoopTask_FP P a)
  selected := selected13 P F
  selected_FP := selected13_FP P a F h
  model := productValue P F
  clock := matrixDimension P F
  clock_binary := matrixDimension_binary P a F h
  stateBound := productSumStateBound P F
  stateBound_unary := productSumStateBound_unary P a F h

theorem correct13 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ProductTermMatches P F answer) :
    Correct (stage13 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (productSumProgram P F).halted_after answer q
  · intro q t hq hh
    have H := (selected13_iff P F q).mp hq
    exact ((productSumProgram P F).output_when_halted answer q t hh).trans (productSum_value P F g answer hx q H.1.1 H.2)
  · intro q t hq
    have H := (selected13_iff P F q).mp hq
    exact productSum_state P F g answer hx q H.1.1 H.2 t
  · intro q c budget hq hc
    have H := (selected13_iff P F q).mp hq
    let C := productSumProgram P F
    change C.controller.Requests answer budget q c at hc
    obtain ⟨t, _, _, _, he⟩ := hc
    rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at he
    rw [he]
    change IntegralMixedRoutineTaskBits.Frame P q (productLoopTask P (pair q (BinaryNatCode.encode (min t (C.count q)))))
    have HP := H.1.2.2
    change phase q = 13 at HP
    have HF := IntegralMixedValueFieldQuery.query_frame_phase P pairFst .normalization .frozenLower .target
      (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode (min t (C.count q))))
      (by simpa only [pairFst_pair, IntegralMixedRoutineTaskBits.Routine.code] using H.1.2.1)
      (by simp only [pairFst_pair]; change 12 < phase q; omega)
    unfold productLoopTask
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
