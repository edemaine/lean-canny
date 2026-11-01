/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseSumQueries
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseMatrix
public import LeanCanny.Algebra.ModularFoldRecursiveController
/-! # A streamed sum computes the actual inverse normalization matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseSummand (P : Parameters) (F : Family) (q : List Bool) (k : ℕ) : ZMod (modulus P q) :=
  (((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff k : ℤ) : ZMod (modulus P q)) *
    ((modularTop P F q ^ k) (topRow P F q) (topCol P F q))

noncomputable def inverseMatrixValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q)
    (topRow P F q) (topCol P F q) : ZMod (modulus P q))

theorem inverseMatrixValue_sum (P : Parameters) (F : Family) (q : List Bool) :
    inverseMatrixValue P F q = residueBits (∑ k ∈ Finset.range (matrixDimension P F q + 1), inverseSummand P F q k) :=
  congrArg residueBits (inverse_matrix_sum P F q (topRow P F q) (topCol P F q))

def inverseSumCount (P : Parameters) (F : Family) (q : List Bool) : ℕ := matrixDimension P F q + 1

def inverseSumModulus (P : Parameters) (q : List Bool) : List Bool := BinaryNatCode.encode (modulus P q)

def inverseSumProgram (P : Parameters) (F : Family) :=
  ModularFold.RecursiveStage.sumProgram (inverseSumCount P F) (inverseSumModulus P) (termTask P)

theorem inverseSum_modulus (P : Parameters) : (fun q => Nat.fromBitsLE (inverseSumModulus P q)) = modulus P :=
  funext (fun _ => Nat.fromBitsLE_bits _)

theorem inverseSum_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : InverseTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) : (inverseSumProgram P F).value answer q = inverseMatrixValue P F q := by
  have HE := ModularFold.RecursiveStage.sum_partialValueWithModulus (inverseSumCount P F) (inverseSumModulus P)
    (termTask P) answer (modulus P) (inverseSum_modulus P) q (inverseSummand P F q)
    (Nat.pos_of_ne_zero (modulus_ne_zero P q)) (termTask_reply P F g answer hx q hv)
    (inverseSumCount P F q) le_rfl
  exact HE.trans (inverseMatrixValue_sum P F q).symm

def inverseSumStateBound (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat (inverseSumCount P F q)).length + IntegralCriticalHistoryEvaluator.residueWidth P q + 2

theorem inverseSumStateBound_unary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : UnaryFn (inverseSumStateBound P F) := by
  have HC : BinaryFn (inverseSumCount P F) := (matrixDimension_binary P a F h).add (BinaryFn.const 1)
  have HL : UnaryFn (fun q => (encNat (inverseSumCount P F q)).length) :=
    (UnaryFn.length HC.bits_mem_FP).of_eq (fun q => by
      simp only [length_encNat_eq_size, Nat.size_eq_bits_len, BinaryNatCode.encode])
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HL)).add
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)).add (UnaryFn.const 2)

theorem inverseSum_state (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : InverseTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (t : ℕ) :
    (RecursiveFold.encState ((((inverseSumProgram P F).controller.reference answer)^[t])
      ((inverseSumProgram P F).initial q))).length ≤ inverseSumStateBound P F q := by
  apply (inverseSumProgram P F).orbit_length answer q t (IntegralCriticalHistoryEvaluator.residueWidth P q)
  intro k hk
  unfold inverseSumProgram
  rw [ModularFold.RecursiveStage.sum_partialValueWithModulus (inverseSumCount P F) (inverseSumModulus P)
    (termTask P) answer (modulus P) (inverseSum_modulus P) q (inverseSummand P F q)
    (Nat.pos_of_ne_zero (modulus_ne_zero P q)) (termTask_reply P F g answer hx q hv) k hk]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))

noncomputable def stage11 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (inverseSumProgram P F).controller
  certificates := ModularFold.RecursiveStage.sum_certificates _ _ _
    ((matrixDimension_binary P a F h).add (BinaryFn.const 1)) (modulus_binary P a).bits_mem_FP (termTask_FP P a)
  selected := selected P .frozenConstant
  selected_FP := selected_FP P a .frozenConstant
  model := inverseMatrixValue P F
  clock := inverseSumCount P F
  clock_binary := (matrixDimension_binary P a F h).add (BinaryFn.const 1)
  stateBound := inverseSumStateBound P F
  stateBound_unary := inverseSumStateBound_unary P a F h

theorem correct11 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : InverseTermMatches P F answer) :
    Correct (stage11 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (inverseSumProgram P F).halted_after answer q
  · intro q t hq hh
    have H := (selected_iff P .frozenConstant q).mp hq
    exact ((inverseSumProgram P F).output_when_halted answer q t hh).trans (inverseSum_value P F g answer hx q H.1)
  · intro q t hq
    exact inverseSum_state P F g answer hx q ((selected_iff P .frozenConstant q).mp hq).1 t
  · intro q c budget hq hc
    have H := (selected_iff P .frozenConstant q).mp hq
    let C := inverseSumProgram P F
    change C.controller.Requests answer budget q c at hc
    obtain ⟨t, _, _, _, he⟩ := hc
    rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at he
    rw [he]
    change IntegralMixedRoutineTaskBits.Frame P q (termTask P (pair q (BinaryNatCode.encode (min t (C.count q)))))
    have HP := H.2.2
    change phase q = 11 at HP
    have HF := IntegralMixedValueFieldQuery.query_frame_phase P pairFst .normalization .frozenPowerSum .target
      (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode (min t (C.count q))))
      (by simpa only [pairFst_pair, IntegralMixedRoutineTaskBits.Routine.code] using H.2.1)
      (by simp only [pairFst_pair]; change 10 < phase q; omega)
    unfold termTask
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
