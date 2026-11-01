/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatCoordinateQuery
public import LeanCanny.Algebra.IntegralCriticalFlatGenericPower
public import LeanCanny.Algebra.IntegralFrozenLowerController
/-! # Actual flat frozen-height Fermat terms

Free coordinates return zero locally. A retained coordinate powers its
actual old multiplication matrix and requests only phase 2 height entries.
No height evaluator is used by the native controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFrozenTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

def input (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .slot8 c))
theorem input_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : input P ∈ FP :=
  mem_FP_pair id_mem_FP (IntegralCriticalHistoryTask.get_binary P a .slot8).bits_mem_FP

def free (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) : Prop :=
  IntegralFrozenPowerBits.freePosition S (input P c)
instance (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) :
    Decidable (free P S c) := inferInstanceAs (Decidable (IntegralFrozenPowerBits.freePosition S _))
theorem free_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : FPPred (free P S) :=
  (IntegralFrozenPowerBits.freePosition_fppred S b).comp (input_FP P a)

noncomputable def family (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) : ModularFamily where
  dimension := S.rank
  modulus := S.modulus
  exponent := S.allowance
  row := S.row
  col := S.col
  matrix c := by
    let := S.ring c
    exact (Algebra.leftMulMatrix (S.basis c) (S.height c (IntegralCriticalHistoryTask.get P .slot8 c))).map
      (Int.castRingHom (ZMod (S.modulus c)))
  modulus_ne_zero := S.modulus_ne_zero

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) : ModularAccess (family P S) where
  dimension c := BinaryNatCode.encode (S.rank c)
  modulus c := BinaryNatCode.encode (S.modulus c)
  exponent c := BinaryNatCode.encode (S.allowance c)
  row c := BinaryNatCode.encode (S.row c).val
  col c := BinaryNatCode.encode (S.col c).val
  entry p := b.height (pair (pairFst p) (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .slot8 (pairFst p))) (pairSnd p)))
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq c i j := by
    simp only [pairFst_pair, pairSnd_pair]
    exact b.height_eq c _ i j

theorem controls (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) : (access P S b).ControlsPolyTime :=
  ⟨b.rank.bits_mem_FP, b.modulus.bits_mem_FP, b.allowance.bits_mem_FP, b.row.bits_mem_FP, b.col.bits_mem_FP⟩

theorem family_value (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) :
    (family P S).value c = (IntegralFrozenPowerBits.powerFamily S).value (input P c) := by
  generalize hp : input P c = p
  have HO : pairFst p = c := by rw [← hp]; exact pairFst_pair _ _
  have HW : Nat.fromBitsLE (pairSnd p) = IntegralCriticalHistoryTask.get P .slot8 c := by
    rw [← hp]
    simp only [input, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  let := S.ring (pairFst p)
  rw [IntegralFrozenPowerBits.power_value]
  rw [HW]
  unfold ModularFamily.value
  change residueBits (((Algebra.leftMulMatrix (S.basis (pairFst p))
    (S.height (pairFst p) (IntegralCriticalHistoryTask.get P .slot8 (pairFst p)))).map
    (Int.castRingHom (ZMod (S.modulus (pairFst p)))) ^ S.allowance (pairFst p))
    (S.row (pairFst p)) (S.col (pairFst p))) = _
  rw [← Matrix.map_pow, Matrix.map_apply, ← map_pow]
  rfl

def zero : SingleCall.Program where
  request _ := false
  query _ := []
  immediate _ := []
  finish := pairSnd
theorem zero_controls : zero.Controls :=
  ⟨constFn_mem_FP [false], constFn_mem_FP [], constFn_mem_FP [], pairSnd_mem_FP⟩

noncomputable def powerController (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) :=
  IntegralCriticalFlatGenericPowerBits.controller P (access P S b) .clearedHeight
noncomputable def controller (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) :=
  RecursiveController.Controller.choose (fun c => decide (free P S c)) zero.controller (powerController P S b)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) :
    (controller P S b).Certificates (encQ := encBits)
      (encS := RecursiveController.Controller.encChoice SingleCall.encState encBits) :=
  RecursiveController.Controller.choose_certificates _ _ _ (free_FP P a S b).computable
    (zero.certificates zero_controls)
    (IntegralCriticalFlatGenericPowerBits.certificates P a (access P S b) (controls P S b) .clearedHeight)

noncomputable def clock (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) : ℕ :=
  if free P S c then 0 else ModularRecursiveStage.clock (family P S) c
theorem clock_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : BinaryFn (clock P S) :=
  BinaryFn.ite (free_FP P a S b) (BinaryFn.const 0) (ModularRecursiveStage.clock_binary (access P S b) (controls P S b))

abbrev RepliesAt (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ¬free P S c → IntegralCriticalFlatGenericPowerBits.RepliesAt P (family P S) .clearedHeight answer c

theorem zero_orbit (answer : List Bool → List Bool) (c : List Bool) (t : ℕ) :
    (zero.controller.reference answer)^[t] (SingleCall.Program.initial c) = SingleCall.Program.initial c := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [zero.reference_iterate]
    rfl

theorem halted_after_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) :
    (controller P S b).halted (((controller P S b).reference answer)^[clock P S c] ((controller P S b).initial c)) = true := by
  rw [controller, RecursiveController.Controller.choose_halted_iterate]
  by_cases hf : free P S c
  · simp only [hf, decide_true, ite_true, clock]
    rfl
  · simp only [hf, decide_false, Bool.false_eq_true, ite_false, clock]
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local P (access P S b) .clearedHeight answer c (he hf)

theorem value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ)
    (hh : (controller P S b).halted (((controller P S b).reference answer)^[t] ((controller P S b).initial c)) = true) :
    (controller P S b).output (((controller P S b).reference answer)^[t] ((controller P S b).initial c)) =
      IntegralFrozenPowerBits.termProgram S (input P c) := by
  rw [controller, RecursiveController.Controller.choose_output_iterate]
  rw [controller, RecursiveController.Controller.choose_halted_iterate] at hh
  by_cases hf : free P S c
  · simp only [hf, decide_true, ite_true] at hh ⊢
    rw [show zero.controller.initial c = SingleCall.Program.initial c from rfl, zero_orbit]
    change [] = if IntegralFrozenPowerBits.freePosition S (input P c) then [] else _
    exact (ite_eq_left hf).symm
  · simp only [hf, decide_false, Bool.false_eq_true, ite_false] at hh ⊢
    have HV := IntegralCriticalFlatGenericPowerBits.output_when_halted_local P (access P S b) .clearedHeight answer c (he hf) t hh
    rw [family_value] at HV
    exact HV.trans (ite_eq_right hf).symm

noncomputable def stateBound (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) : ℕ :=
  12 + 2 * (2 * c.length + 4 + ModularRecursiveStage.stateBound (family P S) c)

theorem stateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) : UnaryFn (stateBound P S) :=
  (UnaryFn.const 12).add ((UnaryFn.const 2).mul
    ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add
      (ModularRecursiveStage.stateBound_unary (access P S b) (controls P S b))))

theorem state_length_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ) :
    (RecursiveController.Controller.encChoice SingleCall.encState encBits
      (((controller P S b).reference answer)^[t] ((controller P S b).initial c))).length ≤ stateBound P S c := by
  have H := RecursiveController.Controller.choose_state_length (fun c => decide (free P S c))
    zero.controller (powerController P S b) SingleCall.encState encBits answer c t
    (2 * c.length + 4 + ModularRecursiveStage.stateBound (family P S) c)
  have HA : decide (free P S c) = true →
      (SingleCall.encState ((zero.controller.reference answer)^[t] (zero.controller.initial c))).length ≤
        2 * c.length + 4 + ModularRecursiveStage.stateBound (family P S) c := by
    intro _
    have HZ := zero.state_length_of_bound answer c t 0 (by intro hr; change false = true at hr; cases hr)
    change (SingleCall.encState ((zero.controller.reference answer)^[t] (SingleCall.Program.initial c))).length ≤ _
    omega
  have HB : decide (free P S c) = false →
      (encBits (((powerController P S b).reference answer)^[t] ((powerController P S b).initial c))).length ≤
        2 * c.length + 4 + ModularRecursiveStage.stateBound (family P S) c := by
    intro hf
    have HN : ¬free P S c := of_decide_eq_false hf
    have HP := IntegralCriticalFlatGenericPowerBits.state_length_local P (access P S b) .clearedHeight answer c (he HN) t
    simpa only [encBits_apply, powerController] using HP.trans (Nat.le_add_left _ _)
  have HH := H HA HB
  have HZ : (SingleCall.encState (default : SingleCall.State)).length = 4 := rfl
  have HP : (encBits (default : List Bool)).length = 0 := rfl
  rw [HZ, HP] at HH
  unfold controller stateBound
  omega

theorem requests_in_bounds_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c)
    (budget : List Bool → ℕ) (child : List Bool) (hc : (controller P S b).Requests answer budget c child) :
    ∃ r t : Fin (S.rank c), child = IntegralCriticalFlatMatrixQuery.writer P .clearedHeight
      (pair c (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) := by
  rw [controller, RecursiveController.Controller.choose_requests_iff] at hc
  by_cases hf : free P S c
  · simp only [hf, decide_true, ite_true] at hc
    rw [SingleCall.Program.requests_iff] at hc
    have HF : zero.request c = false := rfl
    rw [HF] at hc
    exact False.elim (Bool.false_ne_true hc.1)
  · simp only [hf, decide_false, Bool.false_eq_true, ite_false] at hc
    exact IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P (access P S b) .clearedHeight answer c (he hf) budget child hc

theorem requests_rank_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c)
    (budget : List Bool → ℕ) (child : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .frozenPowerTerm c)
    (hc : (controller P S b).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨r, t, rfl⟩ := requests_in_bounds_local P S b answer c he budget child hc
  have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .clearedHeight
    (pair c (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  simp only [pairFst_pair] at H
  apply H
  change IntegralCriticalHistoryTask.phase c = 9 at hp
  change 2 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c)
    (budget : List Bool → ℕ) (root child : List Bool) (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P S b).Requests answer budget c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨r, t, rfl⟩ := requests_in_bounds_local P S b answer c he budget child hc
  apply IntegralCriticalFlatMatrixQuery.writer_tasks
  simpa only [pairFst_pair] using ht

end LeanCanny.Algebra.IntegralCriticalFlatFrozenTermBits
