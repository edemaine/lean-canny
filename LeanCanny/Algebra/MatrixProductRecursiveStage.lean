/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixProductSpace
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStage
public import LeanCanny.Computation.ControllerRequests

/-! # Recursive ordered products through the layered matrix

The existing layered reduction streams arbitrary binary product lengths.
One local power stack suffices; a separate selector requests a factor
entry only across adjacent layers. Neither certificate assumes a factor
evaluator, and the ordering of the factors is unchanged.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixProductBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.succ BinaryNat.div BinaryNat.mod

theorem power_controls (F : Family) (a : Access F) : (powerAccess F a).ControlsPolyTime :=
  ⟨((a.count.add (BinaryFn.const 1)).mul a.width).bits_mem_FP, a.modulus.bits_mem_FP,
    a.count.bits_mem_FP, a.row.bits_mem_FP, ((a.width.mul a.count).add a.col).bits_mem_FP⟩

def adjacent (F : Family) (p : List Bool) : Prop := BinaryNat.succ (rowLayer F p) = colLayer F p
instance (F : Family) (p : List Bool) : Decidable (adjacent F p) := inferInstanceAs (Decidable (_ = _))

theorem adjacent_FP (F : Family) (a : Access F) : FPPred (adjacent F) := by
  obtain ⟨hr, hc, _, _⟩ := query_controls F a
  exact stringEq_fppred (mem_FP_comp hr BinaryNat.succ_mem_FP) hc

noncomputable def entryProgram (F : Family) (task : List Bool → List Bool) : SingleCall.Program where
  request p := decide (adjacent F p)
  query p := task (factorQuery F p)
  immediate _ := []
  finish := pairSnd

theorem entry_controls (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (entryProgram F task).Controls :=
  ⟨(adjacent_FP F a).flag_mem_FP,
    mem_FP_comp (f := factorQuery F) (g := task) (factorQuery_FP F a) ht, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem entry_value (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = a.entry q) (p : List Bool) :
    (entryProgram F task).value answer p = powerEntry F a p := by
  simp only [SingleCall.Program.value, entryProgram, decide_eq_true_eq, pairSnd_pair, he, powerEntry, adjacent]

theorem entry_requests_iff (F : Family) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (entryProgram F task).controller.Requests answer budget p child ↔ adjacent F p ∧ child = task (factorQuery F p) := by
  rw [SingleCall.Program.requests_iff]
  simp only [entryProgram, decide_eq_true_eq]

theorem factorQuery_packet (F : Family) (c : List Bool) (i j : Fin ((F.count c + 1) * F.width c)) :
    factorQuery F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair c (pair (BinaryNatCode.encode i.divNat.val)
        (pair (BinaryNatCode.encode i.modNat.val) (BinaryNatCode.encode j.modNat.val))) := by
  simp only [factorQuery, rowLayer, rowOffset, colOffset, rowWord, colWord,
    pairFst_pair, pairSnd_pair, BinaryNat.div_pair, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem adjacent_packet (F : Family) (c : List Bool) (i j : Fin ((F.count c + 1) * F.width c)) :
    adjacent F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) ↔
      i.divNat.val + 1 = j.divNat.val := by
  simp only [adjacent, rowLayer, colLayer, rowWord, colWord, pairFst_pair, pairSnd_pair,
    BinaryNat.div_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact BinaryNatCode.encode_injective.eq_iff

theorem entry_requests_in_bounds (F : Family) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) (i j : Fin ((F.count c + 1) * F.width c))
    (hreq : (entryProgram F task).controller.Requests answer budget
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) child) :
    ∃ s : Fin (F.count c), ∃ r t : Fin (F.width c), child = task (pair c
      (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) := by
  obtain ⟨ha, hq⟩ := (entry_requests_iff F task answer budget _ child).mp hreq
  rw [adjacent_packet] at ha
  have HJ := j.divNat.isLt
  refine ⟨⟨i.divNat.val, by omega⟩, i.modNat, j.modNat, ?_⟩
  exact hq.trans (congrArg task (factorQuery_packet F c i j))

noncomputable def controller (F : Family) (a : Access F) (task : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) := ModularRecursiveStage.stage (powerAccess F a) task

theorem certificates (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller F a task).Certificates (encQ := encBits) (encS := encBits) :=
  ModularRecursiveStage.certificates (powerAccess F a) (power_controls F a) task ht

theorem clock_binary (F : Family) (a : Access F) : BinaryFn (ModularRecursiveStage.clock F.power) :=
  ModularRecursiveStage.clock_binary (powerAccess F a) (power_controls F a)

theorem stateBound_unary (F : Family) (a : Access F) : UnaryFn (ModularRecursiveStage.stateBound F.power) :=
  ModularRecursiveStage.stateBound_unary (powerAccess F a) (power_controls F a)

variable (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.power.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.power.matrix c i j))

include he

theorem halted_after (c : List Bool) :
    (controller F a task).halted (((controller F a task).reference answer)^[ModularRecursiveStage.clock F.power c]
      ((controller F a task).initial c)) = true :=
  ModularRecursiveStage.halted_after (powerAccess F a) task answer he c

theorem output_when_halted (c : List Bool) (t : ℕ)
    (hh : (controller F a task).halted (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = true) :
    (controller F a task).output (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = F.value c :=
  (ModularRecursiveStage.output_when_halted (powerAccess F a) task answer he c t hh).trans (congrFun F.power_value c)

theorem state_length (c : List Bool) (t : ℕ) :
    (((controller F a task).reference answer)^[t] ((controller F a task).initial c)).length ≤
      ModularRecursiveStage.stateBound F.power c :=
  ModularRecursiveStage.state_length (powerAccess F a) task answer he c t

theorem requests_in_bounds (budget : List Bool → ℕ) (c child : List Bool)
    (hreq : (controller F a task).Requests answer budget c child) :
    ∃ i j : Fin (F.power.dimension c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds (powerAccess F a) task answer he budget c child hreq

end LeanCanny.Algebra.MatrixProductBits.RecursiveStage
