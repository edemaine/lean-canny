/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzFactorChildBounds

/-!
# The suspended determinant controller

The ideal layered-entry function is used only to state the contracted parent
semantics. Physical transitions instead run the certified factor child while
retaining the outer controller packet.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.Suspended
open Complexity
open LeanCanny.Encoding
open MatrixPower
open LeanCanny.Computation

def dimension (a : FactorChild.Access) (c : List Bool) : List Bool :=
  let w := BinaryNat.succ (a.dimension c)
  BinaryNat.mul (pair w w)

def target (a : FactorChild.Access) (c : List Bool) : List Bool :=
  BinaryNat.mul (pair (a.dimension c) (BinaryNat.succ (a.dimension c)))

def computedEntry (a : FactorChild.Access) (p : List Bool) : List Bool :=
  FactorChild.output a ((FactorChild.advance a)^[FactorChild.time a p] (FactorChild.start a p))

def ops (a : FactorChild.Access) : Controller.Callbacks :=
  Controller.modularCallbacks (dimension a) a.modulus (computedEntry a)

def program (a : FactorChild.Access) : SubroutineIteration.Program :=
  Controller.entryProgram (ops a) (FactorChild.start a) (FactorChild.advance a)
    FactorChild.halted (FactorChild.output a)

def childTime (a : FactorChild.Access) (p : List Bool) : ℕ :=
  FactorChild.time a (Controller.entryInput p)

def init (a : FactorChild.Access) : List Bool → List Bool :=
  Controller.initialPacket a.dimension (fun _ => []) (target a)

def parentTime (n : ℕ) : ℕ := MatrixPower.work ((n + 1) * (n + 1)) n.size n + 1

theorem dimension_mem_FP (a : FactorChild.Access) (ha : a.PolyTime) : dimension a ∈ FP := by
  have hw := mem_FP_comp ha.dimension BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hw hw) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := dimension a) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem target_mem_FP (a : FactorChild.Access) (ha : a.PolyTime) : target a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.dimension
    (mem_FP_comp ha.dimension BinaryNat.succ_mem_FP)) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := target a) h ?_
  intro c
  simp only [Function.comp_apply, target]

theorem ops_controls_polyTime (a : FactorChild.Access) (ha : a.PolyTime) :
    (ops a).ControlsPolyTime := by
  have h := Controller.modularCallbacks_polyTime (dimension_mem_FP a ha) ha.modulus
    (constFn_mem_FP [])
  constructor
  · simpa only [ops, Controller.modularCallbacks] using h.dimension
  · simpa only [ops, Controller.modularCallbacks] using h.zero
  · simpa only [ops, Controller.modularCallbacks] using h.one
  · simpa only [ops, Controller.modularCallbacks] using h.combine

theorem program_polyTime (a : FactorChild.Access) (ha : a.PolyTime) : (program a).PolyTime :=
  Controller.entryProgram_polyTime _ (ops_controls_polyTime a ha)
    (FactorChild.start_mem_FP a ha) (FactorChild.advance_mem_FP a ha)
    FactorChild.halted_mem_FP (FactorChild.output_mem_FP a ha)

theorem init_mem_FP (a : FactorChild.Access) (ha : a.PolyTime) : init a ∈ FP :=
  Controller.initialPacket_mem_FP ha.dimension (constFn_mem_FP []) (target_mem_FP a ha)

theorem dimension_code (a : FactorChild.Access) (c : List Bool) (n : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    dimension a c = BinaryNatCode.encode ((n + 1) * (n + 1)) := by
  simp only [dimension, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem target_code (a : FactorChild.Access) (c : List Bool) (n : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    target a c = BinaryNatCode.encode (n * (n + 1)) := by
  simp only [target, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem init_encode (a : FactorChild.Access) (c : List Bool) (m n : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    init a c = pair c (stateBits (residueBits (m := m)) (.eval (powerQuery n 0) [])) := by
  apply Controller.initialPacket_encode a.dimension (fun _ => []) (target a) c
    (residueBits (m := m)) n (powerQuery n 0).row (powerQuery n 0).col hd
  · simp [powerQuery, finProdFinEquiv, BinaryNatCode.encode]
  · simpa [powerQuery, finProdFinEquiv, Nat.mul_comm] using target_code a c n hd

theorem ops_correctAt (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) :
    Controller.CorrectAt (ops a) c (powerMatrix A) residueBits := by
  exact Controller.modularCallbacks_correctAt _ _ _ c m (powerMatrix A)
    (dimension_code a c n hb.dimension) hb.modulus (FactorChild.run_packet a c m n A hb)

theorem step_eq (a : FactorChild.Access) (p : List Bool) :
    SubroutineIteration.abstractStep (program a) (childTime a) p = Controller.step (ops a) p := by
  have ho : FactorChild.output a
      ((FactorChild.advance a)^[childTime a p] (FactorChild.start a (Controller.entryInput p))) =
        (ops a).entry (Controller.entryInput p) := by
    simp only [ops, Controller.modularCallbacks, computedEntry, childTime]
  have h := Controller.entryProgram_abstractStep (ops a) (FactorChild.start a)
    (FactorChild.advance a) FactorChild.halted (FactorChild.output a) (childTime a) p (fun _ => ho)
  exact h

theorem iterate_eq (a : FactorChild.Access) (p : List Bool) (u : ℕ) :
    (SubroutineIteration.abstractStep (program a) (childTime a))^[u] p =
      (Controller.step (ops a))^[u] p := by
  rw [show SubroutineIteration.abstractStep (program a) (childTime a) = Controller.step (ops a)
    from funext (step_eq a)]

theorem entryInput_state {R : Type*} {n : ℕ} (c : List Bool) (enc : R → List Bool)
    (st : State R n) (hr : Controller.needsEntry (pair c (stateBits enc st)) = true) :
    ∃ i j : Fin n, Controller.entryInput (pair c (stateBits enc st)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  cases st with
  | eval q stack => exact ⟨q.row, q.col, Controller.entryInput_eval c enc q stack⟩
  | ret x stack => simp [Controller.needsEntry, stateBits] at hr
  | done x => simp [Controller.needsEntry, stateBits] at hr

theorem requested_packet (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) (u : ℕ)
    (hr : (program a).request
      ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) = true) :
    ∃ i j : Fin ((n + 1) * (n + 1)),
      Controller.entryInput
        ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) =
          pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  rw [iterate_eq, init_encode a c m n hb.dimension,
    Controller.iterate_packet _ c (powerMatrix A) residueBits (ops_correctAt a c m n A hb)] at hr ⊢
  exact entryInput_state c residueBits _ hr

theorem requested_first_halt (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) (u : ℕ)
    (hr : (program a).request
      ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) = true) :
    let p := (SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)
    SubroutineIteration.TerminatesAt (program a) p (childTime a p) := by
  obtain ⟨i, j, hp⟩ := requested_packet a c m n A hb u hr
  dsimp only
  generalize (SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c) = parent at hp ⊢
  have h := FactorChild.first_halt a
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    m n _ _ _ _ A (by simpa only [pairFst_pair] using hb)
    (FactorChild.decoded_packet a c n i.val j.val hb.dimension)
  constructor
  · intro v hv
    have hv' : v < FactorChild.time a
        (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
      simpa only [childTime, hp] using hv
    simp only [program, Controller.entryProgram, hp]
    exact h.1 v hv'
  · simp only [program, Controller.entryProgram, childTime, hp]
    exact h.2

end LeanCanny.Algebra.Berkowitz.Suspended
