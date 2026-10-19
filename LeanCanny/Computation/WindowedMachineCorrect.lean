/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.WindowedMachineFP

/-!
# Correct windowed machine iteration and verdict extraction

The encoding follows any run whose heads stay within the chosen window;
the number of simulated steps need not fit inside that window. The verdict
reader rewinds only the bounded output head and returns its cell-one bit.
-/

@[expose] public section

namespace LeanCanny.Computation.WindowedMachine
open Complexity

noncomputable def init {k : ℕ} (tm : TM k) (ruler : List Bool → List Bool) (x : List Bool) : List Bool :=
  pair (ruler x) (Cobham.initFn tm (ruler x) x)

theorem init_mem_FP {k : ℕ} (tm : TM k) {ruler : List Bool → List Bool} (hr : ruler ∈ FP) : init tm ruler ∈ FP := by
  have hc : (fun x => Cobham.initFn tm (ruler x) x) ∈ FP :=
    CobhamFP_subset_FP (Cobham.initFn_mem tm (FP_subset_CobhamFP hr) (Cobham.proj 0))
  exact mem_FP_pair hr hc

theorem halt_packet {k : ℕ} (tm : TM k) (W : ℕ) (c : Cfg k tm.Q)
    (hq : Fintype.card tm.Q ≤ Cobham.blockWidth W) :
    halt tm (pair (Cobham.blockRuler W) (Cobham.cfgCode W c)) = decide (tm.halted c) := by
  simp only [halt, block, pairFst_pair, pairSnd_pair, Cobham.state_of_cfgCode W c hq,
    Cobham.stateCode_injective.eq_iff, TM.halted]

theorem iterate_run {k : ℕ} (tm : TM k) (W : ℕ) (x : List Bool)
    (hx : x.length ≤ W) (hq : Fintype.card tm.Q ≤ Cobham.blockWidth W)
    (hheads : ∀ n, ∀ t ∈ Cobham.cfgTapes (TM.runCfg tm (tm.initCfg x) n), t.head ≤ W) (n : ℕ) :
    (advance tm)^[n] (pair (Cobham.blockRuler W) (Cobham.initFn tm (Cobham.blockRuler W) x)) =
      pair (Cobham.blockRuler W) (Cobham.cfgCode W (TM.runCfg tm (tm.initCfg x) n)) := by
  rw [iterate_advance, Cobham.initFn_eq tm W x hx]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, TM.runCfg_succ]
      have hi := TM.runCfg_startInvariant tm x n
      have hinv : ∀ t ∈ Cobham.cfgTapes (TM.runCfg tm (tm.initCfg x) n), t.StartInvariant := by
        intro t ht
        simp only [Cobham.cfgTapes, List.mem_cons, List.mem_ofFn] at ht
        rcases ht with rfl | rfl | ⟨i, rfl⟩
        · exact hi.1
        · exact hi.2.2
        · exact hi.2.1 i
      cases hs : tm.step (TM.runCfg tm (tm.initCfg x) n) with
      | none =>
          rw [Option.getD_none]
          exact Cobham.stepFn_halted tm (TM.step_eq_none_iff_halted.mp hs) hq (hheads n)
      | some c' =>
          rw [Option.getD_some]
          exact Cobham.stepFn_eq tm hs hq (hheads n) hi.2.2 hi.2.1
            (Cobham.stepActs_forall₂ tm _ hinv (hheads n))

theorem iterate_length {k : ℕ} (tm : TM k) (R x : List Bool) (n : ℕ) :
    ((advance tm)^[n] (pair R (Cobham.initFn tm R x))).length ≤ (2 * (k + 2) + 3) * R.length + 2 := by
  rw [iterate_advance, pair_length]
  have h := Cobham.iterate_stepFn_length_le tm R x n
  nlinarith

theorem output_blocks {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ) (c : Cfg k Q) :
    block 3 (pair (Cobham.blockRuler W) (Cobham.cfgCode W c)) ++
      block 4 (pair (Cobham.blockRuler W) (Cobham.cfgCode W c)) = Cobham.pairCode W c.output := by
  have h := Cobham.blockAt_cfgCode_tape W c 1 (by simp)
  change blockAt (Cobham.blockRuler W) (Cobham.cfgCode W c) 3 = padTo (Cobham.blockRuler W) (Cobham.leftCode c.output) ∧
    blockAt (Cobham.blockRuler W) (Cobham.cfgCode W c) 4 = padTo (Cobham.blockRuler W) (Cobham.rightCode c.output W) at h
  simp only [block, pairFst_pair, pairSnd_pair, h.1, h.2, Cobham.pairCode]

theorem answer_packet {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ) (c : Cfg k Q)
    (hW : 1 ≤ W) (hi : c.output.StartInvariant) (hh : c.output.head ≤ W) :
    answer (pair (Cobham.blockRuler W) (Cobham.cfgCode W c)) =
      bitOf (Cobham.symCode (c.output.cells 1)) 1 := by
  unfold answer rewound rewindInit
  simp only [pairFst_pair, pairSnd_pair, iterate_rewindAdvance, output_blocks]
  rw [Cobham.iterate_rewindFn _ hi hh]
  have hb : c.output.head ≤ (Cobham.blockRuler W).length := by
    rw [Cobham.blockRuler_length, Cobham.blockWidth]
    omega
  rw [Cobham.rewound _ hb, Cobham.drop_pairCode_rewound]
  have hbit := Cobham.bitOf_cellsCode c.output (w := W + 1) (j := 1) (o := 1) (by omega) (by decide)
  have hp : 3 < (Cobham.cellsCode c.output 0 (W + 1)).length := by rw [Cobham.cellsCode_length]; omega
  rw [bitOf_eq_getElem (by simpa using hp)] at hbit
  simpa only [List.getElem?_eq_getElem hp, Option.getD_some] using hbit

end LeanCanny.Computation.WindowedMachine
