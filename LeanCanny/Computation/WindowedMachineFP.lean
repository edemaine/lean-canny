/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDecider
public import LeanCanny.Encoding.BracketsFP
public import Complexitylib.Classes.P.Cobham.Internal.Simulate
public import Complexitylib.Classes.P.Iterate
public import Complexitylib.Classes.P.StringAccess

/-!
# FP operations on a windowed machine encoding

A packet retains a ruler and Cobham's fixed-block configuration code. The
transition and halting test are FP on all packets. Reading the verdict first
rewinds the encoded output head for the ruler's length, a polynomial-time
bounded iteration, then reads the encoded cell-one bit.
-/

@[expose] public section

namespace LeanCanny.Computation.WindowedMachine
open Complexity
open LeanCanny.Encoding.Brackets

def block (i : ℕ) (p : List Bool) : List Bool := blockAt (pairFst p) (pairSnd p) i

theorem block_mem_FP (i : ℕ) : block i ∈ FP :=
  CobhamFP_subset_FP (Cobham.blockFn (FP_subset_CobhamFP pairFst_mem_FP)
    (FP_subset_CobhamFP pairSnd_mem_FP) i)

noncomputable def advance {k : ℕ} (tm : TM k) (p : List Bool) : List Bool :=
  pair (pairFst p) (Cobham.stepFn tm (pairFst p) (pairSnd p))

theorem advance_mem_FP {k : ℕ} (tm : TM k) : advance tm ∈ FP := by
  have hs : (fun p => Cobham.stepFn tm (pairFst p) (pairSnd p)) ∈ FP :=
    CobhamFP_subset_FP (Cobham.stepFn_mem tm (FP_subset_CobhamFP pairFst_mem_FP)
    (FP_subset_CobhamFP pairSnd_mem_FP))
  exact mem_FP_pair pairFst_mem_FP hs

theorem iterate_advance {k : ℕ} (tm : TM k) (R z : List Bool) (t : ℕ) :
    (advance tm)^[t] (pair R z) = pair R ((Cobham.stepFn tm R)^[t] z) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, advance, pairFst_pair, pairSnd_pair,
        Function.iterate_succ_apply']

noncomputable def halt {k : ℕ} (tm : TM k) (p : List Bool) : Bool :=
  decide ((block 0 p).take (Fintype.card tm.Q) = Cobham.stateCode tm.qhalt)

theorem halt_mem_FP {k : ℕ} (tm : TM k) : (fun p => [halt tm p]) ∈ FP := by
  have hs := take_mem_FP (block_mem_FP 0) (UnaryFn.const (Fintype.card tm.Q))
  exact (stringEq_fppred hs (constFn_mem_FP (Cobham.stateCode tm.qhalt))).flag_mem_FP

def rewindAdvance (p : List Bool) : List Bool :=
  pair (pairFst p) (Cobham.rewindFn (pairFst p) (pairSnd p))

theorem rewindAdvance_mem_FP : rewindAdvance ∈ FP := by
  have hr : (fun p => Cobham.rewindFn (pairFst p) (pairSnd p)) ∈ FP :=
    CobhamFP_subset_FP (Cobham.rewindFn_mem (FP_subset_CobhamFP pairFst_mem_FP)
    (FP_subset_CobhamFP pairSnd_mem_FP))
  exact mem_FP_pair pairFst_mem_FP hr

theorem iterate_rewindAdvance (R z : List Bool) (t : ℕ) :
    rewindAdvance^[t] (pair R z) = pair R ((Cobham.rewindFn R)^[t] z) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, rewindAdvance, pairFst_pair, pairSnd_pair,
        Function.iterate_succ_apply']

def rewindInit (p : List Bool) : List Bool := pair (pairFst p) (block 3 p ++ block 4 p)

theorem rewindInit_mem_FP : rewindInit ∈ FP :=
  mem_FP_pair pairFst_mem_FP (Cobham.appendFn_mem_FP (block_mem_FP 3) (block_mem_FP 4))

def rewound (p : List Bool) : List Bool :=
  pairSnd (rewindAdvance^[(pairFst p).length] (rewindInit p))

theorem rewind_packet_length (p : List Bool) (t : ℕ) :
    (rewindAdvance^[t] (rewindInit p)).length ≤ 4 * (pairFst p).length + 2 := by
  rw [rewindInit, iterate_rewindAdvance, pair_length]
  have hz : (block 3 p ++ block 4 p).length ≤ 2 * (pairFst p).length := by
    simp only [block, blockAt, List.length_append, List.length_take]
    omega
  have h := Cobham.iterate_rewindFn_length_le (pairFst p) _ hz t
  omega

theorem rewound_mem_FP : rewound ∈ FP := by
  have hb : PolyBound (fun n => 4 * n + 2) := (PolyBound.const 4).mul PolyBound.id |>.add (PolyBound.const 2)
  have hi := iterate_mem_FP_of_polyBound rewindAdvance_mem_FP rewindInit_mem_FP pairFst_mem_FP hb
    (fun p t _ => by have h := rewind_packet_length p t; have hp := pairFst_length_le p; omega)
  exact mem_FP_comp hi pairSnd_mem_FP

def answer (p : List Bool) : Bool := ((rewound p).drop (pairFst p).length)[3]?.getD false

theorem answer_mem_FP : (fun p => [answer p]) ∈ FP := by
  have hd := drop_mem_FP rewound_mem_FP (UnaryFn.length pairFst_mem_FP)
  have h := (FPPred.getBit hd (UnaryFn.const 3)).flag_mem_FP
  refine mem_FP_of_eq (g := fun p => [answer p]) h ?_
  intro p
  simp only [answer]
  cases (((rewound p).drop (pairFst p).length)[3]?.getD false) <;> simp

end LeanCanny.Computation.WindowedMachine
