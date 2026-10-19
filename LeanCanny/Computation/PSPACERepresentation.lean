/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.WindowedMachineCorrect
public import Complexitylib.Classes.Containments.Internal.PolyWindow
public import Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP

/-!
# PSPACE membership supplies a reusable decider certificate

An arbitrary Complexitylib PSPACE machine is encoded in a polynomial-sized
window. Its encoded transition, halting test, and verdict reader are FP. The
configuration-count bound supplies an exponential clock and the first halt
supplies the exact-time protocol. Thus `SpaceDecider` characterizes PSPACE.
-/

@[expose] public section

namespace LeanCanny.Computation
open Complexity

theorem nonempty_spaceDecider_of_mem_PSPACE {L : Language} (hL : L ∈ PSPACE) : Nonempty (SpaceDecider L) := by
  classical
  obtain ⟨k, tm, q, hwin, hdec⟩ := exists_poly_window_of_mem_PSPACE hL
  have hDS : tm.DecidesInSpace L (fun n => q.eval n) := ⟨hwin, hdec⟩
  let W := fun n => n + q.eval n + Fintype.card tm.Q + 2
  let r : Polynomial ℕ := 2 * (Polynomial.X + q + Polynomial.C (Fintype.card tm.Q + 3))
  obtain ⟨u, hu, hlen⟩ := Cobham.exists_exact_ruler r
  let R := fun x => List.replicate (u x).length false
  have hRFP : R ∈ FP := (UnaryFn.length hu).replicate_mem_FP false
  have hR (x : List Bool) : R x = Cobham.blockRuler (W x.length) := by
    simp only [R, Cobham.blockRuler, Cobham.blockWidth, hlen, r, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_C, W]
    congr 1
  have hRlen (x : List Bool) : (R x).length = r.eval x.length := by simp only [R, List.length_replicate, hlen]
  have hx (x : List Bool) : x.length ≤ W x.length := by dsimp only [W]; omega
  have hq (x : List Bool) : Fintype.card tm.Q ≤ Cobham.blockWidth (W x.length) := by
    dsimp only [Cobham.blockWidth, W]
    omega
  have hheads (x : List Bool) (n : ℕ) :
      ∀ t ∈ Cobham.cfgTapes (TM.runCfg tm (tm.initCfg x) n), t.head ≤ W x.length := by
    have hw := hwin x _ (TM.reaches_runCfg tm (tm.initCfg x) n)
    intro t ht
    simp only [Cobham.cfgTapes, List.mem_cons, List.mem_ofFn] at ht
    rcases ht with rfl | rfl | ⟨i, rfl⟩
    · have h := hw.1.2; dsimp only [W]; omega
    · have h := hw.2; dsimp only [W]; omega
    · have h := hw.1.1 i; dsimp only [W]; omega
  have hrun (x : List Bool) (n : ℕ) :
      (WindowedMachine.advance tm)^[n] (WindowedMachine.init tm R x) =
        pair (Cobham.blockRuler (W x.length)) (Cobham.cfgCode (W x.length) (TM.runCfg tm (tm.initCfg x) n)) := by
    simp only [WindowedMachine.init, hR]
    exact WindowedMachine.iterate_run tm (W x.length) x (hx x) (hq x) (hheads x) n
  have hex (x : List Bool) : ∃ n, tm.halted (TM.runCfg tm (tm.initCfg x) n) := by
    obtain ⟨c, hc, hh, _, _⟩ := hdec x
    obtain ⟨n, hn⟩ := TM.exists_reachesIn hc
    exact ⟨n, by rw [TM.runCfg_of_reachesIn tm hn]; exact hh⟩
  let T := fun x => Nat.find (hex x)
  have hbefore (x : List Bool) (n : ℕ) (hn : n < T x) : ¬ tm.halted (TM.runCfg tm (tm.initCfg x) n) :=
    Nat.find_min (hex x) hn
  have hafter (x : List Bool) : tm.halted (TM.runCfg tm (tm.initCfg x) (T x)) := Nat.find_spec (hex x)
  refine ⟨{
    init := WindowedMachine.init tm R
    advance := WindowedMachine.advance tm
    halt := WindowedMachine.halt tm
    answer := WindowedMachine.answer
    initFP := WindowedMachine.init_mem_FP tm hRFP
    advanceFP := WindowedMachine.advance_mem_FP tm
    haltFP := WindowedMachine.halt_mem_FP tm
    answerFP := WindowedMachine.answer_mem_FP
    space := Polynomial.C (2 * (k + 2) + 3) * r + 2
    clock := TM.boundExp tm q
    time := T
    length_le := ?_
    time_le := ?_
    before := ?_
    after := ?_
    correct := ?_ }⟩
  · intro x n _
    have h := WindowedMachine.iterate_length tm (R x) x n
    simpa only [WindowedMachine.init, hRlen, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_ofNat] using h
  · intro x
    exact (TM.halt_time_le hDS x (hbefore x) (hafter x)).le.trans
      (TM.spaceTimeBound_le_two_pow_poly tm (fun n => q.eval n) q (fun _ => le_rfl) x.length)
  · intro x n hn
    rw [hrun, WindowedMachine.halt_packet tm _ _ (hq x)]
    exact decide_eq_false (hbefore x n hn)
  · intro x
    rw [hrun, WindowedMachine.halt_packet tm _ _ (hq x)]
    exact decide_eq_true (hafter x)
  · intro x
    obtain ⟨c, hc, hh, hy, hn⟩ := hdec x
    obtain ⟨n, hreach⟩ := TM.exists_reachesIn hc
    have hrunN : TM.runCfg tm (tm.initCfg x) n = c := TM.runCfg_of_reachesIn tm hreach
    have hT : T x ≤ n := Nat.find_le (by rw [hrunN]; exact hh)
    have hfinal : TM.runCfg tm (tm.initCfg x) (T x) = c := by
      rw [← hrunN, show n = T x + (n - T x) from by omega, TM.runCfg_add,
        TM.runCfg_of_halted tm (hafter x)]
    have hi := (TM.runCfg_startInvariant tm x (T x)).2.2
    have ho := (hwin x _ (TM.reaches_runCfg tm (tm.initCfg x) (T x))).2
    have hW : 1 ≤ W x.length := by dsimp only [W]; omega
    have hhW : (TM.runCfg tm (tm.initCfg x) (T x)).output.head ≤ W x.length := by dsimp only [W]; omega
    rw [hrun, WindowedMachine.answer_packet _ _ hW hi hhW, hfinal]
    by_cases hxL : x ∈ L
    · simp only [hxL, hy hxL, Cobham.symCode, bitOf, List.drop_succ_cons, List.drop_zero, List.headD_cons]
    · simp only [hxL, hn hxL, Cobham.symCode, bitOf, List.drop_succ_cons, List.drop_zero, List.headD_cons,
        Bool.false_eq_true]

noncomputable def SpaceDecider.ofPSPACE {L : Language} (hL : L ∈ PSPACE) : SpaceDecider L :=
  Classical.choice (nonempty_spaceDecider_of_mem_PSPACE hL)

theorem mem_PSPACE_iff_nonempty_spaceDecider (L : Language) : L ∈ PSPACE ↔ Nonempty (SpaceDecider L) :=
  ⟨nonempty_spaceDecider_of_mem_PSPACE, fun ⟨D⟩ => D.mem_PSPACE⟩

end LeanCanny.Computation
