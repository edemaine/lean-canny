/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductWork
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing
import Mathlib.Tactic.Linarith

/-!
# Binary state bounds for balanced product bits

The continuation tail is the undoubled right field of each self-delimiting pair.
Stack encoding therefore grows linearly in depth. Correct reachable carries,
query bounds, and the stack-depth invariant give a quadratic bound in root
height and the selected index's binary length. FP execution is separate.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct
open Complexity

def queryBits (q : Query) : List Bool :=
  pair (BinaryNatCode.encode q.height) (pair (BinaryNatCode.encode q.node) (BinaryNatCode.encode q.index))

def frameBits : Frame → List Bool
  | .left q t acc => false :: pair (queryBits q) (pair (BinaryNatCode.encode t) (BinaryNatCode.encode acc))
  | .right q t acc b => true :: b :: pair (queryBits q) (pair (BinaryNatCode.encode t) (BinaryNatCode.encode acc))

def stackBits : List Frame → List Bool
  | [] => []
  | f :: stack => true :: pair (frameBits f) (stackBits stack)

def stateBits : State → List Bool
  | .eval q stack => false :: false :: pair (queryBits q) (stackBits stack)
  | .scan q t acc stack => false :: true :: pair (queryBits q)
      (pair (BinaryNatCode.encode t) (pair (BinaryNatCode.encode acc) (stackBits stack)))
  | .ret b stack => true :: false :: b :: stackBits stack
  | .done b => [true, true, b]

def queryBitBound (H K : ℕ) : ℕ := 2 * H.size + 2 * H + K.size + 4
def frameBitBound (H K : ℕ) : ℕ :=
  2 * queryBitBound H K + 2 * (limit K).size + (2 * (K + 1)).size + 6
def stateBitBound (H K : ℕ) : ℕ :=
  2 * queryBitBound H K + 2 * (limit K).size + 2 * (2 * (K + 1)).size + 8 + H * (2 * frameBitBound H K + 3)

theorem queryBits_length_le (H K : ℕ) (q : Query) (hq : QueryFits H K q) :
    (queryBits q).length ≤ queryBitBound H K := by
  have hh := Nat.size_le_size hq.1
  have hn := query_node_size hq
  have hk := query_index_size hq
  simp only [queryBits, pair_length, BinaryNatCode.length_encode, queryBitBound]
  omega

theorem carry_le (a : ℕ → ℕ) (q : Query) (t K : ℕ) (hk : q.index ≤ K) : q.carry a t ≤ 2 * (K + 1) := by
  exact (BinarySum.carryValue_le (count q.index) (q.terms a) t).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hk 1))

theorem stack_acc_bound (a : ℕ → ℕ) (out : Bool) (K : ℕ) (stack : List Frame) (b : Bool)
    (hc : StackCorrect a out stack b) (hi : ∀ f ∈ stack, f.parent.index ≤ K) :
    ∀ f ∈ stack, f.accumulator ≤ 2 * (K + 1) := by
  induction stack generalizing b with
  | nil => simp
  | cons f stack ih =>
    cases f with
    | left q t acc =>
      obtain ⟨_, _, ha, ht⟩ := hc
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · change acc ≤ 2 * (K + 1)
        rw [ha]
        exact carry_le a q t K (hi _ List.mem_cons_self)
      · exact ih (q.value a) ht (fun f hf => hi f (List.mem_cons_of_mem _ hf)) g hg
    | right q t acc lhs =>
      obtain ⟨_, _, _, ha, ht⟩ := hc
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · change acc ≤ 2 * (K + 1)
        rw [ha]
        exact carry_le a q t K (hi _ List.mem_cons_self)
      · exact ih (q.value a) ht (fun f hf => hi f (List.mem_cons_of_mem _ hf)) g hg

theorem frameBits_length_le (H K : ℕ) (f : Frame) (hq : QueryFits H K f.parent)
    (ht : Active f.parent f.time) (ha : f.accumulator ≤ 2 * (K + 1)) :
    (frameBits f).length ≤ frameBitBound H K := by
  have htime : f.time ≤ limit K := ht.2.1.le.trans (limit_mono hq.2.1)
  have hts := Nat.size_le_size htime
  have has := Nat.size_le_size ha
  have hqs := queryBits_length_le H K f.parent hq
  cases f <;>
    simp only [frameBits, List.length_cons, pair_length, BinaryNatCode.length_encode, frameBitBound,
      Frame.parent, Frame.time, Frame.accumulator] at * <;> omega

theorem stackBits_length_le (F : ℕ) (stack : List Frame) (hf : ∀ f ∈ stack, (frameBits f).length ≤ F) :
    (stackBits stack).length ≤ stack.length * (2 * F + 3) := by
  induction stack with
  | nil => simp [stackBits]
  | cons f stack ih =>
    have hh := hf f List.mem_cons_self
    have ht := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg))
    simp only [stackBits, List.length_cons, pair_length]
    nlinarith

theorem stackBits_length_of_correct (a : ℕ → ℕ) (out : Bool) (H K h : ℕ) (stack : List Frame) (b : Bool)
    (hf : StackFits H K h stack) (hc : StackCorrect a out stack b) :
    (stackBits stack).length ≤ H * (2 * frameBitBound H K + 3) := by
  have ha := stack_acc_bound a out K stack b hc (fun f hmem => (hf.parents f hmem).1.2.1)
  have he := stackBits_length_le (frameBitBound H K) stack (fun f hmem =>
    frameBits_length_le H K f (hf.parents f hmem).1 (hf.parents f hmem).2 (ha f hmem))
  have hlen : stack.length ≤ H := by have := hf.length_le; omega
  exact he.trans (Nat.mul_le_mul_right _ hlen)

theorem stateBits_length_le (a : ℕ → ℕ) (out : Bool) (H K : ℕ) (s : State)
    (hf : Fits H K s) (hc : Correct a out s) : (stateBits s).length ≤ stateBitBound H K := by
  cases s with
  | eval q stack =>
    obtain ⟨hq, hs⟩ := hf
    have hqbits := queryBits_length_le H K q hq
    have hsb := stackBits_length_of_correct a out H K _ stack _ hs hc
    simp only [stateBits, List.length_cons, pair_length, stateBitBound]
    omega
  | scan q t acc stack =>
    obtain ⟨hq, _, ht, hs⟩ := hf
    obtain ⟨_, _, ha, hc⟩ := hc
    have hqbits := queryBits_length_le H K q hq
    have hsb := stackBits_length_of_correct a out H K _ stack _ hs hc
    have hts := Nat.size_le_size (ht.trans (limit_mono hq.2.1))
    have has := Nat.size_le_size (ha ▸ carry_le a q t K hq.2.1)
    simp only [stateBits, List.length_cons, pair_length, BinaryNatCode.length_encode, stateBitBound]
    omega
  | ret b stack =>
    have hsb := stackBits_length_of_correct a out H K 0 stack b hf hc
    simp only [stateBits, List.length_cons, stateBitBound]
    omega
  | done b => simp only [stateBits, List.length_cons, List.length_nil, stateBitBound]; omega

theorem stateBitBound_poly (H K : ℕ) : stateBitBound H K ≤ 128 * (H + K.size + 1) ^ 2 := by
  let S := H + K.size + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hh : H.size ≤ H := Nat.size_le.mpr Nat.lt_two_pow_self
  have hT : (limit K).size ≤ 2 * K.size + 5 := by
    have he := limit_base_bound K
    exact Nat.size_le.mpr (by omega)
  have hA : (2 * (K + 1)).size ≤ K.size + 2 := by
    have hk : K + 1 ≤ 2 ^ K.size := by have := Nat.lt_size_self K; omega
    have he : 2 * (K + 1) ≤ 2 ^ (K.size + 1) := by rw [pow_succ]; omega
    simpa only [Nat.size_pow] using Nat.size_le_size he
  have hq : queryBitBound H K ≤ 6 * S := by unfold queryBitBound; dsimp [S]; omega
  have hf : frameBitBound H K ≤ 35 * S := by unfold frameBitBound; dsimp [S] at *; omega
  have hb : 2 * queryBitBound H K + 2 * (limit K).size + 2 * (2 * (K + 1)).size + 8 ≤ 40 * S := by
    dsimp [S] at *
    omega
  have hm := Nat.mul_le_mul (show H ≤ S by dsimp [S]; omega)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hf) 3)
  have hs2 : S ≤ S ^ 2 := by have := Nat.mul_le_mul_left S hS; nlinarith
  change stateBitBound H K ≤ 128 * S ^ 2
  unfold stateBitBound
  nlinarith

theorem run_stateBits_length_le (a : ℕ → ℕ) (H K t : ℕ) :
    (stateBits ((step a)^[t] (start H K))).length ≤ 128 * (H + K.size + 1) ^ 2 := by
  apply (stateBits_length_le a ((tree a H 0).testBit K) H K _
    (iterate_fits a H K _ (start_fits H K) t)
    (iterate_correct a _ _ (start_correct a H K) t)).trans
  exact stateBitBound_poly H K

end LeanCanny.Algebra.BalancedProduct
