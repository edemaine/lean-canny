/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductController

/-!
# Exact simulation by the binary product controller

The callback contract specifies only leaf bits at one context. Every encoded
transition simulates its typed counterpart, including zero-height trees,
completed scans, both frame kinds, and the terminal state.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct.Controller

open LeanCanny.Encoding

@[simp] theorem height_queryBits (q : Query) :
    QueryBits.height (queryBits q) = BinaryNatCode.encode q.height := by simp [QueryBits.height, queryBits]
@[simp] theorem node_queryBits (q : Query) :
    QueryBits.node (queryBits q) = BinaryNatCode.encode q.node := by simp [QueryBits.node, queryBits]
@[simp] theorem index_queryBits (q : Query) :
    QueryBits.index (queryBits q) = BinaryNatCode.encode q.index := by simp [QueryBits.index, queryBits]
@[simp] theorem code_eq_nil (n : ℕ) : BinaryNatCode.encode n = [] ↔ n = 0 := BinaryNat.bits_eq_nil_iff n
@[simp] theorem code_value (n : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode n) = n := Nat.fromBitsLE_bits n
@[simp] theorem succ_code (n : ℕ) : BinaryNat.succ (BinaryNatCode.encode n) = BinaryNatCode.encode (n + 1) := by
  simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
@[simp] theorem half_code (n : ℕ) : BinaryNat.half (BinaryNatCode.encode n) = BinaryNatCode.encode (n / 2) := by
  simp only [BinaryNat.half_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem code_head (n : ℕ) : (BinaryNatCode.encode n)[0]?.getD false = decide (n % 2 = 1) := by
  have h (bits : List Bool) : bits[0]?.getD false = decide (Nat.fromBitsLE bits % 2 = 1) := by
    cases bits with
    | nil => rfl
    | cons b tail => cases b <;> simp [Nat.fromBitsLE_cons, Nat.add_mod]
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using h n.bits

theorem queryLimit_queryBits (q : Query) : queryLimit (queryBits q) = BinaryNatCode.encode (limit q.index) := by
  simp only [queryLimit, index_queryBits, QueryBits.width_queryBits, BinaryNat.add_pair,
    BinaryNat.mul_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, limit, count]

theorem evalNext_packet (leaf : List Bool → List Bool) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (leaf (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (q : Query) (s : List Frame) :
    evalNext leaf (pair c (stateBits (.eval q s))) = stateBits (BalancedProduct.step a (.eval q s)) := by
  simp only [evalNext, query, evalStack, body, stateBits, pairFst_pair, pairSnd_pair,
    List.drop_succ_cons, List.drop_zero, height_queryBits, code_eq_nil]
  by_cases hh : q.height = 0
  · simp only [hh, ↓reduceIte, leafQuery, query, body, pairFst_pair, pairSnd_pair,
      List.drop_succ_cons, List.drop_zero, node_queryBits, index_queryBits,
      retBits, putBit, hl, BalancedProduct.step]
  · simp only [hh, ↓reduceIte, scanBits, BalancedProduct.step, BinaryNatCode.encode]
    rfl

theorem scanNext_packet (c : List Bool) (a : ℕ → ℕ) (q : Query) (t acc : ℕ) (s : List Frame) :
    scanNext (pair c (stateBits (.scan q t acc s))) =
      stateBits (BalancedProduct.step a (.scan q t acc s)) := by
  simp only [scanNext, query, scanTime, scanAcc, scanStack, evalStack, body, stateBits,
    pairFst_pair, pairSnd_pair, List.drop_succ_cons, List.drop_zero, queryLimit_queryBits,
    QueryBits.coordinate_packet, index_queryBits, succ_code, half_code, code_value]
  by_cases hend : limit q.index ≤ t
  · simp only [hend, ↓reduceIte, BalancedProduct.step, retBits, putBit, code_head]
  · by_cases hi : position q.index t < count q.index
    · simp only [hend, show q.index + 1 = count q.index from rfl, hi, ↓reduceIte, BalancedProduct.step,
        QueryBits.childLeft_queryBits, evalBits, pushBits, leftBits, stackBits, frameBits]
    · simp only [hend, show q.index + 1 = count q.index from rfl, hi, ↓reduceIte,
        BalancedProduct.step, scanBits]

theorem returnLeft_packet (c : List Bool) (q : Query) (t acc : ℕ) (x : Bool) (s : List Frame) :
    returnLeft (pair c (stateBits (.ret x (.left q t acc :: s)))) =
      stateBits (.eval (q.right t) (.right q t acc x :: s)) := by
  simp [returnLeft, parent, frameTime, frameAcc, frameBody, top, rest, retStack, body,
    stateBits, stackBits, frameBits, QueryBits.childRight_queryBits, evalBits, pushBits, rightBits, putBit]

theorem addContribution_packet (c : List Bool) (q : Query) (t acc : ℕ) (x lhs : Bool) (s : List Frame) :
    addContribution (pair c (stateBits (.ret x (.right q t acc lhs :: s)))) =
      BinaryNatCode.encode (acc + contribution q t lhs x) := by
  simp only [addContribution, selector, parent, frameTime, frameAcc, frameBody, top, retStack, body,
    stateBits, stackBits, frameBits, pairFst_pair, pairSnd_pair, List.drop_succ_cons, List.drop_zero,
    List.getElem?_cons_zero, Option.getD_some, ↓reduceIte, QueryBits.coordinate_packet,
    succ_code, code_value]
  cases lhs <;> cases x <;> by_cases hi : position q.index t ≤ column q.index t <;>
    simp [contribution, hi]

theorem returnRight_packet (c : List Bool) (q : Query) (t acc : ℕ) (x lhs : Bool) (s : List Frame) :
    returnRight (pair c (stateBits (.ret x (.right q t acc lhs :: s)))) =
      stateBits (.scan q (t + 1) (acc + contribution q t lhs x) s) := by
  rw [returnRight, addContribution_packet]
  simp [parent, frameTime, frameBody, top, rest, retStack, stateBits, stackBits, frameBits,
    succ_code, scanBits]

theorem step_packet (leaf : List Bool → List Bool) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (leaf (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (s : State) :
    step leaf (pair c (stateBits s)) = pair c (stateBits (BalancedProduct.step a s)) := by
  cases s with
  | eval q s =>
    simp only [step, nextState, pairFst_pair, pairSnd_pair, stateBits,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (pair c) (evalNext_packet leaf c a hl q s)
  | scan q t acc s =>
    simp only [step, nextState, pairFst_pair, pairSnd_pair, stateBits,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (pair c) (scanNext_packet c a q t acc s)
  | ret x s =>
    cases s with
    | nil => simp [step, nextState, returnNext, retStack, body, stateBits, stackBits,
        doneBits, putBit, BalancedProduct.step]
    | cons f s =>
      cases f with
      | left q t acc =>
        simp only [step, nextState, returnNext, top, retStack, pairFst_pair, pairSnd_pair,
          stateBits, stackBits, frameBits, List.drop_succ_cons, List.drop_zero,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          Bool.false_eq_true, List.cons_ne_nil, ↓reduceIte]
        exact congrArg (pair c) (returnLeft_packet c q t acc x s)
      | right q t acc lhs =>
        simp only [step, nextState, returnNext, top, retStack, pairFst_pair, pairSnd_pair,
          stateBits, stackBits, frameBits, List.drop_succ_cons, List.drop_zero,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          Bool.false_eq_true, List.cons_ne_nil, ↓reduceIte]
        exact congrArg (pair c) (returnRight_packet c q t acc x lhs s)
  | done x => simp [step, nextState, stateBits, BalancedProduct.step]

theorem iterate_packet (leaf : List Bool → List Bool) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (leaf (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (t : ℕ) (s : State) :
    (step leaf)^[t] (pair c (stateBits s)) = pair c (stateBits ((BalancedProduct.step a)^[t] s)) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_packet leaf c a hl, Function.iterate_succ_apply']

theorem initialPacket_encode (count index : List Bool → List Bool) (c : List Bool) :
    initialPacket count index c = pair c (stateBits (start (count c).length (Nat.fromBitsLE (index c)))) := by
  simp only [initialPacket, QueryBits.initial_queryBits, start, stateBits, stackBits, evalBits]

theorem run_length_le (leaf : List Bool → List Bool) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (leaf (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (H K t : ℕ) :
    ((step leaf)^[t] (pair c (stateBits (start H K)))).length ≤
      2 * c.length + 2 + 128 * (H + K.size + 1) ^ 2 := by
  rw [iterate_packet leaf c a hl, pair_length]
  exact Nat.add_le_add_left (run_stateBits_length_le a H K t) _

end LeanCanny.Algebra.BalancedProduct.Controller
