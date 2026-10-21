/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerController

/-!
# Correctness of the context-carrying power controller

The callback contract specifies the dimension, scalar constants, entry access,
and multiply-accumulate for one context. The bitstring controller simulates every
typed transition and therefore inherits the computed result and state bounds.
The modular specialization supplies all scalar callbacks from the certified
binary arithmetic, leaving dimension/modulus extraction and entry access explicit.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.Controller

open LeanCanny.Encoding

variable {R : Type*} [Semiring R] {n : ℕ}

structure CorrectAt (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) : Prop where
  dimension : ops.dimension c = BinaryNatCode.encode n
  zero : ops.zero c = enc 0
  one : ops.one c = enc 1
  entry : ∀ i j, ops.entry (pair c
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = enc (A i j)
  combine : ∀ acc lhs rhs, ops.combine (pair c (pair (enc acc) (pair (enc lhs) (enc rhs)))) =
    enc (acc + lhs * rhs)

@[simp] theorem code_eq_nil (k : ℕ) : BinaryNatCode.encode k = [] ↔ k = 0 :=
  BinaryNat.bits_eq_nil_iff k

@[simp] theorem code_eq_one (k : ℕ) : BinaryNatCode.encode k = [true] ↔ k = 1 := by
  change BinaryNatCode.encode k = BinaryNatCode.encode 1 ↔ k = 1
  exact BinaryNatCode.encode_injective.eq_iff

@[simp] theorem code_fin_eq (i j : Fin n) :
    BinaryNatCode.encode i.val = BinaryNatCode.encode j.val ↔ i = j := by
  rw [BinaryNatCode.encode_injective.eq_iff, Fin.val_inj]

@[simp] theorem pred_code (k : ℕ) :
    BinaryNat.pred (BinaryNatCode.encode k) = BinaryNatCode.encode (k - 1) := by
  simp only [BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

@[simp] theorem height_queryBits (q : Query n) :
    QueryBits.height (queryBits q) = BinaryNatCode.encode q.height := by
  simp [QueryBits.height, queryBits]

@[simp] theorem exponent_queryBits (q : Query n) :
    QueryBits.exponent (queryBits q) = BinaryNatCode.encode q.exponent := by
  simp [QueryBits.exponent, queryBits]

@[simp] theorem row_queryBits (q : Query n) :
    QueryBits.row (queryBits q) = BinaryNatCode.encode q.row.val := by
  simp [QueryBits.row, queryBits]

@[simp] theorem col_queryBits (q : Query n) :
    QueryBits.col (queryBits q) = BinaryNatCode.encode q.col.val := by
  simp [QueryBits.col, queryBits]

theorem evalNext_packet (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (q : Query n) (s : List (Frame R n)) :
    evalNext ops (pair c (stateBits enc (.eval q s))) =
      stateBits enc (MatrixPower.step A (.eval q s)) := by
  simp only [evalNext, payload, stack, body, pairFst_pair, pairSnd_pair, stateBits,
    List.drop_succ_cons, List.drop_zero, exponent_queryBits, height_queryBits,
    row_queryBits, col_queryBits, code_eq_nil, code_eq_one, code_fin_eq,
    hc.dimension, hc.zero, hc.one, hc.entry, pred_code]
  by_cases he0 : q.exponent = 0
  · simp only [he0, ↓reduceIte, retBits, MatrixPower.step, apply_ite]
  by_cases he1 : q.exponent = 1
  · simp only [he1, Nat.one_ne_zero, ↓reduceIte, retBits, MatrixPower.step]
  by_cases hh : q.height = 0
  · simp only [he0, he1, hh, ↓reduceIte, retBits, MatrixPower.step]
  · have hk : BinaryNatCode.encode (n - 1) = BinaryNatCode.encode q.last.val := rfl
    rw [hk, QueryBits.childLeft_queryBits]
    simp only [he0, he1, hh, ↓reduceIte, evalBits, pushBits, leftBits,
      MatrixPower.step, stackBits, frameBits]

omit [Semiring R] in
theorem returnLeft_packet (c : List Bool) (enc : R → List Bool)
    (x acc : R) (q : Query n) (k : Fin n) (s : List (Frame R n)) :
    returnLeft (pair c (stateBits enc (.ret x (.left q k acc :: s)))) =
      stateBits enc (.eval (q.right k) (.right q k acc x :: s)) := by
  simp [returnLeft, parent, pivot, scalars, fields, frameBody, top, rest, payload, stack, body,
    stateBits, stackBits, frameBits, QueryBits.childRight_queryBits, evalBits, pushBits, rightBits]

theorem returnRight_packet (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (x acc lhs : R) (q : Query n) (k : Fin n) (s : List (Frame R n)) :
    returnRight ops (pair c (stateBits enc (.ret x (.right q k acc lhs :: s)))) =
      stateBits enc (MatrixPower.step A (.ret x (.right q k acc lhs :: s))) := by
  simp only [returnRight, parent, pivot, scalars, fields, frameBody, top, rest, payload, stack, body,
    stateBits, stackBits, frameBits, pairFst_pair, pairSnd_pair, List.drop_succ_cons, List.drop_zero,
    hc.combine, code_eq_nil, pred_code]
  by_cases hk : k.val = 0
  · simp only [hk, ↓reduceIte, retBits, MatrixPower.step]
  · let next : Fin n := ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hn : BinaryNatCode.encode (k.val - 1) = BinaryNatCode.encode next.val := rfl
    rw [hn, QueryBits.childLeft_queryBits]
    simp only [hk, ↓reduceIte, evalBits, pushBits, leftBits, MatrixPower.step,
      stackBits, frameBits, next]

theorem step_packet (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (s : State R n) : step ops (pair c (stateBits enc s)) =
      pair c (stateBits enc (MatrixPower.step A s)) := by
  cases s with
  | eval q s =>
      simp only [step, nextState, pairFst_pair, pairSnd_pair, stateBits,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.false_eq_true,
        ↓reduceIte]
      exact congrArg (pair c) (evalNext_packet ops c A enc hc q s)
  | ret x s =>
      cases s with
      | nil => simp [step, nextState, returnNext, payload, stack, body, stateBits, stackBits,
          doneBits, MatrixPower.step]
      | cons f s =>
          cases f with
          | left q k acc =>
              simp only [step, nextState, returnNext, top, stack, body, pairFst_pair, pairSnd_pair,
                stateBits, stackBits, frameBits, List.drop_succ_cons, List.drop_zero,
                List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                Bool.false_eq_true, ↓reduceIte]
              exact congrArg (pair c) (returnLeft_packet c enc x acc q k s)
          | right q k acc lhs =>
              simp only [step, nextState, returnNext, top, stack, body, pairFst_pair, pairSnd_pair,
                stateBits, stackBits, frameBits, List.drop_succ_cons, List.drop_zero,
                List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                Bool.false_eq_true, ↓reduceIte]
              exact congrArg (pair c) (returnRight_packet ops c A enc hc x acc lhs q k s)
  | done x => simp [step, nextState, stateBits, MatrixPower.step]

theorem iterate_packet (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (t : ℕ) (s : State R n) :
    (step ops)^[t] (pair c (stateBits enc s)) = pair c (stateBits enc ((MatrixPower.step A)^[t] s)) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_packet ops c A enc hc,
      Function.iterate_succ_apply']

theorem run_pow (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (e : ℕ) (i j : Fin n) :
    (step ops)^[work n e.size e + 1] (pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ []))) =
      pair c (stateBits (n := n) enc (.done ((A ^ e) i j))) := by
  rw [iterate_packet ops c A enc hc, MatrixPower.run_pow]

omit [Semiring R] in
theorem initialPacket_encode (exponent row col : List Bool → List Bool) (c : List Bool)
    (enc : R → List Bool) (e : ℕ) (i j : Fin n)
    (he : exponent c = BinaryNatCode.encode e)
    (hi : row c = BinaryNatCode.encode i.val) (hj : col c = BinaryNatCode.encode j.val) :
    initialPacket exponent row col c = pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])) := by
  simp only [initialPacket, he, hi, hj, QueryBits.initial_queryBits, evalBits, stateBits, stackBits]

theorem run_initialPacket (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (exponent row col : List Bool → List Bool) (e : ℕ) (i j : Fin n)
    (he : exponent c = BinaryNatCode.encode e)
    (hi : row c = BinaryNatCode.encode i.val) (hj : col c = BinaryNatCode.encode j.val) :
    (step ops)^[work n e.size e + 1] (initialPacket exponent row col c) =
      pair c (stateBits (n := n) enc (.done ((A ^ e) i j))) := by
  rw [initialPacket_encode exponent row col c enc e i j he hi hj, run_pow ops c A enc hc]

def modularCallbacks (dimension modulus entry : List Bool → List Bool) : Callbacks where
  dimension := dimension
  zero := ArithmeticBits.zero
  one := fun c => ArithmeticBits.one (modulus c)
  entry := entry
  combine := fun p => ArithmeticBits.combine (pair (modulus (pairFst p)) (pairSnd p))

theorem modularCallbacks_polyTime {dimension modulus entry : List Bool → List Bool}
    (hd : dimension ∈ FP) (hm : modulus ∈ FP) (he : entry ∈ FP) :
    (modularCallbacks dimension modulus entry).PolyTime := by
  have hone := mem_FP_comp hm ArithmeticBits.one_mem_FP
  refine ⟨hd, ArithmeticBits.zero_mem_FP, hone, he, ?_⟩
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hm) pairSnd_mem_FP)
    ArithmeticBits.combine_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem modularCallbacks_correctAt (dimension modulus entry : List Bool → List Bool)
    (c : List Bool) (m : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hd : dimension c = BinaryNatCode.encode n) (hm : modulus c = BinaryNatCode.encode m)
    (he : ∀ i j, entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (A i j)) :
    CorrectAt (modularCallbacks dimension modulus entry) c A residueBits := by
  refine ⟨hd, ?_, ?_, he, ?_⟩
  · exact ArithmeticBits.zero_residueBits m
  · simpa only [modularCallbacks, hm] using ArithmeticBits.one_residueBits m
  · intro acc lhs rhs
    simpa only [modularCallbacks, pairFst_pair, pairSnd_pair, hm] using
      ArithmeticBits.combine_residueBits m acc lhs rhs

theorem modular_run_length_le (dimension modulus entry : List Bool → List Bool)
    (c : List Bool) (m : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : CorrectAt (modularCallbacks dimension modulus entry) c A residueBits)
    (e t : ℕ) (i j : Fin n) :
    ((step (modularCallbacks dimension modulus entry))^[t]
      (pair c (stateBits (residueBits (m := m)) (.eval ⟨e.size, e, i, j⟩ [])))).length ≤
        2 * c.length + 2 + 64 * (n.size + e.size + m.size + 1) ^ 2 := by
  rw [iterate_packet _ c A residueBits hc, pair_length]
  exact Nat.add_le_add_left (run_residueBits_quadratic m A e t i j) _

end LeanCanny.Algebra.MatrixPower.Controller
