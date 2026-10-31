/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeIteration
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Polynomial-time lookup in growing lists of short words

Prepending a word places the old list in the second pair field, so its
encoding grows linearly. Lookup clips a binary index to the literal input
length and is total even for malformed encodings.
-/

@[expose] public section
namespace LeanCanny.Encoding.WordList
set_option backward.isDefEq.respectTransparency false

def encode : List (List Bool) → List Bool
  | [] => []
  | w :: ws => pair w (encode ws)

theorem count_le_length (ws : List (List Bool)) : ws.length ≤ (encode ws).length := by
  induction ws with
  | nil => exact le_rfl
  | cons w ws ih => simp only [encode, pair_length, List.length_cons]; omega

theorem length_le (ws : List (List Bool)) (B : ℕ) (h : ∀ w ∈ ws, w.length ≤ B) :
    (encode ws).length ≤ (2 * B + 2) * ws.length := by
  induction ws with
  | nil => simp only [encode, List.length_nil, Nat.mul_zero, le_refl]
  | cons w ws ih =>
    have HW := h w (List.mem_cons_self)
    have HT := ih (fun v hv => h v (List.mem_cons_of_mem w hv))
    simp only [encode, pair_length, List.length_cons, Nat.mul_succ]
    omega

theorem tail_iterate (ws : List (List Bool)) (n : ℕ) :
    pairSnd^[n] (encode ws) = encode (ws.drop n) := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil => simpa only [encode, List.drop_nil, show pairSnd ([] : List Bool) = [] from rfl] using ih []
    | cons w ws => rw [encode, pairSnd_pair, ih]; rfl

theorem head_encode (ws : List (List Bool)) : pairFst (encode ws) = ws.headD [] := by
  cases ws with
  | nil => rfl
  | cons w ws => exact pairFst_pair _ _

theorem tail_iterate_length (code : List Bool) (n : ℕ) : (pairSnd^[n] code).length ≤ code.length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (pairSnd_length_le _).trans ih

def get (code : List Bool) (i : ℕ) : List Bool := pairFst (pairSnd^[min i code.length] code)
def reader (q : List Bool) : List Bool := get (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem headD_drop (ws : List (List Bool)) (i : ℕ) : (ws.drop i).headD [] = (ws[i]?).getD [] := by
  induction i generalizing ws with
  | zero => cases ws <;> rfl
  | succ i ih => cases ws with
    | nil => rfl
    | cons w ws => exact ih ws

theorem get_encode (ws : List (List Bool)) (i : ℕ) : get (encode ws) i = (ws[i]?).getD [] := by
  unfold get
  rw [tail_iterate, head_encode]
  by_cases hi : i ≤ (encode ws).length
  · rw [min_eq_left hi]
    exact headD_drop ws i
  · have HI : (encode ws).length ≤ i := by omega
    have HW := count_le_length ws
    rw [min_eq_right HI, List.drop_eq_nil_of_le HW]
    rw [← headD_drop, List.drop_eq_nil_of_le (HW.trans HI)]

theorem reader_packet (code : List Bool) (i : ℕ) :
    reader (pair code (BinaryNatCode.encode i)) = get code i := by
  simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem reader_FP : reader ∈ FP := by
  let count := fun q : List Bool => min (Nat.fromBitsLE (pairSnd q)) (pairFst q).length
  have HC : UnaryFn count := UnaryFn.fromBitsLE_min pairSnd_mem_FP (UnaryFn.length pairFst_mem_FP)
  have E := iterate_mem_FP pairSnd_mem_FP pairFst_mem_FP (HC.replicate_mem_FP false) pairFst_mem_FP
    (by intro q n _hn; exact tail_iterate_length (pairFst q) n)
  refine mem_FP_of_eq (mem_FP_comp E pairFst_mem_FP) (fun q => ?_)
  simp only [Function.comp_apply, List.length_replicate, reader, get, count]

end LeanCanny.Encoding.WordList
