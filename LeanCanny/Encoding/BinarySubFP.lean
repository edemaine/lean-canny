/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryAddFP

/-!
# Polynomial-time binary comparison and truncated subtraction

A width equal to the sum of the input bit lengths accommodates both operands.
Adding the complemented second operand and one produces a carry exactly when
the first operand is at least the second. The remaining low bits are their
difference. All loops run over bit positions, without expanding magnitudes.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat


def complement (w : ℕ) (bits : List Bool) : List Bool :=
  (List.range w).map fun i => !(bits[i]?.getD false)

@[simp] theorem complement_length (w : ℕ) (bits : List Bool) :
    (complement w bits).length = w := by simp [complement]

theorem complement_succ (w : ℕ) (bits : List Bool) :
    complement (w + 1) bits = (!(bits[0]?.getD false)) :: complement w (bits.drop 1) := by
  simp only [complement, List.range_succ_eq_map, List.map_cons, List.map_map, List.getElem?_drop]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.add_comm 1]

theorem complement_value (w : ℕ) (bits : List Bool) :
    Nat.fromBitsLE (complement w bits) + Nat.fromBitsLE (bits.take w) + 1 = 2 ^ w := by
  induction w generalizing bits with
  | zero => simp [complement, Nat.fromBitsLE, Nat.fromBits]
  | succ w ih =>
      rw [complement_succ]
      cases bits with
      | nil =>
          have h := ih []
          simp only [List.getElem?_nil, Option.getD_none, Bool.not_false, List.drop_nil,
            List.take_nil, Nat.fromBitsLE_cons, ↓reduceIte, pow_succ] at *
          change 1 + 2 * Nat.fromBitsLE (complement w []) + 0 + 1 = 2 ^ w * 2
          change Nat.fromBitsLE (complement w []) + 0 + 1 = 2 ^ w at h
          omega
      | cons bit t =>
          have h := ih t
          simp only [List.getElem?_cons_zero, Option.getD_some, List.drop_succ_cons,
            List.drop_zero, List.take_succ_cons, Nat.fromBitsLE_cons, pow_succ]
          cases bit <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte] <;> omega

theorem complement_mem_FP {bits : List Bool → List Bool} {w : List Bool → ℕ}
    (hbits : bits ∈ FP) (hw : UnaryFn w) :
    (fun z => complement (w z) (bits z)) ∈ FP := by
  have hp := (FPPred.getBit (mem_FP_comp pairFst_mem_FP hbits) UnaryFn.index).not
  refine bitwise_mem_FP hw hp.flag_mem_FP (fun z i => ?_)
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Function.comp_apply]
  cases (bits z)[i]?.getD false <;> simp

theorem value_take_add_drop (bits : List Bool) (w : ℕ) :
    Nat.fromBitsLE (bits.take w) + 2 ^ w * Nat.fromBitsLE (bits.drop w) = Nat.fromBitsLE bits := by
  induction w generalizing bits with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | succ w ih =>
      cases bits with
      | nil => simp [Nat.fromBitsLE, Nat.fromBits]
      | cons bit t =>
          have h := ih t
          simp only [List.take_succ_cons, List.drop_succ_cons, Nat.fromBitsLE_cons, pow_succ]
          cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

theorem value_take (bits : List Bool) (w : ℕ) :
    Nat.fromBitsLE (bits.take w) = Nat.fromBitsLE bits % 2 ^ w := by
  have hl : Nat.fromBitsLE (bits.take w) < 2 ^ w :=
    (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by simp))
  rw [← value_take_add_drop bits w]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hl]

def subWidth (packet : List Bool) : ℕ := (pairFst packet).length + (pairSnd packet).length

def subSum (packet : List Bool) : List Bool :=
  add (pair (pairFst packet) (increment (complement (subWidth packet) (pairSnd packet))))

theorem subWidth_unary : UnaryFn subWidth :=
  (UnaryFn.length pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP)

theorem subSum_mem_FP : subSum ∈ FP := by
  have hc := complement_mem_FP pairSnd_mem_FP subWidth_unary
  have hi := mem_FP_comp hc increment_mem_FP
  have h := mem_FP_comp (mem_FP_pair pairFst_mem_FP hi) add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem subSum_spec (packet : List Bool) :
    Nat.fromBitsLE (subSum packet) + Nat.fromBitsLE (pairSnd packet) =
      2 ^ subWidth packet + Nat.fromBitsLE (pairFst packet) := by
  have hc := complement_value (subWidth packet) (pairSnd packet)
  have hb : (pairSnd packet).length ≤ subWidth packet := by unfold subWidth; omega
  rw [List.take_of_length_le hb] at hc
  simp only [subSum, add_pair, Nat.fromBitsLE_bits, increment_value]
  omega

theorem subSum_length (packet : List Bool) :
    (subSum packet).length = (Nat.fromBitsLE (subSum packet)).size := by
  simp only [subSum, add_pair, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]

theorem subSum_carry_iff (packet : List Bool) :
    subWidth packet < (subSum packet).length ↔
      Nat.fromBitsLE (pairSnd packet) ≤ Nat.fromBitsLE (pairFst packet) := by
  rw [subSum_length, Nat.lt_size]
  have h := subSum_spec packet
  omega

theorem ge_fppred : FPPred fun packet =>
    Nat.fromBitsLE (pairSnd packet) ≤ Nat.fromBitsLE (pairFst packet) :=
  (FPPred.lt subWidth_unary (UnaryFn.length subSum_mem_FP)).of_iff subSum_carry_iff

theorem le_fppred {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred fun z => Nat.fromBitsLE (a z) ≤ Nat.fromBitsLE (b z) := by
  have h := ge_fppred.comp (mem_FP_pair hb ha)
  exact h.of_iff (fun z => by simp only [pairFst_pair, pairSnd_pair])

/-- Numeric equality also accepts noncanonical binary words. -/
theorem eq_fppred {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred fun z => Nat.fromBitsLE (a z) = Nat.fromBitsLE (b z) :=
  .of_computable (Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq
    Turing.MultiTapeTM.encNat |>.comp
      ((fromBitsLE_computable.comp (FP.computable ha)).prod
        (fromBitsLE_computable.comp (FP.computable hb))))
    fun _ => decide_eq_true_iff.symm

theorem eq_const_fppred {a : List Bool → List Bool} (ha : a ∈ FP) (k : ℕ) :
    FPPred fun z => Nat.fromBitsLE (a z) = k := by
  simpa only [Nat.fromBitsLE_bits] using eq_fppred ha (constFn_mem_FP k.bits)

theorem lt_fppred {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred fun z => Nat.fromBitsLE (a z) < Nat.fromBitsLE (b z) :=
  (le_fppred hb ha).not.of_iff (fun _ => by omega)

def sub (packet : List Bool) : List Bool :=
  if subWidth packet < (subSum packet).length then
    normalize ((subSum packet).take (subWidth packet))
  else []

theorem sub_eq_bits (packet : List Bool) : sub packet =
    (Nat.fromBitsLE (pairFst packet) - Nat.fromBitsLE (pairSnd packet)).bits := by
  have hs := subSum_spec packet
  have ha : Nat.fromBitsLE (pairFst packet) < 2 ^ subWidth packet :=
    (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by unfold subWidth; omega))
  by_cases hge : Nat.fromBitsLE (pairSnd packet) ≤ Nat.fromBitsLE (pairFst packet)
  · have hc := (subSum_carry_iff packet).mpr hge
    rw [sub, ite_eq_left hc, normalize_eq_bits, value_take]
    have hd : Nat.fromBitsLE (pairFst packet) - Nat.fromBitsLE (pairSnd packet) <
        2 ^ subWidth packet := (Nat.sub_le _ _).trans_lt ha
    have he : Nat.fromBitsLE (subSum packet) = 2 ^ subWidth packet +
        (Nat.fromBitsLE (pairFst packet) - Nat.fromBitsLE (pairSnd packet)) := by omega
    simp [he, Nat.mod_eq_of_lt hd]
  · have hc : ¬ subWidth packet < (subSum packet).length := by
      rwa [subSum_carry_iff]
    simp only [sub, ite_eq_right hc, Nat.sub_eq_zero_of_le (by omega :
      Nat.fromBitsLE (pairFst packet) ≤ Nat.fromBitsLE (pairSnd packet)), Nat.zero_bits]

@[simp] theorem sub_pair (a b : List Bool) :
    sub (pair a b) = (Nat.fromBitsLE a - Nat.fromBitsLE b).bits := by
  simp only [sub_eq_bits, pairFst_pair, pairSnd_pair]

theorem sub_mem_FP : sub ∈ FP := by
  have htake := take_mem_FP subSum_mem_FP subWidth_unary
  have hnorm := mem_FP_comp htake normalize_mem_FP
  have h := (FPPred.lt subWidth_unary (UnaryFn.length subSum_mem_FP)).ite_mem_FP
    hnorm (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

end LeanCanny.Encoding.BinaryNat
