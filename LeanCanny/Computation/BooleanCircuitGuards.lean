/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BooleanCircuitValues
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Native conjunction of a source circuit with nonzero guards

Three slots per guard test an atom, negate it, and conjoin the result with the
previous output. Original wires retain their indices. The guard count is unary
bounded, while every gate address is read in binary.
-/

@[expose] public section
namespace LeanCanny.Computation.BooleanCircuitGuards
open LeanCanny.Encoding BooleanCircuitSpace

def index (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q)
def delta (F : Family) (q : List Bool) : ℕ := index q - F.count (pairFst q)

def extend (F : Family) (checks : List Bool → ℕ) : Family where
  count c := F.count c + 3 * checks c
  tag q := if index q < F.count (pairFst q) then F.tag q
    else if delta F q % 3 = 0 then 2 else if delta F q % 3 = 1 then 3 else 4
  left q := if index q < F.count (pairFst q) then F.left q
    else if delta F q % 3 = 2 then index q - 3 else index q - 1
  right q := if index q < F.count (pairFst q) then F.right q else index q - 1

theorem access (F : Family) (A : Access F) (checks : List Bool → ℕ) (hc : UnaryFn checks) : Access (extend F checks) := by
  have hi : BinaryFn index := BinaryFn.fromBits pairSnd_mem_FP
  have hn : BinaryFn (fun q => F.count (pairFst q)) := (BinaryFn.ofUnary A.count).comp pairFst_mem_FP
  have hd : BinaryFn (delta F) := hi.sub hn
  have hr := hd.mod (BinaryFn.const 3)
  exact ⟨A.count.add ((UnaryFn.const 3).mul hc),
    BinaryFn.ite (hi.lt hn) A.tag (BinaryFn.ite (hr.eq (BinaryFn.const 0)) (BinaryFn.const 2)
      (BinaryFn.ite (hr.eq (BinaryFn.const 1)) (BinaryFn.const 3) (BinaryFn.const 4))),
    BinaryFn.ite (hi.lt hn) A.left (BinaryFn.ite (hr.eq (BinaryFn.const 2)) (hi.sub (BinaryFn.const 3)) (hi.sub (BinaryFn.const 1))),
    BinaryFn.ite (hi.lt hn) A.right (hi.sub (BinaryFn.const 1))⟩

private theorem op_atom (a l r : Bool) : operation 2 a l r = a := by cases a <;> cases l <;> cases r <;> decide
private theorem op_not (a l r : Bool) : operation 3 a l r = !l := by cases a <;> cases l <;> cases r <;> decide
private theorem op_and (a l r : Bool) : operation 4 a l r = (l && r) := by cases a <;> cases l <;> cases r <;> decide

theorem values_original (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool)
    (n : ℕ) (hn : n ≤ F.count c) : values (extend F checks) atom c n = values F atom c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : n < F.count c := by omega
    simp only [values, ih (by omega)]
    simp only [extend, index, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi, ite_true]

theorem wire_original (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool)
    (i : ℕ) (hi : i < F.count c) : wireValue (extend F checks) atom c i = wireValue F atom c i := by
  unfold wireValue
  rw [values_original F checks atom c (i + 1) (by omega)]

theorem atom_tag (F : Family) (checks : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    (extend F checks).tag (pair c (BinaryNatCode.encode (F.count c + 3 * i))) = 2 := by
  simp only [extend, index, delta, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> omega

theorem not_metadata (F : Family) (checks : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    (extend F checks).tag (pair c (BinaryNatCode.encode (F.count c + 3 * i + 1))) = 3 ∧
    (extend F checks).left (pair c (BinaryNatCode.encode (F.count c + 3 * i + 1))) = F.count c + 3 * i := by
  simp only [extend, index, delta, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> omega

theorem and_metadata (F : Family) (checks : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    (extend F checks).tag (pair c (BinaryNatCode.encode (F.count c + 3 * i + 2))) = 4 ∧
    (extend F checks).left (pair c (BinaryNatCode.encode (F.count c + 3 * i + 2))) = F.count c + 3 * i - 1 ∧
    (extend F checks).right (pair c (BinaryNatCode.encode (F.count c + 3 * i + 2))) = F.count c + 3 * i + 1 := by
  simp only [extend, index, delta, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> omega

theorem guard_wire (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool) (i : ℕ) :
    wireValue (extend F checks) atom c (F.count c + 3 * i + 1) =
      !atom (pair c (BinaryNatCode.encode (F.count c + 3 * i))) := by
  rw [wireValue_step, (not_metadata F checks c i).1, (not_metadata F checks c i).2, op_not,
    read_wire _ _ _ _ _ (by omega), wireValue_step, atom_tag, op_atom]

def stage (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool) (m : ℕ) : Bool :=
  if m = 0 then value F atom c else wireValue (extend F checks) atom c (F.count c + 3 * m - 1)

theorem stage_succ (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool)
    (hpos : 0 < F.count c) (m : ℕ) :
    stage F checks atom c (m + 1) = (stage F checks atom c m &&
      !atom (pair c (BinaryNatCode.encode (F.count c + 3 * m)))) := by
  have hi : F.count c + 3 * (m + 1) - 1 = F.count c + 3 * m + 2 := by omega
  simp only [stage, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, hi]
  rw [wireValue_step, (and_metadata F checks c m).1, (and_metadata F checks c m).2.1,
    (and_metadata F checks c m).2.2, op_and, read_wire _ _ _ _ _ (by omega),
    read_wire _ _ _ _ _ (by omega), guard_wire]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.mul_zero, Nat.add_zero, ite_true]
    rw [wire_original F checks atom c _ (by omega), ← value_eq_wireValue F atom c hpos]
  · simp only [hm, ite_false]

theorem stage_true (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool)
    (hpos : 0 < F.count c) (m : ℕ) :
    stage F checks atom c m = true ↔ value F atom c = true ∧
      ∀ i, i < m → atom (pair c (BinaryNatCode.encode (F.count c + 3 * i))) = false := by
  induction m with
  | zero => simp [stage]
  | succ m ih =>
    rw [stage_succ F checks atom c hpos m, Bool.and_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨⟨hs, hall⟩, hm⟩
      refine ⟨hs, fun i hi => ?_⟩
      by_cases he : i = m
      · simpa only [he] using hm
      · exact hall i (by omega)
    · rintro ⟨hs, hall⟩
      exact ⟨⟨hs, fun i hi => hall i (by omega)⟩, hall m (by omega)⟩

theorem value_true (F : Family) (checks : List Bool → ℕ) (atom : List Bool → Bool) (c : List Bool)
    (hpos : 0 < F.count c) :
    value (extend F checks) atom c = true ↔ value F atom c = true ∧
      ∀ i, i < checks c → atom (pair c (BinaryNatCode.encode (F.count c + 3 * i))) = false := by
  have he : value (extend F checks) atom c = stage F checks atom c (checks c) := by
    rw [value_eq_wireValue _ _ _ (by change 0 < F.count c + 3 * checks c; omega)]
    have hcount : (extend F checks).count c = F.count c + 3 * checks c := rfl
    by_cases hc : checks c = 0
    · simp only [stage, hc, ite_true, hcount, Nat.mul_zero, Nat.add_zero]
      rw [wire_original F checks atom c _ (by omega), ← value_eq_wireValue F atom c hpos]
    · simp only [stage, hc, ite_false, hcount]
  rw [he, stage_true F checks atom c hpos]

end LeanCanny.Computation.BooleanCircuitGuards
