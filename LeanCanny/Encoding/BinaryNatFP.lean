/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BracketsFP
public import LeanCanny.Encoding.BinaryNatCode

/-!
# Polynomial-time control arithmetic on binary natural numbers

Every operation acts on bit lists, without converting a magnitude to a unary
string. The certificates use the native verified bounded folds and therefore
establish its machine-level `FP`. Normalization removes redundant high zeroes;
the arithmetic specifications cover arbitrary little-endian words.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat

open Brackets

@[simp] theorem bits_eq_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    exact BinaryNatCode.encode_injective (show BinaryNatCode.encode n = BinaryNatCode.encode 0 from h)
  · rintro rfl
    rfl

def normalize : List Bool → List Bool
  | [] => []
  | true :: t => true :: normalize t
  | false :: t => if normalize t = [] then [] else false :: normalize t

theorem normalize_length_le (bits : List Bool) : (normalize bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | false => simp only [normalize, List.length_cons]; split_ifs <;> simp_all
      | true => simp only [normalize, List.length_cons]; omega

theorem normalize_eq_bits (bits : List Bool) : normalize bits = (Nat.fromBitsLE bits).bits := by
  induction bits with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | false =>
          simp only [normalize, ih, bits_eq_nil_iff, Nat.fromBitsLE_cons,
            Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          by_cases ht : Nat.fromBitsLE t = 0
          · simp [ht]
          · simp only [ht, ↓reduceIte, Nat.bit0_bits _ ht]
      | true =>
          simp only [normalize, ih, Nat.fromBitsLE_cons, ↓reduceIte]
          rw [Nat.add_comm 1, Nat.bit1_bits]

@[simp] theorem normalize_bits (n : ℕ) : normalize n.bits = n.bits := by
  rw [normalize_eq_bits, Nat.fromBitsLE_bits]

theorem normalize_mem_FP : normalize ∈ FP := by
  have hprev := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hempty := stringEq_fppred hprev (constFn_mem_FP [])
  have hfalse := hempty.ite_mem_FP (constFn_mem_FP [])
    (mem_FP_comp hprev (cons_mem_FP false))
  have htrue := mem_FP_comp hprev (cons_mem_FP true)
  refine recFold_mem_FP_of_bound (g := fun _ t => normalize t)
    hfalse htrue (constFn_mem_FP []) (constFn_mem_FP []) id_mem_FP
    (bound := id) ?_ ?_ ?_ PolyBound.id ?_
  · intro z; rfl
  · intro z t; simp only [normalize, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t; simp only [normalize, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t ht; exact (normalize_length_le t).trans ht.length_le

def increment : List Bool → List Bool
  | [] => [true]
  | false :: t => true :: t
  | true :: t => false :: increment t

theorem increment_length_le (bits : List Bool) :
    (increment bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => decide
  | cons b t ih => cases b <;> simp_all [increment]

theorem increment_value (bits : List Bool) :
    Nat.fromBitsLE (increment bits) = Nat.fromBitsLE bits + 1 := by
  induction bits with
  | nil => rfl
  | cons b t ih => cases b <;> simp only [increment, Nat.fromBitsLE_cons,
      Bool.false_eq_true, ↓reduceIte, ih] <;> omega

theorem increment_mem_FP : increment ∈ FP := by
  have hprev := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hfalse := mem_FP_comp pairSnd_mem_FP (cons_mem_FP true)
  have htrue := mem_FP_comp hprev (cons_mem_FP false)
  refine recFold_mem_FP_of_bound (g := fun _ t => increment t)
    hfalse htrue (constFn_mem_FP [true]) (constFn_mem_FP []) id_mem_FP
    (bound := fun n => n + 1) ?_ ?_ ?_ (PolyBound.id.add (PolyBound.const 1)) ?_
  · intro z; rfl
  · intro z t; simp only [increment, pairSnd_pair, Function.comp_apply]
  · intro z t; simp only [increment, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t ht; exact (increment_length_le t).trans (Nat.add_le_add_right ht.length_le 1)

def succ (bits : List Bool) : List Bool := normalize (increment bits)

theorem succ_eq_bits (bits : List Bool) :
    succ bits = (Nat.fromBitsLE bits + 1).bits := by rw [succ, normalize_eq_bits, increment_value]

theorem succ_mem_FP : succ ∈ FP := mem_FP_comp increment_mem_FP normalize_mem_FP

def decrement : List Bool → List Bool
  | [] => []
  | true :: t => false :: t
  | false :: t => if normalize t = [] then [] else true :: decrement t

theorem decrement_length_le (bits : List Bool) : (decrement bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | false => simp only [decrement, List.length_cons]; split_ifs <;> simp_all
      | true => simp only [decrement, List.length_cons]; exact le_rfl

theorem decrement_value (bits : List Bool) :
    Nat.fromBitsLE (decrement bits) = Nat.fromBitsLE bits - 1 := by
  induction bits with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | true => simp only [decrement, Nat.fromBitsLE_cons, Bool.false_eq_true, ↓reduceIte]; omega
      | false =>
          simp only [decrement, normalize_eq_bits, bits_eq_nil_iff]
          split_ifs with hz
          · simp only [Nat.fromBitsLE_cons, Bool.false_eq_true, ↓reduceIte, hz,
              mul_zero, Nat.zero_add, Nat.zero_sub]
            rfl
          · simp only [Nat.fromBitsLE_cons, Bool.false_eq_true, ↓reduceIte, ih]
            omega

theorem decrement_mem_FP : decrement ∈ FP := by
  have hprev := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hnormalized := mem_FP_comp pairSnd_mem_FP normalize_mem_FP
  have hempty := stringEq_fppred hnormalized (constFn_mem_FP [])
  have hfalse := hempty.ite_mem_FP (constFn_mem_FP [])
    (mem_FP_comp hprev (cons_mem_FP true))
  have htrue := mem_FP_comp pairSnd_mem_FP (cons_mem_FP false)
  refine recFold_mem_FP_of_bound (g := fun _ t => decrement t)
    hfalse htrue (constFn_mem_FP []) (constFn_mem_FP []) id_mem_FP
    (bound := id) ?_ ?_ ?_ PolyBound.id ?_
  · intro z; rfl
  · intro z t; simp only [decrement, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t; simp only [decrement, pairSnd_pair, Function.comp_apply]
  · intro z t ht; exact (decrement_length_le t).trans ht.length_le

def pred (bits : List Bool) : List Bool := normalize (decrement bits)

theorem pred_eq_bits (bits : List Bool) :
    pred bits = (Nat.fromBitsLE bits - 1).bits := by rw [pred, normalize_eq_bits, decrement_value]

theorem pred_mem_FP : pred ∈ FP := mem_FP_comp decrement_mem_FP normalize_mem_FP

theorem drop_one_value (bits : List Bool) :
    Nat.fromBitsLE (bits.drop 1) = Nat.fromBitsLE bits / 2 := by
  cases bits with
  | nil => rfl
  | cons b t => cases b <;> simp only [List.drop_succ_cons, List.drop_zero,
      Nat.fromBitsLE_cons, Bool.false_eq_true, ↓reduceIte] <;> omega

def half (bits : List Bool) : List Bool := normalize (bits.drop 1)

theorem half_eq_bits (bits : List Bool) : half bits = (Nat.fromBitsLE bits / 2).bits := by
  rw [half, normalize_eq_bits, drop_one_value]

theorem half_mem_FP : half ∈ FP :=
  mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) normalize_mem_FP

def upperHalf (bits : List Bool) : List Bool :=
  if bits[0]?.getD false then succ (bits.drop 1) else half bits

theorem upperHalf_eq_bits (bits : List Bool) :
    upperHalf bits = (Nat.fromBitsLE bits - Nat.fromBitsLE bits / 2).bits := by
  cases bits with
  | nil => rfl
  | cons b t =>
      cases b <;> simp only [upperHalf, List.getElem?_cons_zero, Option.getD_some,
        Bool.false_eq_true, ↓reduceIte, succ_eq_bits, half_eq_bits, List.drop_succ_cons,
        List.drop_zero, Nat.fromBitsLE_cons]
      all_goals congr 1; omega

theorem upperHalf_mem_FP : upperHalf ∈ FP := by
  have hdrop := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have hs := mem_FP_comp hdrop succ_mem_FP
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP hs half_mem_FP
  refine mem_FP_of_eq h (fun bits => ?_)
  simp only [upperHalf, Function.comp_apply, id_eq]

theorem canonical_fppred : FPPred fun bits => ∃ n : ℕ, bits = BinaryNatCode.encode n := by
  refine (stringEq_fppred normalize_mem_FP id_mem_FP).of_iff fun bits => ?_
  constructor
  · intro h
    exact ⟨Nat.fromBitsLE bits, h.symm.trans (normalize_eq_bits bits)⟩
  · rintro ⟨n, rfl⟩
    exact normalize_bits n

end LeanCanny.Encoding.BinaryNat
